import V185TrunkScan23Chunk0740

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4381296 : List Nat := [2, 1, 1, 1, 8, 1, 2, 1, 1, 2, 3]
def baseStart_4381296 : Nat := 118140960795 + 4381296 * 2 ^ 59
def prefixEnd_4381296 : Nat := 4983230072969 + 3 ^ 40 * 4381296 * 2
def baseEnd_4381296 : Nat := 2249710737621195392950793

theorem tailTrace_4381296 : CollatzResearch.WordTrace tailWord_4381296 prefixEnd_4381296 2249710737621195392950793 := by
  unfold tailWord_4381296
  simp only [CollatzResearch.WordTrace]
  refine ⟨79899496567660166314713871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106532662090213555086285161 79899496567660166314713871)
  ·
    refine ⟨119849244851490249472070807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79899496567660166314713871 119849244851490249472070807)
    ·
      refine ⟨179773867277235374208106211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119849244851490249472070807 179773867277235374208106211)
      ·
        refine ⟨269660800915853061312159317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179773867277235374208106211 269660800915853061312159317)
        ·
          refine ⟨3160087510732653062251867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 269660800915853061312159317 3160087510732653062251867)
          ·
            refine ⟨4740131266098979593377801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3160087510732653062251867 4740131266098979593377801)
            ·
              refine ⟨3555098449574234695033351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4740131266098979593377801 3555098449574234695033351)
              ·
                refine ⟨5332647674361352042550027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3555098449574234695033351 5332647674361352042550027)
                ·
                  refine ⟨7998971511542028063825041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5332647674361352042550027 7998971511542028063825041)
                  ·
                    refine ⟨5999228633656521047868781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7998971511542028063825041 5999228633656521047868781)
                    ·
                      refine ⟨2249710737621195392950793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5999228633656521047868781 2249710737621195392950793)
                      ·
                        rfl

theorem cell23_4381296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 2, 1, 1, 2, 3].length) (baseStart_4381296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381296 prefixEnd_4381296 := by exact prefixLift 4381296
  have htrace : WordTrace (prefixWord ++ tailWord_4381296) baseStart_4381296 baseEnd_4381296 := by
    simpa [prefixWord, tailWord_4381296, baseEnd_4381296] using wordTrace_append hprefix tailTrace_4381296
  have hstable : (prefixWord ++ tailWord_4381296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381296).length < 2 ^ (prefixWord ++ tailWord_4381296).sum := by decide
  have hdescent : baseEnd_4381296 < baseStart_4381296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381308 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 2, 6]
def baseStart_4381308 : Nat := 118140960795 + 4381308 * 2 ^ 59
def prefixEnd_4381308 : Nat := 4983230072969 + 3 ^ 40 * 4381308 * 2
def baseEnd_4381308 : Nat := 749905633129683115333579

theorem tailTrace_4381308 : CollatzResearch.WordTrace tailWord_4381308 prefixEnd_4381308 749905633129683115333579 := by
  unfold tailWord_4381308
  simp only [CollatzResearch.WordTrace]
  refine ⟨79899715405638429339432289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106532953874184572452576385 79899715405638429339432289)
  ·
    refine ⟨59924786554228822004574217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79899715405638429339432289 59924786554228822004574217)
    ·
      refine ⟨44943589915671616503430663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59924786554228822004574217 44943589915671616503430663)
      ·
        refine ⟨67415384873507424755145995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44943589915671616503430663 67415384873507424755145995)
        ·
          refine ⟨101123077310261137132718993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67415384873507424755145995 101123077310261137132718993)
          ·
            refine ⟨75842307982695852849539245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101123077310261137132718993 75842307982695852849539245)
            ·
              refine ⟨28440865493510944818577217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75842307982695852849539245 28440865493510944818577217)
              ·
                refine ⟨21330649120133208613932913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28440865493510944818577217 21330649120133208613932913)
                ·
                  refine ⟨15997986840099906460449685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21330649120133208613932913 15997986840099906460449685)
                  ·
                    refine ⟨749905633129683115333579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15997986840099906460449685 749905633129683115333579)
                    ·
                      rfl

theorem cell23_4381308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_4381308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381308 prefixEnd_4381308 := by exact prefixLift 4381308
  have htrace : WordTrace (prefixWord ++ tailWord_4381308) baseStart_4381308 baseEnd_4381308 := by
    simpa [prefixWord, tailWord_4381308, baseEnd_4381308] using wordTrace_append hprefix tailTrace_4381308
  have hstable : (prefixWord ++ tailWord_4381308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381308).length < 2 ^ (prefixWord ++ tailWord_4381308).sum := by decide
  have hdescent : baseEnd_4381308 < baseStart_4381308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381315 : List Nat := [1, 1, 1, 3, 3, 1, 2, 2, 3, 4, 2]
def baseStart_4381315 : Nat := 118140960795 + 4381315 * 2 ^ 59
def prefixEnd_4381315 : Nat := 4983230072969 + 3 ^ 40 * 4381315 * 2
def baseEnd_4381315 : Nat := 2249720493753630818613205

theorem tailTrace_4381315 : CollatzResearch.WordTrace tailWord_4381315 prefixEnd_4381315 2249720493753630818613205 := by
  unfold tailWord_4381315
  simp only [CollatzResearch.WordTrace]
  refine ⟨159799686122251498874369399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106533124081500999249579599 159799686122251498874369399)
  ·
    refine ⟨239699529183377248311554099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159799686122251498874369399 239699529183377248311554099)
    ·
      refine ⟨359549293775065872467331149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239699529183377248311554099 359549293775065872467331149)
      ·
        refine ⟨134830985165649702175249181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 359549293775065872467331149 134830985165649702175249181)
        ·
          refine ⟨50561619437118638315718443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134830985165649702175249181 50561619437118638315718443)
          ·
            refine ⟨75842429155677957473577665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50561619437118638315718443 75842429155677957473577665)
            ·
              refine ⟨56881821866758468105183249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75842429155677957473577665 56881821866758468105183249)
              ·
                refine ⟨42661366400068851078887437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56881821866758468105183249 42661366400068851078887437)
                ·
                  refine ⟨15998012400025819154582789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42661366400068851078887437 15998012400025819154582789)
                  ·
                    refine ⟨2999627325004841091484273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15998012400025819154582789 2999627325004841091484273)
                    ·
                      refine ⟨2249720493753630818613205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2999627325004841091484273 2249720493753630818613205)
                      ·
                        rfl

theorem cell23_4381315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 2, 3, 4, 2].length) (baseStart_4381315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381315 prefixEnd_4381315 := by exact prefixLift 4381315
  have htrace : WordTrace (prefixWord ++ tailWord_4381315) baseStart_4381315 baseEnd_4381315 := by
    simpa [prefixWord, tailWord_4381315, baseEnd_4381315] using wordTrace_append hprefix tailTrace_4381315
  have hstable : (prefixWord ++ tailWord_4381315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381315).length < 2 ^ (prefixWord ++ tailWord_4381315).sum := by decide
  have hdescent : baseEnd_4381315 < baseStart_4381315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381422 : List Nat := [4, 1, 2, 1, 1, 3, 2, 2, 2, 1, 4]
def baseStart_4381422 : Nat := 118140960795 + 4381422 * 2 ^ 59
def prefixEnd_4381422 : Nat := 4983230072969 + 3 ^ 40 * 4381422 * 2
def baseEnd_4381422 : Nat := 2249775436183661899975213

theorem tailTrace_4381422 : CollatzResearch.WordTrace tailWord_4381422 prefixEnd_4381422 2249775436183661899975213 := by
  unfold tailWord_4381422
  simp only [CollatzResearch.WordTrace]
  refine ⟨19975448591607982018564315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106535725821909237432343013 19975448591607982018564315)
  ·
    refine ⟨29963172887411973027846473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19975448591607982018564315 29963172887411973027846473)
    ·
      refine ⟨22472379665558979770884855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29963172887411973027846473 22472379665558979770884855)
      ·
        refine ⟨33708569498338469656327283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22472379665558979770884855 33708569498338469656327283)
        ·
          refine ⟨50562854247507704484490925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33708569498338469656327283 50562854247507704484490925)
          ·
            refine ⟨18961070342815389181684097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50562854247507704484490925 18961070342815389181684097)
            ·
              refine ⟨14220802757111541886263073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18961070342815389181684097 14220802757111541886263073)
              ·
                refine ⟨10665602067833656414697305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14220802757111541886263073 10665602067833656414697305)
                ·
                  refine ⟨7999201550875242311022979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10665602067833656414697305 7999201550875242311022979)
                  ·
                    refine ⟨11998802326312863466534469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7999201550875242311022979 11998802326312863466534469)
                    ·
                      refine ⟨2249775436183661899975213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11998802326312863466534469 2249775436183661899975213)
                      ·
                        rfl

theorem cell23_4381422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 2, 2, 2, 1, 4].length) (baseStart_4381422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381422 prefixEnd_4381422 := by exact prefixLift 4381422
  have htrace : WordTrace (prefixWord ++ tailWord_4381422) baseStart_4381422 baseEnd_4381422 := by
    simpa [prefixWord, tailWord_4381422, baseEnd_4381422] using wordTrace_append hprefix tailTrace_4381422
  have hstable : (prefixWord ++ tailWord_4381422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381422).length < 2 ^ (prefixWord ++ tailWord_4381422).sum := by decide
  have hdescent : baseEnd_4381422 < baseStart_4381422 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381489 : List Nat := [1, 2, 2, 3, 2, 1, 4, 1, 3, 1, 3]
def baseStart_4381489 : Nat := 118140960795 + 4381489 * 2 ^ 59
def prefixEnd_4381489 : Nat := 4983230072969 + 3 ^ 40 * 4381489 * 2
def baseEnd_4381489 : Nat := 2249809839387513137837405

theorem tailTrace_4381489 : CollatzResearch.WordTrace tailWord_4381489 prefixEnd_4381489 2249809839387513137837405 := by
  unfold tailWord_4381489
  simp only [CollatzResearch.WordTrace]
  refine ⟨159806032423621126591203521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106537354949080751060802347 159806032423621126591203521)
  ·
    refine ⟨119854524317715844943402641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159806032423621126591203521 119854524317715844943402641)
    ·
      refine ⟨89890893238286883707551981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119854524317715844943402641 89890893238286883707551981)
      ·
        refine ⟨33709084964357581390331993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89890893238286883707551981 33709084964357581390331993)
        ·
          refine ⟨25281813723268186042748995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33709084964357581390331993 25281813723268186042748995)
          ·
            refine ⟨37922720584902279064123493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25281813723268186042748995 37922720584902279064123493)
            ·
              refine ⟨7110510109669177324523155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37922720584902279064123493 7110510109669177324523155)
              ·
                refine ⟨10665765164503765986784733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7110510109669177324523155 10665765164503765986784733)
                ·
                  refine ⟨3999661936688912245044275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10665765164503765986784733 3999661936688912245044275)
                  ·
                    refine ⟨5999492905033368367566413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3999661936688912245044275 5999492905033368367566413)
                    ·
                      refine ⟨2249809839387513137837405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5999492905033368367566413 2249809839387513137837405)
                      ·
                        rfl

theorem cell23_4381489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 4, 1, 3, 1, 3].length) (baseStart_4381489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381489 prefixEnd_4381489 := by exact prefixLift 4381489
  have htrace : WordTrace (prefixWord ++ tailWord_4381489) baseStart_4381489 baseEnd_4381489 := by
    simpa [prefixWord, tailWord_4381489, baseEnd_4381489] using wordTrace_append hprefix tailTrace_4381489
  have hstable : (prefixWord ++ tailWord_4381489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381489).length < 2 ^ (prefixWord ++ tailWord_4381489).sum := by decide
  have hdescent : baseEnd_4381489 < baseStart_4381489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381512 : List Nat := [2, 1, 3, 1, 1, 3, 1, 1, 2, 6, 2]
def baseStart_4381512 : Nat := 118140960795 + 4381512 * 2 ^ 59
def prefixEnd_4381512 : Nat := 4983230072969 + 3 ^ 40 * 4381512 * 2
def baseEnd_4381512 : Nat := 2249821649442566547849799

theorem tailTrace_4381512 : CollatzResearch.WordTrace tailWord_4381512 prefixEnd_4381512 2249821649442566547849799 := by
  unfold tailWord_4381512
  simp only [CollatzResearch.WordTrace]
  refine ⟨79903435651268900759645395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106537914201691867679527193 79903435651268900759645395)
  ·
    refine ⟨119855153476903351139468093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79903435651268900759645395 119855153476903351139468093)
    ·
      refine ⟨44945682553838756677300535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119855153476903351139468093 44945682553838756677300535)
      ·
        refine ⟨67418523830758135015950803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44945682553838756677300535 67418523830758135015950803)
        ·
          refine ⟨101127785746137202523926205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67418523830758135015950803 101127785746137202523926205)
          ·
            refine ⟨37922919654801450946472327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101127785746137202523926205 37922919654801450946472327)
            ·
              refine ⟨56884379482202176419708491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37922919654801450946472327 56884379482202176419708491)
              ·
                refine ⟨85326569223303264629562737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56884379482202176419708491 85326569223303264629562737)
                ·
                  refine ⟨63994926917477448472172053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85326569223303264629562737 63994926917477448472172053)
                  ·
                    refine ⟨2999762199256755397133065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 63994926917477448472172053 2999762199256755397133065)
                    ·
                      refine ⟨2249821649442566547849799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2999762199256755397133065 2249821649442566547849799)
                      ·
                        rfl

theorem cell23_4381512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 1, 2, 6, 2].length) (baseStart_4381512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381512 prefixEnd_4381512 := by exact prefixLift 4381512
  have htrace : WordTrace (prefixWord ++ tailWord_4381512) baseStart_4381512 baseEnd_4381512 := by
    simpa [prefixWord, tailWord_4381512, baseEnd_4381512] using wordTrace_append hprefix tailTrace_4381512
  have hstable : (prefixWord ++ tailWord_4381512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381512).length < 2 ^ (prefixWord ++ tailWord_4381512).sum := by decide
  have hdescent : baseEnd_4381512 < baseStart_4381512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381515 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 3]
def baseStart_4381515 : Nat := 118140960795 + 4381515 * 2 ^ 59
def prefixEnd_4381515 : Nat := 4983230072969 + 3 ^ 40 * 4381515 * 2
def baseEnd_4381515 : Nat := 2249823189884530036112285

theorem tailTrace_4381515 : CollatzResearch.WordTrace tailWord_4381515 prefixEnd_4381515 2249823189884530036112285 := by
  unfold tailWord_4381515
  simp only [CollatzResearch.WordTrace]
  refine ⟨159806980721526933031649999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106537987147684622021099999 159806980721526933031649999)
  ·
    refine ⟨239710471082290399547474999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159806980721526933031649999 239710471082290399547474999)
    ·
      refine ⟨359565706623435599321212499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239710471082290399547474999 359565706623435599321212499)
      ·
        refine ⟨539348559935153398981818749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359565706623435599321212499 539348559935153398981818749)
        ·
          refine ⟨202255709975682524618182031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 539348559935153398981818749 202255709975682524618182031)
          ·
            refine ⟨303383564963523786927273047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202255709975682524618182031 303383564963523786927273047)
            ·
              refine ⟨455075347445285680390909571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303383564963523786927273047 455075347445285680390909571)
              ·
                refine ⟨682613021167928520586364357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455075347445285680390909571 682613021167928520586364357)
                ·
                  refine ⟨127989941468986597609943317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 682613021167928520586364357 127989941468986597609943317)
                  ·
                    refine ⟨5999528506358746762966093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 127989941468986597609943317 5999528506358746762966093)
                    ·
                      refine ⟨2249823189884530036112285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5999528506358746762966093 2249823189884530036112285)
                      ·
                        rfl

theorem cell23_4381515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 4, 6, 3].length) (baseStart_4381515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381515 prefixEnd_4381515 := by exact prefixLift 4381515
  have htrace : WordTrace (prefixWord ++ tailWord_4381515) baseStart_4381515 baseEnd_4381515 := by
    simpa [prefixWord, tailWord_4381515, baseEnd_4381515] using wordTrace_append hprefix tailTrace_4381515
  have hstable : (prefixWord ++ tailWord_4381515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381515).length < 2 ^ (prefixWord ++ tailWord_4381515).sum := by decide
  have hdescent : baseEnd_4381515 < baseStart_4381515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381522 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 6, 4]
def baseStart_4381522 : Nat := 118140960795 + 4381522 * 2 ^ 59
def prefixEnd_4381522 : Nat := 4983230072969 + 3 ^ 40 * 4381522 * 2
def baseEnd_4381522 : Nat := 749942261416370502908251

theorem tailTrace_4381522 : CollatzResearch.WordTrace tailWord_4381522 prefixEnd_4381522 749942261416370502908251 := by
  unfold tailWord_4381522
  simp only [CollatzResearch.WordTrace]
  refine ⟨39951809008125393306788705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106538157355001048818103213 39951809008125393306788705)
  ·
    refine ⟨29963856756094044980091529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39951809008125393306788705 29963856756094044980091529)
    ·
      refine ⟨22472892567070533735068647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29963856756094044980091529 22472892567070533735068647)
      ·
        refine ⟨33709338850605800602602971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22472892567070533735068647 33709338850605800602602971)
        ·
          refine ⟨50564008275908700903904457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33709338850605800602602971 50564008275908700903904457)
          ·
            refine ⟨37923006206931525677928343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50564008275908700903904457 37923006206931525677928343)
            ·
              refine ⟨56884509310397288516892515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37923006206931525677928343 56884509310397288516892515)
              ·
                refine ⟨85326763965595932775338773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56884509310397288516892515 85326763965595932775338773)
                ·
                  refine ⟨3999692060887309348844005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85326763965595932775338773 3999692060887309348844005)
                  ·
                    refine ⟨749942261416370502908251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3999692060887309348844005 749942261416370502908251)
                    ·
                      rfl

theorem cell23_4381522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 6, 4].length) (baseStart_4381522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381522 prefixEnd_4381522 := by exact prefixLift 4381522
  have htrace : WordTrace (prefixWord ++ tailWord_4381522) baseStart_4381522 baseEnd_4381522 := by
    simpa [prefixWord, tailWord_4381522, baseEnd_4381522] using wordTrace_append hprefix tailTrace_4381522
  have hstable : (prefixWord ++ tailWord_4381522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381522).length < 2 ^ (prefixWord ++ tailWord_4381522).sum := by decide
  have hdescent : baseEnd_4381522 < baseStart_4381522 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381562 : List Nat := [3, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3]
def baseStart_4381562 : Nat := 118140960795 + 4381562 * 2 ^ 59
def prefixEnd_4381562 : Nat := 4983230072969 + 3 ^ 40 * 4381562 * 2
def baseEnd_4381562 : Nat := 2249847323475291352224569

theorem tailTrace_4381562 : CollatzResearch.WordTrace tailWord_4381562 prefixEnd_4381562 2249847323475291352224569 := by
  unfold tailWord_4381562
  simp only [CollatzResearch.WordTrace]
  refine ⟨39952173738089165014652735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106539129968237773372407293 39952173738089165014652735)
  ·
    refine ⟨59928260607133747521979103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39952173738089165014652735 59928260607133747521979103)
    ·
      refine ⟨89892390910700621282968655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59928260607133747521979103 89892390910700621282968655)
      ·
        refine ⟨134838586366050931924452983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89892390910700621282968655 134838586366050931924452983)
        ·
          refine ⟨202257879549076397886679475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134838586366050931924452983 202257879549076397886679475)
          ·
            refine ⟨303386819323614596830019213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202257879549076397886679475 303386819323614596830019213)
            ·
              refine ⟨113770057246355473811257205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 303386819323614596830019213 113770057246355473811257205)
              ·
                refine ⟨10665942866845825669805363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 113770057246355473811257205 10665942866845825669805363)
                ·
                  refine ⟨15998914300268738504708045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10665942866845825669805363 15998914300268738504708045)
                  ·
                    refine ⟨5999592862600776939265517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15998914300268738504708045 5999592862600776939265517)
                    ·
                      refine ⟨2249847323475291352224569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5999592862600776939265517 2249847323475291352224569)
                      ·
                        rfl

theorem cell23_4381562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3].length) (baseStart_4381562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381562 prefixEnd_4381562 := by exact prefixLift 4381562
  have htrace : WordTrace (prefixWord ++ tailWord_4381562) baseStart_4381562 baseEnd_4381562 := by
    simpa [prefixWord, tailWord_4381562, baseEnd_4381562] using wordTrace_append hprefix tailTrace_4381562
  have hstable : (prefixWord ++ tailWord_4381562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381562).length < 2 ^ (prefixWord ++ tailWord_4381562).sum := by decide
  have hdescent : baseEnd_4381562 < baseStart_4381562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381590 : List Nat := [5, 3, 1, 1, 1, 2, 2, 2, 2, 4]
def baseStart_4381590 : Nat := 118140960795 + 4381590 * 2 ^ 59
def prefixEnd_4381590 : Nat := 4983230072969 + 3 ^ 40 * 4381590 * 2
def baseEnd_4381590 : Nat := 749953900311205747558147

theorem tailTrace_4381590 : CollatzResearch.WordTrace tailWord_4381590 prefixEnd_4381590 749953900311205747558147 := by
  unfold tailWord_4381590
  simp only [CollatzResearch.WordTrace]
  refine ⟨9988107262265951302539389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106539810797503480560420149 9988107262265951302539389)
  ·
    refine ⟨3745540223349731738452271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9988107262265951302539389 3745540223349731738452271)
    ·
      refine ⟨5618310335024597607678407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3745540223349731738452271 5618310335024597607678407)
      ·
        refine ⟨8427465502536896411517611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5618310335024597607678407 8427465502536896411517611)
        ·
          refine ⟨12641198253805344617276417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8427465502536896411517611 12641198253805344617276417)
          ·
            refine ⟨9480898690354008462957313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12641198253805344617276417 9480898690354008462957313)
            ·
              refine ⟨7110674017765506347217985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9480898690354008462957313 7110674017765506347217985)
              ·
                refine ⟨5333005513324129760413489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7110674017765506347217985 5333005513324129760413489)
                ·
                  refine ⟨3999754134993097320310117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5333005513324129760413489 3999754134993097320310117)
                  ·
                    refine ⟨749953900311205747558147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3999754134993097320310117 749953900311205747558147)
                    ·
                      rfl

theorem cell23_4381590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 2, 4].length) (baseStart_4381590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381590 prefixEnd_4381590 := by exact prefixLift 4381590
  have htrace : WordTrace (prefixWord ++ tailWord_4381590) baseStart_4381590 baseEnd_4381590 := by
    simpa [prefixWord, tailWord_4381590, baseEnd_4381590] using wordTrace_append hprefix tailTrace_4381590
  have hstable : (prefixWord ++ tailWord_4381590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381590).length < 2 ^ (prefixWord ++ tailWord_4381590).sum := by decide
  have hdescent : baseEnd_4381590 < baseStart_4381590 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381613 : List Nat := [1, 5, 2, 3, 1, 1, 2, 1, 1, 3, 3]
def baseStart_4381613 : Nat := 118140960795 + 4381613 * 2 ^ 59
def prefixEnd_4381613 : Nat := 4983230072969 + 3 ^ 40 * 4381613 * 2
def baseEnd_4381613 : Nat := 2249873510988670652686835

theorem tailTrace_4381613 : CollatzResearch.WordTrace tailWord_4381613 prefixEnd_4381613 2249873510988670652686835 := by
  unfold tailWord_4381613
  simp only [CollatzResearch.WordTrace]
  refine ⟨159810555075171895768717493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106540370050114597179144995 159810555075171895768717493)
  ·
    refine ⟨14982239538297365228317265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 159810555075171895768717493 14982239538297365228317265)
    ·
      refine ⟨11236679653723023921237949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14982239538297365228317265 11236679653723023921237949)
      ·
        refine ⟨4213754870146133970464231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11236679653723023921237949 4213754870146133970464231)
        ·
          refine ⟨6320632305219200955696347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4213754870146133970464231 6320632305219200955696347)
          ·
            refine ⟨9480948457828801433544521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6320632305219200955696347 9480948457828801433544521)
            ·
              refine ⟨7110711343371601075158391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9480948457828801433544521 7110711343371601075158391)
              ·
                refine ⟨10666067015057401612737587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7110711343371601075158391 10666067015057401612737587)
                ·
                  refine ⟨15999100522586102419106381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10666067015057401612737587 15999100522586102419106381)
                  ·
                    refine ⟨5999662695969788407164893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15999100522586102419106381 5999662695969788407164893)
                    ·
                      refine ⟨2249873510988670652686835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5999662695969788407164893 2249873510988670652686835)
                      ·
                        rfl

theorem cell23_4381613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 1, 3, 3].length) (baseStart_4381613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381613 prefixEnd_4381613 := by exact prefixLift 4381613
  have htrace : WordTrace (prefixWord ++ tailWord_4381613) baseStart_4381613 baseEnd_4381613 := by
    simpa [prefixWord, tailWord_4381613, baseEnd_4381613] using wordTrace_append hprefix tailTrace_4381613
  have hstable : (prefixWord ++ tailWord_4381613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381613).length < 2 ^ (prefixWord ++ tailWord_4381613).sum := by decide
  have hdescent : baseEnd_4381613 < baseStart_4381613 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381640 : List Nat := [2, 1, 3, 1, 5, 2, 2, 1, 1, 3, 2]
def baseStart_4381640 : Nat := 118140960795 + 4381640 * 2 ^ 59
def prefixEnd_4381640 : Nat := 4983230072969 + 3 ^ 40 * 4381640 * 2
def baseEnd_4381640 : Nat := 2249887374966342047049211

theorem tailTrace_4381640 : CollatzResearch.WordTrace tailWord_4381640 prefixEnd_4381640 2249887374966342047049211 := by
  unfold tailWord_4381640
  simp only [CollatzResearch.WordTrace]
  refine ⟨79905769923037039689975187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106541026564049386253300249 79905769923037039689975187)
  ·
    refine ⟨119858654884555559534962781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79905769923037039689975187 119858654884555559534962781)
    ·
      refine ⟨44946995581708334825611043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119858654884555559534962781 44946995581708334825611043)
      ·
        refine ⟨67420493372562502238416565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44946995581708334825611043 67420493372562502238416565)
        ·
          refine ⟨6320671253677734584851553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67420493372562502238416565 6320671253677734584851553)
          ·
            refine ⟨4740503440258300938638665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6320671253677734584851553 4740503440258300938638665)
            ·
              refine ⟨3555377580193725703978999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4740503440258300938638665 3555377580193725703978999)
              ·
                refine ⟨5333066370290588555968499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3555377580193725703978999 5333066370290588555968499)
                ·
                  refine ⟨7999599555435882833952749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5333066370290588555968499 7999599555435882833952749)
                  ·
                    refine ⟨2999849833288456062732281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7999599555435882833952749 2999849833288456062732281)
                    ·
                      refine ⟨2249887374966342047049211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2999849833288456062732281 2249887374966342047049211)
                      ·
                        rfl

theorem cell23_4381640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 2, 1, 1, 3, 2].length) (baseStart_4381640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381640 prefixEnd_4381640 := by exact prefixLift 4381640
  have htrace : WordTrace (prefixWord ++ tailWord_4381640) baseStart_4381640 baseEnd_4381640 := by
    simpa [prefixWord, tailWord_4381640, baseEnd_4381640] using wordTrace_append hprefix tailTrace_4381640
  have hstable : (prefixWord ++ tailWord_4381640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381640).length < 2 ^ (prefixWord ++ tailWord_4381640).sum := by decide
  have hdescent : baseEnd_4381640 < baseStart_4381640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381653 : List Nat := [1, 3, 2, 3, 3, 1, 1, 1, 4, 2, 2]
def baseStart_4381653 : Nat := 118140960795 + 4381653 * 2 ^ 59
def prefixEnd_4381653 : Nat := 4983230072969 + 3 ^ 40 * 4381653 * 2
def baseEnd_4381653 : Nat := 2249894050214850496186651

theorem tailTrace_4381653 : CollatzResearch.WordTrace tailWord_4381653 prefixEnd_4381653 2249894050214850496186651 := by
  unfold tailWord_4381653
  simp only [CollatzResearch.WordTrace]
  refine ⟨159812013995026982600173613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106541342663351321733449075 159812013995026982600173613)
  ·
    refine ⟨59929505248135118475065105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159812013995026982600173613 59929505248135118475065105)
    ·
      refine ⟨44947128936101338856298829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59929505248135118475065105 44947128936101338856298829)
      ·
        refine ⟨16855173351038002071112061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44947128936101338856298829 16855173351038002071112061)
        ·
          refine ⟨6320690006639250776667023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16855173351038002071112061 6320690006639250776667023)
          ·
            refine ⟨9481035009958876165000535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6320690006639250776667023 9481035009958876165000535)
            ·
              refine ⟨14221552514938314247500803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9481035009958876165000535 14221552514938314247500803)
              ·
                refine ⟨21332328772407471371251205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14221552514938314247500803 21332328772407471371251205)
                ·
                  refine ⟨3999811644826400882109601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21332328772407471371251205 3999811644826400882109601)
                  ·
                    refine ⟨2999858733619800661582201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3999811644826400882109601 2999858733619800661582201)
                    ·
                      refine ⟨2249894050214850496186651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2999858733619800661582201 2249894050214850496186651)
                      ·
                        rfl

theorem cell23_4381653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 1, 1, 4, 2, 2].length) (baseStart_4381653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381653 prefixEnd_4381653 := by exact prefixLift 4381653
  have htrace : WordTrace (prefixWord ++ tailWord_4381653) baseStart_4381653 baseEnd_4381653 := by
    simpa [prefixWord, tailWord_4381653, baseEnd_4381653] using wordTrace_append hprefix tailTrace_4381653
  have hstable : (prefixWord ++ tailWord_4381653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381653).length < 2 ^ (prefixWord ++ tailWord_4381653).sum := by decide
  have hdescent : baseEnd_4381653 < baseStart_4381653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381666 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 2, 2, 4]
def baseStart_4381666 : Nat := 118140960795 + 4381666 * 2 ^ 59
def prefixEnd_4381666 : Nat := 4983230072969 + 3 ^ 40 * 4381666 * 2
def baseEnd_4381666 : Nat := 2249900725463358945324091

theorem tailTrace_4381666 : CollatzResearch.WordTrace tailWord_4381666 prefixEnd_4381666 2249900725463358945324091 := by
  unfold tailWord_4381666
  simp only [CollatzResearch.WordTrace]
  refine ⟨39953122035994971455099213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106541658762653257213597901 39953122035994971455099213)
  ·
    refine ⟨14982420763498114295662205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39953122035994971455099213 14982420763498114295662205)
    ·
      refine ⟨5618407786311792860873327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14982420763498114295662205 5618407786311792860873327)
      ·
        refine ⟨8427611679467689291309991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5618407786311792860873327 8427611679467689291309991)
        ·
          refine ⟨12641417519201533936964987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8427611679467689291309991 12641417519201533936964987)
          ·
            refine ⟨18962126278802300905447481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12641417519201533936964987 18962126278802300905447481)
            ·
              refine ⟨14221594709101725679085611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18962126278802300905447481 14221594709101725679085611)
              ·
                refine ⟨21332392063652588518628417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14221594709101725679085611 21332392063652588518628417)
                ·
                  refine ⟨15999294047739441388971313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21332392063652588518628417 15999294047739441388971313)
                  ·
                    refine ⟨11999470535804581041728485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15999294047739441388971313 11999470535804581041728485)
                    ·
                      refine ⟨2249900725463358945324091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11999470535804581041728485 2249900725463358945324091)
                      ·
                        rfl

theorem cell23_4381666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_4381666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381666 prefixEnd_4381666 := by exact prefixLift 4381666
  have htrace : WordTrace (prefixWord ++ tailWord_4381666) baseStart_4381666 baseEnd_4381666 := by
    simpa [prefixWord, tailWord_4381666, baseEnd_4381666] using wordTrace_append hprefix tailTrace_4381666
  have hstable : (prefixWord ++ tailWord_4381666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381666).length < 2 ^ (prefixWord ++ tailWord_4381666).sum := by decide
  have hdescent : baseEnd_4381666 < baseStart_4381666 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381672 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 1, 7]
def baseStart_4381672 : Nat := 118140960795 + 4381672 * 2 ^ 59
def prefixEnd_4381672 : Nat := 4983230072969 + 3 ^ 40 * 4381672 * 2
def baseEnd_4381672 : Nat := 749967935449095307283021

theorem tailTrace_4381672 : CollatzResearch.WordTrace tailWord_4381672 prefixEnd_4381672 749967935449095307283021 := by
  unfold tailWord_4381672
  simp only [CollatzResearch.WordTrace]
  refine ⟨79906353490979074422557635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106541804654638765896743513 79906353490979074422557635)
  ·
    refine ⟨119859530236468611633836453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79906353490979074422557635 119859530236468611633836453)
    ·
      refine ⟨22473661919337864681344335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119859530236468611633836453 22473661919337864681344335)
      ·
        refine ⟨33710492879006797022016503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22473661919337864681344335 33710492879006797022016503)
        ·
          refine ⟨50565739318510195533024755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33710492879006797022016503 50565739318510195533024755)
          ·
            refine ⟨75848608977765293299537133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50565739318510195533024755 75848608977765293299537133)
            ·
              refine ⟨28443228366661984987326425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75848608977765293299537133 28443228366661984987326425)
              ·
                refine ⟨21332421274996488740494819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28443228366661984987326425 21332421274996488740494819)
                ·
                  refine ⟨31998631912494733110742229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21332421274996488740494819 31998631912494733110742229)
                  ·
                    refine ⟨749967935449095307283021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 31998631912494733110742229 749967935449095307283021)
                    ·
                      rfl

theorem cell23_4381672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 1, 7].length) (baseStart_4381672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381672 prefixEnd_4381672 := by exact prefixLift 4381672
  have htrace : WordTrace (prefixWord ++ tailWord_4381672) baseStart_4381672 baseEnd_4381672 := by
    simpa [prefixWord, tailWord_4381672, baseEnd_4381672] using wordTrace_append hprefix tailTrace_4381672
  have hstable : (prefixWord ++ tailWord_4381672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381672).length < 2 ^ (prefixWord ++ tailWord_4381672).sum := by decide
  have hdescent : baseEnd_4381672 < baseStart_4381672 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381746 : List Nat := [3, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3]
def baseStart_4381746 : Nat := 118140960795 + 4381746 * 2 ^ 59
def prefixEnd_4381746 : Nat := 4983230072969 + 3 ^ 40 * 4381746 * 2
def baseEnd_4381746 : Nat := 2249941803915718632323723

theorem tailTrace_4381746 : CollatzResearch.WordTrace tailWord_4381746 prefixEnd_4381746 2249941803915718632323723 := by
  unfold tailWord_4381746
  simp only [CollatzResearch.WordTrace]
  refine ⟨39953851495922514870827273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106543603989126706322206061 39953851495922514870827273)
  ·
    refine ⟨29965388621941886153120455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39953851495922514870827273 29965388621941886153120455)
    ·
      refine ⟨44948082932912829229680683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29965388621941886153120455 44948082932912829229680683)
      ·
        refine ⟨67422124399369243844521025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44948082932912829229680683 67422124399369243844521025)
        ·
          refine ⟨50566593299526932883390769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67422124399369243844521025 50566593299526932883390769)
          ·
            refine ⟨37924944974645199662543077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50566593299526932883390769 37924944974645199662543077)
            ·
              refine ⟨7110927182745974936726827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37924944974645199662543077 7110927182745974936726827)
              ·
                refine ⟨10666390774118962405090241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7110927182745974936726827 10666390774118962405090241)
                ·
                  refine ⟨7999793080589221803817681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10666390774118962405090241 7999793080589221803817681)
                  ·
                    refine ⟨5999844810441916352863261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7999793080589221803817681 5999844810441916352863261)
                    ·
                      refine ⟨2249941803915718632323723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5999844810441916352863261 2249941803915718632323723)
                      ·
                        rfl

theorem cell23_4381746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 4, 1, 2, 2, 3].length) (baseStart_4381746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381746 prefixEnd_4381746 := by exact prefixLift 4381746
  have htrace : WordTrace (prefixWord ++ tailWord_4381746) baseStart_4381746 baseEnd_4381746 := by
    simpa [prefixWord, tailWord_4381746, baseEnd_4381746] using wordTrace_append hprefix tailTrace_4381746
  have hstable : (prefixWord ++ tailWord_4381746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381746).length < 2 ^ (prefixWord ++ tailWord_4381746).sum := by decide
  have hdescent : baseEnd_4381746 < baseStart_4381746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381810 : List Nat := [3, 2, 1, 2, 2, 1, 4, 3, 1, 1, 3]
def baseStart_4381810 : Nat := 118140960795 + 4381810 * 2 ^ 59
def prefixEnd_4381810 : Nat := 4983230072969 + 3 ^ 40 * 4381810 * 2
def baseEnd_4381810 : Nat := 2249974666677606381923429

theorem tailTrace_4381810 : CollatzResearch.WordTrace tailWord_4381810 prefixEnd_4381810 2249974666677606381923429 := by
  unfold tailWord_4381810
  simp only [CollatzResearch.WordTrace]
  refine ⟨39954435063864549603409721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106545160170305465609092589 39954435063864549603409721)
  ·
    refine ⟨29965826297898412202557291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39954435063864549603409721 29965826297898412202557291)
    ·
      refine ⟨44948739446847618303835937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29965826297898412202557291 44948739446847618303835937)
      ·
        refine ⟨33711554585135713727876953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44948739446847618303835937 33711554585135713727876953)
        ·
          refine ⟨25283665938851785295907715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33711554585135713727876953 25283665938851785295907715)
          ·
            refine ⟨37925498908277677943861573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25283665938851785295907715 37925498908277677943861573)
            ·
              refine ⟨7111031045302064614474045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37925498908277677943861573 7111031045302064614474045)
              ·
                refine ⟨2666636641988274230427767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7111031045302064614474045 2666636641988274230427767)
                ·
                  refine ⟨3999954962982411345641651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2666636641988274230427767 3999954962982411345641651)
                  ·
                    refine ⟨5999932444473617018462477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3999954962982411345641651 5999932444473617018462477)
                    ·
                      refine ⟨2249974666677606381923429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5999932444473617018462477 2249974666677606381923429)
                      ·
                        rfl

theorem cell23_4381810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 3, 1, 1, 3].length) (baseStart_4381810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381810 prefixEnd_4381810 := by exact prefixLift 4381810
  have htrace : WordTrace (prefixWord ++ tailWord_4381810) baseStart_4381810 baseEnd_4381810 := by
    simpa [prefixWord, tailWord_4381810, baseEnd_4381810] using wordTrace_append hprefix tailTrace_4381810
  have hstable : (prefixWord ++ tailWord_4381810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381810).length < 2 ^ (prefixWord ++ tailWord_4381810).sum := by decide
  have hdescent : baseEnd_4381810 < baseStart_4381810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381833 : List Nat := [1, 2, 1, 1, 4, 3, 1, 3, 3, 2, 2]
def baseStart_4381833 : Nat := 118140960795 + 4381833 * 2 ^ 59
def prefixEnd_4381833 : Nat := 4983230072969 + 3 ^ 40 * 4381833 * 2
def baseEnd_4381833 : Nat := 2249986476732659791935823

theorem tailTrace_4381833 : CollatzResearch.WordTrace tailWord_4381833 prefixEnd_4381833 2249986476732659791935823 := by
  unfold tailWord_4381833
  simp only [CollatzResearch.WordTrace]
  refine ⟨159818579134374873341726153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106545719422916582227817435 159818579134374873341726153)
  ·
    refine ⟨119863934350781155006294615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159818579134374873341726153 119863934350781155006294615)
    ·
      refine ⟨179795901526171732509441923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119863934350781155006294615 179795901526171732509441923)
      ·
        refine ⟨269693852289257598764162885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179795901526171732509441923 269693852289257598764162885)
        ·
          refine ⟨50567597304235799768280541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 269693852289257598764162885 50567597304235799768280541)
          ·
            refine ⟨18962848989088424913105203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50567597304235799768280541 18962848989088424913105203)
            ·
              refine ⟨28444273483632637369657805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18962848989088424913105203 28444273483632637369657805)
              ·
                refine ⟨10666602556362239013621677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28444273483632637369657805 10666602556362239013621677)
                ·
                  refine ⟨3999975958635839630108129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10666602556362239013621677 3999975958635839630108129)
                  ·
                    refine ⟨2999981968976879722581097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3999975958635839630108129 2999981968976879722581097)
                    ·
                      refine ⟨2249986476732659791935823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2999981968976879722581097 2249986476732659791935823)
                      ·
                        rfl

theorem cell23_4381833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 1, 3, 3, 2, 2].length) (baseStart_4381833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381833 prefixEnd_4381833 := by exact prefixLift 4381833
  have htrace : WordTrace (prefixWord ++ tailWord_4381833) baseStart_4381833 baseEnd_4381833 := by
    simpa [prefixWord, tailWord_4381833, baseEnd_4381833] using wordTrace_append hprefix tailTrace_4381833
  have hstable : (prefixWord ++ tailWord_4381833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381833).length < 2 ^ (prefixWord ++ tailWord_4381833).sum := by decide
  have hdescent : baseEnd_4381833 < baseStart_4381833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381850 : List Nat := [3, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2]
def baseStart_4381850 : Nat := 118140960795 + 4381850 * 2 ^ 59
def prefixEnd_4381850 : Nat := 4983230072969 + 3 ^ 40 * 4381850 * 2
def baseEnd_4381850 : Nat := 2249995205903786225423245

theorem tailTrace_4381850 : CollatzResearch.WordTrace tailWord_4381850 prefixEnd_4381850 2249995205903786225423245 := by
  unfold tailWord_4381850
  simp only [CollatzResearch.WordTrace]
  refine ⟨39954799793828321311273751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106546132783542190163396669 39954799793828321311273751)
  ·
    refine ⟨59932199690742481966910627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39954799793828321311273751 59932199690742481966910627)
    ·
      refine ⟨89898299536113722950365941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59932199690742481966910627 89898299536113722950365941)
      ·
        refine ⟨8427965581510661526596807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 89898299536113722950365941 8427965581510661526596807)
        ·
          refine ⟨12641948372265992289895211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8427965581510661526596807 12641948372265992289895211)
          ·
            refine ⟨18962922558398988434842817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12641948372265992289895211 18962922558398988434842817)
            ·
              refine ⟨14222191918799241326132113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18962922558398988434842817 14222191918799241326132113)
              ·
                refine ⟨10666643939099430994599085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14222191918799241326132113 10666643939099430994599085)
                ·
                  refine ⟨3999991477162286622974657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10666643939099430994599085 3999991477162286622974657)
                  ·
                    refine ⟨2999993607871714967230993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3999991477162286622974657 2999993607871714967230993)
                    ·
                      refine ⟨2249995205903786225423245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2999993607871714967230993 2249995205903786225423245)
                      ·
                        rfl

theorem cell23_4381850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_4381850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381850 prefixEnd_4381850 := by exact prefixLift 4381850
  have htrace : WordTrace (prefixWord ++ tailWord_4381850) baseStart_4381850 baseEnd_4381850 := by
    simpa [prefixWord, tailWord_4381850, baseEnd_4381850] using wordTrace_append hprefix tailTrace_4381850
  have hstable : (prefixWord ++ tailWord_4381850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381850).length < 2 ^ (prefixWord ++ tailWord_4381850).sum := by decide
  have hdescent : baseEnd_4381850 < baseStart_4381850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381853 : List Nat := [1, 4, 2, 1, 1, 2, 4, 2, 1, 2, 3]
def baseStart_4381853 : Nat := 118140960795 + 4381853 * 2 ^ 59
def prefixEnd_4381853 : Nat := 4983230072969 + 3 ^ 40 * 4381853 * 2
def baseEnd_4381853 : Nat := 2249996746345749713685731

theorem tailTrace_4381853 : CollatzResearch.WordTrace tailWord_4381853 prefixEnd_4381853 2249996746345749713685731 := by
  unfold tailWord_4381853
  simp only [CollatzResearch.WordTrace]
  refine ⟨159819308594302416757454213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106546205729534944504969475 159819308594302416757454213)
  ·
    refine ⟨29966120361431703142022665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159819308594302416757454213 29966120361431703142022665)
    ·
      refine ⟨22474590271073777356516999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29966120361431703142022665 22474590271073777356516999)
      ·
        refine ⟨33711885406610666034775499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22474590271073777356516999 33711885406610666034775499)
        ·
          refine ⟨50567828109915999052163249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33711885406610666034775499 50567828109915999052163249)
          ·
            refine ⟨37925871082436999289122437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50567828109915999052163249 37925871082436999289122437)
            ·
              refine ⟨7111100827956937366710457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37925871082436999289122437 7111100827956937366710457)
              ·
                refine ⟨5333325620967703025032843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7111100827956937366710457 5333325620967703025032843)
                ·
                  refine ⟨7999988431451554537549265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5333325620967703025032843 7999988431451554537549265)
                  ·
                    refine ⟨5999991323588665903161949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7999988431451554537549265 5999991323588665903161949)
                    ·
                      refine ⟨2249996746345749713685731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5999991323588665903161949 2249996746345749713685731)
                      ·
                        rfl

theorem cell23_4381853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 4, 2, 1, 2, 3].length) (baseStart_4381853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381853 prefixEnd_4381853 := by exact prefixLift 4381853
  have htrace : WordTrace (prefixWord ++ tailWord_4381853) baseStart_4381853 baseEnd_4381853 := by
    simpa [prefixWord, tailWord_4381853, baseEnd_4381853] using wordTrace_append hprefix tailTrace_4381853
  have hstable : (prefixWord ++ tailWord_4381853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381853).length < 2 ^ (prefixWord ++ tailWord_4381853).sum := by decide
  have hdescent : baseEnd_4381853 < baseStart_4381853 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381879 : List Nat := [1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 5]
def baseStart_4381879 : Nat := 118140960795 + 4381879 * 2 ^ 59
def prefixEnd_4381879 : Nat := 4983230072969 + 3 ^ 40 * 4381879 * 2
def baseEnd_4381879 : Nat := 2250010096842766611960611

theorem tailTrace_4381879 : CollatzResearch.WordTrace tailWord_4381879 prefixEnd_4381879 2250010096842766611960611 := by
  unfold tailWord_4381879
  simp only [CollatzResearch.WordTrace]
  refine ⟨159820256892208223197900691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106546837928138815465267127 159820256892208223197900691)
  ·
    refine ⟨239730385338312334796851037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159820256892208223197900691 239730385338312334796851037)
    ·
      refine ⟨89898894501867125548819139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239730385338312334796851037 89898894501867125548819139)
      ·
        refine ⟨134848341752800688323228709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89898894501867125548819139 134848341752800688323228709)
        ·
          refine ⟨25284064078650129060605383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134848341752800688323228709 25284064078650129060605383)
          ·
            refine ⟨37926096117975193590908075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25284064078650129060605383 37926096117975193590908075)
            ·
              refine ⟨56889144176962790386362113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37926096117975193590908075 56889144176962790386362113)
              ·
                refine ⟨42666858132722092789771585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56889144176962790386362113 42666858132722092789771585)
                ·
                  refine ⟨32000143599541569592328689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42666858132722092789771585 32000143599541569592328689)
                  ·
                    refine ⟨24000107699656177194246517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32000143599541569592328689 24000107699656177194246517)
                    ·
                      refine ⟨2250010096842766611960611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24000107699656177194246517 2250010096842766611960611)
                      ·
                        rfl

theorem cell23_4381879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_4381879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381879 prefixEnd_4381879 := by exact prefixLift 4381879
  have htrace : WordTrace (prefixWord ++ tailWord_4381879) baseStart_4381879 baseEnd_4381879 := by
    simpa [prefixWord, tailWord_4381879, baseEnd_4381879] using wordTrace_append hprefix tailTrace_4381879
  have hstable : (prefixWord ++ tailWord_4381879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381879).length < 2 ^ (prefixWord ++ tailWord_4381879).sum := by decide
  have hdescent : baseEnd_4381879 < baseStart_4381879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381884 : List Nat := [2, 2, 2, 3, 2, 2, 3, 2, 1, 2, 2]
def baseStart_4381884 : Nat := 118140960795 + 4381884 * 2 ^ 59
def prefixEnd_4381884 : Nat := 4983230072969 + 3 ^ 40 * 4381884 * 2
def baseEnd_4381884 : Nat := 2250012664246039092398089

theorem tailTrace_4381884 : CollatzResearch.WordTrace tailWord_4381884 prefixEnd_4381884 2250012664246039092398089 := by
  unfold tailWord_4381884
  simp only [CollatzResearch.WordTrace]
  refine ⟨79910219628595054525916353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106546959504793406034555137 79910219628595054525916353)
  ·
    refine ⟨59932664721446290894437265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79910219628595054525916353 59932664721446290894437265)
    ·
      refine ⟨44949498541084718170827949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59932664721446290894437265 44949498541084718170827949)
      ·
        refine ⟨16856061952906769314060481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44949498541084718170827949 16856061952906769314060481)
        ·
          refine ⟨12642046464680076985545361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16856061952906769314060481 12642046464680076985545361)
          ·
            refine ⟨9481534848510057739159021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12642046464680076985545361 9481534848510057739159021)
            ·
              refine ⟨3555575568191271652184633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9481534848510057739159021 3555575568191271652184633)
              ·
                refine ⟨2666681676143453739138475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3555575568191271652184633 2666681676143453739138475)
                ·
                  refine ⟨4000022514215180608707713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2666681676143453739138475 4000022514215180608707713)
                  ·
                    refine ⟨3000016885661385456530785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4000022514215180608707713 3000016885661385456530785)
                    ·
                      refine ⟨2250012664246039092398089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3000016885661385456530785 2250012664246039092398089)
                      ·
                        rfl

theorem cell23_4381884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 3, 2, 1, 2, 2].length) (baseStart_4381884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381884 prefixEnd_4381884 := by exact prefixLift 4381884
  have htrace : WordTrace (prefixWord ++ tailWord_4381884) baseStart_4381884 baseEnd_4381884 := by
    simpa [prefixWord, tailWord_4381884, baseEnd_4381884] using wordTrace_append hprefix tailTrace_4381884
  have hstable : (prefixWord ++ tailWord_4381884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381884).length < 2 ^ (prefixWord ++ tailWord_4381884).sum := by decide
  have hdescent : baseEnd_4381884 < baseStart_4381884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381890 : List Nat := [3, 5, 1, 1, 2, 1, 2, 8]
def baseStart_4381890 : Nat := 118140960795 + 4381890 * 2 ^ 59
def prefixEnd_4381890 : Nat := 4983230072969 + 3 ^ 40 * 4381890 * 2
def baseEnd_4381890 : Nat := 83333916486295039589743

theorem tailTrace_4381890 : CollatzResearch.WordTrace tailWord_4381890 prefixEnd_4381890 83333916486295039589743 := by
  unfold tailWord_4381890
  simp only [CollatzResearch.WordTrace]
  refine ⟨39955164523792093019137781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106547105396778914717700749 39955164523792093019137781)
  ·
    refine ⟨3745796674105508720544167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39955164523792093019137781 3745796674105508720544167)
    ·
      refine ⟨5618695011158263080816251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3745796674105508720544167 5618695011158263080816251)
      ·
        refine ⟨8428042516737394621224377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5618695011158263080816251 8428042516737394621224377)
        ·
          refine ⟨6321031887553045965918283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8428042516737394621224377 6321031887553045965918283)
          ·
            refine ⟨9481547831329568948877425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6321031887553045965918283 9481547831329568948877425)
            ·
              refine ⟨7111160873497176711658069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9481547831329568948877425 7111160873497176711658069)
              ·
                refine ⟨83333916486295039589743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7111160873497176711658069 83333916486295039589743)
                ·
                  rfl

theorem cell23_4381890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 8].length) (baseStart_4381890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381890 prefixEnd_4381890 := by exact prefixLift 4381890
  have htrace : WordTrace (prefixWord ++ tailWord_4381890) baseStart_4381890 baseEnd_4381890 := by
    simpa [prefixWord, tailWord_4381890, baseEnd_4381890] using wordTrace_append hprefix tailTrace_4381890
  have hstable : (prefixWord ++ tailWord_4381890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381890).length < 2 ^ (prefixWord ++ tailWord_4381890).sum := by decide
  have hdescent : baseEnd_4381890 < baseStart_4381890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381894 : List Nat := [6, 1, 2, 2, 1, 1, 1, 3, 2, 4]
def baseStart_4381894 : Nat := 118140960795 + 4381894 * 2 ^ 59
def prefixEnd_4381894 : Nat := 4983230072969 + 3 ^ 40 * 4381894 * 2
def baseEnd_4381894 : Nat := 750005933017528017757681

theorem tailTrace_4381894 : CollatzResearch.WordTrace tailWord_4381894 prefixEnd_4381894 750005933017528017757681 := by
  unfold tailWord_4381894
  simp only [CollatzResearch.WordTrace]
  refine ⟨4994400124598558773740523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 106547202658102587173131157 4994400124598558773740523)
  ·
    refine ⟨7491600186897838160610785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4994400124598558773740523 7491600186897838160610785)
    ·
      refine ⟨5618700140173378620458089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7491600186897838160610785 5618700140173378620458089)
      ·
        refine ⟨4214025105130033965343567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5618700140173378620458089 4214025105130033965343567)
        ·
          refine ⟨6321037657695050948015351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4214025105130033965343567 6321037657695050948015351)
          ·
            refine ⟨9481556486542576422023027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6321037657695050948015351 9481556486542576422023027)
            ·
              refine ⟨14222334729813864633034541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9481556486542576422023027 14222334729813864633034541)
              ·
                refine ⟨5333375523680199237387953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14222334729813864633034541 5333375523680199237387953)
                ·
                  refine ⟨4000031642760149428040965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5333375523680199237387953 4000031642760149428040965)
                  ·
                    refine ⟨750005933017528017757681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4000031642760149428040965 750005933017528017757681)
                    ·
                      rfl

theorem cell23_4381894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 2, 4].length) (baseStart_4381894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381894 prefixEnd_4381894 := by exact prefixLift 4381894
  have htrace : WordTrace (prefixWord ++ tailWord_4381894) baseStart_4381894 baseEnd_4381894 := by
    simpa [prefixWord, tailWord_4381894, baseEnd_4381894] using wordTrace_append hprefix tailTrace_4381894
  have hstable : (prefixWord ++ tailWord_4381894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381894).length < 2 ^ (prefixWord ++ tailWord_4381894).sum := by decide
  have hdescent : baseEnd_4381894 < baseStart_4381894 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381949 : List Nat := [1, 4, 1, 1, 1, 1, 1, 1, 1, 3, 8]
def baseStart_4381949 : Nat := 118140960795 + 4381949 * 2 ^ 59
def prefixEnd_4381949 : Nat := 4983230072969 + 3 ^ 40 * 4381949 * 2
def baseEnd_4381949 : Nat := 2250046040488581338085289

theorem tailTrace_4381949 : CollatzResearch.WordTrace tailWord_4381949 prefixEnd_4381949 2250046040488581338085289 := by
  unfold tailWord_4381949
  simp only [CollatzResearch.WordTrace]
  refine ⟨159822810001954625152948901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106548540001303083435299267 159822810001954625152948901)
  ·
    refine ⟨29966776875366492216177919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159822810001954625152948901 29966776875366492216177919)
    ·
      refine ⟨44950165313049738324266879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29966776875366492216177919 44950165313049738324266879)
      ·
        refine ⟨67425247969574607486400319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44950165313049738324266879 67425247969574607486400319)
        ·
          refine ⟨101137871954361911229600479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67425247969574607486400319 101137871954361911229600479)
          ·
            refine ⟨151706807931542866844400719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101137871954361911229600479 151706807931542866844400719)
            ·
              refine ⟨227560211897314300266601079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151706807931542866844400719 227560211897314300266601079)
              ·
                refine ⟨341340317845971450399901619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227560211897314300266601079 341340317845971450399901619)
                ·
                  refine ⟨512010476768957175599852429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 341340317845971450399901619 512010476768957175599852429)
                  ·
                    refine ⟨192003928788358940849944661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 512010476768957175599852429 192003928788358940849944661)
                    ·
                      refine ⟨2250046040488581338085289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 192003928788358940849944661 2250046040488581338085289)
                      ·
                        rfl

theorem cell23_4381949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 1, 1, 1, 3, 8].length) (baseStart_4381949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381949 prefixEnd_4381949 := by exact prefixLift 4381949
  have htrace : WordTrace (prefixWord ++ tailWord_4381949) baseStart_4381949 baseEnd_4381949 := by
    simpa [prefixWord, tailWord_4381949, baseEnd_4381949] using wordTrace_append hprefix tailTrace_4381949
  have hstable : (prefixWord ++ tailWord_4381949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381949).length < 2 ^ (prefixWord ++ tailWord_4381949).sum := by decide
  have hdescent : baseEnd_4381949 < baseStart_4381949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381976 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 1, 7]
def baseStart_4381976 : Nat := 118140960795 + 4381976 * 2 ^ 59
def prefixEnd_4381976 : Nat := 4983230072969 + 3 ^ 40 * 4381976 * 2
def baseEnd_4381976 : Nat := 750019968155417577482555

theorem tailTrace_4381976 : CollatzResearch.WordTrace tailWord_4381976 prefixEnd_4381976 750019968155417577482555 := by
  unfold tailWord_4381976
  simp only [CollatzResearch.WordTrace]
  refine ⟨79911897386428404382090891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106549196515237872509454521 79911897386428404382090891)
  ·
    refine ⟨119867846079642606573136337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79911897386428404382090891 119867846079642606573136337)
    ·
      refine ⟨89900884559731954929852253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119867846079642606573136337 89900884559731954929852253)
      ·
        refine ⟨33712831709899483098694595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89900884559731954929852253 33712831709899483098694595)
        ·
          refine ⟨50569247564849224648041893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33712831709899483098694595 50569247564849224648041893)
          ·
            refine ⟨9481733918409229621507855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50569247564849224648041893 9481733918409229621507855)
            ·
              refine ⟨14222600877613844432261783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9481733918409229621507855 14222600877613844432261783)
              ·
                refine ⟨21333901316420766648392675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14222600877613844432261783 21333901316420766648392675)
                ·
                  refine ⟨32000851974631149972589013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21333901316420766648392675 32000851974631149972589013)
                  ·
                    refine ⟨750019968155417577482555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32000851974631149972589013 750019968155417577482555)
                    ·
                      rfl

theorem cell23_4381976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_4381976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381976 prefixEnd_4381976 := by exact prefixLift 4381976
  have htrace : WordTrace (prefixWord ++ tailWord_4381976) baseStart_4381976 baseEnd_4381976 := by
    simpa [prefixWord, tailWord_4381976, baseEnd_4381976] using wordTrace_append hprefix tailTrace_4381976
  have hstable : (prefixWord ++ tailWord_4381976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381976).length < 2 ^ (prefixWord ++ tailWord_4381976).sum := by decide
  have hdescent : baseEnd_4381976 < baseStart_4381976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4381996 : List Nat := [2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 4]
def baseStart_4381996 : Nat := 118140960795 + 4381996 * 2 ^ 59
def prefixEnd_4381996 : Nat := 4983230072969 + 3 ^ 40 * 4381996 * 2
def baseEnd_4381996 : Nat := 2250070174079342654197573

theorem tailTrace_4381996 : CollatzResearch.WordTrace tailWord_4381996 prefixEnd_4381996 2250070174079342654197573 := by
  unfold tailWord_4381996
  simp only [CollatzResearch.WordTrace]
  refine ⟨79912262116392176089954921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106549682821856234786606561 79912262116392176089954921)
  ·
    refine ⟨59934196587294132067466191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79912262116392176089954921 59934196587294132067466191)
    ·
      refine ⟨89901294880941198101199287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59934196587294132067466191 89901294880941198101199287)
      ·
        refine ⟨134851942321411797151798931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89901294880941198101199287 134851942321411797151798931)
        ·
          refine ⟨202277913482117695727698397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134851942321411797151798931 202277913482117695727698397)
          ·
            refine ⟨75854217555794135897886899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202277913482117695727698397 75854217555794135897886899)
            ·
              refine ⟨113781326333691203846830349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75854217555794135897886899 113781326333691203846830349)
              ·
                refine ⟨42667997375134201442561381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113781326333691203846830349 42667997375134201442561381)
                ·
                  refine ⟨8000249507837662770480259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42667997375134201442561381 8000249507837662770480259)
                  ·
                    refine ⟨12000374261756494155720389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8000249507837662770480259 12000374261756494155720389)
                    ·
                      refine ⟨2250070174079342654197573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12000374261756494155720389 2250070174079342654197573)
                      ·
                        rfl

theorem cell23_4381996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 4].length) (baseStart_4381996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4381996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4381996 prefixEnd_4381996 := by exact prefixLift 4381996
  have htrace : WordTrace (prefixWord ++ tailWord_4381996) baseStart_4381996 baseEnd_4381996 := by
    simpa [prefixWord, tailWord_4381996, baseEnd_4381996] using wordTrace_append hprefix tailTrace_4381996
  have hstable : (prefixWord ++ tailWord_4381996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4381996).length < 2 ^ (prefixWord ++ tailWord_4381996).sum := by decide
  have hdescent : baseEnd_4381996 < baseStart_4381996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4381996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382016 : List Nat := [2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 3]
def baseStart_4382016 : Nat := 118140960795 + 4382016 * 2 ^ 59
def prefixEnd_4382016 : Nat := 4983230072969 + 3 ^ 40 * 4382016 * 2
def baseEnd_4382016 : Nat := 2250080443692432575947481

theorem tailTrace_4382016 : CollatzResearch.WordTrace tailWord_4382016 prefixEnd_4382016 2250080443692432575947481 := by
  unfold tailWord_4382016
  simp only [CollatzResearch.WordTrace]
  refine ⟨79912626846355947797818951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106550169128474597063758601 79912626846355947797818951)
  ·
    refine ⟨119868940269533921696728427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79912626846355947797818951 119868940269533921696728427)
    ·
      refine ⟨179803410404300882545092641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119868940269533921696728427 179803410404300882545092641)
      ·
        refine ⟨134852557803225661908819481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179803410404300882545092641 134852557803225661908819481)
        ·
          refine ⟨101139418352419246431614611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134852557803225661908819481 101139418352419246431614611)
          ·
            refine ⟨151709127528628869647421917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101139418352419246431614611 151709127528628869647421917)
            ·
              refine ⟨56890922823235826117783219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151709127528628869647421917 56890922823235826117783219)
              ·
                refine ⟨85336384234853739176674829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56890922823235826117783219 85336384234853739176674829)
                ·
                  refine ⟨32001144088070152191253061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85336384234853739176674829 32001144088070152191253061)
                  ·
                    refine ⟨6000214516513153535859949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32001144088070152191253061 6000214516513153535859949)
                    ·
                      refine ⟨2250080443692432575947481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6000214516513153535859949 2250080443692432575947481)
                      ·
                        rfl

theorem cell23_4382016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 1, 3, 4, 3].length) (baseStart_4382016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382016 prefixEnd_4382016 := by exact prefixLift 4382016
  have htrace : WordTrace (prefixWord ++ tailWord_4382016) baseStart_4382016 baseEnd_4382016 := by
    simpa [prefixWord, tailWord_4382016, baseEnd_4382016] using wordTrace_append hprefix tailTrace_4382016
  have hstable : (prefixWord ++ tailWord_4382016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382016).length < 2 ^ (prefixWord ++ tailWord_4382016).sum := by decide
  have hdescent : baseEnd_4382016 < baseStart_4382016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382023 : List Nat := [1, 1, 4, 1, 2, 3, 2, 2, 3, 4]
def baseStart_4382023 : Nat := 118140960795 + 4382023 * 2 ^ 59
def prefixEnd_4382023 : Nat := 4983230072969 + 3 ^ 40 * 4382023 * 2
def baseEnd_4382023 : Nat := 750028012685671349519983

theorem tailTrace_4382023 : CollatzResearch.WordTrace tailWord_4382023 prefixEnd_4382023 750028012685671349519983 := by
  unfold tailWord_4382023
  simp only [CollatzResearch.WordTrace]
  refine ⟨159825509003686535791142723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106550339335791023860761815 159825509003686535791142723)
  ·
    refine ⟨239738263505529803686714085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159825509003686535791142723 239738263505529803686714085)
    ·
      refine ⟨44950924407286838191258891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 239738263505529803686714085 44950924407286838191258891)
      ·
        refine ⟨67426386610930257286888337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44950924407286838191258891 67426386610930257286888337)
        ·
          refine ⟨50569789958197692965166253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67426386610930257286888337 50569789958197692965166253)
          ·
            refine ⟨18963671234324134861937345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50569789958197692965166253 18963671234324134861937345)
            ·
              refine ⟨14222753425743101146453009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18963671234324134861937345 14222753425743101146453009)
              ·
                refine ⟨10667065069307325859839757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14222753425743101146453009 10667065069307325859839757)
                ·
                  refine ⟨4000149400990247197439909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10667065069307325859839757 4000149400990247197439909)
                  ·
                    refine ⟨750028012685671349519983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4000149400990247197439909 750028012685671349519983)
                    ·
                      rfl

theorem cell23_4382023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 4].length) (baseStart_4382023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382023 prefixEnd_4382023 := by exact prefixLift 4382023
  have htrace : WordTrace (prefixWord ++ tailWord_4382023) baseStart_4382023 baseEnd_4382023 := by
    simpa [prefixWord, tailWord_4382023, baseEnd_4382023] using wordTrace_append hprefix tailTrace_4382023
  have hstable : (prefixWord ++ tailWord_4382023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382023).length < 2 ^ (prefixWord ++ tailWord_4382023).sum := by decide
  have hdescent : baseEnd_4382023 < baseStart_4382023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382033 : List Nat := [1, 2, 2, 1, 4, 1, 2, 3, 2, 2, 3]
def baseStart_4382033 : Nat := 118140960795 + 4382033 * 2 ^ 59
def prefixEnd_4382033 : Nat := 4983230072969 + 3 ^ 40 * 4382033 * 2
def baseEnd_4382033 : Nat := 2250089172863559009434903

theorem tailTrace_4382033 : CollatzResearch.WordTrace tailWord_4382033 prefixEnd_4382033 2250089172863559009434903 := by
  unfold tailWord_4382033
  simp only [CollatzResearch.WordTrace]
  refine ⟨159825873733650307499006753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106550582489100204999337835 159825873733650307499006753)
  ·
    refine ⟨119869405300237730624255065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159825873733650307499006753 119869405300237730624255065)
    ·
      refine ⟨89902053975178297968191299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119869405300237730624255065 89902053975178297968191299)
      ·
        refine ⟨134853080962767446952286949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89902053975178297968191299 134853080962767446952286949)
        ·
          refine ⟨25284952680518896303553803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134853080962767446952286949 25284952680518896303553803)
          ·
            refine ⟨37927429020778344455330705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25284952680518896303553803 37927429020778344455330705)
            ·
              refine ⟨28445571765583758341498029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37927429020778344455330705 28445571765583758341498029)
              ·
                refine ⟨10667089412093909378061761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28445571765583758341498029 10667089412093909378061761)
                ·
                  refine ⟨8000317059070432033546321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10667089412093909378061761 8000317059070432033546321)
                  ·
                    refine ⟨6000237794302824025159741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8000317059070432033546321 6000237794302824025159741)
                    ·
                      refine ⟨2250089172863559009434903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6000237794302824025159741 2250089172863559009434903)
                      ·
                        rfl

theorem cell23_4382033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 2, 3, 2, 2, 3].length) (baseStart_4382033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382033 prefixEnd_4382033 := by exact prefixLift 4382033
  have htrace : WordTrace (prefixWord ++ tailWord_4382033) baseStart_4382033 baseEnd_4382033 := by
    simpa [prefixWord, tailWord_4382033, baseEnd_4382033] using wordTrace_append hprefix tailTrace_4382033
  have hstable : (prefixWord ++ tailWord_4382033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382033).length < 2 ^ (prefixWord ++ tailWord_4382033).sum := by decide
  have hdescent : baseEnd_4382033 < baseStart_4382033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382036 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 10]
def baseStart_4382036 : Nat := 118140960795 + 4382036 * 2 ^ 59
def prefixEnd_4382036 : Nat := 4983230072969 + 3 ^ 40 * 4382036 * 2
def baseEnd_4382036 : Nat := 250010079256169166410821

theorem tailTrace_4382036 : CollatzResearch.WordTrace tailWord_4382036 prefixEnd_4382036 250010079256169166410821 := by
  unfold tailWord_4382036
  simp only [CollatzResearch.WordTrace]
  refine ⟨79912991576319719505682981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106550655435092959340910641 79912991576319719505682981)
  ·
    refine ⟨14983685920559947407315559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79912991576319719505682981 14983685920559947407315559)
    ·
      refine ⟨22475528880839921110973339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14983685920559947407315559 22475528880839921110973339)
      ·
        refine ⟨33713293321259881666460009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22475528880839921110973339 33713293321259881666460009)
        ·
          refine ⟨25284969990944911249845007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33713293321259881666460009 25284969990944911249845007)
          ·
            refine ⟨37927454986417366874767511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25284969990944911249845007 37927454986417366874767511)
            ·
              refine ⟨56891182479626050312151267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37927454986417366874767511 56891182479626050312151267)
              ·
                refine ⟨85336773719439075468226901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56891182479626050312151267 85336773719439075468226901)
                ·
                  refine ⟨250010079256169166410821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 85336773719439075468226901 250010079256169166410821)
                  ·
                    rfl

theorem cell23_4382036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_4382036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382036 prefixEnd_4382036 := by exact prefixLift 4382036
  have htrace : WordTrace (prefixWord ++ tailWord_4382036) baseStart_4382036 baseEnd_4382036 := by
    simpa [prefixWord, tailWord_4382036, baseEnd_4382036] using wordTrace_append hprefix tailTrace_4382036
  have hstable : (prefixWord ++ tailWord_4382036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382036).length < 2 ^ (prefixWord ++ tailWord_4382036).sum := by decide
  have hdescent : baseEnd_4382036 < baseStart_4382036 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382050 : List Nat := [3, 3, 2, 1, 1, 1, 3, 2, 2, 2, 3]
def baseStart_4382050 : Nat := 118140960795 + 4382050 * 2 ^ 59
def prefixEnd_4382050 : Nat := 4983230072969 + 3 ^ 40 * 4382050 * 2
def baseEnd_4382050 : Nat := 2250097902034685442922325

theorem tailTrace_4382050 : CollatzResearch.WordTrace tailWord_4382050 prefixEnd_4382050 2250097902034685442922325 := by
  unfold tailWord_4382050
  simp only [CollatzResearch.WordTrace]
  refine ⟨39956623443647179850593901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106550995849725812934917069 39956623443647179850593901)
  ·
    refine ⟨14983733791367692443972713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39956623443647179850593901 14983733791367692443972713)
    ·
      refine ⟨11237800343525769332979535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14983733791367692443972713 11237800343525769332979535)
      ·
        refine ⟨16856700515288653999469303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11237800343525769332979535 16856700515288653999469303)
        ·
          refine ⟨25285050772932980999203955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16856700515288653999469303 25285050772932980999203955)
          ·
            refine ⟨37927576159399471498805933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25285050772932980999203955 37927576159399471498805933)
            ·
              refine ⟨14222841059774801812052225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37927576159399471498805933 14222841059774801812052225)
              ·
                refine ⟨10667130794831101359039169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14222841059774801812052225 10667130794831101359039169)
                ·
                  refine ⟨8000348096123326019279377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10667130794831101359039169 8000348096123326019279377)
                  ·
                    refine ⟨6000261072092494514459533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8000348096123326019279377 6000261072092494514459533)
                    ·
                      refine ⟨2250097902034685442922325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6000261072092494514459533 2250097902034685442922325)
                      ·
                        rfl

theorem cell23_4382050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 3, 2, 2, 2, 3].length) (baseStart_4382050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382050 prefixEnd_4382050 := by exact prefixLift 4382050
  have htrace : WordTrace (prefixWord ++ tailWord_4382050) baseStart_4382050 baseEnd_4382050 := by
    simpa [prefixWord, tailWord_4382050, baseEnd_4382050] using wordTrace_append hprefix tailTrace_4382050
  have hstable : (prefixWord ++ tailWord_4382050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382050).length < 2 ^ (prefixWord ++ tailWord_4382050).sum := by decide
  have hdescent : baseEnd_4382050 < baseStart_4382050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382073 : List Nat := [1, 2, 1, 3, 2, 1, 2, 1, 3, 5, 2]
def baseStart_4382073 : Nat := 118140960795 + 4382073 * 2 ^ 59
def prefixEnd_4382073 : Nat := 4983230072969 + 3 ^ 40 * 4382073 * 2
def baseEnd_4382073 : Nat := 2250109712089738852934719

theorem tailTrace_4382073 : CollatzResearch.WordTrace tailWord_4382073 prefixEnd_4382073 2250109712089738852934719 := by
  unfold tailWord_4382073
  simp only [CollatzResearch.WordTrace]
  refine ⟨159827332653505394330462873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106551555102336929553641915 159827332653505394330462873)
  ·
    refine ⟨119870499490129045747847155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159827332653505394330462873 119870499490129045747847155)
    ·
      refine ⟨179805749235193568621770733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119870499490129045747847155 179805749235193568621770733)
      ·
        refine ⟨67427155963197588233164025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179805749235193568621770733 67427155963197588233164025)
        ·
          refine ⟨50570366972398191174873019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67427155963197588233164025 50570366972398191174873019)
          ·
            refine ⟨75855550458597286762309529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50570366972398191174873019 75855550458597286762309529)
            ·
              refine ⟨56891662843947965071732147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75855550458597286762309529 56891662843947965071732147)
              ·
                refine ⟨85337494265921947607598221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56891662843947965071732147 85337494265921947607598221)
                ·
                  refine ⟨32001560349720730352849333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85337494265921947607598221 32001560349720730352849333)
                  ·
                    refine ⟨3000146282786318470579625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32001560349720730352849333 3000146282786318470579625)
                    ·
                      refine ⟨2250109712089738852934719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3000146282786318470579625 2250109712089738852934719)
                      ·
                        rfl

theorem cell23_4382073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 1, 3, 5, 2].length) (baseStart_4382073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382073 prefixEnd_4382073 := by exact prefixLift 4382073
  have htrace : WordTrace (prefixWord ++ tailWord_4382073) baseStart_4382073 baseEnd_4382073 := by
    simpa [prefixWord, tailWord_4382073, baseEnd_4382073] using wordTrace_append hprefix tailTrace_4382073
  have hstable : (prefixWord ++ tailWord_4382073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382073).length < 2 ^ (prefixWord ++ tailWord_4382073).sum := by decide
  have hdescent : baseEnd_4382073 < baseStart_4382073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382083 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 3, 5]
def baseStart_4382083 : Nat := 118140960795 + 4382083 * 2 ^ 59
def prefixEnd_4382083 : Nat := 4983230072969 + 3 ^ 40 * 4382083 * 2
def baseEnd_4382083 : Nat := 750038282298761271269891

theorem tailTrace_4382083 : CollatzResearch.WordTrace tailWord_4382083 prefixEnd_4382083 750038282298761271269891 := by
  unfold tailWord_4382083
  simp only [CollatzResearch.WordTrace]
  refine ⟨159827697383469166038326903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106551798255646110692217935 159827697383469166038326903)
  ·
    refine ⟨239741546075203749057490355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159827697383469166038326903 239741546075203749057490355)
    ·
      refine ⟨359612319112805623586235533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239741546075203749057490355 359612319112805623586235533)
      ·
        refine ⟨134854619667302108844838325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 359612319112805623586235533 134854619667302108844838325)
        ·
          refine ⟨12642620593809572704203593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 134854619667302108844838325 12642620593809572704203593)
          ·
            refine ⟨9481965445357179528152695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12642620593809572704203593 9481965445357179528152695)
            ·
              refine ⟨14222948168035769292229043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9481965445357179528152695 14222948168035769292229043)
              ·
                refine ⟨21334422252053653938343565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14222948168035769292229043 21334422252053653938343565)
                ·
                  refine ⟨8000408344520120226878837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21334422252053653938343565 8000408344520120226878837)
                  ·
                    refine ⟨750038282298761271269891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8000408344520120226878837 750038282298761271269891)
                    ·
                      rfl

theorem cell23_4382083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 5].length) (baseStart_4382083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382083 prefixEnd_4382083 := by exact prefixLift 4382083
  have htrace : WordTrace (prefixWord ++ tailWord_4382083) baseStart_4382083 baseEnd_4382083 := by
    simpa [prefixWord, tailWord_4382083, baseEnd_4382083] using wordTrace_append hprefix tailTrace_4382083
  have hstable : (prefixWord ++ tailWord_4382083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382083).length < 2 ^ (prefixWord ++ tailWord_4382083).sum := by decide
  have hdescent : baseEnd_4382083 < baseStart_4382083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382108 : List Nat := [2, 2, 3, 4, 2, 1, 2, 2, 1, 4]
def baseStart_4382108 : Nat := 118140960795 + 4382108 * 2 ^ 59
def prefixEnd_4382108 : Nat := 4983230072969 + 3 ^ 40 * 4382108 * 2
def baseEnd_4382108 : Nat := 750042561304215405332353

theorem tailTrace_4382108 : CollatzResearch.WordTrace tailWord_4382108 prefixEnd_4382108 750042561304215405332353 := by
  unfold tailWord_4382108
  simp only [CollatzResearch.WordTrace]
  refine ⟨79914304604189297653993489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106552406138919063538657985 79914304604189297653993489)
  ·
    refine ⟨59935728453141973240495117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79914304604189297653993489 59935728453141973240495117)
    ·
      refine ⟨22475898169928239965185669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59935728453141973240495117 22475898169928239965185669)
      ·
        refine ⟨4214230906861544993472313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22475898169928239965185669 4214230906861544993472313)
        ·
          refine ⟨3160673180146158745104235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4214230906861544993472313 3160673180146158745104235)
          ·
            refine ⟨4741009770219238117656353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3160673180146158745104235 4741009770219238117656353)
            ·
              refine ⟨3555757327664428588242265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4741009770219238117656353 3555757327664428588242265)
              ·
                refine ⟨2666817995748321441181699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3555757327664428588242265 2666817995748321441181699)
                ·
                  refine ⟨4000226993622482161772549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2666817995748321441181699 4000226993622482161772549)
                  ·
                    refine ⟨750042561304215405332353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4000226993622482161772549 750042561304215405332353)
                    ·
                      rfl

theorem cell23_4382108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 1, 4].length) (baseStart_4382108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382108 prefixEnd_4382108 := by exact prefixLift 4382108
  have htrace : WordTrace (prefixWord ++ tailWord_4382108) baseStart_4382108 baseEnd_4382108 := by
    simpa [prefixWord, tailWord_4382108, baseEnd_4382108] using wordTrace_append hprefix tailTrace_4382108
  have hstable : (prefixWord ++ tailWord_4382108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382108).length < 2 ^ (prefixWord ++ tailWord_4382108).sum := by decide
  have hdescent : baseEnd_4382108 < baseStart_4382108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382114 : List Nat := [3, 3, 1, 2, 1, 3, 1, 4, 1, 1, 3]
def baseStart_4382114 : Nat := 118140960795 + 4382114 * 2 ^ 59
def prefixEnd_4382114 : Nat := 4983230072969 + 3 ^ 40 * 4382114 * 2
def baseEnd_4382114 : Nat := 2250130764796573192522031

theorem tailTrace_4382114 : CollatzResearch.WordTrace tailWord_4382114 prefixEnd_4382114 2250130764796573192522031 := by
  unfold tailWord_4382114
  simp only [CollatzResearch.WordTrace]
  refine ⟨39957207011589214583176349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106552552030904572221803597 39957207011589214583176349)
  ·
    refine ⟨14983952629345955468691131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39957207011589214583176349 14983952629345955468691131)
    ·
      refine ⟨22475928944018933203036697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14983952629345955468691131 22475928944018933203036697)
      ·
        refine ⟨16856946708014199902277523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22475928944018933203036697 16856946708014199902277523)
        ·
          refine ⟨25285420062021299853416285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16856946708014199902277523 25285420062021299853416285)
          ·
            refine ⟨9482032523257987445031107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25285420062021299853416285 9482032523257987445031107)
            ·
              refine ⟨14223048784886981167546661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9482032523257987445031107 14223048784886981167546661)
              ·
                refine ⟨2666821647166308968914999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14223048784886981167546661 2666821647166308968914999)
                ·
                  refine ⟨4000232470749463453372499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2666821647166308968914999 4000232470749463453372499)
                  ·
                    refine ⟨6000348706124195180058749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4000232470749463453372499 6000348706124195180058749)
                    ·
                      refine ⟨2250130764796573192522031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6000348706124195180058749 2250130764796573192522031)
                      ·
                        rfl

theorem cell23_4382114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_4382114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382114 prefixEnd_4382114 := by exact prefixLift 4382114
  have htrace : WordTrace (prefixWord ++ tailWord_4382114) baseStart_4382114 baseEnd_4382114 := by
    simpa [prefixWord, tailWord_4382114, baseEnd_4382114] using wordTrace_append hprefix tailTrace_4382114
  have hstable : (prefixWord ++ tailWord_4382114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382114).length < 2 ^ (prefixWord ++ tailWord_4382114).sum := by decide
  have hdescent : baseEnd_4382114 < baseStart_4382114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382154 : List Nat := [3, 1, 2, 1, 2, 3, 1, 5, 1, 2, 2]
def baseStart_4382154 : Nat := 118140960795 + 4382154 * 2 ^ 59
def prefixEnd_4382154 : Nat := 4983230072969 + 3 ^ 40 * 4382154 * 2
def baseEnd_4382154 : Nat := 2250151304022753036021847

theorem tailTrace_4382154 : CollatzResearch.WordTrace tailWord_4382154 prefixEnd_4382154 2250151304022753036021847 := by
  unfold tailWord_4382154
  simp only [CollatzResearch.WordTrace]
  refine ⟨39957571741552986291040379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106553524644141296776107677 39957571741552986291040379)
  ·
    refine ⟨59936357612329479436560569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39957571741552986291040379 59936357612329479436560569)
    ·
      refine ⟨44952268209247109577420427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59936357612329479436560569 44952268209247109577420427)
      ·
        refine ⟨67428402313870664366130641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44952268209247109577420427 67428402313870664366130641)
        ·
          refine ⟨50571301735402998274597981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67428402313870664366130641 50571301735402998274597981)
          ·
            refine ⟨18964238150776124352974243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50571301735402998274597981 18964238150776124352974243)
            ·
              refine ⟨28446357226164186529461365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18964238150776124352974243 28446357226164186529461365)
              ·
                refine ⟨2666845989952892487137003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28446357226164186529461365 2666845989952892487137003)
                ·
                  refine ⟨4000268984929338730705505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2666845989952892487137003 4000268984929338730705505)
                  ·
                    refine ⟨3000201738697004048029129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4000268984929338730705505 3000201738697004048029129)
                    ·
                      refine ⟨2250151304022753036021847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3000201738697004048029129 2250151304022753036021847)
                      ·
                        rfl

theorem cell23_4382154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 5, 1, 2, 2].length) (baseStart_4382154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382154 prefixEnd_4382154 := by exact prefixLift 4382154
  have htrace : WordTrace (prefixWord ++ tailWord_4382154) baseStart_4382154 baseEnd_4382154 := by
    simpa [prefixWord, tailWord_4382154, baseEnd_4382154] using wordTrace_append hprefix tailTrace_4382154
  have hstable : (prefixWord ++ tailWord_4382154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382154).length < 2 ^ (prefixWord ++ tailWord_4382154).sum := by decide
  have hdescent : baseEnd_4382154 < baseStart_4382154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382164 : List Nat := [2, 4, 1, 2, 3, 2, 1, 2, 2, 4]
def baseStart_4382164 : Nat := 118140960795 + 4382164 * 2 ^ 59
def prefixEnd_4382164 : Nat := 4983230072969 + 3 ^ 40 * 4382164 * 2
def baseEnd_4382164 : Nat := 750052146276432665632267

theorem tailTrace_4382164 : CollatzResearch.WordTrace tailWord_4382164 prefixEnd_4382164 750052146276432665632267 := by
  unfold tailWord_4382164
  simp only [CollatzResearch.WordTrace]
  refine ⟨79915325848087858436012773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106553767797450477914683697 79915325848087858436012773)
  ·
    refine ⟨14984123596516473456752395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79915325848087858436012773 14984123596516473456752395)
    ·
      refine ⟨22476185394774710185128593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14984123596516473456752395 22476185394774710185128593)
      ·
        refine ⟨16857139046081032638846445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22476185394774710185128593 16857139046081032638846445)
        ·
          refine ⟨6321427142280387239567417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16857139046081032638846445 6321427142280387239567417)
          ·
            refine ⟨4741070356710290429675563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6321427142280387239567417 4741070356710290429675563)
            ·
              refine ⟨7111605535065435644513345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4741070356710290429675563 7111605535065435644513345)
              ·
                refine ⟨5333704151299076733385009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7111605535065435644513345 5333704151299076733385009)
                ·
                  refine ⟨4000278113474307550038757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5333704151299076733385009 4000278113474307550038757)
                  ·
                    refine ⟨750052146276432665632267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4000278113474307550038757 750052146276432665632267)
                    ·
                      rfl

theorem cell23_4382164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_4382164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382164 prefixEnd_4382164 := by exact prefixLift 4382164
  have htrace : WordTrace (prefixWord ++ tailWord_4382164) baseStart_4382164 baseEnd_4382164 := by
    simpa [prefixWord, tailWord_4382164, baseEnd_4382164] using wordTrace_append hprefix tailTrace_4382164
  have hstable : (prefixWord ++ tailWord_4382164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382164).length < 2 ^ (prefixWord ++ tailWord_4382164).sum := by decide
  have hdescent : baseEnd_4382164 < baseStart_4382164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382180 : List Nat := [2, 3, 1, 1, 1, 1, 1, 3, 5, 3, 2]
def baseStart_4382180 : Nat := 118140960795 + 4382180 * 2 ^ 59
def prefixEnd_4382180 : Nat := 4983230072969 + 3 ^ 40 * 4382180 * 2
def baseEnd_4382180 : Nat := 2250164654519769934296727

theorem tailTrace_4382180 : CollatzResearch.WordTrace tailWord_4382180 prefixEnd_4382180 2250164654519769934296727 := by
  unfold tailWord_4382180
  simp only [CollatzResearch.WordTrace]
  refine ⟨79915617632058875802303997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106554156842745167736405329 79915617632058875802303997)
  ·
    refine ⟨29968356612022078425863999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79915617632058875802303997 29968356612022078425863999)
    ·
      refine ⟨44952534918033117638795999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29968356612022078425863999 44952534918033117638795999)
      ·
        refine ⟨67428802377049676458193999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44952534918033117638795999 67428802377049676458193999)
        ·
          refine ⟨101143203565574514687290999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67428802377049676458193999 101143203565574514687290999)
          ·
            refine ⟨151714805348361772030936499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101143203565574514687290999 151714805348361772030936499)
            ·
              refine ⟨227572208022542658046404749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151714805348361772030936499 227572208022542658046404749)
              ·
                refine ⟨85339578008453496767401781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227572208022542658046404749 85339578008453496767401781)
                ·
                  refine ⟨8000585438292515321943917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85339578008453496767401781 8000585438292515321943917)
                  ·
                    refine ⟨3000219539359693245728969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8000585438292515321943917 3000219539359693245728969)
                    ·
                      refine ⟨2250164654519769934296727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3000219539359693245728969 2250164654519769934296727)
                      ·
                        rfl

theorem cell23_4382180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 3, 5, 3, 2].length) (baseStart_4382180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382180 prefixEnd_4382180 := by exact prefixLift 4382180
  have htrace : WordTrace (prefixWord ++ tailWord_4382180) baseStart_4382180 baseEnd_4382180 := by
    simpa [prefixWord, tailWord_4382180, baseEnd_4382180] using wordTrace_append hprefix tailTrace_4382180
  have hstable : (prefixWord ++ tailWord_4382180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382180).length < 2 ^ (prefixWord ++ tailWord_4382180).sum := by decide
  have hdescent : baseEnd_4382180 < baseStart_4382180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382213 : List Nat := [1, 3, 1, 1, 2, 2, 1, 2, 1, 6, 3]
def baseStart_4382213 : Nat := 118140960795 + 4382213 * 2 ^ 59
def prefixEnd_4382213 : Nat := 4983230072969 + 3 ^ 40 * 4382213 * 2
def baseEnd_4382213 : Nat := 2250181599381368305184075

theorem tailTrace_4382213 : CollatzResearch.WordTrace tailWord_4382213 prefixEnd_4382213 2250181599381368305184075 := by
  unfold tailWord_4382213
  simp only [CollatzResearch.WordTrace]
  refine ⟨159832438872998198240559293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106554959248665465493706195 159832438872998198240559293)
  ·
    refine ⟨59937164577374324340209735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159832438872998198240559293 59937164577374324340209735)
    ·
      refine ⟨89905746866061486510314603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59937164577374324340209735 89905746866061486510314603)
      ·
        refine ⟨134858620299092229765471905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89905746866061486510314603 134858620299092229765471905)
        ·
          refine ⟨101143965224319172324103929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134858620299092229765471905 101143965224319172324103929)
          ·
            refine ⟨75857973918239379243077947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101143965224319172324103929 75857973918239379243077947)
            ·
              refine ⟨113786960877359068864616921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75857973918239379243077947 113786960877359068864616921)
              ·
                refine ⟨85340220658019301648462691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113786960877359068864616921 85340220658019301648462691)
                ·
                  refine ⟨128010330987028952472694037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85340220658019301648462691 128010330987028952472694037)
                  ·
                    refine ⟨6000484265016982147157533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 128010330987028952472694037 6000484265016982147157533)
                    ·
                      refine ⟨2250181599381368305184075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6000484265016982147157533 2250181599381368305184075)
                      ·
                        rfl

theorem cell23_4382213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 6, 3].length) (baseStart_4382213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382213 prefixEnd_4382213 := by exact prefixLift 4382213
  have htrace : WordTrace (prefixWord ++ tailWord_4382213) baseStart_4382213 baseEnd_4382213 := by
    simpa [prefixWord, tailWord_4382213, baseEnd_4382213] using wordTrace_append hprefix tailTrace_4382213
  have hstable : (prefixWord ++ tailWord_4382213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382213).length < 2 ^ (prefixWord ++ tailWord_4382213).sum := by decide
  have hdescent : baseEnd_4382213 < baseStart_4382213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382227 : List Nat := [1, 1, 1, 2, 1, 6, 2, 1, 4, 2, 2]
def baseStart_4382227 : Nat := 118140960795 + 4382227 * 2 ^ 59
def prefixEnd_4382227 : Nat := 4983230072969 + 3 ^ 40 * 4382227 * 2
def baseEnd_4382227 : Nat := 2250188788110531250409011

theorem tailTrace_4382227 : CollatzResearch.WordTrace tailWord_4382227 prefixEnd_4382227 2250188788110531250409011 := by
  unfold tailWord_4382227
  simp only [CollatzResearch.WordTrace]
  refine ⟨159832949494947478631568935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106555299663298319087712623 159832949494947478631568935)
  ·
    refine ⟨239749424242421217947353403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159832949494947478631568935 239749424242421217947353403)
    ·
      refine ⟨359624136363631826921030105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239749424242421217947353403 359624136363631826921030105)
      ·
        refine ⟨269718102272723870190772579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 359624136363631826921030105 269718102272723870190772579)
        ·
          refine ⟨404577153409085805286158869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269718102272723870190772579 404577153409085805286158869)
          ·
            refine ⟨18964554066050897122788697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 404577153409085805286158869 18964554066050897122788697)
            ·
              refine ⟨14223415549538172842091523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18964554066050897122788697 14223415549538172842091523)
              ·
                refine ⟨21335123324307259263137285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14223415549538172842091523 21335123324307259263137285)
                ·
                  refine ⟨4000335623307611111838241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21335123324307259263137285 4000335623307611111838241)
                  ·
                    refine ⟨3000251717480708333878681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4000335623307611111838241 3000251717480708333878681)
                    ·
                      refine ⟨2250188788110531250409011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3000251717480708333878681 2250188788110531250409011)
                      ·
                        rfl

theorem cell23_4382227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 2, 1, 4, 2, 2].length) (baseStart_4382227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382227 prefixEnd_4382227 := by exact prefixLift 4382227
  have htrace : WordTrace (prefixWord ++ tailWord_4382227) baseStart_4382227 baseEnd_4382227 := by
    simpa [prefixWord, tailWord_4382227, baseEnd_4382227] using wordTrace_append hprefix tailTrace_4382227
  have hstable : (prefixWord ++ tailWord_4382227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382227).length < 2 ^ (prefixWord ++ tailWord_4382227).sum := by decide
  have hdescent : baseEnd_4382227 < baseStart_4382227 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382248 : List Nat := [2, 1, 5, 2, 3, 1, 1, 2, 1, 3, 2]
def baseStart_4382248 : Nat := 118140960795 + 4382248 * 2 ^ 59
def prefixEnd_4382248 : Nat := 4983230072969 + 3 ^ 40 * 4382248 * 2
def baseEnd_4382248 : Nat := 2250199571204275668246415

theorem tailTrace_4382248 : CollatzResearch.WordTrace tailWord_4382248 prefixEnd_4382248 2250199571204275668246415 := by
  unfold tailWord_4382248
  simp only [CollatzResearch.WordTrace]
  refine ⟨79916857713935699609041699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106555810285247599478722265 79916857713935699609041699)
  ·
    refine ⟨119875286570903549413562549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79916857713935699609041699 119875286570903549413562549)
    ·
      refine ⟨11238308116022207757521489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119875286570903549413562549 11238308116022207757521489)
      ·
        refine ⟨8428731087016655818141117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11238308116022207757521489 8428731087016655818141117)
        ·
          refine ⟨3160774157631245931802919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8428731087016655818141117 3160774157631245931802919)
          ·
            refine ⟨4741161236446868897704379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3160774157631245931802919 4741161236446868897704379)
            ·
              refine ⟨7111741854670303346556569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4741161236446868897704379 7111741854670303346556569)
              ·
                refine ⟨5333806391002727509917427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7111741854670303346556569 5333806391002727509917427)
                ·
                  refine ⟨8000709586504091264876141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5333806391002727509917427 8000709586504091264876141)
                  ·
                    refine ⟨3000266094939034224328553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8000709586504091264876141 3000266094939034224328553)
                    ·
                      refine ⟨2250199571204275668246415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3000266094939034224328553 2250199571204275668246415)
                      ·
                        rfl

theorem cell23_4382248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_4382248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382248 prefixEnd_4382248 := by exact prefixLift 4382248
  have htrace : WordTrace (prefixWord ++ tailWord_4382248) baseStart_4382248 baseEnd_4382248 := by
    simpa [prefixWord, tailWord_4382248, baseEnd_4382248] using wordTrace_append hprefix tailTrace_4382248
  have hstable : (prefixWord ++ tailWord_4382248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382248).length < 2 ^ (prefixWord ++ tailWord_4382248).sum := by decide
  have hdescent : baseEnd_4382248 < baseStart_4382248 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382283 : List Nat := [1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 4]
def baseStart_4382283 : Nat := 118140960795 + 4382283 * 2 ^ 59
def prefixEnd_4382283 : Nat := 4983230072969 + 3 ^ 40 * 4382283 * 2
def baseEnd_4382283 : Nat := 2250217543027183031308753

theorem tailTrace_4382283 : CollatzResearch.WordTrace tailWord_4382283 prefixEnd_4382283 2250217543027183031308753 := by
  unfold tailWord_4382283
  simp only [CollatzResearch.WordTrace]
  refine ⟨159834991982744600195607503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106556661321829733463738335 159834991982744600195607503)
  ·
    refine ⟨239752487974116900293411255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159834991982744600195607503 239752487974116900293411255)
    ·
      refine ⟨359628731961175350440116883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239752487974116900293411255 359628731961175350440116883)
      ·
        refine ⟨539443097941763025660175325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359628731961175350440116883 539443097941763025660175325)
        ·
          refine ⟨202291161728161134622565747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 539443097941763025660175325 202291161728161134622565747)
          ·
            refine ⟨303436742592241701933848621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202291161728161134622565747 303436742592241701933848621)
            ·
              refine ⟨113788778472090638225193233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 303436742592241701933848621 113788778472090638225193233)
              ·
                refine ⟨85341583854067978668894925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113788778472090638225193233 85341583854067978668894925)
                ·
                  refine ⟨32003093945275492000835597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85341583854067978668894925 32003093945275492000835597)
                  ·
                    refine ⟨12001160229478309500313349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32003093945275492000835597 12001160229478309500313349)
                    ·
                      refine ⟨2250217543027183031308753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12001160229478309500313349 2250217543027183031308753)
                      ·
                        rfl

theorem cell23_4382283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 2, 3, 3, 4].length) (baseStart_4382283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382283 prefixEnd_4382283 := by exact prefixLift 4382283
  have htrace : WordTrace (prefixWord ++ tailWord_4382283) baseStart_4382283 baseEnd_4382283 := by
    simpa [prefixWord, tailWord_4382283, baseEnd_4382283] using wordTrace_append hprefix tailTrace_4382283
  have hstable : (prefixWord ++ tailWord_4382283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382283).length < 2 ^ (prefixWord ++ tailWord_4382283).sum := by decide
  have hdescent : baseEnd_4382283 < baseStart_4382283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382284 : List Nat := [2, 2, 1, 3, 1, 5, 2, 2, 5]
def baseStart_4382284 : Nat := 118140960795 + 4382284 * 2 ^ 59
def prefixEnd_4382284 : Nat := 4983230072969 + 3 ^ 40 * 4382284 * 2
def baseEnd_4382284 : Nat := 250024228500870836377361

theorem tailTrace_4382284 : CollatzResearch.WordTrace tailWord_4382284 prefixEnd_4382284 250024228500870836377361 := by
  unfold tailWord_4382284
  simp only [CollatzResearch.WordTrace]
  refine ⟨79917514227870488683196953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106556685637160651577595937 79917514227870488683196953)
  ·
    refine ⟨59938135670902866512397715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79917514227870488683196953 59938135670902866512397715)
    ·
      refine ⟨89907203506354299768596573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59938135670902866512397715 89907203506354299768596573)
      ·
        refine ⟨33715201314882862413223715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89907203506354299768596573 33715201314882862413223715)
        ·
          refine ⟨50572801972324293619835573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33715201314882862413223715 50572801972324293619835573)
          ·
            refine ⟨4741200184905402526859585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50572801972324293619835573 4741200184905402526859585)
            ·
              refine ⟨3555900138679051895144689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4741200184905402526859585 3555900138679051895144689)
              ·
                refine ⟨2666925104009288921358517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3555900138679051895144689 2666925104009288921358517)
                ·
                  refine ⟨250024228500870836377361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2666925104009288921358517 250024228500870836377361)
                  ·
                    rfl

theorem cell23_4382284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 5].length) (baseStart_4382284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382284 prefixEnd_4382284 := by exact prefixLift 4382284
  have htrace : WordTrace (prefixWord ++ tailWord_4382284) baseStart_4382284 baseEnd_4382284 := by
    simpa [prefixWord, tailWord_4382284, baseEnd_4382284] using wordTrace_append hprefix tailTrace_4382284
  have hstable : (prefixWord ++ tailWord_4382284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382284).length < 2 ^ (prefixWord ++ tailWord_4382284).sum := by decide
  have hdescent : baseEnd_4382284 < baseStart_4382284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382290 : List Nat := [3, 2, 2, 1, 2, 2, 2, 1, 1, 2, 5]
def baseStart_4382290 : Nat := 118140960795 + 4382290 * 2 ^ 59
def prefixEnd_4382290 : Nat := 4983230072969 + 3 ^ 40 * 4382290 * 2
def baseEnd_4382290 : Nat := 2250221137391764503921221

theorem tailTrace_4382290 : CollatzResearch.WordTrace tailWord_4382290 prefixEnd_4382290 2250221137391764503921221 := by
  unfold tailWord_4382290
  simp only [CollatzResearch.WordTrace]
  refine ⟨39958811823429810097778081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106556831529146160260741549 39958811823429810097778081)
  ·
    refine ⟨29969108867572357573333561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39958811823429810097778081 29969108867572357573333561)
    ·
      refine ⟨22476831650679268180000171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29969108867572357573333561 22476831650679268180000171)
      ·
        refine ⟨33715247476018902270000257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22476831650679268180000171 33715247476018902270000257)
        ·
          refine ⟨25286435607014176702500193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33715247476018902270000257 25286435607014176702500193)
          ·
            refine ⟨18964826705260632526875145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25286435607014176702500193 18964826705260632526875145)
            ·
              refine ⟨14223620028945474395156359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18964826705260632526875145 14223620028945474395156359)
              ·
                refine ⟨21335430043418211592734539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14223620028945474395156359 21335430043418211592734539)
                ·
                  refine ⟨32003145065127317389101809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21335430043418211592734539 32003145065127317389101809)
                  ·
                    refine ⟨24002358798845488041826357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32003145065127317389101809 24002358798845488041826357)
                    ·
                      refine ⟨2250221137391764503921221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24002358798845488041826357 2250221137391764503921221)
                      ·
                        rfl

theorem cell23_4382290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_4382290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382290 prefixEnd_4382290 := by exact prefixLift 4382290
  have htrace : WordTrace (prefixWord ++ tailWord_4382290) baseStart_4382290 baseEnd_4382290 := by
    simpa [prefixWord, tailWord_4382290, baseEnd_4382290] using wordTrace_append hprefix tailTrace_4382290
  have hstable : (prefixWord ++ tailWord_4382290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382290).length < 2 ^ (prefixWord ++ tailWord_4382290).sum := by decide
  have hdescent : baseEnd_4382290 < baseStart_4382290 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382293 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 2, 8]
def baseStart_4382293 : Nat := 118140960795 + 4382293 * 2 ^ 59
def prefixEnd_4382293 : Nat := 4983230072969 + 3 ^ 40 * 4382293 * 2
def baseEnd_4382293 : Nat := 750074225944575997394569

theorem tailTrace_4382293 : CollatzResearch.WordTrace tailWord_4382293 prefixEnd_4382293 750074225944575997394569 := by
  unfold tailWord_4382293
  simp only [CollatzResearch.WordTrace]
  refine ⟨159835356712708371903471533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106556904475138914602314355 159835356712708371903471533)
  ·
    refine ⟨59938258767265639463801825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159835356712708371903471533 59938258767265639463801825)
    ·
      refine ⟨44953694075449229597851369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59938258767265639463801825 44953694075449229597851369)
      ·
        refine ⟨33715270556586922198388527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44953694075449229597851369 33715270556586922198388527)
        ·
          refine ⟨50572905834880383297582791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33715270556586922198388527 50572905834880383297582791)
          ·
            refine ⟨75859358752320574946374187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50572905834880383297582791 75859358752320574946374187)
            ·
              refine ⟨113789038128480862419561281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75859358752320574946374187 113789038128480862419561281)
              ·
                refine ⟨85341778596360646814670961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113789038128480862419561281 85341778596360646814670961)
                ·
                  refine ⟨64006333947270485111003221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85341778596360646814670961 64006333947270485111003221)
                  ·
                    refine ⟨750074225944575997394569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 64006333947270485111003221 750074225944575997394569)
                    ·
                      rfl

theorem cell23_4382293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_4382293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382293 prefixEnd_4382293 := by exact prefixLift 4382293
  have htrace : WordTrace (prefixWord ++ tailWord_4382293) baseStart_4382293 baseEnd_4382293 := by
    simpa [prefixWord, tailWord_4382293, baseEnd_4382293] using wordTrace_append hprefix tailTrace_4382293
  have hstable : (prefixWord ++ tailWord_4382293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382293).length < 2 ^ (prefixWord ++ tailWord_4382293).sum := by decide
  have hdescent : baseEnd_4382293 < baseStart_4382293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382317 : List Nat := [1, 5, 1, 1, 4, 1, 1, 1, 1, 3, 4]
def baseStart_4382317 : Nat := 118140960795 + 4382317 * 2 ^ 59
def prefixEnd_4382317 : Nat := 4983230072969 + 3 ^ 40 * 4382317 * 2
def baseEnd_4382317 : Nat := 2250235001369435898283597

theorem tailTrace_4382317 : CollatzResearch.WordTrace tailWord_4382317 prefixEnd_4382317 2250235001369435898283597 := by
  unfold tailWord_4382317
  simp only [CollatzResearch.WordTrace]
  refine ⟨159836232064621424002345205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106557488043080949334896803 159836232064621424002345205)
  ·
    refine ⟨14984646756058258500219863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 159836232064621424002345205 14984646756058258500219863)
    ·
      refine ⟨22476970134087387750329795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14984646756058258500219863 22476970134087387750329795)
      ·
        refine ⟨33715455201131081625494693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22476970134087387750329795 33715455201131081625494693)
        ·
          refine ⟨6321647850212077804780255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33715455201131081625494693 6321647850212077804780255)
          ·
            refine ⟨9482471775318116707170383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6321647850212077804780255 9482471775318116707170383)
            ·
              refine ⟨14223707662977175060755575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9482471775318116707170383 14223707662977175060755575)
              ·
                refine ⟨21335561494465762591133363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14223707662977175060755575 21335561494465762591133363)
                ·
                  refine ⟨32003342241698643886700045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21335561494465762591133363 32003342241698643886700045)
                  ·
                    refine ⟨12001253340636991457512517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32003342241698643886700045 12001253340636991457512517)
                    ·
                      refine ⟨2250235001369435898283597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12001253340636991457512517 2250235001369435898283597)
                      ·
                        rfl

theorem cell23_4382317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_4382317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382317 prefixEnd_4382317 := by exact prefixLift 4382317
  have htrace : WordTrace (prefixWord ++ tailWord_4382317) baseStart_4382317 baseEnd_4382317 := by
    simpa [prefixWord, tailWord_4382317, baseEnd_4382317] using wordTrace_append hprefix tailTrace_4382317
  have hstable : (prefixWord ++ tailWord_4382317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382317).length < 2 ^ (prefixWord ++ tailWord_4382317).sum := by decide
  have hdescent : baseEnd_4382317 < baseStart_4382317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382353 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 2, 9]
def baseStart_4382353 : Nat := 118140960795 + 4382353 * 2 ^ 59
def prefixEnd_4382353 : Nat := 4983230072969 + 3 ^ 40 * 4382353 * 2
def baseEnd_4382353 : Nat := 750084495557665919144477

theorem tailTrace_4382353 : CollatzResearch.WordTrace tailWord_4382353 prefixEnd_4382353 750084495557665919144477 := by
  unfold tailWord_4382353
  simp only [CollatzResearch.WordTrace]
  refine ⟨159837545092491002150655713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106558363394994001433770475 159837545092491002150655713)
  ·
    refine ⟨119878158819368251612991785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159837545092491002150655713 119878158819368251612991785)
    ·
      refine ⟨89908619114526188709743839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119878158819368251612991785 89908619114526188709743839)
      ·
        refine ⟨134862928671789283064615759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89908619114526188709743839 134862928671789283064615759)
        ·
          refine ⟨202294393007683924596923639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134862928671789283064615759 202294393007683924596923639)
          ·
            refine ⟨303441589511525886895385459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202294393007683924596923639 303441589511525886895385459)
            ·
              refine ⟨455162384267288830343078189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303441589511525886895385459 455162384267288830343078189)
              ·
                refine ⟨170685894100233311378654321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 455162384267288830343078189 170685894100233311378654321)
                ·
                  refine ⟨128014420575174983533990741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170685894100233311378654321 128014420575174983533990741)
                  ·
                    refine ⟨750084495557665919144477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 128014420575174983533990741 750084495557665919144477)
                    ·
                      rfl

theorem cell23_4382353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_4382353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382353 prefixEnd_4382353 := by exact prefixLift 4382353
  have htrace : WordTrace (prefixWord ++ tailWord_4382353) baseStart_4382353 baseEnd_4382353 := by
    simpa [prefixWord, tailWord_4382353, baseEnd_4382353] using wordTrace_append hprefix tailTrace_4382353
  have hstable : (prefixWord ++ tailWord_4382353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382353).length < 2 ^ (prefixWord ++ tailWord_4382353).sum := by decide
  have hdescent : baseEnd_4382353 < baseStart_4382353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382394 : List Nat := [3, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2]
def baseStart_4382394 : Nat := 118140960795 + 4382394 * 2 ^ 59
def prefixEnd_4382394 : Nat := 4983230072969 + 3 ^ 40 * 4382394 * 2
def baseEnd_4382394 : Nat := 2250274539379832097020743

theorem tailTrace_4382394 : CollatzResearch.WordTrace tailWord_4382394 prefixEnd_4382394 2250274539379832097020743 := by
  unfold tailWord_4382394
  simp only [CollatzResearch.WordTrace]
  refine ⟨39959760121335616538224559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106559360323561644101932157 39959760121335616538224559)
  ·
    refine ⟨59939640182003424807336839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39959760121335616538224559 59939640182003424807336839)
    ·
      refine ⟨89909460273005137211005259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59939640182003424807336839 89909460273005137211005259)
      ·
        refine ⟨134864190409507705816507889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89909460273005137211005259 134864190409507705816507889)
        ·
          refine ⟨101148142807130779362380917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134864190409507705816507889 101148142807130779362380917)
          ·
            refine ⟨9482638388168510565223211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101148142807130779362380917 9482638388168510565223211)
            ·
              refine ⟨14223957582252765847834817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9482638388168510565223211 14223957582252765847834817)
              ·
                refine ⟨10667968186689574385876113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14223957582252765847834817 10667968186689574385876113)
                ·
                  refine ⟨8000976140017180789407085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10667968186689574385876113 8000976140017180789407085)
                  ·
                    refine ⟨3000366052506442796027657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8000976140017180789407085 3000366052506442796027657)
                    ·
                      refine ⟨2250274539379832097020743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3000366052506442796027657 2250274539379832097020743)
                      ·
                        rfl

theorem cell23_4382394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 1, 2, 2, 3, 2].length) (baseStart_4382394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382394 prefixEnd_4382394 := by exact prefixLift 4382394
  have htrace : WordTrace (prefixWord ++ tailWord_4382394) baseStart_4382394 baseEnd_4382394 := by
    simpa [prefixWord, tailWord_4382394, baseEnd_4382394] using wordTrace_append hprefix tailTrace_4382394
  have hstable : (prefixWord ++ tailWord_4382394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382394).length < 2 ^ (prefixWord ++ tailWord_4382394).sum := by decide
  have hdescent : baseEnd_4382394 < baseStart_4382394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382424 : List Nat := [2, 1, 2, 2, 3, 1, 2, 1, 5, 2, 2]
def baseStart_4382424 : Nat := 118140960795 + 4382424 * 2 ^ 59
def prefixEnd_4382424 : Nat := 4983230072969 + 3 ^ 40 * 4382424 * 2
def baseEnd_4382424 : Nat := 2250289943799466979645605

theorem tailTrace_4382424 : CollatzResearch.WordTrace tailWord_4382424 prefixEnd_4382424 2250289943799466979645605 := by
  unfold tailWord_4382424
  simp only [CollatzResearch.WordTrace]
  refine ⟨79920067337616890638245163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106560089783489187517660217 79920067337616890638245163)
  ·
    refine ⟨119880101006425335957367745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79920067337616890638245163 119880101006425335957367745)
    ·
      refine ⟨89910075754819001968025809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119880101006425335957367745 89910075754819001968025809)
      ·
        refine ⟨67432556816114251476019357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89910075754819001968025809 67432556816114251476019357)
        ·
          refine ⟨25287208806042844303507259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67432556816114251476019357 25287208806042844303507259)
          ·
            refine ⟨37930813209064266455260889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25287208806042844303507259 37930813209064266455260889)
            ·
              refine ⟨28448109906798199841445667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37930813209064266455260889 28448109906798199841445667)
              ·
                refine ⟨42672164860197299762168501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28448109906798199841445667 42672164860197299762168501)
                ·
                  refine ⟨4000515455643496852703297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42672164860197299762168501 4000515455643496852703297)
                  ·
                    refine ⟨3000386591732622639527473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4000515455643496852703297 3000386591732622639527473)
                    ·
                      refine ⟨2250289943799466979645605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3000386591732622639527473 2250289943799466979645605)
                      ·
                        rfl

theorem cell23_4382424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 1, 5, 2, 2].length) (baseStart_4382424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382424 prefixEnd_4382424 := by exact prefixLift 4382424
  have htrace : WordTrace (prefixWord ++ tailWord_4382424) baseStart_4382424 baseEnd_4382424 := by
    simpa [prefixWord, tailWord_4382424, baseEnd_4382424] using wordTrace_append hprefix tailTrace_4382424
  have hstable : (prefixWord ++ tailWord_4382424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382424).length < 2 ^ (prefixWord ++ tailWord_4382424).sum := by decide
  have hdescent : baseEnd_4382424 < baseStart_4382424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382428 : List Nat := [2, 2, 5, 1, 2, 1, 2, 1, 2, 3, 2]
def baseStart_4382428 : Nat := 118140960795 + 4382428 * 2 ^ 59
def prefixEnd_4382428 : Nat := 4983230072969 + 3 ^ 40 * 4382428 * 2
def baseEnd_4382428 : Nat := 2250291997722084963995587

theorem tailTrace_4382428 : CollatzResearch.WordTrace tailWord_4382428 prefixEnd_4382428 2250291997722084963995587 := by
  unfold tailWord_4382428
  simp only [CollatzResearch.WordTrace]
  refine ⟨79920140283609644979817969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106560187044812859973090625 79920140283609644979817969)
  ·
    refine ⟨59940105212707233734863477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79920140283609644979817969 59940105212707233734863477)
    ·
      refine ⟨5619384863691303162643451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 59940105212707233734863477 5619384863691303162643451)
      ·
        refine ⟨8429077295536954743965177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5619384863691303162643451 8429077295536954743965177)
        ·
          refine ⟨6321807971652716057973883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8429077295536954743965177 6321807971652716057973883)
          ·
            refine ⟨9482711957479074086960825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6321807971652716057973883 9482711957479074086960825)
            ·
              refine ⟨7112033968109305565220619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9482711957479074086960825 7112033968109305565220619)
              ·
                refine ⟨10668050952163958347830929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7112033968109305565220619 10668050952163958347830929)
                ·
                  refine ⟨8001038214122968760873197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10668050952163958347830929 8001038214122968760873197)
                  ·
                    refine ⟨3000389330296113285327449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8001038214122968760873197 3000389330296113285327449)
                    ·
                      refine ⟨2250291997722084963995587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3000389330296113285327449 2250291997722084963995587)
                      ·
                        rfl

theorem cell23_4382428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 2, 1, 2, 3, 2].length) (baseStart_4382428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382428 prefixEnd_4382428 := by exact prefixLift 4382428
  have htrace : WordTrace (prefixWord ++ tailWord_4382428) baseStart_4382428 baseEnd_4382428 := by
    simpa [prefixWord, tailWord_4382428, baseEnd_4382428] using wordTrace_append hprefix tailTrace_4382428
  have hstable : (prefixWord ++ tailWord_4382428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382428).length < 2 ^ (prefixWord ++ tailWord_4382428).sum := by decide
  have hdescent : baseEnd_4382428 < baseStart_4382428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382437 : List Nat := [1, 3, 1, 4, 1, 1, 3, 2, 1, 2, 4]
def baseStart_4382437 : Nat := 118140960795 + 4382437 * 2 ^ 59
def prefixEnd_4382437 : Nat := 4983230072969 + 3 ^ 40 * 4382437 * 2
def baseEnd_4382437 : Nat := 2250296619047975428783045

theorem tailTrace_4382437 : CollatzResearch.WordTrace tailWord_4382437 prefixEnd_4382437 2250296619047975428783045 := by
  unfold tailWord_4382437
  simp only [CollatzResearch.WordTrace]
  refine ⟨159840608824186684496713565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106560405882791122997809043 159840608824186684496713565)
  ·
    refine ⟨59940228309070006686267587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159840608824186684496713565 59940228309070006686267587)
    ·
      refine ⟨89910342463605010029401381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59940228309070006686267587 89910342463605010029401381)
      ·
        refine ⟨16858189211925939380512759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89910342463605010029401381 16858189211925939380512759)
        ·
          refine ⟨25287283817888909070769139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16858189211925939380512759 25287283817888909070769139)
          ·
            refine ⟨37930925726833363606153709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25287283817888909070769139 37930925726833363606153709)
            ·
              refine ⟨14224097147562511352307641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37930925726833363606153709 14224097147562511352307641)
              ·
                refine ⟨10668072860671883514230731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14224097147562511352307641 10668072860671883514230731)
                ·
                  refine ⟨16002109291007825271346097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10668072860671883514230731 16002109291007825271346097)
                  ·
                    refine ⟨12001581968255868953509573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16002109291007825271346097 12001581968255868953509573)
                    ·
                      refine ⟨2250296619047975428783045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12001581968255868953509573 2250296619047975428783045)
                      ·
                        rfl

theorem cell23_4382437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_4382437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382437 prefixEnd_4382437 := by exact prefixLift 4382437
  have htrace : WordTrace (prefixWord ++ tailWord_4382437) baseStart_4382437 baseEnd_4382437 := by
    simpa [prefixWord, tailWord_4382437, baseEnd_4382437] using wordTrace_append hprefix tailTrace_4382437
  have hstable : (prefixWord ++ tailWord_4382437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382437).length < 2 ^ (prefixWord ++ tailWord_4382437).sum := by decide
  have hdescent : baseEnd_4382437 < baseStart_4382437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382441 : List Nat := [1, 2, 1, 1, 1, 2, 3, 7, 1, 2, 2]
def baseStart_4382441 : Nat := 118140960795 + 4382441 * 2 ^ 59
def prefixEnd_4382441 : Nat := 4983230072969 + 3 ^ 40 * 4382441 * 2
def baseEnd_4382441 : Nat := 2250298672970593413133027

theorem tailTrace_4382441 : CollatzResearch.WordTrace tailWord_4382441 prefixEnd_4382441 2250298672970593413133027 := by
  unfold tailWord_4382441
  simp only [CollatzResearch.WordTrace]
  refine ⟨159840754716172193179859177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106560503144114795453239451 159840754716172193179859177)
  ·
    refine ⟨119880566037129144884894383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159840754716172193179859177 119880566037129144884894383)
    ·
      refine ⟨179820849055693717327341575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119880566037129144884894383 179820849055693717327341575)
      ·
        refine ⟨269731273583540575991012363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179820849055693717327341575 269731273583540575991012363)
        ·
          refine ⟨404596910375310863986518545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269731273583540575991012363 404596910375310863986518545)
          ·
            refine ⟨303447682781483147989888909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 404596910375310863986518545 303447682781483147989888909)
            ·
              refine ⟨113792881043056180496208341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 303447682781483147989888909 113792881043056180496208341)
              ·
                refine ⟨2667020649446629230379883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 113792881043056180496208341 2667020649446629230379883)
                ·
                  refine ⟨4000530974169943845569825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2667020649446629230379883 4000530974169943845569825)
                  ·
                    refine ⟨3000398230627457884177369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4000530974169943845569825 3000398230627457884177369)
                    ·
                      refine ⟨2250298672970593413133027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3000398230627457884177369 2250298672970593413133027)
                      ·
                        rfl

theorem cell23_4382441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 7, 1, 2, 2].length) (baseStart_4382441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382441 prefixEnd_4382441 := by exact prefixLift 4382441
  have htrace : WordTrace (prefixWord ++ tailWord_4382441) baseStart_4382441 baseEnd_4382441 := by
    simpa [prefixWord, tailWord_4382441, baseEnd_4382441] using wordTrace_append hprefix tailTrace_4382441
  have hstable : (prefixWord ++ tailWord_4382441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382441).length < 2 ^ (prefixWord ++ tailWord_4382441).sum := by decide
  have hdescent : baseEnd_4382441 < baseStart_4382441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382452 : List Nat := [2, 6, 1, 1, 1, 1, 4, 2, 1, 1, 3]
def baseStart_4382452 : Nat := 118140960795 + 4382452 * 2 ^ 59
def prefixEnd_4382452 : Nat := 4983230072969 + 3 ^ 40 * 4382452 * 2
def baseEnd_4382452 : Nat := 2250304321257792870095477

theorem tailTrace_4382452 : CollatzResearch.WordTrace tailWord_4382452 prefixEnd_4382452 2250304321257792870095477 := by
  unfold tailWord_4382452
  simp only [CollatzResearch.WordTrace]
  refine ⟨79920577959566171029254805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106560770612754894705673073 79920577959566171029254805)
  ·
    refine ⟨3746277091854664266996319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 79920577959566171029254805 3746277091854664266996319)
    ·
      refine ⟨5619415637781996400494479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3746277091854664266996319 5619415637781996400494479)
      ·
        refine ⟨8429123456672994600741719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5619415637781996400494479 8429123456672994600741719)
        ·
          refine ⟨12643685185009491901112579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8429123456672994600741719 12643685185009491901112579)
          ·
            refine ⟨18965527777514237851668869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12643685185009491901112579 18965527777514237851668869)
            ·
              refine ⟨3556036458283919597187913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18965527777514237851668869 3556036458283919597187913)
              ·
                refine ⟨2667027343712939697890935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3556036458283919597187913 2667027343712939697890935)
                ·
                  refine ⟨4000541015569409546836403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2667027343712939697890935 4000541015569409546836403)
                  ·
                    refine ⟨6000811523354114320254605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4000541015569409546836403 6000811523354114320254605)
                    ·
                      refine ⟨2250304321257792870095477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6000811523354114320254605 2250304321257792870095477)
                      ·
                        rfl

theorem cell23_4382452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 4, 2, 1, 1, 3].length) (baseStart_4382452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382452 prefixEnd_4382452 := by exact prefixLift 4382452
  have htrace : WordTrace (prefixWord ++ tailWord_4382452) baseStart_4382452 baseEnd_4382452 := by
    simpa [prefixWord, tailWord_4382452, baseEnd_4382452] using wordTrace_append hprefix tailTrace_4382452
  have hstable : (prefixWord ++ tailWord_4382452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382452).length < 2 ^ (prefixWord ++ tailWord_4382452).sum := by decide
  have hdescent : baseEnd_4382452 < baseStart_4382452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382460 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 1, 9]
def baseStart_4382460 : Nat := 118140960795 + 4382460 * 2 ^ 59
def prefixEnd_4382460 : Nat := 4983230072969 + 3 ^ 40 * 4382460 * 2
def baseEnd_4382460 : Nat := 750102809701009612931813

theorem tailTrace_4382460 : CollatzResearch.WordTrace tailWord_4382460 prefixEnd_4382460 750102809701009612931813 := by
  unfold tailWord_4382460
  simp only [CollatzResearch.WordTrace]
  refine ⟨79920723851551679712400417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106560965135402239616533889 79920723851551679712400417)
  ·
    refine ⟨59940542888663759784300313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79920723851551679712400417 59940542888663759784300313)
    ·
      refine ⟨44955407166497819838225235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59940542888663759784300313 44955407166497819838225235)
      ·
        refine ⟨67433110749746729757337853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44955407166497819838225235 67433110749746729757337853)
        ·
          refine ⟨25287416531155023659001695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67433110749746729757337853 25287416531155023659001695)
          ·
            refine ⟨37931124796732535488502543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25287416531155023659001695 37931124796732535488502543)
            ·
              refine ⟨56896687195098803232753815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37931124796732535488502543 56896687195098803232753815)
              ·
                refine ⟨85345030792648204849130723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56896687195098803232753815 85345030792648204849130723)
                ·
                  refine ⟨128017546188972307273696085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85345030792648204849130723 128017546188972307273696085)
                  ·
                    refine ⟨750102809701009612931813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 128017546188972307273696085 750102809701009612931813)
                    ·
                      rfl

theorem cell23_4382460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_4382460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382460 prefixEnd_4382460 := by exact prefixLift 4382460
  have htrace : WordTrace (prefixWord ++ tailWord_4382460) baseStart_4382460 baseEnd_4382460 := by
    simpa [prefixWord, tailWord_4382460, baseEnd_4382460] using wordTrace_append hprefix tailTrace_4382460
  have hstable : (prefixWord ++ tailWord_4382460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382460).length < 2 ^ (prefixWord ++ tailWord_4382460).sum := by decide
  have hdescent : baseEnd_4382460 < baseStart_4382460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382474 : List Nat := [3, 1, 2, 2, 1, 4, 2, 1, 1, 3, 3]
def baseStart_4382474 : Nat := 118140960795 + 4382474 * 2 ^ 59
def prefixEnd_4382474 : Nat := 4983230072969 + 3 ^ 40 * 4382474 * 2
def baseEnd_4382474 : Nat := 2250315617832191784020375

theorem tailTrace_4382474 : CollatzResearch.WordTrace tailWord_4382474 prefixEnd_4382474 2250315617832191784020375 := by
  unfold tailWord_4382474
  simp only [CollatzResearch.WordTrace]
  refine ⟨39960489581263159953952619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106561305550035093210540317 39960489581263159953952619)
  ·
    refine ⟨59940734371894739930928929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39960489581263159953952619 59940734371894739930928929)
    ·
      refine ⟨44955550778921054948196697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59940734371894739930928929 44955550778921054948196697)
      ·
        refine ⟨33716663084190791211147523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44955550778921054948196697 33716663084190791211147523)
        ·
          refine ⟨50574994626286186816721285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33716663084190791211147523 50574994626286186816721285)
          ·
            refine ⟨9482811492428660028135241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50574994626286186816721285 9482811492428660028135241)
            ·
              refine ⟨7112108619321495021101431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9482811492428660028135241 7112108619321495021101431)
              ·
                refine ⟨10668162928982242531652147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7112108619321495021101431 10668162928982242531652147)
                ·
                  refine ⟨16002244393473363797478221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10668162928982242531652147 16002244393473363797478221)
                  ·
                    refine ⟨6000841647552511424054333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16002244393473363797478221 6000841647552511424054333)
                    ·
                      refine ⟨2250315617832191784020375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6000841647552511424054333 2250315617832191784020375)
                      ·
                        rfl

theorem cell23_4382474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 4, 2, 1, 1, 3, 3].length) (baseStart_4382474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382474 prefixEnd_4382474 := by exact prefixLift 4382474
  have htrace : WordTrace (prefixWord ++ tailWord_4382474) baseStart_4382474 baseEnd_4382474 := by
    simpa [prefixWord, tailWord_4382474, baseEnd_4382474] using wordTrace_append hprefix tailTrace_4382474
  have hstable : (prefixWord ++ tailWord_4382474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382474).length < 2 ^ (prefixWord ++ tailWord_4382474).sum := by decide
  have hdescent : baseEnd_4382474 < baseStart_4382474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382501 : List Nat := [1, 3, 1, 2, 3, 3, 1, 3, 1, 3, 2]
def baseStart_4382501 : Nat := 118140960795 + 4382501 * 2 ^ 59
def prefixEnd_4382501 : Nat := 4983230072969 + 3 ^ 40 * 4382501 * 2
def baseEnd_4382501 : Nat := 2250329481809863178382751

theorem tailTrace_4382501 : CollatzResearch.WordTrace tailWord_4382501 prefixEnd_4382501 2250329481809863178382751 := by
  unfold tailWord_4382501
  simp only [CollatzResearch.WordTrace]
  refine ⟨159842943095954823427043357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106561962063969882284695571 159842943095954823427043357)
  ·
    refine ⟨59941103660983058785141259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159842943095954823427043357 59941103660983058785141259)
    ·
      refine ⟨89911655491474588177711889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59941103660983058785141259 89911655491474588177711889)
      ·
        refine ⟨67433741618605941133283917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89911655491474588177711889 67433741618605941133283917)
        ·
          refine ⟨25287653106977227924981469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67433741618605941133283917 25287653106977227924981469)
          ·
            refine ⟨9482869915116460471868051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25287653106977227924981469 9482869915116460471868051)
            ·
              refine ⟨14224304872674690707802077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9482869915116460471868051 14224304872674690707802077)
              ·
                refine ⟨5334114327253009015425779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14224304872674690707802077 5334114327253009015425779)
                ·
                  refine ⟨8001171490879513523138669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5334114327253009015425779 8001171490879513523138669)
                  ·
                    refine ⟨3000439309079817571177001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8001171490879513523138669 3000439309079817571177001)
                    ·
                      refine ⟨2250329481809863178382751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3000439309079817571177001 2250329481809863178382751)
                      ·
                        rfl

theorem cell23_4382501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 1, 3, 1, 3, 2].length) (baseStart_4382501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382501 prefixEnd_4382501 := by exact prefixLift 4382501
  have htrace : WordTrace (prefixWord ++ tailWord_4382501) baseStart_4382501 baseEnd_4382501 := by
    simpa [prefixWord, tailWord_4382501, baseEnd_4382501] using wordTrace_append hprefix tailTrace_4382501
  have hstable : (prefixWord ++ tailWord_4382501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382501).length < 2 ^ (prefixWord ++ tailWord_4382501).sum := by decide
  have hdescent : baseEnd_4382501 < baseStart_4382501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382531 : List Nat := [1, 1, 1, 3, 1, 7, 1, 1, 1, 4, 2]
def baseStart_4382531 : Nat := 118140960795 + 4382531 * 2 ^ 59
def prefixEnd_4382531 : Nat := 4983230072969 + 3 ^ 40 * 4382531 * 2
def baseEnd_4382531 : Nat := 2250344886229498061007613

theorem tailTrace_4382531 : CollatzResearch.WordTrace tailWord_4382531 prefixEnd_4382531 2250344886229498061007613 := by
  unfold tailWord_4382531
  simp only [CollatzResearch.WordTrace]
  refine ⟨159844037285846138550635447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106562691523897425700423631 159844037285846138550635447)
  ·
    refine ⟨239766055928769207825953171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159844037285846138550635447 239766055928769207825953171)
    ·
      refine ⟨359649083893153811738929757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239766055928769207825953171 359649083893153811738929757)
      ·
        refine ⟨134868406459932679402098659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 359649083893153811738929757 134868406459932679402098659)
        ·
          refine ⟨202302609689899019103147989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134868406459932679402098659 202302609689899019103147989)
          ·
            refine ⟨4741467414607008260230031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 202302609689899019103147989 4741467414607008260230031)
            ·
              refine ⟨7112201121910512390345047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4741467414607008260230031 7112201121910512390345047)
              ·
                refine ⟨10668301682865768585517571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7112201121910512390345047 10668301682865768585517571)
                ·
                  refine ⟨16002452524298652878276357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10668301682865768585517571 16002452524298652878276357)
                  ·
                    refine ⟨3000459848305997414676817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16002452524298652878276357 3000459848305997414676817)
                    ·
                      refine ⟨2250344886229498061007613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3000459848305997414676817 2250344886229498061007613)
                      ·
                        rfl

theorem cell23_4382531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 7, 1, 1, 1, 4, 2].length) (baseStart_4382531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382531 prefixEnd_4382531 := by exact prefixLift 4382531
  have htrace : WordTrace (prefixWord ++ tailWord_4382531) baseStart_4382531 baseEnd_4382531 := by
    simpa [prefixWord, tailWord_4382531, baseEnd_4382531] using wordTrace_append hprefix tailTrace_4382531
  have hstable : (prefixWord ++ tailWord_4382531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382531).length < 2 ^ (prefixWord ++ tailWord_4382531).sum := by decide
  have hdescent : baseEnd_4382531 < baseStart_4382531 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382577 : List Nat := [1, 2, 2, 2, 1, 3, 3, 1, 1, 2, 5]
def baseStart_4382577 : Nat := 118140960795 + 4382577 * 2 ^ 59
def prefixEnd_4382577 : Nat := 4983230072969 + 3 ^ 40 * 4382577 * 2
def baseEnd_4382577 : Nat := 2250368506339604881032401

theorem tailTrace_4382577 : CollatzResearch.WordTrace tailWord_4382577 prefixEnd_4382577 2250368506339604881032401 := by
  unfold tailWord_4382577
  simp only [CollatzResearch.WordTrace]
  refine ⟨159845715043679488406809985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106563810029119658937873323 159845715043679488406809985)
  ·
    refine ⟨119884286282759616305107489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159845715043679488406809985 119884286282759616305107489)
    ·
      refine ⟨89913214712069712228830617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119884286282759616305107489 89913214712069712228830617)
      ·
        refine ⟨67434911034052284171622963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89913214712069712228830617 67434911034052284171622963)
        ·
          refine ⟨101152366551078426257434445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67434911034052284171622963 101152366551078426257434445)
          ·
            refine ⟨37932137456654409846537917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101152366551078426257434445 37932137456654409846537917)
            ·
              refine ⟨14224551546245403692451719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37932137456654409846537917 14224551546245403692451719)
              ·
                refine ⟨21336827319368105538677579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14224551546245403692451719 21336827319368105538677579)
                ·
                  refine ⟨32005240979052158308016369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21336827319368105538677579 32005240979052158308016369)
                  ·
                    refine ⟨24003930734289118731012277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32005240979052158308016369 24003930734289118731012277)
                    ·
                      refine ⟨2250368506339604881032401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24003930734289118731012277 2250368506339604881032401)
                      ·
                        rfl

theorem cell23_4382577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_4382577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382577 prefixEnd_4382577 := by exact prefixLift 4382577
  have htrace : WordTrace (prefixWord ++ tailWord_4382577) baseStart_4382577 baseEnd_4382577 := by
    simpa [prefixWord, tailWord_4382577, baseEnd_4382577] using wordTrace_append hprefix tailTrace_4382577
  have hstable : (prefixWord ++ tailWord_4382577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382577).length < 2 ^ (prefixWord ++ tailWord_4382577).sum := by decide
  have hdescent : baseEnd_4382577 < baseStart_4382577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382587 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 4]
def baseStart_4382587 : Nat := 118140960795 + 4382587 * 2 ^ 59
def prefixEnd_4382587 : Nat := 4983230072969 + 3 ^ 40 * 4382587 * 2
def baseEnd_4382587 : Nat := 2250373641146149841907355

theorem tailTrace_4382587 : CollatzResearch.WordTrace tailWord_4382587 prefixEnd_4382587 2250373641146149841907355 := by
  unfold tailWord_4382587
  simp only [CollatzResearch.WordTrace]
  refine ⟨159846079773643260114674015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106564053182428840076449343 159846079773643260114674015)
  ·
    refine ⟨239769119660464890172011023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159846079773643260114674015 239769119660464890172011023)
    ·
      refine ⟨359653679490697335258016535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239769119660464890172011023 359653679490697335258016535)
      ·
        refine ⟨539480519236046002887024803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359653679490697335258016535 539480519236046002887024803)
        ·
          refine ⟨809220778854069004330537205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539480519236046002887024803 809220778854069004330537205)
          ·
            refine ⟨75864448017568969155987863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 809220778854069004330537205 75864448017568969155987863)
            ·
              refine ⟨113796672026353453733981795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75864448017568969155987863 113796672026353453733981795)
              ·
                refine ⟨170695008039530180600972693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113796672026353453733981795 170695008039530180600972693)
                ·
                  refine ⟨8001328501852977215670595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 170695008039530180600972693 8001328501852977215670595)
                  ·
                    refine ⟨12001992752779465823505893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8001328501852977215670595 12001992752779465823505893)
                    ·
                      refine ⟨2250373641146149841907355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12001992752779465823505893 2250373641146149841907355)
                      ·
                        rfl

theorem cell23_4382587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 6, 1, 4].length) (baseStart_4382587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382587 prefixEnd_4382587 := by exact prefixLift 4382587
  have htrace : WordTrace (prefixWord ++ tailWord_4382587) baseStart_4382587 baseEnd_4382587 := by
    simpa [prefixWord, tailWord_4382587, baseEnd_4382587] using wordTrace_append hprefix tailTrace_4382587
  have hstable : (prefixWord ++ tailWord_4382587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382587).length < 2 ^ (prefixWord ++ tailWord_4382587).sum := by decide
  have hdescent : baseEnd_4382587 < baseStart_4382587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382604 : List Nat := [2, 2, 1, 2, 1, 2, 1, 2, 4, 4, 2]
def baseStart_4382604 : Nat := 118140960795 + 4382604 * 2 ^ 59
def prefixEnd_4382604 : Nat := 4983230072969 + 3 ^ 40 * 4382604 * 2
def baseEnd_4382604 : Nat := 2250382370317276275394777

theorem tailTrace_4382604 : CollatzResearch.WordTrace tailWord_4382604 prefixEnd_4382604 2250382370317276275394777 := by
  unfold tailWord_4382604
  simp only [CollatzResearch.WordTrace]
  refine ⟨79923349907290836009021433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106564466543054448012028577 79923349907290836009021433)
  ·
    refine ⟨59942512430468127006766075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79923349907290836009021433 59942512430468127006766075)
    ·
      refine ⟨89913768645702190510149113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59942512430468127006766075 89913768645702190510149113)
      ·
        refine ⟨67435326484276642882611835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89913768645702190510149113 67435326484276642882611835)
        ·
          refine ⟨101152989726414964323917753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67435326484276642882611835 101152989726414964323917753)
          ·
            refine ⟨75864742294811223242938315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101152989726414964323917753 75864742294811223242938315)
            ·
              refine ⟨113797113442216834864407473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75864742294811223242938315 113797113442216834864407473)
              ·
                refine ⟨85347835081662626148305605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113797113442216834864407473 85347835081662626148305605)
                ·
                  refine ⟨16002719077811742402807301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85347835081662626148305605 16002719077811742402807301)
                  ·
                    refine ⟨3000509827089701700526369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16002719077811742402807301 3000509827089701700526369)
                    ·
                      refine ⟨2250382370317276275394777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3000509827089701700526369 2250382370317276275394777)
                      ·
                        rfl

theorem cell23_4382604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 2, 4, 4, 2].length) (baseStart_4382604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382604 prefixEnd_4382604 := by exact prefixLift 4382604
  have htrace : WordTrace (prefixWord ++ tailWord_4382604) baseStart_4382604 baseEnd_4382604 := by
    simpa [prefixWord, tailWord_4382604, baseEnd_4382604] using wordTrace_append hprefix tailTrace_4382604
  have hstable : (prefixWord ++ tailWord_4382604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382604).length < 2 ^ (prefixWord ++ tailWord_4382604).sum := by decide
  have hdescent : baseEnd_4382604 < baseStart_4382604 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382607 : List Nat := [1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 3]
def baseStart_4382607 : Nat := 118140960795 + 4382607 * 2 ^ 59
def prefixEnd_4382607 : Nat := 4983230072969 + 3 ^ 40 * 4382607 * 2
def baseEnd_4382607 : Nat := 2250383910759239763657263

theorem tailTrace_4382607 : CollatzResearch.WordTrace tailWord_4382607 prefixEnd_4382607 2250383910759239763657263 := by
  unfold tailWord_4382607
  simp only [CollatzResearch.WordTrace]
  refine ⟨159846809233570803530402075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106564539489047202353601383 159846809233570803530402075)
  ·
    refine ⟨239770213850356205295603113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159846809233570803530402075 239770213850356205295603113)
    ·
      refine ⟨179827660387767153971702335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239770213850356205295603113 179827660387767153971702335)
      ·
        refine ⟨269741490581650730957553503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179827660387767153971702335 269741490581650730957553503)
        ·
          refine ⟨404612235872476096436330255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269741490581650730957553503 404612235872476096436330255)
          ·
            refine ⟨606918353808714144654495383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404612235872476096436330255 606918353808714144654495383)
            ·
              refine ⟨910377530713071216981743075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606918353808714144654495383 910377530713071216981743075)
              ·
                refine ⟨1365566296069606825472614613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 910377530713071216981743075 1365566296069606825472614613)
                ·
                  refine ⟨32005460064131409972014405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1365566296069606825472614613 32005460064131409972014405)
                  ·
                    refine ⟨6001023762024639369752701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32005460064131409972014405 6001023762024639369752701)
                    ·
                      refine ⟨2250383910759239763657263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6001023762024639369752701 2250383910759239763657263)
                      ·
                        rfl

theorem cell23_4382607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 7, 4, 3].length) (baseStart_4382607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382607 prefixEnd_4382607 := by exact prefixLift 4382607
  have htrace : WordTrace (prefixWord ++ tailWord_4382607) baseStart_4382607 baseEnd_4382607 := by
    simpa [prefixWord, tailWord_4382607, baseEnd_4382607] using wordTrace_append hprefix tailTrace_4382607
  have hstable : (prefixWord ++ tailWord_4382607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382607).length < 2 ^ (prefixWord ++ tailWord_4382607).sum := by decide
  have hdescent : baseEnd_4382607 < baseStart_4382607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382622 : List Nat := [4, 3, 1, 3, 1, 2, 2, 2, 5]
def baseStart_4382622 : Nat := 118140960795 + 4382622 * 2 ^ 59
def prefixEnd_4382622 : Nat := 4983230072969 + 3 ^ 40 * 4382622 * 2
def baseEnd_4382622 : Nat := 250043512552117467218855

theorem tailTrace_4382622 : CollatzResearch.WordTrace tailWord_4382622 prefixEnd_4382622 250043512552117467218855 := by
  unfold tailWord_4382622
  simp only [CollatzResearch.WordTrace]
  refine ⟨19980919541064557636524765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106564904219010974061465413 19980919541064557636524765)
  ·
    refine ⟨7492844827899209113696787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19980919541064557636524765 7492844827899209113696787)
    ·
      refine ⟨11239267241848813670545181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7492844827899209113696787 11239267241848813670545181)
      ·
        refine ⟨4214725215693305126454443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11239267241848813670545181 4214725215693305126454443)
        ·
          refine ⟨6322087823539957689681665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4214725215693305126454443 6322087823539957689681665)
          ·
            refine ⟨4741565867654968267261249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6322087823539957689681665 4741565867654968267261249)
            ·
              refine ⟨3556174400741226200445937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4741565867654968267261249 3556174400741226200445937)
              ·
                refine ⟨2667130800555919650334453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3556174400741226200445937 2667130800555919650334453)
                ·
                  refine ⟨250043512552117467218855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2667130800555919650334453 250043512552117467218855)
                  ·
                    rfl

theorem cell23_4382622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 5].length) (baseStart_4382622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382622 prefixEnd_4382622 := by exact prefixLift 4382622
  have htrace : WordTrace (prefixWord ++ tailWord_4382622) baseStart_4382622 baseEnd_4382622 := by
    simpa [prefixWord, tailWord_4382622, baseEnd_4382622] using wordTrace_append hprefix tailTrace_4382622
  have hstable : (prefixWord ++ tailWord_4382622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382622).length < 2 ^ (prefixWord ++ tailWord_4382622).sum := by decide
  have hdescent : baseEnd_4382622 < baseStart_4382622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382704 : List Nat := [2, 1, 1, 1, 3, 2, 5, 1, 1, 6]
def baseStart_4382704 : Nat := 118140960795 + 4382704 * 2 ^ 59
def prefixEnd_4382704 : Nat := 4983230072969 + 3 ^ 40 * 4382704 * 2
def baseEnd_4382704 : Nat := 750144572794241961381439

theorem tailTrace_4382704 : CollatzResearch.WordTrace tailWord_4382704 prefixEnd_4382704 750144572794241961381439 := by
  unfold tailWord_4382704
  simp only [CollatzResearch.WordTrace]
  refine ⟨79925173557109694548341583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106566898076146259397788777 79925173557109694548341583)
  ·
    refine ⟨119887760335664541822512375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79925173557109694548341583 119887760335664541822512375)
    ·
      refine ⟨179831640503496812733768563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119887760335664541822512375 179831640503496812733768563)
      ·
        refine ⟨269747460755245219100652845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179831640503496812733768563 269747460755245219100652845)
        ·
          refine ⟨101155297783216957162744817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 269747460755245219100652845 101155297783216957162744817)
          ·
            refine ⟨75866473337412717872058613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101155297783216957162744817 75866473337412717872058613)
            ·
              refine ⟨7112481875382442300505495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75866473337412717872058613 7112481875382442300505495)
              ·
                refine ⟨10668722813073663450758243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7112481875382442300505495 10668722813073663450758243)
                ·
                  refine ⟨16003084219610495176137365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10668722813073663450758243 16003084219610495176137365)
                  ·
                    refine ⟨750144572794241961381439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16003084219610495176137365 750144572794241961381439)
                    ·
                      rfl

theorem cell23_4382704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 1, 6].length) (baseStart_4382704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382704 prefixEnd_4382704 := by exact prefixLift 4382704
  have htrace : WordTrace (prefixWord ++ tailWord_4382704) baseStart_4382704 baseEnd_4382704 := by
    simpa [prefixWord, tailWord_4382704, baseEnd_4382704] using wordTrace_append hprefix tailTrace_4382704
  have hstable : (prefixWord ++ tailWord_4382704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382704).length < 2 ^ (prefixWord ++ tailWord_4382704).sum := by decide
  have hdescent : baseEnd_4382704 < baseStart_4382704 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382731 : List Nat := [1, 1, 1, 1, 6, 1, 1, 5, 1, 2, 3]
def baseStart_4382731 : Nat := 118140960795 + 4382731 * 2 ^ 59
def prefixEnd_4382731 : Nat := 4983230072969 + 3 ^ 40 * 4382731 * 2
def baseEnd_4382731 : Nat := 2250447582360397278506693

theorem tailTrace_4382731 : CollatzResearch.WordTrace tailWord_4382731 prefixEnd_4382731 2250447582360397278506693 := by
  unfold tailWord_4382731
  simp only [CollatzResearch.WordTrace]
  refine ⟨159851331885121572707916047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106567554590081048471944031 159851331885121572707916047)
  ·
    refine ⟨239776997827682359061874071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159851331885121572707916047 239776997827682359061874071)
    ·
      refine ⟨359665496741523538592811107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239776997827682359061874071 359665496741523538592811107)
      ·
        refine ⟨539498245112285307889216661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359665496741523538592811107 539498245112285307889216661)
        ·
          refine ⟨25288980239638373807307031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 539498245112285307889216661 25288980239638373807307031)
          ·
            refine ⟨37933470359457560710960547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25288980239638373807307031 37933470359457560710960547)
            ·
              refine ⟨56900205539186341066440821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37933470359457560710960547 56900205539186341066440821)
              ·
                refine ⟨5334394269298719474978827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56900205539186341066440821 5334394269298719474978827)
                ·
                  refine ⟨8001591403948079212468241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5334394269298719474978827 8001591403948079212468241)
                  ·
                    refine ⟨6001193552961059409351181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8001591403948079212468241 6001193552961059409351181)
                    ·
                      refine ⟨2250447582360397278506693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6001193552961059409351181 2250447582360397278506693)
                      ·
                        rfl

theorem cell23_4382731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 1, 5, 1, 2, 3].length) (baseStart_4382731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382731 prefixEnd_4382731 := by exact prefixLift 4382731
  have htrace : WordTrace (prefixWord ++ tailWord_4382731) baseStart_4382731 baseEnd_4382731 := by
    simpa [prefixWord, tailWord_4382731, baseEnd_4382731] using wordTrace_append hprefix tailTrace_4382731
  have hstable : (prefixWord ++ tailWord_4382731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382731).length < 2 ^ (prefixWord ++ tailWord_4382731).sum := by decide
  have hdescent : baseEnd_4382731 < baseStart_4382731 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382754 : List Nat := [3, 3, 1, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_4382754 : Nat := 118140960795 + 4382754 * 2 ^ 59
def prefixEnd_4382754 : Nat := 4983230072969 + 3 ^ 40 * 4382754 * 2
def baseEnd_4382754 : Nat := 2250459392415450688519087

theorem tailTrace_4382754 : CollatzResearch.WordTrace tailWord_4382754 prefixEnd_4382754 2250459392415450688519087 := by
  unfold tailWord_4382754
  simp only [CollatzResearch.WordTrace]
  refine ⟨39963042691009561909000829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106568113842692165090668877 39963042691009561909000829)
  ·
    refine ⟨14986141009128585715875311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39963042691009561909000829 14986141009128585715875311)
    ·
      refine ⟨22479211513692878573812967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14986141009128585715875311 22479211513692878573812967)
      ·
        refine ⟨33718817270539317860719451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22479211513692878573812967 33718817270539317860719451)
        ·
          refine ⟨50578225905808976791079177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33718817270539317860719451 50578225905808976791079177)
          ·
            refine ⟨37933669429356732593309383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50578225905808976791079177 37933669429356732593309383)
            ·
              refine ⟨56900504144035098889964075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37933669429356732593309383 56900504144035098889964075)
              ·
                refine ⟨85350756216052648334946113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56900504144035098889964075 85350756216052648334946113)
                ·
                  refine ⟨64013067162039486251209585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85350756216052648334946113 64013067162039486251209585)
                  ·
                    refine ⟨48009800371529614688407189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64013067162039486251209585 48009800371529614688407189)
                    ·
                      refine ⟨2250459392415450688519087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48009800371529614688407189 2250459392415450688519087)
                      ·
                        rfl

theorem cell23_4382754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_4382754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382754 prefixEnd_4382754 := by exact prefixLift 4382754
  have htrace : WordTrace (prefixWord ++ tailWord_4382754) baseStart_4382754 baseEnd_4382754 := by
    simpa [prefixWord, tailWord_4382754, baseEnd_4382754] using wordTrace_append hprefix tailTrace_4382754
  have hstable : (prefixWord ++ tailWord_4382754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382754).length < 2 ^ (prefixWord ++ tailWord_4382754).sum := by decide
  have hdescent : baseEnd_4382754 < baseStart_4382754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382782 : List Nat := [4, 2, 1, 3, 2, 1, 3, 1, 1, 2, 3]
def baseStart_4382782 : Nat := 118140960795 + 4382782 * 2 ^ 59
def prefixEnd_4382782 : Nat := 4983230072969 + 3 ^ 40 * 4382782 * 2
def baseEnd_4382782 : Nat := 2250473769873776578968959

theorem tailTrace_4382782 : CollatzResearch.WordTrace tailWord_4382782 prefixEnd_4382782 2250473769873776578968959 := by
  unfold tailWord_4382782
  simp only [CollatzResearch.WordTrace]
  refine ⟨19981649000992101052252825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106568794671957872278681733 19981649000992101052252825)
  ·
    refine ⟨14986236750744075789189619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19981649000992101052252825 14986236750744075789189619)
    ·
      refine ⟨22479355126116113683784429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14986236750744075789189619 22479355126116113683784429)
      ·
        refine ⟨8429758172293542631419161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22479355126116113683784429 8429758172293542631419161)
        ·
          refine ⟨6322318629220156973564371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8429758172293542631419161 6322318629220156973564371)
          ·
            refine ⟨9483477943830235460346557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6322318629220156973564371 9483477943830235460346557)
            ·
              refine ⟨3556304228936338297629959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9483477943830235460346557 3556304228936338297629959)
              ·
                refine ⟨5334456343404507446444939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3556304228936338297629959 5334456343404507446444939)
                ·
                  refine ⟨8001684515106761169667409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5334456343404507446444939 8001684515106761169667409)
                  ·
                    refine ⟨6001263386330070877250557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8001684515106761169667409 6001263386330070877250557)
                    ·
                      refine ⟨2250473769873776578968959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6001263386330070877250557 2250473769873776578968959)
                      ·
                        rfl

theorem cell23_4382782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_4382782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382782 prefixEnd_4382782 := by exact prefixLift 4382782
  have htrace : WordTrace (prefixWord ++ tailWord_4382782) baseStart_4382782 baseEnd_4382782 := by
    simpa [prefixWord, tailWord_4382782, baseEnd_4382782] using wordTrace_append hprefix tailTrace_4382782
  have hstable : (prefixWord ++ tailWord_4382782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382782).length < 2 ^ (prefixWord ++ tailWord_4382782).sum := by decide
  have hdescent : baseEnd_4382782 < baseStart_4382782 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382794 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 2, 6]
def baseStart_4382794 : Nat := 118140960795 + 4382794 * 2 ^ 59
def prefixEnd_4382794 : Nat := 4983230072969 + 3 ^ 40 * 4382794 * 2
def baseEnd_4382794 : Nat := 750159977213876844006301

theorem tailTrace_4382794 : CollatzResearch.WordTrace tailWord_4382794 prefixEnd_4382794 750159977213876844006301 := by
  unfold tailWord_4382794
  simp only [CollatzResearch.WordTrace]
  refine ⟨39963407420973333616864859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106569086455928889644972957 39963407420973333616864859)
  ·
    refine ⟨59945111131460000425297289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39963407420973333616864859 59945111131460000425297289)
    ·
      refine ⟨44958833348595000318972967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59945111131460000425297289 44958833348595000318972967)
      ·
        refine ⟨67438250022892500478459451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44958833348595000318972967 67438250022892500478459451)
        ·
          refine ⟨101157375034338750717689177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67438250022892500478459451 101157375034338750717689177)
          ·
            refine ⟨75868031275754063038266883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101157375034338750717689177 75868031275754063038266883)
            ·
              refine ⟨113802046913631094557400325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75868031275754063038266883 113802046913631094557400325)
              ·
                refine ⟨21337883796305830229512561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 113802046913631094557400325 21337883796305830229512561)
                ·
                  refine ⟨16003412847229372672134421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21337883796305830229512561 16003412847229372672134421)
                  ·
                    refine ⟨750159977213876844006301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16003412847229372672134421 750159977213876844006301)
                    ·
                      rfl

theorem cell23_4382794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 2, 6].length) (baseStart_4382794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382794 prefixEnd_4382794 := by exact prefixLift 4382794
  have htrace : WordTrace (prefixWord ++ tailWord_4382794) baseStart_4382794 baseEnd_4382794 := by
    simpa [prefixWord, tailWord_4382794, baseEnd_4382794] using wordTrace_append hprefix tailTrace_4382794
  have hstable : (prefixWord ++ tailWord_4382794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382794).length < 2 ^ (prefixWord ++ tailWord_4382794).sum := by decide
  have hdescent : baseEnd_4382794 < baseStart_4382794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382801 : List Nat := [1, 2, 2, 1, 3, 1, 1, 1, 5, 4, 2]
def baseStart_4382801 : Nat := 118140960795 + 4382801 * 2 ^ 59
def prefixEnd_4382801 : Nat := 4983230072969 + 3 ^ 40 * 4382801 * 2
def baseEnd_4382801 : Nat := 2250483526006212004631371

theorem tailTrace_4382801 : CollatzResearch.WordTrace tailWord_4382801 prefixEnd_4382801 2250483526006212004631371 := by
  unfold tailWord_4382801
  simp only [CollatzResearch.WordTrace]
  refine ⟨159853884994867974662964257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106569256663245316441976171 159853884994867974662964257)
  ·
    refine ⟨119890413746150980997223193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159853884994867974662964257 119890413746150980997223193)
    ·
      refine ⟨89917810309613235747917395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119890413746150980997223193 89917810309613235747917395)
      ·
        refine ⟨134876715464419853621876093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89917810309613235747917395 134876715464419853621876093)
        ·
          refine ⟨50578768299157445108203535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134876715464419853621876093 50578768299157445108203535)
          ·
            refine ⟨75868152448736167662305303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50578768299157445108203535 75868152448736167662305303)
            ·
              refine ⟨113802228673104251493457955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75868152448736167662305303 113802228673104251493457955)
              ·
                refine ⟨170703343009656377240186933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113802228673104251493457955 170703343009656377240186933)
                ·
                  refine ⟨16003438407155285366267525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 170703343009656377240186933 16003438407155285366267525)
                  ·
                    refine ⟨3000644701341616006175161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16003438407155285366267525 3000644701341616006175161)
                    ·
                      refine ⟨2250483526006212004631371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3000644701341616006175161 2250483526006212004631371)
                      ·
                        rfl

theorem cell23_4382801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 1, 5, 4, 2].length) (baseStart_4382801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382801 prefixEnd_4382801 := by exact prefixLift 4382801
  have htrace : WordTrace (prefixWord ++ tailWord_4382801) baseStart_4382801 baseEnd_4382801 := by
    simpa [prefixWord, tailWord_4382801, baseEnd_4382801] using wordTrace_append hprefix tailTrace_4382801
  have hstable : (prefixWord ++ tailWord_4382801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382801).length < 2 ^ (prefixWord ++ tailWord_4382801).sum := by decide
  have hdescent : baseEnd_4382801 < baseStart_4382801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382851 : List Nat := [1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 3]
def baseStart_4382851 : Nat := 118140960795 + 4382851 * 2 ^ 59
def prefixEnd_4382851 : Nat := 4983230072969 + 3 ^ 40 * 4382851 * 2
def baseEnd_4382851 : Nat := 2250509200038936809006141

theorem tailTrace_4382851 : CollatzResearch.WordTrace tailWord_4382851 prefixEnd_4382851 2250509200038936809006141 := by
  unfold tailWord_4382851
  simp only [CollatzResearch.WordTrace]
  refine ⟨159855708644686833202284407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106570472429791222134856271 159855708644686833202284407)
  ·
    refine ⟨239783562967030249803426611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159855708644686833202284407 239783562967030249803426611)
    ·
      refine ⟨359675344450545374705139917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239783562967030249803426611 359675344450545374705139917)
      ·
        refine ⟨134878254168954515514427469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 359675344450545374705139917 134878254168954515514427469)
        ·
          refine ⟨50579345313357943317910301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134878254168954515514427469 50579345313357943317910301)
          ·
            refine ⟨18967254492509228744216363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50579345313357943317910301 18967254492509228744216363)
            ·
              refine ⟨28450881738763843116324545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18967254492509228744216363 28450881738763843116324545)
              ·
                refine ⟨21338161304072882337243409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28450881738763843116324545 21338161304072882337243409)
                ·
                  refine ⟨16003620978054661752932557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21338161304072882337243409 16003620978054661752932557)
                  ·
                    refine ⟨6001357866770498157349709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16003620978054661752932557 6001357866770498157349709)
                    ·
                      refine ⟨2250509200038936809006141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6001357866770498157349709 2250509200038936809006141)
                      ·
                        rfl

theorem cell23_4382851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 1, 2, 2, 3, 3].length) (baseStart_4382851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382851 prefixEnd_4382851 := by exact prefixLift 4382851
  have htrace : WordTrace (prefixWord ++ tailWord_4382851) baseStart_4382851 baseEnd_4382851 := by
    simpa [prefixWord, tailWord_4382851, baseEnd_4382851] using wordTrace_append hprefix tailTrace_4382851
  have hstable : (prefixWord ++ tailWord_4382851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382851).length < 2 ^ (prefixWord ++ tailWord_4382851).sum := by decide
  have hdescent : baseEnd_4382851 < baseStart_4382851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382858 : List Nat := [3, 1, 2, 3, 1, 2, 2, 4, 5]
def baseStart_4382858 : Nat := 118140960795 + 4382858 * 2 ^ 59
def prefixEnd_4382858 : Nat := 4983230072969 + 3 ^ 40 * 4382858 * 2
def baseEnd_4382858 : Nat := 250056977155946475735401

theorem tailTrace_4382858 : CollatzResearch.WordTrace tailWord_4382858 prefixEnd_4382858 250056977155946475735401 := by
  unfold tailWord_4382858
  simp only [CollatzResearch.WordTrace]
  refine ⟨39963990988915368349447307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106570642637107648931859485 39963990988915368349447307)
  ·
    refine ⟨59945986483373052524170961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39963990988915368349447307 59945986483373052524170961)
    ·
      refine ⟨44959489862529789393128221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59945986483373052524170961 44959489862529789393128221)
      ·
        refine ⟨16859808698448671022423083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44959489862529789393128221 16859808698448671022423083)
        ·
          refine ⟨25289713047673006533634625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16859808698448671022423083 25289713047673006533634625)
          ·
            refine ⟨18967284785754754900225969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25289713047673006533634625 18967284785754754900225969)
            ·
              refine ⟨14225463589316066175169477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18967284785754754900225969 14225463589316066175169477)
              ·
                refine ⟨2667274422996762407844277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14225463589316066175169477 2667274422996762407844277)
                ·
                  refine ⟨250056977155946475735401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2667274422996762407844277 250056977155946475735401)
                  ·
                    rfl

theorem cell23_4382858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 5].length) (baseStart_4382858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382858 prefixEnd_4382858 := by exact prefixLift 4382858
  have htrace : WordTrace (prefixWord ++ tailWord_4382858) baseStart_4382858 baseEnd_4382858 := by
    simpa [prefixWord, tailWord_4382858, baseEnd_4382858] using wordTrace_append hprefix tailTrace_4382858
  have hstable : (prefixWord ++ tailWord_4382858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382858).length < 2 ^ (prefixWord ++ tailWord_4382858).sum := by decide
  have hdescent : baseEnd_4382858 < baseStart_4382858 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4382864 : List Nat := [2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 7]
def baseStart_4382864 : Nat := 118140960795 + 4382864 * 2 ^ 59
def prefixEnd_4382864 : Nat := 4983230072969 + 3 ^ 40 * 4382864 * 2
def baseEnd_4382864 : Nat := 2250515875287445258143581

theorem tailTrace_4382864 : CollatzResearch.WordTrace tailWord_4382864 prefixEnd_4382864 2250515875287445258143581 := by
  unfold tailWord_4382864
  simp only [CollatzResearch.WordTrace]
  refine ⟨79928091396819868211253823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106570788529093157615005097 79928091396819868211253823)
  ·
    refine ⟨119892137095229802316880735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79928091396819868211253823 119892137095229802316880735)
    ·
      refine ⟨179838205642844703475321103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119892137095229802316880735 179838205642844703475321103)
      ·
        refine ⟨269757308464267055212981655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179838205642844703475321103 269757308464267055212981655)
        ·
          refine ⟨404635962696400582819472483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269757308464267055212981655 404635962696400582819472483)
          ·
            refine ⟨606953944044600874229208725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404635962696400582819472483 606953944044600874229208725)
            ·
              refine ⟨28450966127090665979494159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 606953944044600874229208725 28450966127090665979494159)
              ·
                refine ⟨42676449190635998969241239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28450966127090665979494159 42676449190635998969241239)
                ·
                  refine ⟨64014673785953998453861859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42676449190635998969241239 64014673785953998453861859)
                  ·
                    refine ⟨96022010678930997680792789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64014673785953998453861859 96022010678930997680792789)
                    ·
                      refine ⟨2250515875287445258143581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 96022010678930997680792789 2250515875287445258143581)
                      ·
                        rfl

theorem cell23_4382864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 7].length) (baseStart_4382864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4382864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4382864 prefixEnd_4382864 := by exact prefixLift 4382864
  have htrace : WordTrace (prefixWord ++ tailWord_4382864) baseStart_4382864 baseEnd_4382864 := by
    simpa [prefixWord, tailWord_4382864, baseEnd_4382864] using wordTrace_append hprefix tailTrace_4382864
  have hstable : (prefixWord ++ tailWord_4382864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4382864).length < 2 ^ (prefixWord ++ tailWord_4382864).sum := by decide
  have hdescent : baseEnd_4382864 < baseStart_4382864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4382864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383008 : List Nat := [2, 1, 1, 5, 2, 1, 2, 2, 1, 6]
def baseStart_4383008 : Nat := 118140960795 + 4383008 * 2 ^ 59
def prefixEnd_4383008 : Nat := 4983230072969 + 3 ^ 40 * 4383008 * 2
def baseEnd_4383008 : Nat := 750196605500564231580973

theorem tailTrace_4383008 : CollatzResearch.WordTrace tailWord_4383008 prefixEnd_4383008 750196605500564231580973 := by
  unfold tailWord_4383008
  simp only [CollatzResearch.WordTrace]
  refine ⟨79930717452559024507874839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106574289936745366010499785 79930717452559024507874839)
  ·
    refine ⟨119896076178838536761812259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79930717452559024507874839 119896076178838536761812259)
    ·
      refine ⟨179844114268257805142718389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119896076178838536761812259 179844114268257805142718389)
      ·
        refine ⟨16860385712649169232129849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 179844114268257805142718389 16860385712649169232129849)
        ·
          refine ⟨12645289284486876924097387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16860385712649169232129849 12645289284486876924097387)
          ·
            refine ⟨18967933926730315386146081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12645289284486876924097387 18967933926730315386146081)
            ·
              refine ⟨14225950445047736539609561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18967933926730315386146081 14225950445047736539609561)
              ·
                refine ⟨10669462833785802404707171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14225950445047736539609561 10669462833785802404707171)
                ·
                  refine ⟨16004194250678703607060757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10669462833785802404707171 16004194250678703607060757)
                  ·
                    refine ⟨750196605500564231580973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16004194250678703607060757 750196605500564231580973)
                    ·
                      rfl

theorem cell23_4383008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 1, 6].length) (baseStart_4383008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383008 prefixEnd_4383008 := by exact prefixLift 4383008
  have htrace : WordTrace (prefixWord ++ tailWord_4383008) baseStart_4383008 baseEnd_4383008 := by
    simpa [prefixWord, tailWord_4383008, baseEnd_4383008] using wordTrace_append hprefix tailTrace_4383008
  have hstable : (prefixWord ++ tailWord_4383008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383008).length < 2 ^ (prefixWord ++ tailWord_4383008).sum := by decide
  have hdescent : baseEnd_4383008 < baseStart_4383008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383012 : List Nat := [2, 3, 1, 3, 1, 4, 2, 1, 1, 5]
def baseStart_4383012 : Nat := 118140960795 + 4383012 * 2 ^ 59
def prefixEnd_4383012 : Nat := 4983230072969 + 3 ^ 40 * 4383012 * 2
def baseEnd_4383012 : Nat := 750197290141436893030967

theorem tailTrace_4383012 : CollatzResearch.WordTrace tailWord_4383012 prefixEnd_4383012 750197290141436893030967 := by
  unfold tailWord_4383012
  simp only [CollatzResearch.WordTrace]
  refine ⟨79930790398551778849447645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106574387198069038465930193 79930790398551778849447645)
  ·
    refine ⟨29974046399456917068542867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79930790398551778849447645 29974046399456917068542867)
    ·
      refine ⟨44961069599185375602814301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29974046399456917068542867 44961069599185375602814301)
      ·
        refine ⟨16860401099694515851055363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44961069599185375602814301 16860401099694515851055363)
        ·
          refine ⟨25290601649541773776583045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16860401099694515851055363 25290601649541773776583045)
          ·
            refine ⟨4741987809289082583109321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25290601649541773776583045 4741987809289082583109321)
            ·
              refine ⟨3556490856966811937331991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4741987809289082583109321 3556490856966811937331991)
              ·
                refine ⟨5334736285450217905997987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3556490856966811937331991 5334736285450217905997987)
                ·
                  refine ⟨8002104428175326858996981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5334736285450217905997987 8002104428175326858996981)
                  ·
                    refine ⟨750197290141436893030967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8002104428175326858996981 750197290141436893030967)
                    ·
                      rfl

theorem cell23_4383012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_4383012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383012 prefixEnd_4383012 := by exact prefixLift 4383012
  have htrace : WordTrace (prefixWord ++ tailWord_4383012) baseStart_4383012 baseEnd_4383012 := by
    simpa [prefixWord, tailWord_4383012, baseEnd_4383012] using wordTrace_append hprefix tailTrace_4383012
  have hstable : (prefixWord ++ tailWord_4383012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383012).length < 2 ^ (prefixWord ++ tailWord_4383012).sum := by decide
  have hdescent : baseEnd_4383012 < baseStart_4383012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383025 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 4, 4]
def baseStart_4383025 : Nat := 118140960795 + 4383025 * 2 ^ 59
def prefixEnd_4383025 : Nat := 4983230072969 + 3 ^ 40 * 4383025 * 2
def baseEnd_4383025 : Nat := 750199515224273042743447

theorem tailTrace_4383025 : CollatzResearch.WordTrace tailWord_4383025 prefixEnd_4383025 750199515224273042743447 := by
  unfold tailWord_4383025
  simp only [CollatzResearch.WordTrace]
  refine ⟨159862054946056460919118529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106574703297370973946079019 159862054946056460919118529)
  ·
    refine ⟨119896541209542345689338897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159862054946056460919118529 119896541209542345689338897)
    ·
      refine ⟨89922405907156759267004173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119896541209542345689338897 89922405907156759267004173)
      ·
        refine ⟨33720902215183784725126565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89922405907156759267004173 33720902215183784725126565)
        ·
          refine ⟨6322669165346959635961231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33720902215183784725126565 6322669165346959635961231)
          ·
            refine ⟨9484003748020439453941847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6322669165346959635961231 9484003748020439453941847)
            ·
              refine ⟨14226005622030659180912771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9484003748020439453941847 14226005622030659180912771)
              ·
                refine ⟨21339008433045988771369157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14226005622030659180912771 21339008433045988771369157)
                ·
                  refine ⟨4001064081196122894631717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21339008433045988771369157 4001064081196122894631717)
                  ·
                    refine ⟨750199515224273042743447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4001064081196122894631717 750199515224273042743447)
                    ·
                      rfl

theorem cell23_4383025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 4].length) (baseStart_4383025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383025 prefixEnd_4383025 := by exact prefixLift 4383025
  have htrace : WordTrace (prefixWord ++ tailWord_4383025) baseStart_4383025 baseEnd_4383025 := by
    simpa [prefixWord, tailWord_4383025, baseEnd_4383025] using wordTrace_append hprefix tailTrace_4383025
  have hstable : (prefixWord ++ tailWord_4383025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383025).length < 2 ^ (prefixWord ++ tailWord_4383025).sum := by decide
  have hdescent : baseEnd_4383025 < baseStart_4383025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383082 : List Nat := [3, 1, 3, 3, 1, 1, 2, 1, 4, 1, 3]
def baseStart_4383082 : Nat := 118140960795 + 4383082 * 2 ^ 59
def prefixEnd_4383082 : Nat := 4983230072969 + 3 ^ 40 * 4383082 * 2
def baseEnd_4383082 : Nat := 2250627814070125405217579

theorem tailTrace_4383082 : CollatzResearch.WordTrace tailWord_4383082 prefixEnd_4383082 2250627814070125405217579 := by
  unfold tailWord_4383082
  simp only [CollatzResearch.WordTrace]
  refine ⟨39966033476712489913485875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106576089271233306435962333 39966033476712489913485875)
  ·
    refine ⟨59949050215068734870228813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39966033476712489913485875 59949050215068734870228813)
    ·
      refine ⟨22480893830650775576335805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59949050215068734870228813 22480893830650775576335805)
      ·
        refine ⟨8430335186494040841125927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22480893830650775576335805 8430335186494040841125927)
        ·
          refine ⟨12645502779741061261688891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8430335186494040841125927 12645502779741061261688891)
          ·
            refine ⟨18968254169611591892533337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12645502779741061261688891 18968254169611591892533337)
            ·
              refine ⟨14226190627208693919400003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18968254169611591892533337 14226190627208693919400003)
              ·
                refine ⟨21339285940813040879100005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14226190627208693919400003 21339285940813040879100005)
                ·
                  refine ⟨4001116113902445164831251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21339285940813040879100005 4001116113902445164831251)
                  ·
                    refine ⟨6001674170853667747246877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4001116113902445164831251 6001674170853667747246877)
                    ·
                      refine ⟨2250627814070125405217579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6001674170853667747246877 2250627814070125405217579)
                      ·
                        rfl

theorem cell23_4383082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_4383082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383082 prefixEnd_4383082 := by exact prefixLift 4383082
  have htrace : WordTrace (prefixWord ++ tailWord_4383082) baseStart_4383082 baseEnd_4383082 := by
    simpa [prefixWord, tailWord_4383082, baseEnd_4383082] using wordTrace_append hprefix tailTrace_4383082
  have hstable : (prefixWord ++ tailWord_4383082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383082).length < 2 ^ (prefixWord ++ tailWord_4383082).sum := by decide
  have hdescent : baseEnd_4383082 < baseStart_4383082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383099 : List Nat := [1, 1, 1, 1, 1, 9, 2, 1, 2, 1, 3]
def baseStart_4383099 : Nat := 118140960795 + 4383099 * 2 ^ 59
def prefixEnd_4383099 : Nat := 4983230072969 + 3 ^ 40 * 4383099 * 2
def baseEnd_4383099 : Nat := 2250636543241251838705001

theorem tailTrace_4383099 : CollatzResearch.WordTrace tailWord_4383099 prefixEnd_4383099 2250636543241251838705001 := by
  unfold tailWord_4383099
  simp only [CollatzResearch.WordTrace]
  refine ⟨159864753947788371557312351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106576502631858914371541567 159864753947788371557312351)
  ·
    refine ⟨239797130921682557335968527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159864753947788371557312351 239797130921682557335968527)
    ·
      refine ⟨359695696382523836003952791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239797130921682557335968527 359695696382523836003952791)
      ·
        refine ⟨539543544573785754005929187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359695696382523836003952791 539543544573785754005929187)
        ·
          refine ⟨809315316860678631008893781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539543544573785754005929187 809315316860678631008893781)
          ·
            refine ⟨4742081934730538853567737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 809315316860678631008893781 4742081934730538853567737)
            ·
              refine ⟨3556561451047904140175803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4742081934730538853567737 3556561451047904140175803)
              ·
                refine ⟨5334842176571856210263705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3556561451047904140175803 5334842176571856210263705)
                ·
                  refine ⟨4001131632428892157697779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5334842176571856210263705 4001131632428892157697779)
                  ·
                    refine ⟨6001697448643338236546669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4001131632428892157697779 6001697448643338236546669)
                    ·
                      refine ⟨2250636543241251838705001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6001697448643338236546669 2250636543241251838705001)
                      ·
                        rfl

theorem cell23_4383099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 9, 2, 1, 2, 1, 3].length) (baseStart_4383099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383099 prefixEnd_4383099 := by exact prefixLift 4383099
  have htrace : WordTrace (prefixWord ++ tailWord_4383099) baseStart_4383099 baseEnd_4383099 := by
    simpa [prefixWord, tailWord_4383099, baseEnd_4383099] using wordTrace_append hprefix tailTrace_4383099
  have hstable : (prefixWord ++ tailWord_4383099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383099).length < 2 ^ (prefixWord ++ tailWord_4383099).sum := by decide
  have hdescent : baseEnd_4383099 < baseStart_4383099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383108 : List Nat := [2, 3, 2, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_4383108 : Nat := 118140960795 + 4383108 * 2 ^ 59
def prefixEnd_4383108 : Nat := 4983230072969 + 3 ^ 40 * 4383108 * 2
def baseEnd_4383108 : Nat := 2250641164567142303492459

theorem tailTrace_4383108 : CollatzResearch.WordTrace tailWord_4383108 prefixEnd_4383108 2250641164567142303492459 := by
  unfold tailWord_4383108
  simp only [CollatzResearch.WordTrace]
  refine ⟨79932541102377883047194989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106576721469837177396259985 79932541102377883047194989)
  ·
    refine ⟨29974702913391706142698121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79932541102377883047194989 29974702913391706142698121)
    ·
      refine ⟨22481027185043779607023591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29974702913391706142698121 22481027185043779607023591)
      ·
        refine ⟨33721540777565669410535387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22481027185043779607023591 33721540777565669410535387)
        ·
          refine ⟨50582311166348504115803081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33721540777565669410535387 50582311166348504115803081)
          ·
            refine ⟨37936733374761378086852311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50582311166348504115803081 37936733374761378086852311)
            ·
              refine ⟨56905100062142067130278467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37936733374761378086852311 56905100062142067130278467)
              ·
                refine ⟨85357650093213100695417701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56905100062142067130278467 85357650093213100695417701)
                ·
                  refine ⟨16004559392477456380390819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85357650093213100695417701 16004559392477456380390819)
                  ·
                    refine ⟨24006839088716184570586229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16004559392477456380390819 24006839088716184570586229)
                    ·
                      refine ⟨2250641164567142303492459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24006839088716184570586229 2250641164567142303492459)
                      ·
                        rfl

theorem cell23_4383108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_4383108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383108 prefixEnd_4383108 := by exact prefixLift 4383108
  have htrace : WordTrace (prefixWord ++ tailWord_4383108) baseStart_4383108 baseEnd_4383108 := by
    simpa [prefixWord, tailWord_4383108, baseEnd_4383108] using wordTrace_append hprefix tailTrace_4383108
  have hstable : (prefixWord ++ tailWord_4383108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383108).length < 2 ^ (prefixWord ++ tailWord_4383108).sum := by decide
  have hdescent : baseEnd_4383108 < baseStart_4383108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383139 : List Nat := [1, 1, 1, 4, 1, 5, 2, 2, 2, 2, 2]
def baseStart_4383139 : Nat := 118140960795 + 4383139 * 2 ^ 59
def prefixEnd_4383139 : Nat := 4983230072969 + 3 ^ 40 * 4383139 * 2
def baseEnd_4383139 : Nat := 2250657082467431682204817

theorem tailTrace_4383139 : CollatzResearch.WordTrace tailWord_4383139 prefixEnd_4383139 2250657082467431682204817 := by
  unfold tailWord_4383139
  simp only [CollatzResearch.WordTrace]
  refine ⟨159866212867643458388768471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106577475245095638925845647 159866212867643458388768471)
  ·
    refine ⟨239799319301465187583152707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159866212867643458388768471 239799319301465187583152707)
    ·
      refine ⟨359698978952197781374729061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239799319301465187583152707 359698978952197781374729061)
      ·
        refine ⟨67443558553537084007761699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 359698978952197781374729061 67443558553537084007761699)
        ·
          refine ⟨101165337830305626011642549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67443558553537084007761699 101165337830305626011642549)
          ·
            refine ⟨9484250421591152438591489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101165337830305626011642549 9484250421591152438591489)
            ·
              refine ⟨7113187816193364328943617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9484250421591152438591489 7113187816193364328943617)
              ·
                refine ⟨5334890862145023246707713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7113187816193364328943617 5334890862145023246707713)
                ·
                  refine ⟨4001168146608767435030785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5334890862145023246707713 4001168146608767435030785)
                  ·
                    refine ⟨3000876109956575576273089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4001168146608767435030785 3000876109956575576273089)
                    ·
                      refine ⟨2250657082467431682204817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3000876109956575576273089 2250657082467431682204817)
                      ·
                        rfl

theorem cell23_4383139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 2, 2, 2, 2, 2].length) (baseStart_4383139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383139 prefixEnd_4383139 := by exact prefixLift 4383139
  have htrace : WordTrace (prefixWord ++ tailWord_4383139) baseStart_4383139 baseEnd_4383139 := by
    simpa [prefixWord, tailWord_4383139, baseEnd_4383139] using wordTrace_append hprefix tailTrace_4383139
  have hstable : (prefixWord ++ tailWord_4383139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383139).length < 2 ^ (prefixWord ++ tailWord_4383139).sum := by decide
  have hdescent : baseEnd_4383139 < baseStart_4383139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383175 : List Nat := [1, 1, 4, 1, 1, 4, 3, 1, 2, 5]
def baseStart_4383175 : Nat := 118140960795 + 4383175 * 2 ^ 59
def prefixEnd_4383175 : Nat := 4983230072969 + 3 ^ 40 * 4383175 * 2
def baseEnd_4383175 : Nat := 750225189256997847118217

theorem tailTrace_4383175 : CollatzResearch.WordTrace tailWord_4383175 prefixEnd_4383175 750225189256997847118217 := by
  unfold tailWord_4383175
  simp only [CollatzResearch.WordTrace]
  refine ⟨159867525895513036537078979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106578350597008691024719319 159867525895513036537078979)
  ·
    refine ⟨239801288843269554805618469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159867525895513036537078979 239801288843269554805618469)
    ·
      refine ⟨44962741658113041526053463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 239801288843269554805618469 44962741658113041526053463)
      ·
        refine ⟨67444112487169562289080195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44962741658113041526053463 67444112487169562289080195)
        ·
          refine ⟨101166168730754343433620293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67444112487169562289080195 101166168730754343433620293)
          ·
            refine ⟨18968656637016439393803805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101166168730754343433620293 18968656637016439393803805)
            ·
              refine ⟨7113246238881164772676427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18968656637016439393803805 7113246238881164772676427)
              ·
                refine ⟨10669869358321747159014641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7113246238881164772676427 10669869358321747159014641)
                ·
                  refine ⟨8002402018741310369260981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10669869358321747159014641 8002402018741310369260981)
                  ·
                    refine ⟨750225189256997847118217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8002402018741310369260981 750225189256997847118217)
                    ·
                      rfl

theorem cell23_4383175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_4383175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383175 prefixEnd_4383175 := by exact prefixLift 4383175
  have htrace : WordTrace (prefixWord ++ tailWord_4383175) baseStart_4383175 baseEnd_4383175 := by
    simpa [prefixWord, tailWord_4383175, baseEnd_4383175] using wordTrace_append hprefix tailTrace_4383175
  have hstable : (prefixWord ++ tailWord_4383175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383175).length < 2 ^ (prefixWord ++ tailWord_4383175).sum := by decide
  have hdescent : baseEnd_4383175 < baseStart_4383175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383222 : List Nat := [5, 1, 1, 1, 2, 1, 1, 4, 3, 4]
def baseStart_4383222 : Nat := 118140960795 + 4383222 * 2 ^ 59
def prefixEnd_4383222 : Nat := 4983230072969 + 3 ^ 40 * 4383222 * 2
def baseEnd_4383222 : Nat := 750233233787251619155645

theorem tailTrace_4383222 : CollatzResearch.WordTrace tailWord_4383222 prefixEnd_4383222 750233233787251619155645 := by
  unfold tailWord_4383222
  simp only [CollatzResearch.WordTrace]
  refine ⟨9991827507896422722752495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106579493417561842376026613 9991827507896422722752495)
  ·
    refine ⟨14987741261844634084128743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9991827507896422722752495 14987741261844634084128743)
    ·
      refine ⟨22481611892766951126193115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14987741261844634084128743 22481611892766951126193115)
      ·
        refine ⟨33722417839150426689289673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22481611892766951126193115 33722417839150426689289673)
        ·
          refine ⟨25291813379362820016967255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33722417839150426689289673 25291813379362820016967255)
          ·
            refine ⟨37937720069044230025450883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25291813379362820016967255 37937720069044230025450883)
            ·
              refine ⟨56906580103566345038176325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37937720069044230025450883 56906580103566345038176325)
              ·
                refine ⟨10669983769418689694658061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56906580103566345038176325 10669983769418689694658061)
                ·
                  refine ⟨4001243913532008635496773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10669983769418689694658061 4001243913532008635496773)
                  ·
                    refine ⟨750233233787251619155645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4001243913532008635496773 750233233787251619155645)
                    ·
                      rfl

theorem cell23_4383222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 3, 4].length) (baseStart_4383222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383222 prefixEnd_4383222 := by exact prefixLift 4383222
  have htrace : WordTrace (prefixWord ++ tailWord_4383222) baseStart_4383222 baseEnd_4383222 := by
    simpa [prefixWord, tailWord_4383222, baseEnd_4383222] using wordTrace_append hprefix tailTrace_4383222
  have hstable : (prefixWord ++ tailWord_4383222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383222).length < 2 ^ (prefixWord ++ tailWord_4383222).sum := by decide
  have hdescent : baseEnd_4383222 < baseStart_4383222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383252 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 8]
def baseStart_4383252 : Nat := 118140960795 + 4383252 * 2 ^ 59
def prefixEnd_4383252 : Nat := 4983230072969 + 3 ^ 40 * 4383252 * 2
def baseEnd_4383252 : Nat := 250079456197932193343533

theorem tailTrace_4383252 : CollatzResearch.WordTrace tailWord_4383252 prefixEnd_4383252 250079456197932193343533 := by
  unfold tailWord_4383252
  simp only [CollatzResearch.WordTrace]
  refine ⟨79935167158117039343816005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106580222877489385791754673 79935167158117039343816005)
  ·
    refine ⟨14987843842146944876965501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79935167158117039343816005 14987843842146944876965501)
    ·
      refine ⟨5620441440805104328862063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14987843842146944876965501 5620441440805104328862063)
      ·
        refine ⟨8430662161207656493293095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5620441440805104328862063 8430662161207656493293095)
        ·
          refine ⟨12645993241811484739939643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8430662161207656493293095 12645993241811484739939643)
          ·
            refine ⟨18968989862717227109909465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12645993241811484739939643 18968989862717227109909465)
            ·
              refine ⟨14226742397037920332432099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18968989862717227109909465 14226742397037920332432099)
              ·
                refine ⟨21340113595556880498648149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14226742397037920332432099 21340113595556880498648149)
                ·
                  refine ⟨250079456197932193343533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21340113595556880498648149 250079456197932193343533)
                  ·
                    rfl

theorem cell23_4383252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_4383252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383252 prefixEnd_4383252 := by exact prefixLift 4383252
  have htrace : WordTrace (prefixWord ++ tailWord_4383252) baseStart_4383252 baseEnd_4383252 := by
    simpa [prefixWord, tailWord_4383252, baseEnd_4383252] using wordTrace_append hprefix tailTrace_4383252
  have hstable : (prefixWord ++ tailWord_4383252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383252).length < 2 ^ (prefixWord ++ tailWord_4383252).sum := by decide
  have hdescent : baseEnd_4383252 < baseStart_4383252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383256 : List Nat := [2, 1, 2, 3, 3, 2, 3, 2, 1, 4]
def baseStart_4383256 : Nat := 118140960795 + 4383256 * 2 ^ 59
def prefixEnd_4383256 : Nat := 4983230072969 + 3 ^ 40 * 4383256 * 2
def baseEnd_4383256 : Nat := 750239053234669241480593

theorem tailTrace_4383256 : CollatzResearch.WordTrace tailWord_4383256 prefixEnd_4383256 750239053234669241480593 := by
  unfold tailWord_4383256
  simp only [CollatzResearch.WordTrace]
  refine ⟨79935240104109793685388811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106580320138813058247185081 79935240104109793685388811)
  ·
    refine ⟨119902860156164690528083217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79935240104109793685388811 119902860156164690528083217)
    ·
      refine ⟨89927145117123517896062413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119902860156164690528083217 89927145117123517896062413)
      ·
        refine ⟨33722679418921319211023405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89927145117123517896062413 33722679418921319211023405)
        ·
          refine ⟨12646004782095494704133777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33722679418921319211023405 12646004782095494704133777)
          ·
            refine ⟨9484503586571621028100333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12646004782095494704133777 9484503586571621028100333)
            ·
              refine ⟨3556688844964357885537625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9484503586571621028100333 3556688844964357885537625)
              ·
                refine ⟨2667516633723268414153219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3556688844964357885537625 2667516633723268414153219)
                ·
                  refine ⟨4001274950584902621229829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2667516633723268414153219 4001274950584902621229829)
                  ·
                    refine ⟨750239053234669241480593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4001274950584902621229829 750239053234669241480593)
                    ·
                      rfl

theorem cell23_4383256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 1, 4].length) (baseStart_4383256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383256 prefixEnd_4383256 := by exact prefixLift 4383256
  have htrace : WordTrace (prefixWord ++ tailWord_4383256) baseStart_4383256 baseEnd_4383256 := by
    simpa [prefixWord, tailWord_4383256, baseEnd_4383256] using wordTrace_append hprefix tailTrace_4383256
  have hstable : (prefixWord ++ tailWord_4383256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383256).length < 2 ^ (prefixWord ++ tailWord_4383256).sum := by decide
  have hdescent : baseEnd_4383256 < baseStart_4383256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383265 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 3, 5]
def baseStart_4383265 : Nat := 118140960795 + 4383265 * 2 ^ 59
def prefixEnd_4383265 : Nat := 4983230072969 + 3 ^ 40 * 4383265 * 2
def baseEnd_4383265 : Nat := 750240593676632729743079

theorem tailTrace_4383265 : CollatzResearch.WordTrace tailWord_4383265 prefixEnd_4383265 750240593676632729743079 := by
  unfold tailWord_4383265
  simp only [CollatzResearch.WordTrace]
  refine ⟨159870808465186981907855249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106580538976791321271903499 159870808465186981907855249)
  ·
    refine ⟨119903106348890236430891437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159870808465186981907855249 119903106348890236430891437)
    ·
      refine ⟨44963664880833838661584289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119903106348890236430891437 44963664880833838661584289)
      ·
        refine ⟨33722748660625378996188217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44963664880833838661584289 33722748660625378996188217)
        ·
          refine ⟨25292061495469034247141163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33722748660625378996188217 25292061495469034247141163)
          ·
            refine ⟨37938092243203551370711745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25292061495469034247141163 37938092243203551370711745)
            ·
              refine ⟨28453569182402663528033809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37938092243203551370711745 28453569182402663528033809)
              ·
                refine ⟨21340176886801997646025357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28453569182402663528033809 21340176886801997646025357)
                ·
                  refine ⟨8002566332550749117259509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21340176886801997646025357 8002566332550749117259509)
                  ·
                    refine ⟨750240593676632729743079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8002566332550749117259509 750240593676632729743079)
                    ·
                      rfl

theorem cell23_4383265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_4383265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383265 prefixEnd_4383265 := by exact prefixLift 4383265
  have htrace : WordTrace (prefixWord ++ tailWord_4383265) baseStart_4383265 baseEnd_4383265 := by
    simpa [prefixWord, tailWord_4383265, baseEnd_4383265] using wordTrace_append hprefix tailTrace_4383265
  have hstable : (prefixWord ++ tailWord_4383265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383265).length < 2 ^ (prefixWord ++ tailWord_4383265).sum := by decide
  have hdescent : baseEnd_4383265 < baseStart_4383265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383282 : List Nat := [3, 2, 1, 1, 2, 1, 5, 2, 1, 5]
def baseStart_4383282 : Nat := 118140960795 + 4383282 * 2 ^ 59
def prefixEnd_4383282 : Nat := 4983230072969 + 3 ^ 40 * 4383282 * 2
def baseEnd_4383282 : Nat := 750243503400341540905553

theorem tailTrace_4383282 : CollatzResearch.WordTrace tailWord_4383282 prefixEnd_4383282 750243503400341540905553 := by
  unfold tailWord_4383282
  simp only [CollatzResearch.WordTrace]
  refine ⟨39967857126531348452806025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106580952337416929207482733 39967857126531348452806025)
  ·
    refine ⟨29975892844898511339604519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39967857126531348452806025 29975892844898511339604519)
    ·
      refine ⟨44963839267347767009406779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29975892844898511339604519 44963839267347767009406779)
      ·
        refine ⟨67445758901021650514110169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44963839267347767009406779 67445758901021650514110169)
        ·
          refine ⟨50584319175766237885582627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67445758901021650514110169 50584319175766237885582627)
          ·
            refine ⟨75876478763649356828373941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50584319175766237885582627 75876478763649356828373941)
            ·
              refine ⟨7113419884092127202660057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75876478763649356828373941 7113419884092127202660057)
              ·
                refine ⟨5335064913069095401995043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7113419884092127202660057 5335064913069095401995043)
                ·
                  refine ⟨8002597369603643102992565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5335064913069095401995043 8002597369603643102992565)
                  ·
                    refine ⟨750243503400341540905553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8002597369603643102992565 750243503400341540905553)
                    ·
                      rfl

theorem cell23_4383282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 1, 5].length) (baseStart_4383282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383282 prefixEnd_4383282 := by exact prefixLift 4383282
  have htrace : WordTrace (prefixWord ++ tailWord_4383282) baseStart_4383282 baseEnd_4383282 := by
    simpa [prefixWord, tailWord_4383282, baseEnd_4383282] using wordTrace_append hprefix tailTrace_4383282
  have hstable : (prefixWord ++ tailWord_4383282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383282).length < 2 ^ (prefixWord ++ tailWord_4383282).sum := by decide
  have hdescent : baseEnd_4383282 < baseStart_4383282 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383289 : List Nat := [1, 2, 1, 5, 1, 1, 4, 1, 2, 3, 2]
def baseStart_4383289 : Nat := 118140960795 + 4383289 * 2 ^ 59
def prefixEnd_4383289 : Nat := 4983230072969 + 3 ^ 40 * 4383289 * 2
def baseEnd_4383289 : Nat := 2250734104565606095329127

theorem tailTrace_4383289 : CollatzResearch.WordTrace tailWord_4383289 prefixEnd_4383289 2250734104565606095329127 := by
  unfold tailWord_4383289
  simp only [CollatzResearch.WordTrace]
  refine ⟨159871683817100034006728921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106581122544733356004485947 159871683817100034006728921)
  ·
    refine ⟨119903762862825025505046691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159871683817100034006728921 119903762862825025505046691)
    ·
      refine ⟨179855644294237538257570037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119903762862825025505046691 179855644294237538257570037)
      ·
        refine ⟨16861466652584769211647191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 179855644294237538257570037 16861466652584769211647191)
        ·
          refine ⟨25292199978877153817470787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16861466652584769211647191 25292199978877153817470787)
          ·
            refine ⟨37938299968315730726206181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25292199978877153817470787 37938299968315730726206181)
            ·
              refine ⟨7113431244059199511163659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37938299968315730726206181 7113431244059199511163659)
              ·
                refine ⟨10670146866088799266745489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7113431244059199511163659 10670146866088799266745489)
                ·
                  refine ⟨8002610149566599450059117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10670146866088799266745489 8002610149566599450059117)
                  ·
                    refine ⟨3000978806087474793772169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8002610149566599450059117 3000978806087474793772169)
                    ·
                      refine ⟨2250734104565606095329127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3000978806087474793772169 2250734104565606095329127)
                      ·
                        rfl

theorem cell23_4383289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_4383289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383289 prefixEnd_4383289 := by exact prefixLift 4383289
  have htrace : WordTrace (prefixWord ++ tailWord_4383289) baseStart_4383289 baseEnd_4383289 := by
    simpa [prefixWord, tailWord_4383289, baseEnd_4383289] using wordTrace_append hprefix tailTrace_4383289
  have hstable : (prefixWord ++ tailWord_4383289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383289).length < 2 ^ (prefixWord ++ tailWord_4383289).sum := by decide
  have hdescent : baseEnd_4383289 < baseStart_4383289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383295 : List Nat := [1, 1, 2, 2, 3, 2, 3, 2, 1, 6]
def baseStart_4383295 : Nat := 118140960795 + 4383295 * 2 ^ 59
def prefixEnd_4383295 : Nat := 4983230072969 + 3 ^ 40 * 4383295 * 2
def baseEnd_4383295 : Nat := 750245728483177690618033

theorem tailTrace_4383295 : CollatzResearch.WordTrace tailWord_4383295 prefixEnd_4383295 750245728483177690618033 := by
  unfold tailWord_4383295
  simp only [CollatzResearch.WordTrace]
  refine ⟨159871902655078297031447339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106581268436718864687631559 159871902655078297031447339)
  ·
    refine ⟨239807853982617445547171009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159871902655078297031447339 239807853982617445547171009)
    ·
      refine ⟨179855890486963084160378257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239807853982617445547171009 179855890486963084160378257)
      ·
        refine ⟨134891917865222313120283693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179855890486963084160378257 134891917865222313120283693)
        ·
          refine ⟨50584469199458367420106385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134891917865222313120283693 50584469199458367420106385)
          ·
            refine ⟨37938351899593775565079789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50584469199458367420106385 37938351899593775565079789)
            ·
              refine ⟨14226881962347665836904921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37938351899593775565079789 14226881962347665836904921)
              ·
                refine ⟨10670161471760749377678691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14226881962347665836904921 10670161471760749377678691)
                ·
                  refine ⟨16005242207641124066518037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10670161471760749377678691 16005242207641124066518037)
                  ·
                    refine ⟨750245728483177690618033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16005242207641124066518037 750245728483177690618033)
                    ·
                      rfl

theorem cell23_4383295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 6].length) (baseStart_4383295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383295 prefixEnd_4383295 := by exact prefixLift 4383295
  have htrace : WordTrace (prefixWord ++ tailWord_4383295) baseStart_4383295 baseEnd_4383295 := by
    simpa [prefixWord, tailWord_4383295, baseEnd_4383295] using wordTrace_append hprefix tailTrace_4383295
  have hstable : (prefixWord ++ tailWord_4383295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383295).length < 2 ^ (prefixWord ++ tailWord_4383295).sum := by decide
  have hdescent : baseEnd_4383295 < baseStart_4383295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383313 : List Nat := [1, 2, 2, 1, 3, 5, 2, 2, 1, 1, 3]
def baseStart_4383313 : Nat := 118140960795 + 4383313 * 2 ^ 59
def prefixEnd_4383313 : Nat := 4983230072969 + 3 ^ 40 * 4383313 * 2
def baseEnd_4383313 : Nat := 2250746428101314001429017

theorem tailTrace_4383313 : CollatzResearch.WordTrace tailWord_4383313 prefixEnd_4383313 2250746428101314001429017 := by
  unfold tailWord_4383313
  simp only [CollatzResearch.WordTrace]
  refine ⟨159872559169013086105602593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106581706112675390737068395 159872559169013086105602593)
  ·
    refine ⟨119904419376759814579201945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159872559169013086105602593 119904419376759814579201945)
    ·
      refine ⟨89928314532569860934401459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119904419376759814579201945 89928314532569860934401459)
      ·
        refine ⟨134892471798854791401602189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89928314532569860934401459 134892471798854791401602189)
        ·
          refine ⟨50584676924570546775600821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134892471798854791401602189 50584676924570546775600821)
          ·
            refine ⟨4742313461678488760212577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50584676924570546775600821 4742313461678488760212577)
            ·
              refine ⟨3556735096258866570159433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4742313461678488760212577 3556735096258866570159433)
              ·
                refine ⟨2667551322194149927619575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3556735096258866570159433 2667551322194149927619575)
                ·
                  refine ⟨4001326983291224891429363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2667551322194149927619575 4001326983291224891429363)
                  ·
                    refine ⟨6001990474936837337144045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4001326983291224891429363 6001990474936837337144045)
                    ·
                      refine ⟨2250746428101314001429017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6001990474936837337144045 2250746428101314001429017)
                      ·
                        rfl

theorem cell23_4383313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 5, 2, 2, 1, 1, 3].length) (baseStart_4383313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383313 prefixEnd_4383313 := by exact prefixLift 4383313
  have htrace : WordTrace (prefixWord ++ tailWord_4383313) baseStart_4383313 baseEnd_4383313 := by
    simpa [prefixWord, tailWord_4383313, baseEnd_4383313] using wordTrace_append hprefix tailTrace_4383313
  have hstable : (prefixWord ++ tailWord_4383313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383313).length < 2 ^ (prefixWord ++ tailWord_4383313).sum := by decide
  have hdescent : baseEnd_4383313 < baseStart_4383313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383319 : List Nat := [1, 1, 3, 2, 2, 2, 2, 3, 3, 2, 2]
def baseStart_4383319 : Nat := 118140960795 + 4383319 * 2 ^ 59
def prefixEnd_4383319 : Nat := 4983230072969 + 3 ^ 40 * 4383319 * 2
def baseEnd_4383319 : Nat := 2250749508985240977953989

theorem tailTrace_4383319 : CollatzResearch.WordTrace tailWord_4383319 prefixEnd_4383319 2250749508985240977953989 := by
  unfold tailWord_4383319
  simp only [CollatzResearch.WordTrace]
  refine ⟨159872778006991349130321011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106581852004660899420214007 159872778006991349130321011)
  ·
    refine ⟨239809167010487023695481517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159872778006991349130321011 239809167010487023695481517)
    ·
      refine ⟨89928437628932633885805569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239809167010487023695481517 89928437628932633885805569)
      ·
        refine ⟨67446328221699475414354177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89928437628932633885805569 67446328221699475414354177)
        ·
          refine ⟨50584746166274606560765633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67446328221699475414354177 50584746166274606560765633)
          ·
            refine ⟨37938559624705954920574225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50584746166274606560765633 37938559624705954920574225)
            ·
              refine ⟨28453919718529466190430669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37938559624705954920574225 28453919718529466190430669)
              ·
                refine ⟨10670219894448549821411501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28453919718529466190430669 10670219894448549821411501)
                ·
                  refine ⟨4001332460418206183029313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10670219894448549821411501 4001332460418206183029313)
                  ·
                    refine ⟨3000999345313654637271985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4001332460418206183029313 3000999345313654637271985)
                    ·
                      refine ⟨2250749508985240977953989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3000999345313654637271985 2250749508985240977953989)
                      ·
                        rfl

theorem cell23_4383319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 2, 2].length) (baseStart_4383319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383319 prefixEnd_4383319 := by exact prefixLift 4383319
  have htrace : WordTrace (prefixWord ++ tailWord_4383319) baseStart_4383319 baseEnd_4383319 := by
    simpa [prefixWord, tailWord_4383319, baseEnd_4383319] using wordTrace_append hprefix tailTrace_4383319
  have hstable : (prefixWord ++ tailWord_4383319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383319).length < 2 ^ (prefixWord ++ tailWord_4383319).sum := by decide
  have hdescent : baseEnd_4383319 < baseStart_4383319 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383332 : List Nat := [2, 3, 1, 1, 2, 2, 4, 1, 1, 2, 4]
def baseStart_4383332 : Nat := 118140960795 + 4383332 * 2 ^ 59
def prefixEnd_4383332 : Nat := 4983230072969 + 3 ^ 40 * 4383332 * 2
def baseEnd_4383332 : Nat := 2250756184233749427091429

theorem tailTrace_4383332 : CollatzResearch.WordTrace tailWord_4383332 prefixEnd_4383332 2250756184233749427091429 := by
  unfold tailWord_4383332
  simp only [CollatzResearch.WordTrace]
  refine ⟨79936626077972126175272125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106582168103962834900362833 79936626077972126175272125)
  ·
    refine ⟨29976234779239547315727047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79936626077972126175272125 29976234779239547315727047)
    ·
      refine ⟨44964352168859320973590571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29976234779239547315727047 44964352168859320973590571)
      ·
        refine ⟨67446528253288981460385857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44964352168859320973590571 67446528253288981460385857)
        ·
          refine ⟨50584896189966736095289393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67446528253288981460385857 50584896189966736095289393)
          ·
            refine ⟨37938672142475052071467045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50584896189966736095289393 37938672142475052071467045)
            ·
              refine ⟨7113501026714072263400071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37938672142475052071467045 7113501026714072263400071)
              ·
                refine ⟨10670251540071108395100107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7113501026714072263400071 10670251540071108395100107)
                ·
                  refine ⟨16005377310106662592650161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10670251540071108395100107 16005377310106662592650161)
                  ·
                    refine ⟨12004032982579996944487621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16005377310106662592650161 12004032982579996944487621)
                    ·
                      refine ⟨2250756184233749427091429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12004032982579996944487621 2250756184233749427091429)
                      ·
                        rfl

theorem cell23_4383332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_4383332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383332 prefixEnd_4383332 := by exact prefixLift 4383332
  have htrace : WordTrace (prefixWord ++ tailWord_4383332) baseStart_4383332 baseEnd_4383332 := by
    simpa [prefixWord, tailWord_4383332, baseEnd_4383332] using wordTrace_append hprefix tailTrace_4383332
  have hstable : (prefixWord ++ tailWord_4383332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383332).length < 2 ^ (prefixWord ++ tailWord_4383332).sum := by decide
  have hdescent : baseEnd_4383332 < baseStart_4383332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383352 : List Nat := [2, 1, 2, 1, 1, 1, 2, 3, 6, 1, 3]
def baseStart_4383352 : Nat := 118140960795 + 4383352 * 2 ^ 59
def prefixEnd_4383352 : Nat := 4983230072969 + 3 ^ 40 * 4383352 * 2
def baseEnd_4383352 : Nat := 2250766453846839348841337

theorem tailTrace_4383352 : CollatzResearch.WordTrace tailWord_4383352 prefixEnd_4383352 2250766453846839348841337 := by
  unfold tailWord_4383352
  simp only [CollatzResearch.WordTrace]
  refine ⟨79936990807935897883136155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106582654410581197177514873 79936990807935897883136155)
  ·
    refine ⟨119905486211903846824704233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79936990807935897883136155 119905486211903846824704233)
    ·
      refine ⟨89929114658927885118528175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119905486211903846824704233 89929114658927885118528175)
      ·
        refine ⟨134893671988391827677792263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89929114658927885118528175 134893671988391827677792263)
        ·
          refine ⟨202340507982587741516688395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134893671988391827677792263 202340507982587741516688395)
          ·
            refine ⟨303510761973881612275032593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202340507982587741516688395 303510761973881612275032593)
            ·
              refine ⟨227633071480411209206274445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303510761973881612275032593 227633071480411209206274445)
              ·
                refine ⟨85362401805154203452352917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227633071480411209206274445 85362401805154203452352917)
                ·
                  refine ⟨4001362584616603286829043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85362401805154203452352917 4001362584616603286829043)
                  ·
                    refine ⟨6002043876924904930243565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4001362584616603286829043 6002043876924904930243565)
                    ·
                      refine ⟨2250766453846839348841337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6002043876924904930243565 2250766453846839348841337)
                      ·
                        rfl

theorem cell23_4383352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 3, 6, 1, 3].length) (baseStart_4383352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383352 prefixEnd_4383352 := by exact prefixLift 4383352
  have htrace : WordTrace (prefixWord ++ tailWord_4383352) baseStart_4383352 baseEnd_4383352 := by
    simpa [prefixWord, tailWord_4383352, baseEnd_4383352] using wordTrace_append hprefix tailTrace_4383352
  have hstable : (prefixWord ++ tailWord_4383352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383352).length < 2 ^ (prefixWord ++ tailWord_4383352).sum := by decide
  have hdescent : baseEnd_4383352 < baseStart_4383352 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383353 : List Nat := [1, 2, 1, 3, 3, 3, 2, 3, 1, 2, 2]
def baseStart_4383353 : Nat := 118140960795 + 4383353 * 2 ^ 59
def prefixEnd_4383353 : Nat := 4983230072969 + 3 ^ 40 * 4383353 * 2
def baseEnd_4383353 : Nat := 2250766967327493844928833

theorem tailTrace_4383353 : CollatzResearch.WordTrace tailWord_4383353 prefixEnd_4383353 2250766967327493844928833 := by
  unfold tailWord_4383353
  simp only [CollatzResearch.WordTrace]
  refine ⟨159874018088868172937058713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106582678725912115291372475 159874018088868172937058713)
  ·
    refine ⟨119905513566651129702794035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159874018088868172937058713 119905513566651129702794035)
    ·
      refine ⟨179858270349976694554191053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119905513566651129702794035 179858270349976694554191053)
      ·
        refine ⟨67446851381241260457821645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179858270349976694554191053 67446851381241260457821645)
        ·
          refine ⟨25292569267965472671683117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67446851381241260457821645 25292569267965472671683117)
          ·
            refine ⟨9484713475487052251881169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25292569267965472671683117 9484713475487052251881169)
            ·
              refine ⟨7113535106615289188910877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9484713475487052251881169 7113535106615289188910877)
              ·
                refine ⟨2667575664980733445841579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7113535106615289188910877 2667575664980733445841579)
                ·
                  refine ⟨4001363497471100168762369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2667575664980733445841579 4001363497471100168762369)
                  ·
                    refine ⟨3001022623103325126571777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4001363497471100168762369 3001022623103325126571777)
                    ·
                      refine ⟨2250766967327493844928833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3001022623103325126571777 2250766967327493844928833)
                      ·
                        rfl

theorem cell23_4383353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 3, 2, 3, 1, 2, 2].length) (baseStart_4383353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383353 prefixEnd_4383353 := by exact prefixLift 4383353
  have htrace : WordTrace (prefixWord ++ tailWord_4383353) baseStart_4383353 baseEnd_4383353 := by
    simpa [prefixWord, tailWord_4383353, baseEnd_4383353] using wordTrace_append hprefix tailTrace_4383353
  have hstable : (prefixWord ++ tailWord_4383353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383353).length < 2 ^ (prefixWord ++ tailWord_4383353).sum := by decide
  have hdescent : baseEnd_4383353 < baseStart_4383353 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383385 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 2, 6]
def baseStart_4383385 : Nat := 118140960795 + 4383385 * 2 ^ 59
def prefixEnd_4383385 : Nat := 4983230072969 + 3 ^ 40 * 4383385 * 2
def baseEnd_4383385 : Nat := 750261132902812573242895

theorem tailTrace_4383385 : CollatzResearch.WordTrace tailWord_4383385 prefixEnd_4383385 750261132902812573242895 := by
  unfold tailWord_4383385
  simp only [CollatzResearch.WordTrace]
  refine ⟨159875185224752242402223609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106583456816501494934815739 159875185224752242402223609)
  ·
    refine ⟨119906388918564181801667707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159875185224752242402223609 119906388918564181801667707)
    ·
      refine ⟨179859583377846272702501561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119906388918564181801667707 179859583377846272702501561)
      ·
        refine ⟨134894687533384704526876171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179859583377846272702501561 134894687533384704526876171)
        ·
          refine ⟨202342031300077056790314257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134894687533384704526876171 202342031300077056790314257)
          ·
            refine ⟨151756523475057792592735693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202342031300077056790314257 151756523475057792592735693)
            ·
              refine ⟨56908696303146672222275885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 151756523475057792592735693 56908696303146672222275885)
              ·
                refine ⟨21340761113680002083353457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56908696303146672222275885 21340761113680002083353457)
                ·
                  refine ⟨16005570835260001562515093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21340761113680002083353457 16005570835260001562515093)
                  ·
                    refine ⟨750261132902812573242895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16005570835260001562515093 750261132902812573242895)
                    ·
                      rfl

theorem cell23_4383385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 6].length) (baseStart_4383385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383385 prefixEnd_4383385 := by exact prefixLift 4383385
  have htrace : WordTrace (prefixWord ++ tailWord_4383385) baseStart_4383385 baseEnd_4383385 := by
    simpa [prefixWord, tailWord_4383385, baseEnd_4383385] using wordTrace_append hprefix tailTrace_4383385
  have hstable : (prefixWord ++ tailWord_4383385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383385).length < 2 ^ (prefixWord ++ tailWord_4383385).sum := by decide
  have hdescent : baseEnd_4383385 < baseStart_4383385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383396 : List Nat := [2, 3, 1, 2, 2, 1, 4, 2, 1, 3, 2]
def baseStart_4383396 : Nat := 118140960795 + 4383396 * 2 ^ 59
def prefixEnd_4383396 : Nat := 4983230072969 + 3 ^ 40 * 4383396 * 2
def baseEnd_4383396 : Nat := 2250789046995637176691135

theorem tailTrace_4383396 : CollatzResearch.WordTrace tailWord_4383396 prefixEnd_4383396 2250789046995637176691135 := by
  unfold tailWord_4383396
  simp only [CollatzResearch.WordTrace]
  refine ⟨79937793213856195640437021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106583724285141594187249361 79937793213856195640437021)
  ·
    refine ⟨29976672455196073365163883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79937793213856195640437021 29976672455196073365163883)
    ·
      refine ⟨44965008682794110047745825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29976672455196073365163883 44965008682794110047745825)
      ·
        refine ⟨33723756512095582535809369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44965008682794110047745825 33723756512095582535809369)
        ·
          refine ⟨25292817384071686901857027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33723756512095582535809369 25292817384071686901857027)
          ·
            refine ⟨37939226076107530352785541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25292817384071686901857027 37939226076107530352785541)
            ·
              refine ⟨7113604889270161941147289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37939226076107530352785541 7113604889270161941147289)
              ·
                refine ⟨5335203666952621455860467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7113604889270161941147289 5335203666952621455860467)
                ·
                  refine ⟨8002805500428932183790701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5335203666952621455860467 8002805500428932183790701)
                  ·
                    refine ⟨3001052062660849568921513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8002805500428932183790701 3001052062660849568921513)
                    ·
                      refine ⟨2250789046995637176691135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3001052062660849568921513 2250789046995637176691135)
                      ·
                        rfl

theorem cell23_4383396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_4383396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383396 prefixEnd_4383396 := by exact prefixLift 4383396
  have htrace : WordTrace (prefixWord ++ tailWord_4383396) baseStart_4383396 baseEnd_4383396 := by
    simpa [prefixWord, tailWord_4383396, baseEnd_4383396] using wordTrace_append hprefix tailTrace_4383396
  have hstable : (prefixWord ++ tailWord_4383396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383396).length < 2 ^ (prefixWord ++ tailWord_4383396).sum := by decide
  have hdescent : baseEnd_4383396 < baseStart_4383396 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383432 : List Nat := [2, 1, 3, 1, 2, 3, 3, 1, 7]
def baseStart_4383432 : Nat := 118140960795 + 4383432 * 2 ^ 59
def prefixEnd_4383432 : Nat := 4983230072969 + 3 ^ 40 * 4383432 * 2
def baseEnd_4383432 : Nat := 250089725811022115093441

theorem tailTrace_4383432 : CollatzResearch.WordTrace tailWord_4383432 prefixEnd_4383432 250089725811022115093441 := by
  unfold tailWord_4383432
  simp only [CollatzResearch.WordTrace]
  refine ⟨79938449727790984714592275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106584599637054646286123033 79938449727790984714592275)
  ·
    refine ⟨119907674591686477071888413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79938449727790984714592275 119907674591686477071888413)
    ·
      refine ⟨44965377971882428901958155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119907674591686477071888413 44965377971882428901958155)
      ·
        refine ⟨67448066957823643352937233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44965377971882428901958155 67448066957823643352937233)
        ·
          refine ⟨50586050218367732514702925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67448066957823643352937233 50586050218367732514702925)
          ·
            refine ⟨18969768831887899693013597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50586050218367732514702925 18969768831887899693013597)
            ·
              refine ⟨7113663311957962384880099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18969768831887899693013597 7113663311957962384880099)
              ·
                refine ⟨10670494967936943577320149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7113663311957962384880099 10670494967936943577320149)
                ·
                  refine ⟨250089725811022115093441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10670494967936943577320149 250089725811022115093441)
                  ·
                    rfl

theorem cell23_4383432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 7].length) (baseStart_4383432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383432 prefixEnd_4383432 := by exact prefixLift 4383432
  have htrace : WordTrace (prefixWord ++ tailWord_4383432) baseStart_4383432 baseEnd_4383432 := by
    simpa [prefixWord, tailWord_4383432, baseEnd_4383432] using wordTrace_append hprefix tailTrace_4383432
  have hstable : (prefixWord ++ tailWord_4383432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383432).length < 2 ^ (prefixWord ++ tailWord_4383432).sum := by decide
  have hdescent : baseEnd_4383432 < baseStart_4383432 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383437 : List Nat := [1, 6, 2, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_4383437 : Nat := 118140960795 + 4383437 * 2 ^ 59
def prefixEnd_4383437 : Nat := 4983230072969 + 3 ^ 40 * 4383437 * 2
def baseEnd_4383437 : Nat := 2250810099702471516278447

theorem tailTrace_4383437 : CollatzResearch.WordTrace tailWord_4383437 prefixEnd_4383437 2250810099702471516278447 := by
  unfold tailWord_4383437
  simp only [CollatzResearch.WordTrace]
  refine ⟨159877081820563855283116565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106584721213709236855411043 159877081820563855283116565)
  ·
    refine ⟨7494238210338930716396089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 159877081820563855283116565 7494238210338930716396089)
    ·
      refine ⟨5620678657754198037297067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7494238210338930716396089 5620678657754198037297067)
      ·
        refine ⟨8431017986631297055945601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5620678657754198037297067 8431017986631297055945601)
        ·
          refine ⟨6323263489973472791959201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8431017986631297055945601 6323263489973472791959201)
          ·
            refine ⟨4742447617480104593969401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6323263489973472791959201 4742447617480104593969401)
            ·
              refine ⟨3556835713110078445477051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4742447617480104593969401 3556835713110078445477051)
              ·
                refine ⟨5335253569665117668215577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3556835713110078445477051 5335253569665117668215577)
                ·
                  refine ⟨4001440177248838251161683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5335253569665117668215577 4001440177248838251161683)
                  ·
                    refine ⟨6002160265873257376742525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4001440177248838251161683 6002160265873257376742525)
                    ·
                      refine ⟨2250810099702471516278447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6002160265873257376742525 2250810099702471516278447)
                      ·
                        rfl

theorem cell23_4383437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_4383437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383437 prefixEnd_4383437 := by exact prefixLift 4383437
  have htrace : WordTrace (prefixWord ++ tailWord_4383437) baseStart_4383437 baseEnd_4383437 := by
    simpa [prefixWord, tailWord_4383437, baseEnd_4383437] using wordTrace_append hprefix tailTrace_4383437
  have hstable : (prefixWord ++ tailWord_4383437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383437).length < 2 ^ (prefixWord ++ tailWord_4383437).sum := by decide
  have hdescent : baseEnd_4383437 < baseStart_4383437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383486 : List Nat := [4, 2, 2, 1, 2, 1, 1, 1, 2, 5, 2]
def baseStart_4383486 : Nat := 118140960795 + 4383486 * 2 ^ 59
def prefixEnd_4383486 : Nat := 4983230072969 + 3 ^ 40 * 4383486 * 2
def baseEnd_4383486 : Nat := 2250835260254541824565721

theorem tailTrace_4383486 : CollatzResearch.WordTrace tailWord_4383486 prefixEnd_4383486 2250835260254541824565721 := by
  unfold tailWord_4383486
  simp only [CollatzResearch.WordTrace]
  refine ⟨19984858624673292081456289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106585912664924224434433541 19984858624673292081456289)
  ·
    refine ⟨14988643968504969061092217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19984858624673292081456289 14988643968504969061092217)
    ·
      refine ⟨11241482976378726795819163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14988643968504969061092217 11241482976378726795819163)
      ·
        refine ⟨16862224464568090193728745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11241482976378726795819163 16862224464568090193728745)
        ·
          refine ⟨12646668348426067645296559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16862224464568090193728745 12646668348426067645296559)
          ·
            refine ⟨18970002522639101467944839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12646668348426067645296559 18970002522639101467944839)
            ·
              refine ⟨28455003783958652201917259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18970002522639101467944839 28455003783958652201917259)
              ·
                refine ⟨42682505675937978302875889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28455003783958652201917259 42682505675937978302875889)
                ·
                  refine ⟨32011879256953483727156917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42682505675937978302875889 32011879256953483727156917)
                  ·
                    refine ⟨3001113680339389099420961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32011879256953483727156917 3001113680339389099420961)
                    ·
                      refine ⟨2250835260254541824565721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3001113680339389099420961 2250835260254541824565721)
                      ·
                        rfl

theorem cell23_4383486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_4383486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383486 prefixEnd_4383486 := by exact prefixLift 4383486
  have htrace : WordTrace (prefixWord ++ tailWord_4383486) baseStart_4383486 baseEnd_4383486 := by
    simpa [prefixWord, tailWord_4383486, baseEnd_4383486] using wordTrace_append hprefix tailTrace_4383486
  have hstable : (prefixWord ++ tailWord_4383486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383486).length < 2 ^ (prefixWord ++ tailWord_4383486).sum := by decide
  have hdescent : baseEnd_4383486 < baseStart_4383486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383509 : List Nat := [1, 3, 2, 1, 2, 2, 3, 2, 3, 4]
def baseStart_4383509 : Nat := 118140960795 + 4383509 * 2 ^ 59
def prefixEnd_4383509 : Nat := 4983230072969 + 3 ^ 40 * 4383509 * 2
def baseEnd_4383509 : Nat := 750282356769865078192705

theorem tailTrace_4383509 : CollatzResearch.WordTrace tailWord_4383509 prefixEnd_4383509 750282356769865078192705 := by
  unfold tailWord_4383509
  simp only [CollatzResearch.WordTrace]
  refine ⟨159879707876303011579737581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106586471917535341053158387 159879707876303011579737581)
  ·
    refine ⟨59954890453613629342401593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159879707876303011579737581 59954890453613629342401593)
    ·
      refine ⟨44966167840210222006801195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59954890453613629342401593 44966167840210222006801195)
      ·
        refine ⟨67449251760315333010201793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44966167840210222006801195 67449251760315333010201793)
        ·
          refine ⟨50586938820236499757651345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67449251760315333010201793 50586938820236499757651345)
          ·
            refine ⟨37940204115177374818238509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50586938820236499757651345 37940204115177374818238509)
            ·
              refine ⟨14227576543191515556839441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37940204115177374818238509 14227576543191515556839441)
              ·
                refine ⟨10670682407393636667629581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14227576543191515556839441 10670682407393636667629581)
                ·
                  refine ⟨4001505902772613750361093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10670682407393636667629581 4001505902772613750361093)
                  ·
                    refine ⟨750282356769865078192705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4001505902772613750361093 750282356769865078192705)
                    ·
                      rfl

theorem cell23_4383509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_4383509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383509 prefixEnd_4383509 := by exact prefixLift 4383509
  have htrace : WordTrace (prefixWord ++ tailWord_4383509) baseStart_4383509 baseEnd_4383509 := by
    simpa [prefixWord, tailWord_4383509, baseEnd_4383509] using wordTrace_append hprefix tailTrace_4383509
  have hstable : (prefixWord ++ tailWord_4383509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383509).length < 2 ^ (prefixWord ++ tailWord_4383509).sum := by decide
  have hdescent : baseEnd_4383509 < baseStart_4383509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383516 : List Nat := [2, 2, 3, 1, 1, 5, 1, 1, 2, 1, 4]
def baseStart_4383516 : Nat := 118140960795 + 4383516 * 2 ^ 59
def prefixEnd_4383516 : Nat := 4983230072969 + 3 ^ 40 * 4383516 * 2
def baseEnd_4383516 : Nat := 2250850664674176707190583

theorem tailTrace_4383516 : CollatzResearch.WordTrace tailWord_4383516 prefixEnd_4383516 2250850664674176707190583 := by
  unfold tailWord_4383516
  simp only [CollatzResearch.WordTrace]
  refine ⟨79939981593638825887621201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106586642124851767850161601 79939981593638825887621201)
  ·
    refine ⟨59954986195229119415715901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79939981593638825887621201 59954986195229119415715901)
    ·
      refine ⟨22483119823210919780893463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59954986195229119415715901 22483119823210919780893463)
      ·
        refine ⟨33724679734816379671340195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22483119823210919780893463 33724679734816379671340195)
        ·
          refine ⟨50587019602224569507010293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33724679734816379671340195 50587019602224569507010293)
          ·
            refine ⟨4742533087708553391282215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50587019602224569507010293 4742533087708553391282215)
            ·
              refine ⟨7113799631562830086923323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4742533087708553391282215 7113799631562830086923323)
              ·
                refine ⟨10670699447344245130384985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7113799631562830086923323 10670699447344245130384985)
                ·
                  refine ⟨8003024585508183847788739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10670699447344245130384985 8003024585508183847788739)
                  ·
                    refine ⟨12004536878262275771683109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8003024585508183847788739 12004536878262275771683109)
                    ·
                      refine ⟨2250850664674176707190583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12004536878262275771683109 2250850664674176707190583)
                      ·
                        rfl

theorem cell23_4383516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_4383516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383516 prefixEnd_4383516 := by exact prefixLift 4383516
  have htrace : WordTrace (prefixWord ++ tailWord_4383516) baseStart_4383516 baseEnd_4383516 := by
    simpa [prefixWord, tailWord_4383516, baseEnd_4383516] using wordTrace_append hprefix tailTrace_4383516
  have hstable : (prefixWord ++ tailWord_4383516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383516).length < 2 ^ (prefixWord ++ tailWord_4383516).sum := by decide
  have hdescent : baseEnd_4383516 < baseStart_4383516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383519 : List Nat := [1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 3]
def baseStart_4383519 : Nat := 118140960795 + 4383519 * 2 ^ 59
def prefixEnd_4383519 : Nat := 4983230072969 + 3 ^ 40 * 4383519 * 2
def baseEnd_4383519 : Nat := 2250852205116140195453069

theorem tailTrace_4383519 : CollatzResearch.WordTrace tailWord_4383519 prefixEnd_4383519 2250852205116140195453069 := by
  unfold tailWord_4383519
  simp only [CollatzResearch.WordTrace]
  refine ⟨159880072606266783287601611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106586715070844522191734407 159880072606266783287601611)
  ·
    refine ⟨239820108909400174931402417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159880072606266783287601611 239820108909400174931402417)
    ·
      refine ⟨179865081682050131198551813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239820108909400174931402417 179865081682050131198551813)
      ·
        refine ⟨33724702815384399599728465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179865081682050131198551813 33724702815384399599728465)
        ·
          refine ⟨25293527111538299699796349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33724702815384399599728465 25293527111538299699796349)
          ·
            refine ⟨9485072666826862387423631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25293527111538299699796349 9485072666826862387423631)
            ·
              refine ⟨14227609000240293581135447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9485072666826862387423631 14227609000240293581135447)
              ·
                refine ⟨21341413500360440371703171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14227609000240293581135447 21341413500360440371703171)
                ·
                  refine ⟨32012120250540660557554757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21341413500360440371703171 32012120250540660557554757)
                  ·
                    refine ⟨6002272546976373854541517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32012120250540660557554757 6002272546976373854541517)
                    ·
                      refine ⟨2250852205116140195453069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6002272546976373854541517 2250852205116140195453069)
                      ·
                        rfl

theorem cell23_4383519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 3].length) (baseStart_4383519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383519 prefixEnd_4383519 := by exact prefixLift 4383519
  have htrace : WordTrace (prefixWord ++ tailWord_4383519) baseStart_4383519 baseEnd_4383519 := by
    simpa [prefixWord, tailWord_4383519, baseEnd_4383519] using wordTrace_append hprefix tailTrace_4383519
  have hstable : (prefixWord ++ tailWord_4383519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383519).length < 2 ^ (prefixWord ++ tailWord_4383519).sum := by decide
  have hdescent : baseEnd_4383519 < baseStart_4383519 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383539 : List Nat := [1, 1, 1, 2, 6, 1, 3, 2, 6]
def baseStart_4383539 : Nat := 118140960795 + 4383539 * 2 ^ 59
def prefixEnd_4383539 : Nat := 4983230072969 + 3 ^ 40 * 4383539 * 2
def baseEnd_4383539 : Nat := 250095830525470013022553

theorem tailTrace_4383539 : CollatzResearch.WordTrace tailWord_4383539 prefixEnd_4383539 250095830525470013022553 := by
  unfold tailWord_4383539
  simp only [CollatzResearch.WordTrace]
  refine ⟨159880802066194326703329671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106587201377462884468886447 159880802066194326703329671)
  ·
    refine ⟨239821203099291490054994507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159880802066194326703329671 239821203099291490054994507)
    ·
      refine ⟨359731804648937235082491761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239821203099291490054994507 359731804648937235082491761)
      ·
        refine ⟨269798853486702926311868821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 359731804648937235082491761 269798853486702926311868821)
        ·
          refine ⟨12646821257189199670868851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 269798853486702926311868821 12646821257189199670868851)
          ·
            refine ⟨18970231885783799506303277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12646821257189199670868851 18970231885783799506303277)
            ·
              refine ⟨7113836957168924814863729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18970231885783799506303277 7113836957168924814863729)
              ·
                refine ⟨5335377717876693611147797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7113836957168924814863729 5335377717876693611147797)
                ·
                  refine ⟨250095830525470013022553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5335377717876693611147797 250095830525470013022553)
                  ·
                    rfl

theorem cell23_4383539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 6].length) (baseStart_4383539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383539 prefixEnd_4383539 := by exact prefixLift 4383539
  have htrace : WordTrace (prefixWord ++ tailWord_4383539) baseStart_4383539 baseEnd_4383539 := by
    simpa [prefixWord, tailWord_4383539, baseEnd_4383539] using wordTrace_append hprefix tailTrace_4383539
  have hstable : (prefixWord ++ tailWord_4383539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383539).length < 2 ^ (prefixWord ++ tailWord_4383539).sum := by decide
  have hdescent : baseEnd_4383539 < baseStart_4383539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383552 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 5, 5]
def baseStart_4383552 : Nat := 118140960795 + 4383552 * 2 ^ 59
def prefixEnd_4383552 : Nat := 4983230072969 + 3 ^ 40 * 4383552 * 2
def baseEnd_4383552 : Nat := 750289716659246188780139

theorem tailTrace_4383552 : CollatzResearch.WordTrace tailWord_4383552 prefixEnd_4383552 750289716659246188780139 := by
  unfold tailWord_4383552
  simp only [CollatzResearch.WordTrace]
  refine ⟨79940638107573614961776455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106587517476764819949035273 79940638107573614961776455)
  ·
    refine ⟨119910957161360422442664683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79940638107573614961776455 119910957161360422442664683)
    ·
      refine ⟨179866435742040633663997025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119910957161360422442664683 179866435742040633663997025)
      ·
        refine ⟨134899826806530475247997769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179866435742040633663997025 134899826806530475247997769)
        ·
          refine ⟨101174870104897856435998327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134899826806530475247997769 101174870104897856435998327)
          ·
            refine ⟨151762305157346784653997491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101174870104897856435998327 151762305157346784653997491)
            ·
              refine ⟨227643457736020176980996237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151762305157346784653997491 227643457736020176980996237)
              ·
                refine ⟨85366296651007566367873589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227643457736020176980996237 85366296651007566367873589)
                ·
                  refine ⟨8003090311031959346988149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85366296651007566367873589 8003090311031959346988149)
                  ·
                    refine ⟨750289716659246188780139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8003090311031959346988149 750289716659246188780139)
                    ·
                      rfl

theorem cell23_4383552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 5, 5].length) (baseStart_4383552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383552 prefixEnd_4383552 := by exact prefixLift 4383552
  have htrace : WordTrace (prefixWord ++ tailWord_4383552) baseStart_4383552 baseEnd_4383552 := by
    simpa [prefixWord, tailWord_4383552, baseEnd_4383552] using wordTrace_append hprefix tailTrace_4383552
  have hstable : (prefixWord ++ tailWord_4383552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383552).length < 2 ^ (prefixWord ++ tailWord_4383552).sum := by decide
  have hdescent : baseEnd_4383552 < baseStart_4383552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383609 : List Nat := [1, 2, 1, 3, 2, 3, 2, 2, 1, 1, 5]
def baseStart_4383609 : Nat := 118140960795 + 4383609 * 2 ^ 59
def prefixEnd_4383609 : Nat := 4983230072969 + 3 ^ 40 * 4383609 * 2
def baseEnd_4383609 : Nat := 2250898418375044843327655

theorem tailTrace_4383609 : CollatzResearch.WordTrace tailWord_4383609 prefixEnd_4383609 2250898418375044843327655 := by
  unfold tailWord_4383609
  simp only [CollatzResearch.WordTrace]
  refine ⟨159883355175940728658377881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106588903450627152438918587 159883355175940728658377881)
  ·
    refine ⟨119912516381955546493783411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159883355175940728658377881 119912516381955546493783411)
    ·
      refine ⟨179868774572933319740675117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119912516381955546493783411 179868774572933319740675117)
      ·
        refine ⟨67450790464849994902753169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179868774572933319740675117 67450790464849994902753169)
        ·
          refine ⟨50588092848637496177064877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67450790464849994902753169 50588092848637496177064877)
          ·
            refine ⟨18970534818239061066399329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50588092848637496177064877 18970534818239061066399329)
            ·
              refine ⟨14227901113679295799799497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18970534818239061066399329 14227901113679295799799497)
              ·
                refine ⟨10670925835259471849849623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14227901113679295799799497 10670925835259471849849623)
                ·
                  refine ⟨16006388752889207774774435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10670925835259471849849623 16006388752889207774774435)
                  ·
                    refine ⟨24009583129333811662161653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16006388752889207774774435 24009583129333811662161653)
                    ·
                      refine ⟨2250898418375044843327655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24009583129333811662161653 2250898418375044843327655)
                      ·
                        rfl

theorem cell23_4383609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_4383609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383609 prefixEnd_4383609 := by exact prefixLift 4383609
  have htrace : WordTrace (prefixWord ++ tailWord_4383609) baseStart_4383609 baseEnd_4383609 := by
    simpa [prefixWord, tailWord_4383609, baseEnd_4383609] using wordTrace_append hprefix tailTrace_4383609
  have hstable : (prefixWord ++ tailWord_4383609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383609).length < 2 ^ (prefixWord ++ tailWord_4383609).sum := by decide
  have hdescent : baseEnd_4383609 < baseStart_4383609 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383619 : List Nat := [1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 4]
def baseStart_4383619 : Nat := 118140960795 + 4383619 * 2 ^ 59
def prefixEnd_4383619 : Nat := 4983230072969 + 3 ^ 40 * 4383619 * 2
def baseEnd_4383619 : Nat := 2250903553181589804202609

theorem tailTrace_4383619 : CollatzResearch.WordTrace tailWord_4383619 prefixEnd_4383619 2250903553181589804202609 := by
  unfold tailWord_4383619
  simp only [CollatzResearch.WordTrace]
  refine ⟨159883719905904500366241911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106589146603936333577494607 159883719905904500366241911)
  ·
    refine ⟨239825579858856750549362867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159883719905904500366241911 239825579858856750549362867)
    ·
      refine ⟨359738369788285125824044301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239825579858856750549362867 359738369788285125824044301)
      ·
        refine ⟨134901888670606922184016613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 359738369788285125824044301 134901888670606922184016613)
        ·
          refine ⟨25294104125738797909503115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134901888670606922184016613 25294104125738797909503115)
          ·
            refine ⟨37941156188608196864254673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25294104125738797909503115 37941156188608196864254673)
            ·
              refine ⟨28455867141456147648191005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37941156188608196864254673 28455867141456147648191005)
              ·
                refine ⟨10670950178046055368071627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28455867141456147648191005 10670950178046055368071627)
                ·
                  refine ⟨16006425267069083052107441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10670950178046055368071627 16006425267069083052107441)
                  ·
                    refine ⟨12004818950301812289080581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16006425267069083052107441 12004818950301812289080581)
                    ·
                      refine ⟨2250903553181589804202609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12004818950301812289080581 2250903553181589804202609)
                      ·
                        rfl

theorem cell23_4383619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_4383619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383619 prefixEnd_4383619 := by exact prefixLift 4383619
  have htrace : WordTrace (prefixWord ++ tailWord_4383619) baseStart_4383619 baseEnd_4383619 := by
    simpa [prefixWord, tailWord_4383619, baseEnd_4383619] using wordTrace_append hprefix tailTrace_4383619
  have hstable : (prefixWord ++ tailWord_4383619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383619).length < 2 ^ (prefixWord ++ tailWord_4383619).sum := by decide
  have hdescent : baseEnd_4383619 < baseStart_4383619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383623 : List Nat := [1, 1, 4, 2, 3, 3, 1, 2, 1, 1, 4]
def baseStart_4383623 : Nat := 118140960795 + 4383623 * 2 ^ 59
def prefixEnd_4383623 : Nat := 4983230072969 + 3 ^ 40 * 4383623 * 2
def baseEnd_4383623 : Nat := 2250905607104207788552591

theorem tailTrace_4383623 : CollatzResearch.WordTrace tailWord_4383623 prefixEnd_4383623 2250905607104207788552591 := by
  unfold tailWord_4383623
  simp only [CollatzResearch.WordTrace]
  refine ⟨159883865797890009049387523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106589243865260006032925015 159883865797890009049387523)
  ·
    refine ⟨239825798696835013574081285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159883865797890009049387523 239825798696835013574081285)
    ·
      refine ⟨44967337255656565045140241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 239825798696835013574081285 44967337255656565045140241)
      ·
        refine ⟨33725502941742423783855181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44967337255656565045140241 33725502941742423783855181)
        ·
          refine ⟨12647063603153408918945693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33725502941742423783855181 12647063603153408918945693)
          ·
            refine ⟨4742648851182528344604635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12647063603153408918945693 4742648851182528344604635)
            ·
              refine ⟨7113973276773792516906953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4742648851182528344604635 7113973276773792516906953)
              ·
                refine ⟨5335479957580344387680215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7113973276773792516906953 5335479957580344387680215)
                ·
                  refine ⟨8003219936370516581520323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5335479957580344387680215 8003219936370516581520323)
                  ·
                    refine ⟨12004829904555774872280485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8003219936370516581520323 12004829904555774872280485)
                    ·
                      refine ⟨2250905607104207788552591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12004829904555774872280485 2250905607104207788552591)
                      ·
                        rfl

theorem cell23_4383623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_4383623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383623 prefixEnd_4383623 := by exact prefixLift 4383623
  have htrace : WordTrace (prefixWord ++ tailWord_4383623) baseStart_4383623 baseEnd_4383623 := by
    simpa [prefixWord, tailWord_4383623, baseEnd_4383623] using wordTrace_append hprefix tailTrace_4383623
  have hstable : (prefixWord ++ tailWord_4383623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383623).length < 2 ^ (prefixWord ++ tailWord_4383623).sum := by decide
  have hdescent : baseEnd_4383623 < baseStart_4383623 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383632 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 6]
def baseStart_4383632 : Nat := 118140960795 + 4383632 * 2 ^ 59
def prefixEnd_4383632 : Nat := 4983230072969 + 3 ^ 40 * 4383632 * 2
def baseEnd_4383632 : Nat := 2250910228430098253340049

theorem tailTrace_4383632 : CollatzResearch.WordTrace tailWord_4383632 prefixEnd_4383632 2250910228430098253340049 := by
  unfold tailWord_4383632
  simp only [CollatzResearch.WordTrace]
  refine ⟨79942097027428701793232575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106589462703238269057643433 79942097027428701793232575)
  ·
    refine ⟨119913145541143052689848863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79942097027428701793232575 119913145541143052689848863)
    ·
      refine ⟨179869718311714579034773295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119913145541143052689848863 179869718311714579034773295)
      ·
        refine ⟨269804577467571868552159943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179869718311714579034773295 269804577467571868552159943)
        ·
          refine ⟨404706866201357802828239915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269804577467571868552159943 404706866201357802828239915)
          ·
            refine ⟨607060299302036704242359873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404706866201357802828239915 607060299302036704242359873)
            ·
              refine ⟨455295224476527528181769905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 607060299302036704242359873 455295224476527528181769905)
              ·
                refine ⟨341471418357395646136327429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 455295224476527528181769905 341471418357395646136327429)
                ·
                  refine ⟨64025890942011683650561393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 341471418357395646136327429 64025890942011683650561393)
                  ·
                    refine ⟨48019418206508762737921045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64025890942011683650561393 48019418206508762737921045)
                    ·
                      refine ⟨2250910228430098253340049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48019418206508762737921045 2250910228430098253340049)
                      ·
                        rfl

theorem cell23_4383632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 6].length) (baseStart_4383632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383632 prefixEnd_4383632 := by exact prefixLift 4383632
  have htrace : WordTrace (prefixWord ++ tailWord_4383632) baseStart_4383632 baseEnd_4383632 := by
    simpa [prefixWord, tailWord_4383632, baseEnd_4383632] using wordTrace_append hprefix tailTrace_4383632
  have hstable : (prefixWord ++ tailWord_4383632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383632).length < 2 ^ (prefixWord ++ tailWord_4383632).sum := by decide
  have hdescent : baseEnd_4383632 < baseStart_4383632 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383636 : List Nat := [2, 4, 2, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_4383636 : Nat := 118140960795 + 4383636 * 2 ^ 59
def prefixEnd_4383636 : Nat := 4983230072969 + 3 ^ 40 * 4383636 * 2
def baseEnd_4383636 : Nat := 2250912282352716237690031

theorem tailTrace_4383636 : CollatzResearch.WordTrace tailWord_4383636 prefixEnd_4383636 2250912282352716237690031 := by
  unfold tailWord_4383636
  simp only [CollatzResearch.WordTrace]
  refine ⟨79942169973421456134805381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106589559964561941513073841 79942169973421456134805381)
  ·
    refine ⟨14989156870016523025276009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79942169973421456134805381 14989156870016523025276009)
    ·
      refine ⟨11241867652512392268957007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14989156870016523025276009 11241867652512392268957007)
      ·
        refine ⟨16862801478768588403435511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11241867652512392268957007 16862801478768588403435511)
        ·
          refine ⟨25294202218152882605153267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16862801478768588403435511 25294202218152882605153267)
          ·
            refine ⟨37941303327229323907729901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25294202218152882605153267 37941303327229323907729901)
            ·
              refine ⟨14227988747710996465398713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37941303327229323907729901 14227988747710996465398713)
              ·
                refine ⟨10670991560783247349049035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14227988747710996465398713 10670991560783247349049035)
                ·
                  refine ⟨16006487341174871023573553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10670991560783247349049035 16006487341174871023573553)
                  ·
                    refine ⟨12004865505881153267680165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16006487341174871023573553 12004865505881153267680165)
                    ·
                      refine ⟨2250912282352716237690031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12004865505881153267680165 2250912282352716237690031)
                      ·
                        rfl

theorem cell23_4383636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_4383636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383636 prefixEnd_4383636 := by exact prefixLift 4383636
  have htrace : WordTrace (prefixWord ++ tailWord_4383636) baseStart_4383636 baseEnd_4383636 := by
    simpa [prefixWord, tailWord_4383636, baseEnd_4383636] using wordTrace_append hprefix tailTrace_4383636
  have hstable : (prefixWord ++ tailWord_4383636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383636).length < 2 ^ (prefixWord ++ tailWord_4383636).sum := by decide
  have hdescent : baseEnd_4383636 < baseStart_4383636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383673 : List Nat := [1, 2, 1, 4, 2, 2, 2, 3, 2, 1, 3]
def baseStart_4383673 : Nat := 118140960795 + 4383673 * 2 ^ 59
def prefixEnd_4383673 : Nat := 4983230072969 + 3 ^ 40 * 4383673 * 2
def baseEnd_4383673 : Nat := 2250931281136932592927361

theorem tailTrace_4383673 : CollatzResearch.WordTrace tailWord_4383673 prefixEnd_4383673 2250931281136932592927361 := by
  unfold tailWord_4383673
  simp only [CollatzResearch.WordTrace]
  refine ⟨159885689447708867588707673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106590459631805911725805115 159885689447708867588707673)
  ·
    refine ⟨119914267085781650691530755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159885689447708867588707673 119914267085781650691530755)
    ·
      refine ⟨179871400628672476037296133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119914267085781650691530755 179871400628672476037296133)
      ·
        refine ⟨33725887617876089256993025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179871400628672476037296133 33725887617876089256993025)
        ·
          refine ⟨25294415713407066942744769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33725887617876089256993025 25294415713407066942744769)
          ·
            refine ⟨18970811785055300207058577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25294415713407066942744769 18970811785055300207058577)
            ·
              refine ⟨14228108838791475155293933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18970811785055300207058577 14228108838791475155293933)
              ·
                refine ⟨5335540814546803183235225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14228108838791475155293933 5335540814546803183235225)
                ·
                  refine ⟨4001655610910102387426419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5335540814546803183235225 4001655610910102387426419)
                  ·
                    refine ⟨6002483416365153581139629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4001655610910102387426419 6002483416365153581139629)
                    ·
                      refine ⟨2250931281136932592927361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6002483416365153581139629 2250931281136932592927361)
                      ·
                        rfl

theorem cell23_4383673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 2, 3, 2, 1, 3].length) (baseStart_4383673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383673 prefixEnd_4383673 := by exact prefixLift 4383673
  have htrace : WordTrace (prefixWord ++ tailWord_4383673) baseStart_4383673 baseEnd_4383673 := by
    simpa [prefixWord, tailWord_4383673, baseEnd_4383673] using wordTrace_append hprefix tailTrace_4383673
  have hstable : (prefixWord ++ tailWord_4383673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383673).length < 2 ^ (prefixWord ++ tailWord_4383673).sum := by decide
  have hdescent : baseEnd_4383673 < baseStart_4383673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383700 : List Nat := [2, 4, 1, 2, 1, 3, 1, 3, 1, 3, 2]
def baseStart_4383700 : Nat := 118140960795 + 4383700 * 2 ^ 59
def prefixEnd_4383700 : Nat := 4983230072969 + 3 ^ 40 * 4383700 * 2
def baseEnd_4383700 : Nat := 2250945145114603987289737

theorem tailTrace_4383700 : CollatzResearch.WordTrace tailWord_4383700 prefixEnd_4383700 2250945145114603987289737 := by
  unfold tailWord_4383700
  simp only [CollatzResearch.WordTrace]
  refine ⟨79943337109305525599970277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106591116145740700799960369 79943337109305525599970277)
  ·
    refine ⟨14989375707994786049994427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79943337109305525599970277 14989375707994786049994427)
    ·
      refine ⟨22484063561992179074991641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14989375707994786049994427 22484063561992179074991641)
      ·
        refine ⟨16863047671494134306243731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22484063561992179074991641 16863047671494134306243731)
        ·
          refine ⟨25294571507241201459365597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16863047671494134306243731 25294571507241201459365597)
          ·
            refine ⟨9485464315215450547262099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25294571507241201459365597 9485464315215450547262099)
            ·
              refine ⟨14228196472823175820893149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9485464315215450547262099 14228196472823175820893149)
              ·
                refine ⟨5335573677308690932834931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14228196472823175820893149 5335573677308690932834931)
                ·
                  refine ⟨8003360515963036399252397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5335573677308690932834931 8003360515963036399252397)
                  ·
                    refine ⟨3001260193486138649719649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8003360515963036399252397 3001260193486138649719649)
                    ·
                      refine ⟨2250945145114603987289737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3001260193486138649719649 2250945145114603987289737)
                      ·
                        rfl

theorem cell23_4383700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_4383700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383700 prefixEnd_4383700 := by exact prefixLift 4383700
  have htrace : WordTrace (prefixWord ++ tailWord_4383700) baseStart_4383700 baseEnd_4383700 := by
    simpa [prefixWord, tailWord_4383700, baseEnd_4383700] using wordTrace_append hprefix tailTrace_4383700
  have hstable : (prefixWord ++ tailWord_4383700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383700).length < 2 ^ (prefixWord ++ tailWord_4383700).sum := by decide
  have hdescent : baseEnd_4383700 < baseStart_4383700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383749 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 1, 7]
def baseStart_4383749 : Nat := 118140960795 + 4383749 * 2 ^ 59
def prefixEnd_4383749 : Nat := 4983230072969 + 3 ^ 40 * 4383749 * 2
def baseEnd_4383749 : Nat := 750323435222224765192337

theorem tailTrace_4383749 : CollatzResearch.WordTrace tailWord_4383749 prefixEnd_4383749 750323435222224765192337 := by
  unfold tailWord_4383749
  simp only [CollatzResearch.WordTrace]
  refine ⟨159888461395433532568474301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106592307596955688378982867 159888461395433532568474301)
  ·
    refine ⟨59958173023287574713177863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159888461395433532568474301 59958173023287574713177863)
    ·
      refine ⟨89937259534931362069766795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59958173023287574713177863 89937259534931362069766795)
      ·
        refine ⟨134905889302397043104650193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89937259534931362069766795 134905889302397043104650193)
        ·
          refine ⟨101179416976797782328487645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134905889302397043104650193 101179416976797782328487645)
          ·
            refine ⟨37942281366299168373182867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101179416976797782328487645 37942281366299168373182867)
            ·
              refine ⟨56913422049448752559774301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37942281366299168373182867 56913422049448752559774301)
              ·
                refine ⟨21342533268543282209915363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56913422049448752559774301 21342533268543282209915363)
                ·
                  refine ⟨32013799902814923314873045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21342533268543282209915363 32013799902814923314873045)
                  ·
                    refine ⟨750323435222224765192337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32013799902814923314873045 750323435222224765192337)
                    ·
                      rfl

theorem cell23_4383749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_4383749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383749 prefixEnd_4383749 := by exact prefixLift 4383749
  have htrace : WordTrace (prefixWord ++ tailWord_4383749) baseStart_4383749 baseEnd_4383749 := by
    simpa [prefixWord, tailWord_4383749, baseEnd_4383749] using wordTrace_append hprefix tailTrace_4383749
  have hstable : (prefixWord ++ tailWord_4383749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383749).length < 2 ^ (prefixWord ++ tailWord_4383749).sum := by decide
  have hdescent : baseEnd_4383749 < baseStart_4383749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383799 : List Nat := [1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 6]
def baseStart_4383799 : Nat := 118140960795 + 4383799 * 2 ^ 59
def prefixEnd_4383799 : Nat := 4983230072969 + 3 ^ 40 * 4383799 * 2
def baseEnd_4383799 : Nat := 2250995979699399099951781

theorem tailTrace_4383799 : CollatzResearch.WordTrace tailWord_4383799 prefixEnd_4383799 2250995979699399099951781 := by
  unfold tailWord_4383799
  simp only [CollatzResearch.WordTrace]
  refine ⟨159890285045252391107794451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106593523363501594071862967 159890285045252391107794451)
  ·
    refine ⟨239835427567878586661691677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159890285045252391107794451 239835427567878586661691677)
    ·
      refine ⟨89938285337954469998134379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239835427567878586661691677 89938285337954469998134379)
      ·
        refine ⟨134907428006931704997201569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89938285337954469998134379 134907428006931704997201569)
        ·
          refine ⟨101180571005198778747901177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134907428006931704997201569 101180571005198778747901177)
          ·
            refine ⟨75885428253899084060925883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101180571005198778747901177 75885428253899084060925883)
            ·
              refine ⟨113828142380848626091388825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75885428253899084060925883 113828142380848626091388825)
              ·
                refine ⟨85371106785636469568541619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113828142380848626091388825 85371106785636469568541619)
                ·
                  refine ⟨128056660178454704352812429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85371106785636469568541619 128056660178454704352812429)
                  ·
                    refine ⟨48021247566920514132304661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 128056660178454704352812429 48021247566920514132304661)
                    ·
                      refine ⟨2250995979699399099951781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48021247566920514132304661 2250995979699399099951781)
                      ·
                        rfl

theorem cell23_4383799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_4383799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383799 prefixEnd_4383799 := by exact prefixLift 4383799
  have htrace : WordTrace (prefixWord ++ tailWord_4383799) baseStart_4383799 baseEnd_4383799 := by
    simpa [prefixWord, tailWord_4383799, baseEnd_4383799] using wordTrace_append hprefix tailTrace_4383799
  have hstable : (prefixWord ++ tailWord_4383799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383799).length < 2 ^ (prefixWord ++ tailWord_4383799).sum := by decide
  have hdescent : baseEnd_4383799 < baseStart_4383799 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383837 : List Nat := [1, 4, 4, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_4383837 : Nat := 118140960795 + 4383837 * 2 ^ 59
def prefixEnd_4383837 : Nat := 4983230072969 + 3 ^ 40 * 4383837 * 2
def baseEnd_4383837 : Nat := 2251015491964269951276607

theorem tailTrace_4383837 : CollatzResearch.WordTrace tailWord_4383837 prefixEnd_4383837 2251015491964269951276607 := by
  unfold tailWord_4383837
  simp only [CollatzResearch.WordTrace]
  refine ⟨159891671019114723597677765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106594447346076482398451843 159891671019114723597677765)
  ·
    refine ⟨29979688316084010674564581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159891671019114723597677765 29979688316084010674564581)
    ·
      refine ⟨5621191559265752001480859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29979688316084010674564581 5621191559265752001480859)
      ·
        refine ⟨8431787338898628002221289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5621191559265752001480859 8431787338898628002221289)
        ·
          refine ⟨6323840504173971001665967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8431787338898628002221289 6323840504173971001665967)
          ·
            refine ⟨9485760756260956502498951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6323840504173971001665967 9485760756260956502498951)
            ·
              refine ⟨14228641134391434753748427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9485760756260956502498951 14228641134391434753748427)
              ·
                refine ⟨21342961701587152130622641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14228641134391434753748427 21342961701587152130622641)
                ·
                  refine ⟨16007221276190364097966981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21342961701587152130622641 16007221276190364097966981)
                  ·
                    refine ⟨3001353989285693268368809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16007221276190364097966981 3001353989285693268368809)
                    ·
                      refine ⟨2251015491964269951276607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3001353989285693268368809 2251015491964269951276607)
                      ·
                        rfl

theorem cell23_4383837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_4383837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383837 prefixEnd_4383837 := by exact prefixLift 4383837
  have htrace : WordTrace (prefixWord ++ tailWord_4383837) baseStart_4383837 baseEnd_4383837 := by
    simpa [prefixWord, tailWord_4383837, baseEnd_4383837] using wordTrace_append hprefix tailTrace_4383837
  have hstable : (prefixWord ++ tailWord_4383837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383837).length < 2 ^ (prefixWord ++ tailWord_4383837).sum := by decide
  have hdescent : baseEnd_4383837 < baseStart_4383837 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383856 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 3, 5]
def baseStart_4383856 : Nat := 118140960795 + 4383856 * 2 ^ 59
def prefixEnd_4383856 : Nat := 4983230072969 + 3 ^ 40 * 4383856 * 2
def baseEnd_4383856 : Nat := 750341749365568458979673

theorem tailTrace_4383856 : CollatzResearch.WordTrace tailWord_4383856 prefixEnd_4383856 750341749365568458979673 := by
  unfold tailWord_4383856
  simp only [CollatzResearch.WordTrace]
  refine ⟨79946182003022944921309711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106594909337363926561746281 79946182003022944921309711)
  ·
    refine ⟨119919273004534417381964567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79946182003022944921309711 119919273004534417381964567)
    ·
      refine ⟨179878909506801626072946851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119919273004534417381964567 179878909506801626072946851)
      ·
        refine ⟨269818364260202439109420277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179878909506801626072946851 269818364260202439109420277)
        ·
          refine ⟨25295471649393978666508151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 269818364260202439109420277 25295471649393978666508151)
          ·
            refine ⟨37943207474090967999762227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25295471649393978666508151 37943207474090967999762227)
            ·
              refine ⟨56914811211136451999643341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37943207474090967999762227 56914811211136451999643341)
              ·
                refine ⟨21343054204176169499866253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56914811211136451999643341 21343054204176169499866253)
                ·
                  refine ⟨8003645326566063562449845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21343054204176169499866253 8003645326566063562449845)
                  ·
                    refine ⟨750341749365568458979673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8003645326566063562449845 750341749365568458979673)
                    ·
                      rfl

theorem cell23_4383856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 3, 5].length) (baseStart_4383856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383856 prefixEnd_4383856 := by exact prefixLift 4383856
  have htrace : WordTrace (prefixWord ++ tailWord_4383856) baseStart_4383856 baseEnd_4383856 := by
    simpa [prefixWord, tailWord_4383856, baseEnd_4383856] using wordTrace_append hprefix tailTrace_4383856
  have hstable : (prefixWord ++ tailWord_4383856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383856).length < 2 ^ (prefixWord ++ tailWord_4383856).sum := by decide
  have hdescent : baseEnd_4383856 < baseStart_4383856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383863 : List Nat := [1, 1, 3, 1, 1, 4, 3, 1, 1, 5, 2]
def baseStart_4383863 : Nat := 118140960795 + 4383863 * 2 ^ 59
def prefixEnd_4383863 : Nat := 4983230072969 + 3 ^ 40 * 4383863 * 2
def baseEnd_4383863 : Nat := 2251028842461286849551487

theorem tailTrace_4383863 : CollatzResearch.WordTrace tailWord_4383863 prefixEnd_4383863 2251028842461286849551487 := by
  unfold tailWord_4383863
  simp only [CollatzResearch.WordTrace]
  refine ⟨159892619317020530038124243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106595079544680353358749495 159892619317020530038124243)
  ·
    refine ⟨239838928975530795057186365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159892619317020530038124243 239838928975530795057186365)
    ·
      refine ⟨89939598365824048146444887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239838928975530795057186365 89939598365824048146444887)
      ·
        refine ⟨134909397548736072219667331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89939598365824048146444887 134909397548736072219667331)
        ·
          refine ⟨202364096323104108329500997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134909397548736072219667331 202364096323104108329500997)
          ·
            refine ⟨37943268060582020311781437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 202364096323104108329500997 37943268060582020311781437)
            ·
              refine ⟨14228725522718257616918039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37943268060582020311781437 14228725522718257616918039)
              ·
                refine ⟨21343088284077386425377059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14228725522718257616918039 21343088284077386425377059)
                ·
                  refine ⟨32014632426116079638065589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21343088284077386425377059 32014632426116079638065589)
                  ·
                    refine ⟨3001371789948382466068649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32014632426116079638065589 3001371789948382466068649)
                    ·
                      refine ⟨2251028842461286849551487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3001371789948382466068649 2251028842461286849551487)
                      ·
                        rfl

theorem cell23_4383863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 5, 2].length) (baseStart_4383863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383863 prefixEnd_4383863 := by exact prefixLift 4383863
  have htrace : WordTrace (prefixWord ++ tailWord_4383863) baseStart_4383863 baseEnd_4383863 := by
    simpa [prefixWord, tailWord_4383863, baseEnd_4383863] using wordTrace_append hprefix tailTrace_4383863
  have hstable : (prefixWord ++ tailWord_4383863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383863).length < 2 ^ (prefixWord ++ tailWord_4383863).sum := by decide
  have hdescent : baseEnd_4383863 < baseStart_4383863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383938 : List Nat := [3, 5, 1, 1, 3, 1, 1, 1, 3, 1, 3]
def baseStart_4383938 : Nat := 118140960795 + 4383938 * 2 ^ 59
def prefixEnd_4383938 : Nat := 4983230072969 + 3 ^ 40 * 4383938 * 2
def baseEnd_4383938 : Nat := 2251067353510374056113643

theorem tailTrace_4383938 : CollatzResearch.WordTrace tailWord_4383938 prefixEnd_4383938 2251067353510374056113643 := by
  unfold tailWord_4383938
  simp only [CollatzResearch.WordTrace]
  refine ⟨39973838697937204461776117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106596903194499211898069645 39973838697937204461776117)
  ·
    refine ⟨3747547377931612918291511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 39973838697937204461776117 3747547377931612918291511)
    ·
      refine ⟨5621321066897419377437267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3747547377931612918291511 5621321066897419377437267)
      ·
        refine ⟨8431981600346129066155901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5621321066897419377437267 8431981600346129066155901)
        ·
          refine ⟨3161993100129798399808463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8431981600346129066155901 3161993100129798399808463)
          ·
            refine ⟨4742989650194697599712695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3161993100129798399808463 4742989650194697599712695)
            ·
              refine ⟨7114484475292046399569043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4742989650194697599712695 7114484475292046399569043)
              ·
                refine ⟨10671726712938069599353565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7114484475292046399569043 10671726712938069599353565)
                ·
                  refine ⟨4001897517351776099757587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10671726712938069599353565 4001897517351776099757587)
                  ·
                    refine ⟨6002846276027664149636381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4001897517351776099757587 6002846276027664149636381)
                    ·
                      refine ⟨2251067353510374056113643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6002846276027664149636381 2251067353510374056113643)
                      ·
                        rfl

theorem cell23_4383938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_4383938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383938 prefixEnd_4383938 := by exact prefixLift 4383938
  have htrace : WordTrace (prefixWord ++ tailWord_4383938) baseStart_4383938 baseEnd_4383938 := by
    simpa [prefixWord, tailWord_4383938, baseEnd_4383938] using wordTrace_append hprefix tailTrace_4383938
  have hstable : (prefixWord ++ tailWord_4383938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383938).length < 2 ^ (prefixWord ++ tailWord_4383938).sum := by decide
  have hdescent : baseEnd_4383938 < baseStart_4383938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4383953 : List Nat := [1, 2, 2, 1, 2, 2, 1, 1, 2, 7, 2]
def baseStart_4383953 : Nat := 118140960795 + 4383953 * 2 ^ 59
def prefixEnd_4383953 : Nat := 4983230072969 + 3 ^ 40 * 4383953 * 2
def baseEnd_4383953 : Nat := 2251075055720191497426073

theorem tailTrace_4383953 : CollatzResearch.WordTrace tailWord_4383953 prefixEnd_4383953 2251075055720191497426073 := by
  unfold tailWord_4383953
  simp only [CollatzResearch.WordTrace]
  refine ⟨159895901886694475408900513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106597267924462983605933675 159895901886694475408900513)
  ·
    refine ⟨119921926415020856556675385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159895901886694475408900513 119921926415020856556675385)
    ·
      refine ⟨89941444811265642417506539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119921926415020856556675385 89941444811265642417506539)
      ·
        refine ⟨134912167216898463626259809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89941444811265642417506539 134912167216898463626259809)
        ·
          refine ⟨101184125412673847719694857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134912167216898463626259809 101184125412673847719694857)
          ·
            refine ⟨75888094059505385789771143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101184125412673847719694857 75888094059505385789771143)
            ·
              refine ⟨113832141089258078684656715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75888094059505385789771143 113832141089258078684656715)
              ·
                refine ⟨170748211633887118026985073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113832141089258078684656715 170748211633887118026985073)
                ·
                  refine ⟨128061158725415338520238805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170748211633887118026985073 128061158725415338520238805)
                  ·
                    refine ⟨3001433407626921996568097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 128061158725415338520238805 3001433407626921996568097)
                    ·
                      refine ⟨2251075055720191497426073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3001433407626921996568097 2251075055720191497426073)
                      ·
                        rfl

theorem cell23_4383953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 7, 2].length) (baseStart_4383953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4383953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4383953 prefixEnd_4383953 := by exact prefixLift 4383953
  have htrace : WordTrace (prefixWord ++ tailWord_4383953) baseStart_4383953 baseEnd_4383953 := by
    simpa [prefixWord, tailWord_4383953, baseEnd_4383953] using wordTrace_append hprefix tailTrace_4383953
  have hstable : (prefixWord ++ tailWord_4383953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4383953).length < 2 ^ (prefixWord ++ tailWord_4383953).sum := by decide
  have hdescent : baseEnd_4383953 < baseStart_4383953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4383953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384003 : List Nat := [1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 3]
def baseStart_4384003 : Nat := 118140960795 + 4384003 * 2 ^ 59
def prefixEnd_4384003 : Nat := 4983230072969 + 3 ^ 40 * 4384003 * 2
def baseEnd_4384003 : Nat := 2251100729752916301800843

theorem tailTrace_4384003 : CollatzResearch.WordTrace tailWord_4384003 prefixEnd_4384003 2251100729752916301800843 := by
  unfold tailWord_4384003
  simp only [CollatzResearch.WordTrace]
  refine ⟨159897725536513333948220663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106598483691008889298813775 159897725536513333948220663)
  ·
    refine ⟨239846588304770000922330995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159897725536513333948220663 239846588304770000922330995)
    ·
      refine ⟨359769882457155001383496493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239846588304770000922330995 359769882457155001383496493)
      ·
        refine ⟨134913705921433125518811185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 359769882457155001383496493 134913705921433125518811185)
        ·
          refine ⟨101185279441074844139108389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134913705921433125518811185 101185279441074844139108389)
          ·
            refine ⟨18972239895201533276082823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101185279441074844139108389 18972239895201533276082823)
            ·
              refine ⟨28458359842802299914124235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18972239895201533276082823 28458359842802299914124235)
              ·
                refine ⟨42687539764203449871186353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28458359842802299914124235 42687539764203449871186353)
                ·
                  refine ⟨32015654823152587403389765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42687539764203449871186353 32015654823152587403389765)
                  ·
                    refine ⟨6002935279341110138135581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32015654823152587403389765 6002935279341110138135581)
                    ·
                      refine ⟨2251100729752916301800843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6002935279341110138135581 2251100729752916301800843)
                      ·
                        rfl

theorem cell23_4384003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 3].length) (baseStart_4384003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384003 prefixEnd_4384003 := by exact prefixLift 4384003
  have htrace : WordTrace (prefixWord ++ tailWord_4384003) baseStart_4384003 baseEnd_4384003 := by
    simpa [prefixWord, tailWord_4384003, baseEnd_4384003] using wordTrace_append hprefix tailTrace_4384003
  have hstable : (prefixWord ++ tailWord_4384003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384003).length < 2 ^ (prefixWord ++ tailWord_4384003).sum := by decide
  have hdescent : baseEnd_4384003 < baseStart_4384003 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384016 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 7]
def baseStart_4384016 : Nat := 118140960795 + 4384016 * 2 ^ 59
def prefixEnd_4384016 : Nat := 4983230072969 + 3 ^ 40 * 4384016 * 2
def baseEnd_4384016 : Nat := 2251107405001424750938283

theorem tailTrace_4384016 : CollatzResearch.WordTrace tailWord_4384016 prefixEnd_4384016 2251107405001424750938283 := by
  unfold tailWord_4384016
  simp only [CollatzResearch.WordTrace]
  refine ⟨79949099842733118584221951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106598799790310824778962601 79949099842733118584221951)
  ·
    refine ⟨119923649764099677876332927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79949099842733118584221951 119923649764099677876332927)
    ·
      refine ⟨179885474646149516814499391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119923649764099677876332927 179885474646149516814499391)
      ·
        refine ⟨269828211969224275221749087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179885474646149516814499391 269828211969224275221749087)
        ·
          refine ⟨404742317953836412832623631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269828211969224275221749087 404742317953836412832623631)
          ·
            refine ⟨607113476930754619248935447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404742317953836412832623631 607113476930754619248935447)
            ·
              refine ⟨910670215396131928873403171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 607113476930754619248935447 910670215396131928873403171)
              ·
                refine ⟨1366005323094197893310104757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 910670215396131928873403171 1366005323094197893310104757)
                ·
                  refine ⟨128062999040081052497822321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1366005323094197893310104757 128062999040081052497822321)
                  ·
                    refine ⟨96047249280060789373366741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 128062999040081052497822321 96047249280060789373366741)
                    ·
                      refine ⟨2251107405001424750938283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 96047249280060789373366741 2251107405001424750938283)
                      ·
                        rfl

theorem cell23_4384016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 7].length) (baseStart_4384016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384016 prefixEnd_4384016 := by exact prefixLift 4384016
  have htrace : WordTrace (prefixWord ++ tailWord_4384016) baseStart_4384016 baseEnd_4384016 := by
    simpa [prefixWord, tailWord_4384016, baseEnd_4384016] using wordTrace_append hprefix tailTrace_4384016
  have hstable : (prefixWord ++ tailWord_4384016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384016).length < 2 ^ (prefixWord ++ tailWord_4384016).sum := by decide
  have hdescent : baseEnd_4384016 < baseStart_4384016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384017 : List Nat := [1, 2, 2, 1, 1, 4, 1, 5, 2, 2, 2]
def baseStart_4384017 : Nat := 118140960795 + 4384017 * 2 ^ 59
def prefixEnd_4384017 : Nat := 4983230072969 + 3 ^ 40 * 4384017 * 2
def baseEnd_4384017 : Nat := 2251107918482079247025779

theorem tailTrace_4384017 : CollatzResearch.WordTrace tailWord_4384017 prefixEnd_4384017 2251107918482079247025779 := by
  unfold tailWord_4384017
  simp only [CollatzResearch.WordTrace]
  refine ⟨159898236158462614339230305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106598824105641742892820203 159898236158462614339230305)
  ·
    refine ⟨119923677118846960754422729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159898236158462614339230305 119923677118846960754422729)
    ·
      refine ⟨89942757839135220565817047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119923677118846960754422729 89942757839135220565817047)
      ·
        refine ⟨134914136758702830848725571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89942757839135220565817047 134914136758702830848725571)
        ·
          refine ⟨202371205138054246273088357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134914136758702830848725571 202371205138054246273088357)
          ·
            refine ⟨37944600963385171176204067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 202371205138054246273088357 37944600963385171176204067)
            ·
              refine ⟨56916901445077756764306101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37944600963385171176204067 56916901445077756764306101)
              ·
                refine ⟨5335959510476039696653697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56916901445077756764306101 5335959510476039696653697)
                ·
                  refine ⟨4001969632857029772490273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5335959510476039696653697 4001969632857029772490273)
                  ·
                    refine ⟨3001477224642772329367705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4001969632857029772490273 3001477224642772329367705)
                    ·
                      refine ⟨2251107918482079247025779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3001477224642772329367705 2251107918482079247025779)
                      ·
                        rfl

theorem cell23_4384017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 1, 5, 2, 2, 2].length) (baseStart_4384017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384017 prefixEnd_4384017 := by exact prefixLift 4384017
  have htrace : WordTrace (prefixWord ++ tailWord_4384017) baseStart_4384017 baseEnd_4384017 := by
    simpa [prefixWord, tailWord_4384017, baseEnd_4384017] using wordTrace_append hprefix tailTrace_4384017
  have hstable : (prefixWord ++ tailWord_4384017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384017).length < 2 ^ (prefixWord ++ tailWord_4384017).sum := by decide
  have hdescent : baseEnd_4384017 < baseStart_4384017 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384023 : List Nat := [1, 1, 3, 4, 1, 1, 3, 2, 7]
def baseStart_4384023 : Nat := 118140960795 + 4384023 * 2 ^ 59
def prefixEnd_4384023 : Nat := 4983230072969 + 3 ^ 40 * 4384023 * 2
def baseEnd_4384023 : Nat := 250123444374000691505639

theorem tailTrace_4384023 : CollatzResearch.WordTrace tailWord_4384023 prefixEnd_4384023 250123444374000691505639 := by
  unfold tailWord_4384023
  simp only [CollatzResearch.WordTrace]
  refine ⟨159898454996440877363948723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106598969997627251575965815 159898454996440877363948723)
  ·
    refine ⟨239847682494661316045923085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159898454996440877363948723 239847682494661316045923085)
    ·
      refine ⟨89942880935497993517221157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239847682494661316045923085 89942880935497993517221157)
      ·
        refine ⟨16864290175405873784478967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89942880935497993517221157 16864290175405873784478967)
        ·
          refine ⟨25296435263108810676718451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16864290175405873784478967 25296435263108810676718451)
          ·
            refine ⟨37944652894663216015077677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25296435263108810676718451 37944652894663216015077677)
            ·
              refine ⟨14229244835498706005654129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37944652894663216015077677 14229244835498706005654129)
              ·
                refine ⟨10671933626624029504240597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14229244835498706005654129 10671933626624029504240597)
                ·
                  refine ⟨250123444374000691505639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10671933626624029504240597 250123444374000691505639)
                  ·
                    rfl

theorem cell23_4384023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 7].length) (baseStart_4384023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384023 prefixEnd_4384023 := by exact prefixLift 4384023
  have htrace : WordTrace (prefixWord ++ tailWord_4384023) baseStart_4384023 baseEnd_4384023 := by
    simpa [prefixWord, tailWord_4384023, baseEnd_4384023] using wordTrace_append hprefix tailTrace_4384023
  have hstable : (prefixWord ++ tailWord_4384023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384023).length < 2 ^ (prefixWord ++ tailWord_4384023).sum := by decide
  have hdescent : baseEnd_4384023 < baseStart_4384023 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384033 : List Nat := [1, 2, 3, 2, 1, 1, 1, 1, 3, 5, 3]
def baseStart_4384033 : Nat := 118140960795 + 4384033 * 2 ^ 59
def prefixEnd_4384033 : Nat := 4983230072969 + 3 ^ 40 * 4384033 * 2
def baseEnd_4384033 : Nat := 2251116134172551184425705

theorem tailTrace_4384033 : CollatzResearch.WordTrace tailWord_4384033 prefixEnd_4384033 2251116134172551184425705 := by
  unfold tailWord_4384033
  simp only [CollatzResearch.WordTrace]
  refine ⟨159898819726404649071812753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106599213150936432714541835 159898819726404649071812753)
  ·
    refine ⟨119924114794803486803859565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159898819726404649071812753 119924114794803486803859565)
    ·
      refine ⟨44971543048051307551447337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119924114794803486803859565 44971543048051307551447337)
      ·
        refine ⟨33728657286038480663585503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44971543048051307551447337 33728657286038480663585503)
        ·
          refine ⟨50592985929057720995378255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33728657286038480663585503 50592985929057720995378255)
          ·
            refine ⟨75889478893586581493067383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50592985929057720995378255 75889478893586581493067383)
            ·
              refine ⟨113834218340379872239601075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75889478893586581493067383 113834218340379872239601075)
              ·
                refine ⟨170751327510569808359401613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113834218340379872239601075 170751327510569808359401613)
                ·
                  refine ⟨64031747816463678134775605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 170751327510569808359401613 64031747816463678134775605)
                  ·
                    refine ⟨6002976357793469825135213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64031747816463678134775605 6002976357793469825135213)
                    ·
                      refine ⟨2251116134172551184425705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6002976357793469825135213 2251116134172551184425705)
                      ·
                        rfl

theorem cell23_4384033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_4384033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384033 prefixEnd_4384033 := by exact prefixLift 4384033
  have htrace : WordTrace (prefixWord ++ tailWord_4384033) baseStart_4384033 baseEnd_4384033 := by
    simpa [prefixWord, tailWord_4384033, baseEnd_4384033] using wordTrace_append hprefix tailTrace_4384033
  have hstable : (prefixWord ++ tailWord_4384033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384033).length < 2 ^ (prefixWord ++ tailWord_4384033).sum := by decide
  have hdescent : baseEnd_4384033 < baseStart_4384033 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384050 : List Nat := [3, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3]
def baseStart_4384050 : Nat := 118140960795 + 4384050 * 2 ^ 59
def prefixEnd_4384050 : Nat := 4983230072969 + 3 ^ 40 * 4384050 * 2
def baseEnd_4384050 : Nat := 2251124863343677617913127

theorem tailTrace_4384050 : CollatzResearch.WordTrace tailWord_4384050 prefixEnd_4384050 2251124863343677617913127 := by
  unfold tailWord_4384050
  simp only [CollatzResearch.WordTrace]
  refine ⟨39974859941835765243795401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106599626511562040650121069 39974859941835765243795401)
  ·
    refine ⟨29981144956376823932846551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39974859941835765243795401 29981144956376823932846551)
    ·
      refine ⟨44971717434565235899269827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29981144956376823932846551 44971717434565235899269827)
      ·
        refine ⟨67457576151847853848904741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44971717434565235899269827 67457576151847853848904741)
        ·
          refine ⟨12648295528471472596669639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67457576151847853848904741 12648295528471472596669639)
          ·
            refine ⟨18972443292707208895004459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12648295528471472596669639 18972443292707208895004459)
            ·
              refine ⟨28458664939060813342506689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18972443292707208895004459 28458664939060813342506689)
              ·
                refine ⟨21343998704295610006880017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28458664939060813342506689 21343998704295610006880017)
                ·
                  refine ⟨16007999028221707505160013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21343998704295610006880017 16007999028221707505160013)
                  ·
                    refine ⟨6002999635583140314435005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16007999028221707505160013 6002999635583140314435005)
                    ·
                      refine ⟨2251124863343677617913127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6002999635583140314435005 2251124863343677617913127)
                      ·
                        rfl

theorem cell23_4384050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_4384050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384050 prefixEnd_4384050 := by exact prefixLift 4384050
  have htrace : WordTrace (prefixWord ++ tailWord_4384050) baseStart_4384050 baseEnd_4384050 := by
    simpa [prefixWord, tailWord_4384050, baseEnd_4384050] using wordTrace_append hprefix tailTrace_4384050
  have hstable : (prefixWord ++ tailWord_4384050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384050).length < 2 ^ (prefixWord ++ tailWord_4384050).sum := by decide
  have hdescent : baseEnd_4384050 < baseStart_4384050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384068 : List Nat := [2, 3, 4, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_4384068 : Nat := 118140960795 + 4384068 * 2 ^ 59
def prefixEnd_4384068 : Nat := 4983230072969 + 3 ^ 40 * 4384068 * 2
def baseEnd_4384068 : Nat := 2251134105995458547488045

theorem tailTrace_4384068 : CollatzResearch.WordTrace tailWord_4384068 prefixEnd_4384068 2251134105995458547488045 := by
  unfold tailWord_4384068
  simp only [CollatzResearch.WordTrace]
  refine ⟨79950048140638925024668429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106600064187518566699557905 79950048140638925024668429)
  ·
    refine ⟨29981268052739596884250661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79950048140638925024668429 29981268052739596884250661)
    ·
      refine ⟨5621487759888674415796999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 29981268052739596884250661 5621487759888674415796999)
      ·
        refine ⟨8432231639833011623695499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5621487759888674415796999 8432231639833011623695499)
        ·
          refine ⟨12648347459749517435543249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8432231639833011623695499 12648347459749517435543249)
          ·
            refine ⟨9486260594812138076657437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12648347459749517435543249 9486260594812138076657437)
            ·
              refine ⟨3557347723054551778746539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9486260594812138076657437 3557347723054551778746539)
              ·
                refine ⟨5336021584581827668119809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3557347723054551778746539 5336021584581827668119809)
                ·
                  refine ⟨4002016188436370751089857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5336021584581827668119809 4002016188436370751089857)
                  ·
                    refine ⟨3001512141327278063317393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4002016188436370751089857 3001512141327278063317393)
                    ·
                      refine ⟨2251134105995458547488045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3001512141327278063317393 2251134105995458547488045)
                      ·
                        rfl

theorem cell23_4384068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_4384068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384068 prefixEnd_4384068 := by exact prefixLift 4384068
  have htrace : WordTrace (prefixWord ++ tailWord_4384068) baseStart_4384068 baseEnd_4384068 := by
    simpa [prefixWord, tailWord_4384068, baseEnd_4384068] using wordTrace_append hprefix tailTrace_4384068
  have hstable : (prefixWord ++ tailWord_4384068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384068).length < 2 ^ (prefixWord ++ tailWord_4384068).sum := by decide
  have hdescent : baseEnd_4384068 < baseStart_4384068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384073 : List Nat := [1, 2, 1, 1, 2, 3, 3, 2, 1, 3, 4]
def baseStart_4384073 : Nat := 118140960795 + 4384073 * 2 ^ 59
def prefixEnd_4384073 : Nat := 4983230072969 + 3 ^ 40 * 4384073 * 2
def baseEnd_4384073 : Nat := 2251136673398731027925521

theorem tailTrace_4384073 : CollatzResearch.WordTrace tailWord_4384073 prefixEnd_4384073 2251136673398731027925521 := by
  unfold tailWord_4384073
  simp only [CollatzResearch.WordTrace]
  refine ⟨159900278646259735903268873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106600185764173157268845915 159900278646259735903268873)
  ·
    refine ⟨119925208984694801927451655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159900278646259735903268873 119925208984694801927451655)
    ·
      refine ⟨179887813477042202891177483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119925208984694801927451655 179887813477042202891177483)
      ·
        refine ⟨269831720215563304336766225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179887813477042202891177483 269831720215563304336766225)
        ·
          refine ⟨202373790161672478252574669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269831720215563304336766225 202373790161672478252574669)
          ·
            refine ⟨75890171310627179344715501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202373790161672478252574669 75890171310627179344715501)
            ·
              refine ⟨28458814241485192254268313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75890171310627179344715501 28458814241485192254268313)
              ·
                refine ⟨21344110681113894190701235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28458814241485192254268313 21344110681113894190701235)
                ·
                  refine ⟨32016166021670841286051853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21344110681113894190701235 32016166021670841286051853)
                  ·
                    refine ⟨12006062258126565482269445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32016166021670841286051853 12006062258126565482269445)
                    ·
                      refine ⟨2251136673398731027925521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12006062258126565482269445 2251136673398731027925521)
                      ·
                        rfl

theorem cell23_4384073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 2, 1, 3, 4].length) (baseStart_4384073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384073 prefixEnd_4384073 := by exact prefixLift 4384073
  have htrace : WordTrace (prefixWord ++ tailWord_4384073) baseStart_4384073 baseEnd_4384073 := by
    simpa [prefixWord, tailWord_4384073, baseEnd_4384073] using wordTrace_append hprefix tailTrace_4384073
  have hstable : (prefixWord ++ tailWord_4384073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384073).length < 2 ^ (prefixWord ++ tailWord_4384073).sum := by decide
  have hdescent : baseEnd_4384073 < baseStart_4384073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384090 : List Nat := [3, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2]
def baseStart_4384090 : Nat := 118140960795 + 4384090 * 2 ^ 59
def prefixEnd_4384090 : Nat := 4983230072969 + 3 ^ 40 * 4384090 * 2
def baseEnd_4384090 : Nat := 2251145402569857461412943

theorem tailTrace_4384090 : CollatzResearch.WordTrace tailWord_4384090 prefixEnd_4384090 2251145402569857461412943 := by
  unfold tailWord_4384090
  simp only [CollatzResearch.WordTrace]
  refine ⟨39975224671799536951659431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106600599124798765204425149 39975224671799536951659431)
  ·
    refine ⟨59962837007699305427489147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39975224671799536951659431 59962837007699305427489147)
    ·
      refine ⟨89944255511548958141233721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59962837007699305427489147 89944255511548958141233721)
      ·
        refine ⟨67458191633661718605925291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89944255511548958141233721 67458191633661718605925291)
        ·
          refine ⟨101187287450492577908887937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67458191633661718605925291 101187287450492577908887937)
          ·
            refine ⟨75890465587869433431665953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101187287450492577908887937 75890465587869433431665953)
            ·
              refine ⟨56917849190902075073749465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75890465587869433431665953 56917849190902075073749465)
              ·
                refine ⟨42688386893176556305312099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56917849190902075073749465 42688386893176556305312099)
                ·
                  refine ⟨64032580339764834457968149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42688386893176556305312099 64032580339764834457968149)
                  ·
                    refine ⟨3001527203426476615217257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64032580339764834457968149 3001527203426476615217257)
                    ·
                      refine ⟨2251145402569857461412943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3001527203426476615217257 2251145402569857461412943)
                      ·
                        rfl

theorem cell23_4384090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 2, 1, 6, 2].length) (baseStart_4384090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384090 prefixEnd_4384090 := by exact prefixLift 4384090
  have htrace : WordTrace (prefixWord ++ tailWord_4384090) baseStart_4384090 baseEnd_4384090 := by
    simpa [prefixWord, tailWord_4384090, baseEnd_4384090] using wordTrace_append hprefix tailTrace_4384090
  have hstable : (prefixWord ++ tailWord_4384090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384090).length < 2 ^ (prefixWord ++ tailWord_4384090).sum := by decide
  have hdescent : baseEnd_4384090 < baseStart_4384090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384113 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 8]
def baseStart_4384113 : Nat := 118140960795 + 4384113 * 2 ^ 59
def prefixEnd_4384113 : Nat := 4983230072969 + 3 ^ 40 * 4384113 * 2
def baseEnd_4384113 : Nat := 250128579180545652380593

theorem tailTrace_4384113 : CollatzResearch.WordTrace tailWord_4384113 prefixEnd_4384113 250128579180545652380593 := by
  unfold tailWord_4384113
  simp only [CollatzResearch.WordTrace]
  refine ⟨159901737566114822734724993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106601158377409881823149995 159901737566114822734724993)
  ·
    refine ⟨119926303174586117051043745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159901737566114822734724993 119926303174586117051043745)
    ·
      refine ⟨89944727380939587788282809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119926303174586117051043745 89944727380939587788282809)
      ·
        refine ⟨67458545535704690841212107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89944727380939587788282809 67458545535704690841212107)
        ·
          refine ⟨101187818303557036261818161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67458545535704690841212107 101187818303557036261818161)
          ·
            refine ⟨75890863727667777196363621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101187818303557036261818161 75890863727667777196363621)
            ·
              refine ⟨14229536948937708224318179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75890863727667777196363621 14229536948937708224318179)
              ·
                refine ⟨21344305423406562336477269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14229536948937708224318179 21344305423406562336477269)
                ·
                  refine ⟨250128579180545652380593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21344305423406562336477269 250128579180545652380593)
                  ·
                    rfl

theorem cell23_4384113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 8].length) (baseStart_4384113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384113 prefixEnd_4384113 := by exact prefixLift 4384113
  have htrace : WordTrace (prefixWord ++ tailWord_4384113) baseStart_4384113 baseEnd_4384113 := by
    simpa [prefixWord, tailWord_4384113, baseEnd_4384113] using wordTrace_append hprefix tailTrace_4384113
  have hstable : (prefixWord ++ tailWord_4384113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384113).length < 2 ^ (prefixWord ++ tailWord_4384113).sum := by decide
  have hdescent : baseEnd_4384113 < baseStart_4384113 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384133 : List Nat := [1, 3, 1, 1, 3, 1, 2, 2, 1, 2, 6]
def baseStart_4384133 : Nat := 118140960795 + 4384133 * 2 ^ 59
def prefixEnd_4384133 : Nat := 4983230072969 + 3 ^ 40 * 4384133 * 2
def baseEnd_4384133 : Nat := 2251167482238000793175245

theorem tailTrace_4384133 : CollatzResearch.WordTrace tailWord_4384133 prefixEnd_4384133 2251167482238000793175245 := by
  unfold tailWord_4384133
  simp only [CollatzResearch.WordTrace]
  refine ⟨159902467026042366150453053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106601644684028244100302035 159902467026042366150453053)
  ·
    refine ⟨59963425134765887306419895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159902467026042366150453053 59963425134765887306419895)
    ·
      refine ⟨89945137702148830959629843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59963425134765887306419895 89945137702148830959629843)
      ·
        refine ⟨134917706553223246439444765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89945137702148830959629843 134917706553223246439444765)
        ·
          refine ⟨50594139957458717414791787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134917706553223246439444765 50594139957458717414791787)
          ·
            refine ⟨75891209936188076122187681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50594139957458717414791787 75891209936188076122187681)
            ·
              refine ⟨56918407452141057091640761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75891209936188076122187681 56918407452141057091640761)
              ·
                refine ⟨42688805589105792818730571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56918407452141057091640761 42688805589105792818730571)
                ·
                  refine ⟨64033208383658689228095857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42688805589105792818730571 64033208383658689228095857)
                  ·
                    refine ⟨48024906287744016921071893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 64033208383658689228095857 48024906287744016921071893)
                    ·
                      refine ⟨2251167482238000793175245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48024906287744016921071893 2251167482238000793175245)
                      ·
                        rfl

theorem cell23_4384133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_4384133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384133 prefixEnd_4384133 := by exact prefixLift 4384133
  have htrace : WordTrace (prefixWord ++ tailWord_4384133) baseStart_4384133 baseEnd_4384133 := by
    simpa [prefixWord, tailWord_4384133, baseEnd_4384133] using wordTrace_append hprefix tailTrace_4384133
  have hstable : (prefixWord ++ tailWord_4384133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384133).length < 2 ^ (prefixWord ++ tailWord_4384133).sum := by decide
  have hdescent : baseEnd_4384133 < baseStart_4384133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384203 : List Nat := [1, 1, 1, 1, 3, 3, 2, 11]
def baseStart_4384203 : Nat := 118140960795 + 4384203 * 2 ^ 59
def prefixEnd_4384203 : Nat := 4983230072969 + 3 ^ 40 * 4384203 * 2
def baseEnd_4384203 : Nat := 83377904662363537751849

theorem tailTrace_4384203 : CollatzResearch.WordTrace tailWord_4384203 prefixEnd_4384203 83377904662363537751849 := by
  unfold tailWord_4384203
  simp only [CollatzResearch.WordTrace]
  refine ⟨159905020135788768105501263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106603346757192512070334175 159905020135788768105501263)
  ·
    refine ⟨239857530203683152158251895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159905020135788768105501263 239857530203683152158251895)
    ·
      refine ⟨359786295305524728237377843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239857530203683152158251895 359786295305524728237377843)
      ·
        refine ⟨539679442958287092356066765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359786295305524728237377843 539679442958287092356066765)
        ·
          refine ⟨202379791109357659633525037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 539679442958287092356066765 202379791109357659633525037)
          ·
            refine ⟨75892421666009122362571889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202379791109357659633525037 75892421666009122362571889)
            ·
              refine ⟨56919316249506841771928917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75892421666009122362571889 56919316249506841771928917)
              ·
                refine ⟨83377904662363537751849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 56919316249506841771928917 83377904662363537751849)
                ·
                  rfl

theorem cell23_4384203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 11].length) (baseStart_4384203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384203 prefixEnd_4384203 := by exact prefixLift 4384203
  have htrace : WordTrace (prefixWord ++ tailWord_4384203) baseStart_4384203 baseEnd_4384203 := by
    simpa [prefixWord, tailWord_4384203, baseEnd_4384203] using wordTrace_append hprefix tailTrace_4384203
  have hstable : (prefixWord ++ tailWord_4384203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384203).length < 2 ^ (prefixWord ++ tailWord_4384203).sum := by decide
  have hdescent : baseEnd_4384203 < baseStart_4384203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384231 : List Nat := [1, 1, 5, 2, 1, 3, 2, 1, 3, 2, 2]
def baseStart_4384231 : Nat := 118140960795 + 4384231 * 2 ^ 59
def prefixEnd_4384231 : Nat := 4983230072969 + 3 ^ 40 * 4384231 * 2
def baseEnd_4384231 : Nat := 2251217803342141409749795

theorem tailTrace_4384231 : CollatzResearch.WordTrace tailWord_4384231 prefixEnd_4384231 2251217803342141409749795 := by
  unfold tailWord_4384231
  simp only [CollatzResearch.WordTrace]
  refine ⟨159906041379687328887520547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106604027586458219258347031 159906041379687328887520547)
  ·
    refine ⟨239859062069530993331280821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159906041379687328887520547 239859062069530993331280821)
    ·
      refine ⟨22486787069018530624807577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 239859062069530993331280821 22486787069018530624807577)
      ·
        refine ⟨16865090301763897968605683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22486787069018530624807577 16865090301763897968605683)
        ·
          refine ⟨25297635452645846952908525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16865090301763897968605683 25297635452645846952908525)
          ·
            refine ⟨9486613294742192607340697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25297635452645846952908525 9486613294742192607340697)
            ·
              refine ⟨7114959971056644455505523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9486613294742192607340697 7114959971056644455505523)
              ·
                refine ⟨10672439956584966683258285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7114959971056644455505523 10672439956584966683258285)
                ·
                  refine ⟨4002164983719362506221857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10672439956584966683258285 4002164983719362506221857)
                  ·
                    refine ⟨3001623737789521879666393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4002164983719362506221857 3001623737789521879666393)
                    ·
                      refine ⟨2251217803342141409749795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3001623737789521879666393 2251217803342141409749795)
                      ·
                        rfl

theorem cell23_4384231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_4384231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384231 prefixEnd_4384231 := by exact prefixLift 4384231
  have htrace : WordTrace (prefixWord ++ tailWord_4384231) baseStart_4384231 baseEnd_4384231 := by
    simpa [prefixWord, tailWord_4384231, baseEnd_4384231] using wordTrace_append hprefix tailTrace_4384231
  have hstable : (prefixWord ++ tailWord_4384231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384231).length < 2 ^ (prefixWord ++ tailWord_4384231).sum := by decide
  have hdescent : baseEnd_4384231 < baseStart_4384231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384254 : List Nat := [4, 2, 2, 3, 1, 1, 1, 9]
def baseStart_4384254 : Nat := 118140960795 + 4384254 * 2 ^ 59
def prefixEnd_4384254 : Nat := 4983230072969 + 3 ^ 40 * 4384254 * 2
def baseEnd_4384254 : Nat := 83378874570266474806007

theorem tailTrace_4384254 : CollatzResearch.WordTrace tailWord_4384254 prefixEnd_4384254 83378874570266474806007 := by
  unfold tailWord_4384254
  simp only [CollatzResearch.WordTrace]
  refine ⟨19988360032325500476950977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106604586839069335877071877 19988360032325500476950977)
  ·
    refine ⟨14991270024244125357713233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19988360032325500476950977 14991270024244125357713233)
    ·
      refine ⟨11243452518183094018284925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14991270024244125357713233 11243452518183094018284925)
      ·
        refine ⟨4216294694318660256856847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11243452518183094018284925 4216294694318660256856847)
        ·
          refine ⟨6324442041477990385285271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4216294694318660256856847 6324442041477990385285271)
          ·
            refine ⟨9486663062216985577927907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6324442041477990385285271 9486663062216985577927907)
            ·
              refine ⟨14229994593325478366891861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9486663062216985577927907 14229994593325478366891861)
              ·
                refine ⟨83378874570266474806007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14229994593325478366891861 83378874570266474806007)
                ·
                  rfl

theorem cell23_4384254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 9].length) (baseStart_4384254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384254 prefixEnd_4384254 := by exact prefixLift 4384254
  have htrace : WordTrace (prefixWord ++ tailWord_4384254) baseStart_4384254 baseEnd_4384254 := by
    simpa [prefixWord, tailWord_4384254, baseEnd_4384254] using wordTrace_append hprefix tailTrace_4384254
  have hstable : (prefixWord ++ tailWord_4384254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384254).length < 2 ^ (prefixWord ++ tailWord_4384254).sum := by decide
  have hdescent : baseEnd_4384254 < baseStart_4384254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384337 : List Nat := [1, 2, 2, 1, 3, 2, 2, 2, 2, 3, 3]
def baseStart_4384337 : Nat := 118140960795 + 4384337 * 2 ^ 59
def prefixEnd_4384337 : Nat := 4983230072969 + 3 ^ 40 * 4384337 * 2
def baseEnd_4384337 : Nat := 2251272232291517995024307

theorem tailTrace_4384337 : CollatzResearch.WordTrace tailWord_4384337 prefixEnd_4384337 2251272232291517995024307 := by
  unfold tailWord_4384337
  simp only [CollatzResearch.WordTrace]
  refine ⟨159909907517303308990879265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106606605011535539327252843 159909907517303308990879265)
  ·
    refine ⟨119932430637977481743159449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159909907517303308990879265 119932430637977481743159449)
    ·
      refine ⟨89949322978483111307369587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119932430637977481743159449 89949322978483111307369587)
      ·
        refine ⟨134923984467724666961054381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89949322978483111307369587 134923984467724666961054381)
        ·
          refine ⟨50596494175396750110395393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134923984467724666961054381 50596494175396750110395393)
          ·
            refine ⟨37947370631547562582796545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50596494175396750110395393 37947370631547562582796545)
            ·
              refine ⟨28460527973660671937097409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37947370631547562582796545 28460527973660671937097409)
              ·
                refine ⟨21345395980245503952823057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28460527973660671937097409 21345395980245503952823057)
                ·
                  refine ⟨16009046985184127964617293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21345395980245503952823057 16009046985184127964617293)
                  ·
                    refine ⟨6003392619444047986731485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16009046985184127964617293 6003392619444047986731485)
                    ·
                      refine ⟨2251272232291517995024307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6003392619444047986731485 2251272232291517995024307)
                      ·
                        rfl

theorem cell23_4384337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 2, 2, 2, 3, 3].length) (baseStart_4384337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384337 prefixEnd_4384337 := by exact prefixLift 4384337
  have htrace : WordTrace (prefixWord ++ tailWord_4384337) baseStart_4384337 baseEnd_4384337 := by
    simpa [prefixWord, tailWord_4384337, baseEnd_4384337] using wordTrace_append hprefix tailTrace_4384337
  have hstable : (prefixWord ++ tailWord_4384337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384337).length < 2 ^ (prefixWord ++ tailWord_4384337).sum := by decide
  have hdescent : baseEnd_4384337 < baseStart_4384337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384338 : List Nat := [3, 2, 2, 1, 2, 3, 2, 2, 2, 2, 2]
def baseStart_4384338 : Nat := 118140960795 + 4384338 * 2 ^ 59
def prefixEnd_4384338 : Nat := 4983230072969 + 3 ^ 40 * 4384338 * 2
def baseEnd_4384338 : Nat := 2251272745772172491111803

theorem tailTrace_4384338 : CollatzResearch.WordTrace tailWord_4384338 prefixEnd_4384338 2251272745772172491111803 := by
  unfold tailWord_4384338
  simp only [CollatzResearch.WordTrace]
  refine ⟨39977485997574921540416417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106606629326866457441110445 39977485997574921540416417)
  ·
    refine ⟨29983114498181191155312313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39977485997574921540416417 29983114498181191155312313)
    ·
      refine ⟨22487335873635893366484235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29983114498181191155312313 22487335873635893366484235)
      ·
        refine ⟨33731003810453840049726353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22487335873635893366484235 33731003810453840049726353)
        ·
          refine ⟨25298252857840380037294765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33731003810453840049726353 25298252857840380037294765)
          ·
            refine ⟨9486844821690142513985537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25298252857840380037294765 9486844821690142513985537)
            ·
              refine ⟨7115133616267606885489153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9486844821690142513985537 7115133616267606885489153)
              ·
                refine ⟨5336350212200705164116865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7115133616267606885489153 5336350212200705164116865)
                ·
                  refine ⟨4002262659150528873087649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5336350212200705164116865 4002262659150528873087649)
                  ·
                    refine ⟨3001696994362896654815737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4002262659150528873087649 3001696994362896654815737)
                    ·
                      refine ⟨2251272745772172491111803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3001696994362896654815737 2251272745772172491111803)
                      ·
                        rfl

theorem cell23_4384338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 2, 2, 2, 2, 2].length) (baseStart_4384338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384338 prefixEnd_4384338 := by exact prefixLift 4384338
  have htrace : WordTrace (prefixWord ++ tailWord_4384338) baseStart_4384338 baseEnd_4384338 := by
    simpa [prefixWord, tailWord_4384338, baseEnd_4384338] using wordTrace_append hprefix tailTrace_4384338
  have hstable : (prefixWord ++ tailWord_4384338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384338).length < 2 ^ (prefixWord ++ tailWord_4384338).sum := by decide
  have hdescent : baseEnd_4384338 < baseStart_4384338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384374 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 1, 7]
def baseStart_4384374 : Nat := 118140960795 + 4384374 * 2 ^ 59
def prefixEnd_4384374 : Nat := 4983230072969 + 3 ^ 40 * 4384374 * 2
def baseEnd_4384374 : Nat := 750430410358578116753879

theorem tailTrace_4384374 : CollatzResearch.WordTrace tailWord_4384374 prefixEnd_4384374 750430410358578116753879 := by
  unfold tailWord_4384374
  simp only [CollatzResearch.WordTrace]
  refine ⟨9994453563635579019373511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106607504678779509539984117 9994453563635579019373511)
  ·
    refine ⟨14991680345453368529060267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9994453563635579019373511 14991680345453368529060267)
    ·
      refine ⟨22487520518180052793590401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14991680345453368529060267 22487520518180052793590401)
      ·
        refine ⟨16865640388635039595192801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22487520518180052793590401 16865640388635039595192801)
        ·
          refine ⟨12649230291476279696394601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16865640388635039595192801 12649230291476279696394601)
          ·
            refine ⟨9486922718607209772295951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12649230291476279696394601 9486922718607209772295951)
            ·
              refine ⟨14230384077910814658443927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9486922718607209772295951 14230384077910814658443927)
              ·
                refine ⟨21345576116866221987665891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14230384077910814658443927 21345576116866221987665891)
                ·
                  refine ⟨32018364175299332981498837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21345576116866221987665891 32018364175299332981498837)
                  ·
                    refine ⟨750430410358578116753879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32018364175299332981498837 750430410358578116753879)
                    ·
                      rfl

theorem cell23_4384374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 1, 7].length) (baseStart_4384374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384374 prefixEnd_4384374 := by exact prefixLift 4384374
  have htrace : WordTrace (prefixWord ++ tailWord_4384374) baseStart_4384374 baseEnd_4384374 := by
    simpa [prefixWord, tailWord_4384374, baseEnd_4384374] using wordTrace_append hprefix tailTrace_4384374
  have hstable : (prefixWord ++ tailWord_4384374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384374).length < 2 ^ (prefixWord ++ tailWord_4384374).sum := by decide
  have hdescent : baseEnd_4384374 < baseStart_4384374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384377 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 1, 3, 4]
def baseStart_4384377 : Nat := 118140960795 + 4384377 * 2 ^ 59
def prefixEnd_4384377 : Nat := 4983230072969 + 3 ^ 40 * 4384377 * 2
def baseEnd_4384377 : Nat := 2251292771517697838524123

theorem tailTrace_4384377 : CollatzResearch.WordTrace tailWord_4384377 prefixEnd_4384377 2251292771517697838524123 := by
  unfold tailWord_4384377
  simp only [CollatzResearch.WordTrace]
  refine ⟨159911366437158395822335385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106607577624772263881556923 159911366437158395822335385)
  ·
    refine ⟨119933524827868796866751539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159911366437158395822335385 119933524827868796866751539)
    ·
      refine ⟨179900287241803195300127309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119933524827868796866751539 179900287241803195300127309)
      ·
        refine ⟨67462607715676198237547741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179900287241803195300127309 67462607715676198237547741)
        ·
          refine ⟨25298477893378574339080403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67462607715676198237547741 25298477893378574339080403)
          ·
            refine ⟨37947716840067861508620605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25298477893378574339080403 37947716840067861508620605)
            ·
              refine ⟨14230393815025448065732727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37947716840067861508620605 14230393815025448065732727)
              ·
                refine ⟨21345590722538172098599091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14230393815025448065732727 21345590722538172098599091)
                ·
                  refine ⟨32018386083807258147898637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21345590722538172098599091 32018386083807258147898637)
                  ·
                    refine ⟨12006894781427721805461989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32018386083807258147898637 12006894781427721805461989)
                    ·
                      refine ⟨2251292771517697838524123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12006894781427721805461989 2251292771517697838524123)
                      ·
                        rfl

theorem cell23_4384377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_4384377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384377 prefixEnd_4384377 := by exact prefixLift 4384377
  have htrace : WordTrace (prefixWord ++ tailWord_4384377) baseStart_4384377 baseEnd_4384377 := by
    simpa [prefixWord, tailWord_4384377, baseEnd_4384377] using wordTrace_append hprefix tailTrace_4384377
  have hstable : (prefixWord ++ tailWord_4384377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384377).length < 2 ^ (prefixWord ++ tailWord_4384377).sum := by decide
  have hdescent : baseEnd_4384377 < baseStart_4384377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384387 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 7, 4]
def baseStart_4384387 : Nat := 118140960795 + 4384387 * 2 ^ 59
def prefixEnd_4384387 : Nat := 4983230072969 + 3 ^ 40 * 4384387 * 2
def baseEnd_4384387 : Nat := 750432635441414266466359

theorem tailTrace_4384387 : CollatzResearch.WordTrace tailWord_4384387 prefixEnd_4384387 750432635441414266466359 := by
  unfold tailWord_4384387
  simp only [CollatzResearch.WordTrace]
  refine ⟨159911731167122167530199415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106607820778081445020132943 159911731167122167530199415)
  ·
    refine ⟨239867596750683251295299123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159911731167122167530199415 239867596750683251295299123)
    ·
      refine ⟨359801395126024876942948685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239867596750683251295299123 359801395126024876942948685)
      ·
        refine ⟨134925523172259328853605757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 359801395126024876942948685 134925523172259328853605757)
        ·
          refine ⟨50597071189597248320102159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134925523172259328853605757 50597071189597248320102159)
          ·
            refine ⟨75895606784395872480153239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50597071189597248320102159 75895606784395872480153239)
            ·
              refine ⟨113843410176593808720229859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75895606784395872480153239 113843410176593808720229859)
              ·
                refine ⟨170765115264890713080344789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113843410176593808720229859 170765115264890713080344789)
                ·
                  refine ⟨4002307389020876087820581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 170765115264890713080344789 4002307389020876087820581)
                  ·
                    refine ⟨750432635441414266466359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4002307389020876087820581 750432635441414266466359)
                    ·
                      rfl

theorem cell23_4384387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 4].length) (baseStart_4384387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384387 prefixEnd_4384387 := by exact prefixLift 4384387
  have htrace : WordTrace (prefixWord ++ tailWord_4384387) baseStart_4384387 baseEnd_4384387 := by
    simpa [prefixWord, tailWord_4384387, baseEnd_4384387] using wordTrace_append hprefix tailTrace_4384387
  have hstable : (prefixWord ++ tailWord_4384387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384387).length < 2 ^ (prefixWord ++ tailWord_4384387).sum := by decide
  have hdescent : baseEnd_4384387 < baseStart_4384387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384468 : List Nat := [2, 4, 1, 3, 1, 3, 2, 1, 6]
def baseStart_4384468 : Nat := 118140960795 + 4384468 * 2 ^ 59
def prefixEnd_4384468 : Nat := 4983230072969 + 3 ^ 40 * 4384468 * 2
def baseEnd_4384468 : Nat := 250148833139695220276245

theorem tailTrace_4384468 : CollatzResearch.WordTrace tailWord_4384468 prefixEnd_4384468 250148833139695220276245 := by
  unfold tailWord_4384468
  simp only [CollatzResearch.WordTrace]
  refine ⟨79957342739914359181949029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106609790319885812242598705 79957342739914359181949029)
  ·
    refine ⟨14992001763733942346615443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 79957342739914359181949029 14992001763733942346615443)
    ·
      refine ⟨22488002645600913519923165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14992001763733942346615443 22488002645600913519923165)
      ·
        refine ⟨8433000992100342569971187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22488002645600913519923165 8433000992100342569971187)
        ·
          refine ⟨12649501488150513854956781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8433000992100342569971187 12649501488150513854956781)
          ·
            refine ⟨4743563058056442695608793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12649501488150513854956781 4743563058056442695608793)
            ·
              refine ⟨3557672293542332021706595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4743563058056442695608793 3557672293542332021706595)
              ·
                refine ⟨5336508440313498032559893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3557672293542332021706595 5336508440313498032559893)
                ·
                  refine ⟨250148833139695220276245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5336508440313498032559893 250148833139695220276245)
                  ·
                    rfl

theorem cell23_4384468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 6].length) (baseStart_4384468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384468 prefixEnd_4384468 := by exact prefixLift 4384468
  have htrace : WordTrace (prefixWord ++ tailWord_4384468) baseStart_4384468 baseEnd_4384468 := by
    simpa [prefixWord, tailWord_4384468, baseEnd_4384468] using wordTrace_append hprefix tailTrace_4384468
  have hstable : (prefixWord ++ tailWord_4384468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384468).length < 2 ^ (prefixWord ++ tailWord_4384468).sum := by decide
  have hdescent : baseEnd_4384468 < baseStart_4384468 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384484 : List Nat := [2, 3, 1, 1, 1, 3, 3, 1, 3, 1, 4]
def baseStart_4384484 : Nat := 118140960795 + 4384484 * 2 ^ 59
def prefixEnd_4384484 : Nat := 4983230072969 + 3 ^ 40 * 4384484 * 2
def baseEnd_4384484 : Nat := 2251347713947728919886131

theorem tailTrace_4384484 : CollatzResearch.WordTrace tailWord_4384484 prefixEnd_4384484 2251347713947728919886131 := by
  unfold tailWord_4384484
  simp only [CollatzResearch.WordTrace]
  refine ⟨79957634523885376548240253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106610179365180502064320337 79957634523885376548240253)
  ·
    refine ⟨29984112946457016205590095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79957634523885376548240253 29984112946457016205590095)
    ·
      refine ⟨44976169419685524308385143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29984112946457016205590095 44976169419685524308385143)
      ·
        refine ⟨67464254129528286462577715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44976169419685524308385143 67464254129528286462577715)
        ·
          refine ⟨101196381194292429693866573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67464254129528286462577715 101196381194292429693866573)
          ·
            refine ⟨37948642947859661135199965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101196381194292429693866573 37948642947859661135199965)
            ·
              refine ⟨14230741105447372925699987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37948642947859661135199965 14230741105447372925699987)
              ·
                refine ⟨21346111658171059388549981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14230741105447372925699987 21346111658171059388549981)
                ·
                  refine ⟨8004791871814147270706243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21346111658171059388549981 8004791871814147270706243)
                  ·
                    refine ⟨12007187807721220906059365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8004791871814147270706243 12007187807721220906059365)
                    ·
                      refine ⟨2251347713947728919886131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12007187807721220906059365 2251347713947728919886131)
                      ·
                        rfl

theorem cell23_4384484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_4384484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384484 prefixEnd_4384484 := by exact prefixLift 4384484
  have htrace : WordTrace (prefixWord ++ tailWord_4384484) baseStart_4384484 baseEnd_4384484 := by
    simpa [prefixWord, tailWord_4384484, baseEnd_4384484] using wordTrace_append hprefix tailTrace_4384484
  have hstable : (prefixWord ++ tailWord_4384484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384484).length < 2 ^ (prefixWord ++ tailWord_4384484).sum := by decide
  have hdescent : baseEnd_4384484 < baseStart_4384484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384488 : List Nat := [2, 1, 4, 1, 3, 2, 2, 1, 2, 3, 2]
def baseStart_4384488 : Nat := 118140960795 + 4384488 * 2 ^ 59
def prefixEnd_4384488 : Nat := 4983230072969 + 3 ^ 40 * 4384488 * 2
def baseEnd_4384488 : Nat := 2251349767870346904236113

theorem tailTrace_4384488 : CollatzResearch.WordTrace tailWord_4384488 prefixEnd_4384488 2251349767870346904236113 := by
  unfold tailWord_4384488
  simp only [CollatzResearch.WordTrace]
  refine ⟨79957707469878130889813059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106610276626504174519750745 79957707469878130889813059)
  ·
    refine ⟨119936561204817196334719589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79957707469878130889813059 119936561204817196334719589)
    ·
      refine ⟨22488105225903224312759923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119936561204817196334719589 22488105225903224312759923)
      ·
        refine ⟨33732157838854836469139885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22488105225903224312759923 33732157838854836469139885)
        ·
          refine ⟨12649559189570563675927457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33732157838854836469139885 12649559189570563675927457)
          ·
            refine ⟨9487169392177922756945593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12649559189570563675927457 9487169392177922756945593)
            ·
              refine ⟨7115377044133442067709195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9487169392177922756945593 7115377044133442067709195)
              ·
                refine ⟨10673065566200163101563793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7115377044133442067709195 10673065566200163101563793)
                ·
                  refine ⟨8004799174650122326172845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10673065566200163101563793 8004799174650122326172845)
                  ·
                    refine ⟨3001799690493795872314817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8004799174650122326172845 3001799690493795872314817)
                    ·
                      refine ⟨2251349767870346904236113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3001799690493795872314817 2251349767870346904236113)
                      ·
                        rfl

theorem cell23_4384488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_4384488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384488 prefixEnd_4384488 := by exact prefixLift 4384488
  have htrace : WordTrace (prefixWord ++ tailWord_4384488) baseStart_4384488 baseEnd_4384488 := by
    simpa [prefixWord, tailWord_4384488, baseEnd_4384488] using wordTrace_append hprefix tailTrace_4384488
  have hstable : (prefixWord ++ tailWord_4384488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384488).length < 2 ^ (prefixWord ++ tailWord_4384488).sum := by decide
  have hdescent : baseEnd_4384488 < baseStart_4384488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384494 : List Nat := [4, 1, 2, 1, 1, 2, 3, 2, 1, 6]
def baseStart_4384494 : Nat := 118140960795 + 4384494 * 2 ^ 59
def prefixEnd_4384494 : Nat := 4983230072969 + 3 ^ 40 * 4384494 * 2
def baseEnd_4384494 : Nat := 750450949584757960253695

theorem tailTrace_4384494 : CollatzResearch.WordTrace tailWord_4384494 prefixEnd_4384494 750450949584757960253695 := by
  unfold tailWord_4384494
  simp only [CollatzResearch.WordTrace]
  refine ⟨19989454222216815600543067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106610422518489683202896357 19989454222216815600543067)
  ·
    refine ⟨29984181333325223400814601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19989454222216815600543067 29984181333325223400814601)
    ·
      refine ⟨22488135999993917550610951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29984181333325223400814601 22488135999993917550610951)
      ·
        refine ⟨33732203999990876325916427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22488135999993917550610951 33732203999990876325916427)
        ·
          refine ⟨50598305999986314488874641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33732203999990876325916427 50598305999986314488874641)
          ·
            refine ⟨37948729499989735866655981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50598305999986314488874641 37948729499989735866655981)
            ·
              refine ⟨14230773562496150949995993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37948729499989735866655981 14230773562496150949995993)
              ·
                refine ⟨10673080171872113212496995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14230773562496150949995993 10673080171872113212496995)
                ·
                  refine ⟨16009620257808169818745493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10673080171872113212496995 16009620257808169818745493)
                  ·
                    refine ⟨750450949584757960253695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16009620257808169818745493 750450949584757960253695)
                    ·
                      rfl

theorem cell23_4384494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_4384494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384494 prefixEnd_4384494 := by exact prefixLift 4384494
  have htrace : WordTrace (prefixWord ++ tailWord_4384494) baseStart_4384494 baseEnd_4384494 := by
    simpa [prefixWord, tailWord_4384494, baseEnd_4384494] using wordTrace_append hprefix tailTrace_4384494
  have hstable : (prefixWord ++ tailWord_4384494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384494).length < 2 ^ (prefixWord ++ tailWord_4384494).sum := by decide
  have hdescent : baseEnd_4384494 < baseStart_4384494 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384552 : List Nat := [2, 1, 5, 1, 1, 3, 2, 3, 1, 2, 2]
def baseStart_4384552 : Nat := 118140960795 + 4384552 * 2 ^ 59
def prefixEnd_4384552 : Nat := 4983230072969 + 3 ^ 40 * 4384552 * 2
def baseEnd_4384552 : Nat := 2251382630632234653835819

theorem tailTrace_4384552 : CollatzResearch.WordTrace tailWord_4384552 prefixEnd_4384552 2251382630632234653835819 := by
  unfold tailWord_4384552
  simp only [CollatzResearch.WordTrace]
  refine ⟨79958874605762200354977955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106611832807682933806637273 79958874605762200354977955)
  ·
    refine ⟨119938311908643300532466933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79958874605762200354977955 119938311908643300532466933)
    ·
      refine ⟨11244216741435309424918775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119938311908643300532466933 11244216741435309424918775)
      ·
        refine ⟨16866325112152964137378163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11244216741435309424918775 16866325112152964137378163)
        ·
          refine ⟨25299487668229446206067245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16866325112152964137378163 25299487668229446206067245)
          ·
            refine ⟨9487307875586042327275217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25299487668229446206067245 9487307875586042327275217)
            ·
              refine ⟨7115480906689531745456413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9487307875586042327275217 7115480906689531745456413)
              ·
                refine ⟨2668305340008574404546155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7115480906689531745456413 2668305340008574404546155)
                ·
                  refine ⟨4002458010012861606819233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2668305340008574404546155 4002458010012861606819233)
                  ·
                    refine ⟨3001843507509646205114425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4002458010012861606819233 3001843507509646205114425)
                    ·
                      refine ⟨2251382630632234653835819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3001843507509646205114425 2251382630632234653835819)
                      ·
                        rfl

theorem cell23_4384552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_4384552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384552 prefixEnd_4384552 := by exact prefixLift 4384552
  have htrace : WordTrace (prefixWord ++ tailWord_4384552) baseStart_4384552 baseEnd_4384552 := by
    simpa [prefixWord, tailWord_4384552, baseEnd_4384552] using wordTrace_append hprefix tailTrace_4384552
  have hstable : (prefixWord ++ tailWord_4384552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384552).length < 2 ^ (prefixWord ++ tailWord_4384552).sum := by decide
  have hdescent : baseEnd_4384552 < baseStart_4384552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384568 : List Nat := [2, 1, 2, 1, 3, 3, 3, 2, 2, 1, 3]
def baseStart_4384568 : Nat := 118140960795 + 4384568 * 2 ^ 59
def prefixEnd_4384568 : Nat := 4983230072969 + 3 ^ 40 * 4384568 * 2
def baseEnd_4384568 : Nat := 2251390846322706591235745

theorem tailTrace_4384568 : CollatzResearch.WordTrace tailWord_4384568 prefixEnd_4384568 2251390846322706591235745 := by
  unfold tailWord_4384568
  simp only [CollatzResearch.WordTrace]
  refine ⟨79959166389733217721269179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106612221852977623628358905 79959166389733217721269179)
  ·
    refine ⟨119938749584599826581903769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79959166389733217721269179 119938749584599826581903769)
    ·
      refine ⟨89954062188449869936427827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119938749584599826581903769 89954062188449869936427827)
      ·
        refine ⟨134931093282674804904641741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89954062188449869936427827 134931093282674804904641741)
        ·
          refine ⟨50599159981003051839240653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134931093282674804904641741 50599159981003051839240653)
          ·
            refine ⟨18974684992876144439715245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50599159981003051839240653 18974684992876144439715245)
            ·
              refine ⟨7115506872328554164893217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18974684992876144439715245 7115506872328554164893217)
              ·
                refine ⟨5336630154246415623669913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7115506872328554164893217 5336630154246415623669913)
                ·
                  refine ⟨4002472615684811717752435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5336630154246415623669913 4002472615684811717752435)
                  ·
                    refine ⟨6003708923527217576628653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4002472615684811717752435 6003708923527217576628653)
                    ·
                      refine ⟨2251390846322706591235745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6003708923527217576628653 2251390846322706591235745)
                      ·
                        rfl

theorem cell23_4384568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 3, 2, 2, 1, 3].length) (baseStart_4384568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384568 prefixEnd_4384568 := by exact prefixLift 4384568
  have htrace : WordTrace (prefixWord ++ tailWord_4384568) baseStart_4384568 baseEnd_4384568 := by
    simpa [prefixWord, tailWord_4384568, baseEnd_4384568] using wordTrace_append hprefix tailTrace_4384568
  have hstable : (prefixWord ++ tailWord_4384568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384568).length < 2 ^ (prefixWord ++ tailWord_4384568).sum := by decide
  have hdescent : baseEnd_4384568 < baseStart_4384568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384584 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 2, 6]
def baseStart_4384584 : Nat := 118140960795 + 4384584 * 2 ^ 59
def prefixEnd_4384584 : Nat := 4983230072969 + 3 ^ 40 * 4384584 * 2
def baseEnd_4384584 : Nat := 750466354004392842878557

theorem tailTrace_4384584 : CollatzResearch.WordTrace tailWord_4384584 prefixEnd_4384584 750466354004392842878557 := by
  unfold tailWord_4384584
  simp only [CollatzResearch.WordTrace]
  refine ⟨79959458173704235087560403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106612610898272313450080537 79959458173704235087560403)
  ·
    refine ⟨119939187260556352631340605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79959458173704235087560403 119939187260556352631340605)
    ·
      refine ⟨44977195222708632236752727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119939187260556352631340605 44977195222708632236752727)
      ·
        refine ⟨67465792834062948355129091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44977195222708632236752727 67465792834062948355129091)
        ·
          refine ⟨101198689251094422532693637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67465792834062948355129091 101198689251094422532693637)
          ·
            refine ⟨18974754234580204224880057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101198689251094422532693637 18974754234580204224880057)
            ·
              refine ⟨14231065675935153168660043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18974754234580204224880057 14231065675935153168660043)
              ·
                refine ⟨21346598513902729752990065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14231065675935153168660043 21346598513902729752990065)
                ·
                  refine ⟨16009948885427047314742549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21346598513902729752990065 16009948885427047314742549)
                  ·
                    refine ⟨750466354004392842878557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16009948885427047314742549 750466354004392842878557)
                    ·
                      rfl

theorem cell23_4384584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_4384584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384584 prefixEnd_4384584 := by exact prefixLift 4384584
  have htrace : WordTrace (prefixWord ++ tailWord_4384584) baseStart_4384584 baseEnd_4384584 := by
    simpa [prefixWord, tailWord_4384584, baseEnd_4384584] using wordTrace_append hprefix tailTrace_4384584
  have hstable : (prefixWord ++ tailWord_4384584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384584).length < 2 ^ (prefixWord ++ tailWord_4384584).sum := by decide
  have hdescent : baseEnd_4384584 < baseStart_4384584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384587 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 10]
def baseStart_4384587 : Nat := 118140960795 + 4384587 * 2 ^ 59
def prefixEnd_4384587 : Nat := 4983230072969 + 3 ^ 40 * 4384587 * 2
def baseEnd_4384587 : Nat := 2251400602455142016898157

theorem tailTrace_4384587 : CollatzResearch.WordTrace tailWord_4384587 prefixEnd_4384587 2251400602455142016898157 := by
  unfold tailWord_4384587
  simp only [CollatzResearch.WordTrace]
  refine ⟨159919025766397601687480015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106612683844265067791653343 159919025766397601687480015)
  ·
    refine ⟨239878538649596402531220023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159919025766397601687480015 239878538649596402531220023)
    ·
      refine ⟨359817807974394603796830035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239878538649596402531220023 359817807974394603796830035)
      ·
        refine ⟨539726711961591905695245053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359817807974394603796830035 539726711961591905695245053)
        ·
          refine ⟨202397516985596964635716895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 539726711961591905695245053 202397516985596964635716895)
          ·
            refine ⟨303596275478395446953575343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202397516985596964635716895 303596275478395446953575343)
            ·
              refine ⟨455394413217593170430363015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303596275478395446953575343 455394413217593170430363015)
              ·
                refine ⟨683091619826389755645544523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455394413217593170430363015 683091619826389755645544523)
                ·
                  refine ⟨1024637429739584633468316785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 683091619826389755645544523 1024637429739584633468316785)
                  ·
                    refine ⟨768478072304688475101237589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1024637429739584633468316785 768478072304688475101237589)
                    ·
                      refine ⟨2251400602455142016898157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 768478072304688475101237589 2251400602455142016898157)
                      ·
                        rfl

theorem cell23_4384587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 10].length) (baseStart_4384587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384587 prefixEnd_4384587 := by exact prefixLift 4384587
  have htrace : WordTrace (prefixWord ++ tailWord_4384587) baseStart_4384587 baseEnd_4384587 := by
    simpa [prefixWord, tailWord_4384587, baseEnd_4384587] using wordTrace_append hprefix tailTrace_4384587
  have hstable : (prefixWord ++ tailWord_4384587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384587).length < 2 ^ (prefixWord ++ tailWord_4384587).sum := by decide
  have hdescent : baseEnd_4384587 < baseStart_4384587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384608 : List Nat := [2, 1, 1, 3, 3, 2, 1, 2, 4, 2, 2]
def baseStart_4384608 : Nat := 118140960795 + 4384608 * 2 ^ 59
def prefixEnd_4384608 : Nat := 4983230072969 + 3 ^ 40 * 4384608 * 2
def baseEnd_4384608 : Nat := 2251411385548886434735561

theorem tailTrace_4384608 : CollatzResearch.WordTrace tailWord_4384608 prefixEnd_4384608 2251411385548886434735561 := by
  unfold tailWord_4384608
  simp only [CollatzResearch.WordTrace]
  refine ⟨79959895849660761136997239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106613194466214348182662985 79959895849660761136997239)
  ·
    refine ⟨119939843774491141705495859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79959895849660761136997239 119939843774491141705495859)
    ·
      refine ⟨179909765661736712558243789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119939843774491141705495859 179909765661736712558243789)
      ·
        refine ⟨67466162123151267209341421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179909765661736712558243789 67466162123151267209341421)
        ·
          refine ⟨25299810796181725203503033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67466162123151267209341421 25299810796181725203503033)
          ·
            refine ⟨18974858097136293902627275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25299810796181725203503033 18974858097136293902627275)
            ·
              refine ⟨28462287145704440853940913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18974858097136293902627275 28462287145704440853940913)
              ·
                refine ⟨21346715359278330640455685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28462287145704440853940913 21346715359278330640455685)
                ·
                  refine ⟨4002509129864686995085441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21346715359278330640455685 4002509129864686995085441)
                  ·
                    refine ⟨3001881847398515246314081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4002509129864686995085441 3001881847398515246314081)
                    ·
                      refine ⟨2251411385548886434735561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3001881847398515246314081 2251411385548886434735561)
                      ·
                        rfl

theorem cell23_4384608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 1, 2, 4, 2, 2].length) (baseStart_4384608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384608 prefixEnd_4384608 := by exact prefixLift 4384608
  have htrace : WordTrace (prefixWord ++ tailWord_4384608) baseStart_4384608 baseEnd_4384608 := by
    simpa [prefixWord, tailWord_4384608, baseEnd_4384608] using wordTrace_append hprefix tailTrace_4384608
  have hstable : (prefixWord ++ tailWord_4384608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384608).length < 2 ^ (prefixWord ++ tailWord_4384608).sum := by decide
  have hdescent : baseEnd_4384608 < baseStart_4384608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384611 : List Nat := [1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 5]
def baseStart_4384611 : Nat := 118140960795 + 4384611 * 2 ^ 59
def prefixEnd_4384611 : Nat := 4983230072969 + 3 ^ 40 * 4384611 * 2
def baseEnd_4384611 : Nat := 2251412925990849922998047

theorem tailTrace_4384611 : CollatzResearch.WordTrace tailWord_4384611 prefixEnd_4384611 2251412925990849922998047 := by
  unfold tailWord_4384611
  simp only [CollatzResearch.WordTrace]
  refine ⟨159919901118310653786353687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106613267412207102524235791 159919901118310653786353687)
  ·
    refine ⟨239879851677465980679530531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159919901118310653786353687 239879851677465980679530531)
    ·
      refine ⟨359819777516198971019295797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239879851677465980679530531 359819777516198971019295797)
      ·
        refine ⟨33733104142143653533058981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 359819777516198971019295797 33733104142143653533058981)
        ·
          refine ⟨6324957026651935037448559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33733104142143653533058981 6324957026651935037448559)
          ·
            refine ⟨9487435539977902556172839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6324957026651935037448559 9487435539977902556172839)
            ·
              refine ⟨14231153309966853834259259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9487435539977902556172839 14231153309966853834259259)
              ·
                refine ⟨21346729964950280751388889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14231153309966853834259259 21346729964950280751388889)
                ·
                  refine ⟨16010047473712710563541667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21346729964950280751388889 16010047473712710563541667)
                  ·
                    refine ⟨24015071210569065845312501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16010047473712710563541667 24015071210569065845312501)
                    ·
                      refine ⟨2251412925990849922998047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24015071210569065845312501 2251412925990849922998047)
                      ·
                        rfl

theorem cell23_4384611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_4384611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384611 prefixEnd_4384611 := by exact prefixLift 4384611
  have htrace : WordTrace (prefixWord ++ tailWord_4384611) baseStart_4384611 baseEnd_4384611 := by
    simpa [prefixWord, tailWord_4384611, baseEnd_4384611] using wordTrace_append hprefix tailTrace_4384611
  have hstable : (prefixWord ++ tailWord_4384611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384611).length < 2 ^ (prefixWord ++ tailWord_4384611).sum := by decide
  have hdescent : baseEnd_4384611 < baseStart_4384611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384644 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 3, 7]
def baseStart_4384644 : Nat := 118140960795 + 4384644 * 2 ^ 59
def prefixEnd_4384644 : Nat := 4983230072969 + 3 ^ 40 * 4384644 * 2
def baseEnd_4384644 : Nat := 750476623617482764628465

theorem tailTrace_4384644 : CollatzResearch.WordTrace tailWord_4384644 prefixEnd_4384644 750476623617482764628465 := by
  unfold tailWord_4384644
  simp only [CollatzResearch.WordTrace]
  refine ⟨79960552363595550211152493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106614069818127400281536657 79960552363595550211152493)
  ·
    refine ⟨29985207136348331329182185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79960552363595550211152493 29985207136348331329182185)
    ·
      refine ⟨22488905352261248496886639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29985207136348331329182185 22488905352261248496886639)
      ·
        refine ⟨33733358028391872745329959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22488905352261248496886639 33733358028391872745329959)
        ·
          refine ⟨50600037042587809117994939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33733358028391872745329959 50600037042587809117994939)
          ·
            refine ⟨75900055563881713676992409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50600037042587809117994939 75900055563881713676992409)
            ·
              refine ⟨56925041672911285257744307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75900055563881713676992409 56925041672911285257744307)
              ·
                refine ⟨85387562509366927886616461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56925041672911285257744307 85387562509366927886616461)
                ·
                  refine ⟨32020335941012597957481173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85387562509366927886616461 32020335941012597957481173)
                  ·
                    refine ⟨750476623617482764628465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32020335941012597957481173 750476623617482764628465)
                    ·
                      rfl

theorem cell23_4384644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_4384644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384644 prefixEnd_4384644 := by exact prefixLift 4384644
  have htrace : WordTrace (prefixWord ++ tailWord_4384644) baseStart_4384644 baseEnd_4384644 := by
    simpa [prefixWord, tailWord_4384644, baseEnd_4384644] using wordTrace_append hprefix tailTrace_4384644
  have hstable : (prefixWord ++ tailWord_4384644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384644).length < 2 ^ (prefixWord ++ tailWord_4384644).sum := by decide
  have hdescent : baseEnd_4384644 < baseStart_4384644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384661 : List Nat := [1, 3, 2, 1, 1, 3, 4, 1, 2, 5]
def baseStart_4384661 : Nat := 118140960795 + 4384661 * 2 ^ 59
def prefixEnd_4384661 : Nat := 4983230072969 + 3 ^ 40 * 4384661 * 2
def baseEnd_4384661 : Nat := 750479533341191575790939

theorem tailTrace_4384661 : CollatzResearch.WordTrace tailWord_4384661 prefixEnd_4384661 750479533341191575790939 := by
  unfold tailWord_4384661
  simp only [CollatzResearch.WordTrace]
  refine ⟨159921724768129512325673837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106614483178753008217115891 159921724768129512325673837)
  ·
    refine ⟨59970646788048567122127689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159921724768129512325673837 59970646788048567122127689)
    ·
      refine ⟨44977985091036425341595767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59970646788048567122127689 44977985091036425341595767)
      ·
        refine ⟨67466977636554638012393651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44977985091036425341595767 67466977636554638012393651)
        ·
          refine ⟨101200466454831957018590477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67466977636554638012393651 101200466454831957018590477)
          ·
            refine ⟨37950174920561983881971429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101200466454831957018590477 37950174920561983881971429)
            ·
              refine ⟨7115657797605371977869643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37950174920561983881971429 7115657797605371977869643)
              ·
                refine ⟨10673486696408057966804465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7115657797605371977869643 10673486696408057966804465)
                ·
                  refine ⟨8005115022306043475103349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10673486696408057966804465 8005115022306043475103349)
                  ·
                    refine ⟨750479533341191575790939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8005115022306043475103349 750479533341191575790939)
                    ·
                      rfl

theorem cell23_4384661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_4384661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384661 prefixEnd_4384661 := by exact prefixLift 4384661
  have htrace : WordTrace (prefixWord ++ tailWord_4384661) baseStart_4384661 baseEnd_4384661 := by
    simpa [prefixWord, tailWord_4384661, baseEnd_4384661] using wordTrace_append hprefix tailTrace_4384661
  have hstable : (prefixWord ++ tailWord_4384661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384661).length < 2 ^ (prefixWord ++ tailWord_4384661).sum := by decide
  have hdescent : baseEnd_4384661 < baseStart_4384661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384691 : List Nat := [1, 1, 1, 2, 3, 1, 4, 3, 3, 4]
def baseStart_4384691 : Nat := 118140960795 + 4384691 * 2 ^ 59
def prefixEnd_4384691 : Nat := 4983230072969 + 3 ^ 40 * 4384691 * 2
def baseEnd_4384691 : Nat := 750484668147736536665893

theorem tailTrace_4384691 : CollatzResearch.WordTrace tailWord_4384691 prefixEnd_4384691 750484668147736536665893 := by
  unfold tailWord_4384691
  simp only [CollatzResearch.WordTrace]
  refine ⟨159922818958020827449265927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106615212638680551632843951 159922818958020827449265927)
  ·
    refine ⟨239884228437031241173898891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159922818958020827449265927 239884228437031241173898891)
    ·
      refine ⟨359826342655546861760848337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239884228437031241173898891 359826342655546861760848337)
      ·
        refine ⟨269869756991660146320636253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 359826342655546861760848337 269869756991660146320636253)
        ·
          refine ⟨101201158871872554870238595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 269869756991660146320636253 101201158871872554870238595)
          ·
            refine ⟨151801738307808832305357893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101201158871872554870238595 151801738307808832305357893)
            ·
              refine ⟨28462825932714156057254605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 151801738307808832305357893 28462825932714156057254605)
              ·
                refine ⟨10673559724767808521470477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28462825932714156057254605 10673559724767808521470477)
                ·
                  refine ⟨4002584896787928195551429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10673559724767808521470477 4002584896787928195551429)
                  ·
                    refine ⟨750484668147736536665893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4002584896787928195551429 750484668147736536665893)
                    ·
                      rfl

theorem cell23_4384691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 4].length) (baseStart_4384691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384691 prefixEnd_4384691 := by exact prefixLift 4384691
  have htrace : WordTrace (prefixWord ++ tailWord_4384691) baseStart_4384691 baseEnd_4384691 := by
    simpa [prefixWord, tailWord_4384691, baseEnd_4384691] using wordTrace_append hprefix tailTrace_4384691
  have hstable : (prefixWord ++ tailWord_4384691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384691).length < 2 ^ (prefixWord ++ tailWord_4384691).sum := by decide
  have hdescent : baseEnd_4384691 < baseStart_4384691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384725 : List Nat := [1, 3, 2, 3, 2, 1, 1, 5, 1, 4]
def baseStart_4384725 : Nat := 118140960795 + 4384725 * 2 ^ 59
def prefixEnd_4384725 : Nat := 4983230072969 + 3 ^ 40 * 4384725 * 2
def baseEnd_4384725 : Nat := 750490487595154158990841

theorem tailTrace_4384725 : CollatzResearch.WordTrace tailWord_4384725 prefixEnd_4384725 750490487595154158990841 := by
  unfold tailWord_4384725
  simp only [CollatzResearch.WordTrace]
  refine ⟨159924059039897651256003629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106616039359931767504002419 159924059039897651256003629)
  ·
    refine ⟨59971522139961619221001361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159924059039897651256003629 59971522139961619221001361)
    ·
      refine ⟨44978641604971214415751021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59971522139961619221001361 44978641604971214415751021)
      ·
        refine ⟨16866990601864205405906633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44978641604971214415751021 16866990601864205405906633)
        ·
          refine ⟨12650242951398154054429975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16866990601864205405906633 12650242951398154054429975)
          ·
            refine ⟨18975364427097231081644963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12650242951398154054429975 18975364427097231081644963)
            ·
              refine ⟨28463046640645846622467445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18975364427097231081644963 28463046640645846622467445)
              ·
                refine ⟨2668410622560548120856323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28463046640645846622467445 2668410622560548120856323)
                ·
                  refine ⟨4002615933840822181284485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2668410622560548120856323 4002615933840822181284485)
                  ·
                    refine ⟨750490487595154158990841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4002615933840822181284485 750490487595154158990841)
                    ·
                      rfl

theorem cell23_4384725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_4384725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384725 prefixEnd_4384725 := by exact prefixLift 4384725
  have htrace : WordTrace (prefixWord ++ tailWord_4384725) baseStart_4384725 baseEnd_4384725 := by
    simpa [prefixWord, tailWord_4384725, baseEnd_4384725] using wordTrace_append hprefix tailTrace_4384725
  have hstable : (prefixWord ++ tailWord_4384725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384725).length < 2 ^ (prefixWord ++ tailWord_4384725).sum := by decide
  have hdescent : baseEnd_4384725 < baseStart_4384725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384771 : List Nat := [1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 4]
def baseStart_4384771 : Nat := 118140960795 + 4384771 * 2 ^ 59
def prefixEnd_4384771 : Nat := 4983230072969 + 3 ^ 40 * 4384771 * 2
def baseEnd_4384771 : Nat := 2251495082895569296997311

theorem tailTrace_4384771 : CollatzResearch.WordTrace tailWord_4384771 prefixEnd_4384771 2251495082895569296997311 := by
  unfold tailWord_4384771
  simp only [CollatzResearch.WordTrace]
  refine ⟨159925736797731001112178167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106617157865154000741452111 159925736797731001112178167)
  ·
    refine ⟨239888605196596501668267251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159925736797731001112178167 239888605196596501668267251)
    ·
      refine ⟨359832907794894752502400877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239888605196596501668267251 359832907794894752502400877)
      ·
        refine ⟨134937340423085532188400329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 359832907794894752502400877 134937340423085532188400329)
        ·
          refine ⟨101203005317314149141300247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134937340423085532188400329 101203005317314149141300247)
          ·
            refine ⟨151804507975971223711950371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101203005317314149141300247 151804507975971223711950371)
            ·
              refine ⟨227706761963956835567925557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151804507975971223711950371 227706761963956835567925557)
              ·
                refine ⟨21347508934120953334493021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 227706761963956835567925557 21347508934120953334493021)
                ·
                  refine ⟨8005315850295357500434883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21347508934120953334493021 8005315850295357500434883)
                  ·
                    refine ⟨12007973775443036250652325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8005315850295357500434883 12007973775443036250652325)
                    ·
                      refine ⟨2251495082895569296997311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12007973775443036250652325 2251495082895569296997311)
                      ·
                        rfl

theorem cell23_4384771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_4384771 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384771 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384771 prefixEnd_4384771 := by exact prefixLift 4384771
  have htrace : WordTrace (prefixWord ++ tailWord_4384771) baseStart_4384771 baseEnd_4384771 := by
    simpa [prefixWord, tailWord_4384771, baseEnd_4384771] using wordTrace_append hprefix tailTrace_4384771
  have hstable : (prefixWord ++ tailWord_4384771).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384771).length < 2 ^ (prefixWord ++ tailWord_4384771).sum := by decide
  have hdescent : baseEnd_4384771 < baseStart_4384771 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384822 : List Nat := [5, 1, 2, 1, 1, 1, 2, 1, 5, 2, 2]
def baseStart_4384822 : Nat := 118140960795 + 4384822 * 2 ^ 59
def prefixEnd_4384822 : Nat := 4983230072969 + 3 ^ 40 * 4384822 * 2
def baseEnd_4384822 : Nat := 2251521270408948597459577

theorem tailTrace_4384822 : CollatzResearch.WordTrace tailWord_4384822 prefixEnd_4384822 2251521270408948597459577 := by
  unfold tailWord_4384822
  simp only [CollatzResearch.WordTrace]
  refine ⟨9995474807534139801392795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106618397947030824548189813 9995474807534139801392795)
  ·
    refine ⟨14993212211301209702089193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9995474807534139801392795 14993212211301209702089193)
    ·
      refine ⟨11244909158475907276566895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14993212211301209702089193 11244909158475907276566895)
      ·
        refine ⟨16867363737713860914850343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11244909158475907276566895 16867363737713860914850343)
        ·
          refine ⟨25301045606570791372275515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16867363737713860914850343 25301045606570791372275515)
          ·
            refine ⟨37951568409856187058413273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25301045606570791372275515 37951568409856187058413273)
            ·
              refine ⟨28463676307392140293809955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37951568409856187058413273 28463676307392140293809955)
              ·
                refine ⟨42695514461088210440714933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28463676307392140293809955 42695514461088210440714933)
                ·
                  refine ⟨4002704480727019728817025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42695514461088210440714933 4002704480727019728817025)
                  ·
                    refine ⟨3002028360545264796612769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4002704480727019728817025 3002028360545264796612769)
                    ·
                      refine ⟨2251521270408948597459577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3002028360545264796612769 2251521270408948597459577)
                      ·
                        rfl

theorem cell23_4384822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 1, 5, 2, 2].length) (baseStart_4384822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384822 prefixEnd_4384822 := by exact prefixLift 4384822
  have htrace : WordTrace (prefixWord ++ tailWord_4384822) baseStart_4384822 baseEnd_4384822 := by
    simpa [prefixWord, tailWord_4384822, baseEnd_4384822] using wordTrace_append hprefix tailTrace_4384822
  have hstable : (prefixWord ++ tailWord_4384822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384822).length < 2 ^ (prefixWord ++ tailWord_4384822).sum := by decide
  have hdescent : baseEnd_4384822 < baseStart_4384822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384825 : List Nat := [1, 2, 1, 5, 3, 1, 1, 1, 3, 2, 3]
def baseStart_4384825 : Nat := 118140960795 + 4384825 * 2 ^ 59
def prefixEnd_4384825 : Nat := 4983230072969 + 3 ^ 40 * 4384825 * 2
def baseEnd_4384825 : Nat := 2251522810850912085722063

theorem tailTrace_4384825 : CollatzResearch.WordTrace tailWord_4384825 prefixEnd_4384825 2251522810850912085722063 := by
  unfold tailWord_4384825
  simp only [CollatzResearch.WordTrace]
  refine ⟨159927706339535368334643929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106618470893023578889762619 159927706339535368334643929)
  ·
    refine ⟨119945779754651526250982947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159927706339535368334643929 119945779754651526250982947)
    ·
      refine ⟨179918669631977289376474421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119945779754651526250982947 179918669631977289376474421)
      ·
        refine ⟨16867375277997870879044477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 179918669631977289376474421 16867375277997870879044477)
        ·
          refine ⟨6325265729249201579641679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16867375277997870879044477 6325265729249201579641679)
          ·
            refine ⟨9487898593873802369462519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6325265729249201579641679 9487898593873802369462519)
            ·
              refine ⟨14231847890810703554193779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9487898593873802369462519 14231847890810703554193779)
              ·
                refine ⟨21347771836216055331290669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14231847890810703554193779 21347771836216055331290669)
                ·
                  refine ⟨8005414438581020749234001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21347771836216055331290669 8005414438581020749234001)
                  ·
                    refine ⟨6004060828935765561925501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8005414438581020749234001 6004060828935765561925501)
                    ·
                      refine ⟨2251522810850912085722063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6004060828935765561925501 2251522810850912085722063)
                      ·
                        rfl

theorem cell23_4384825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 1, 3, 2, 3].length) (baseStart_4384825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384825 prefixEnd_4384825 := by exact prefixLift 4384825
  have htrace : WordTrace (prefixWord ++ tailWord_4384825) baseStart_4384825 baseEnd_4384825 := by
    simpa [prefixWord, tailWord_4384825, baseEnd_4384825] using wordTrace_append hprefix tailTrace_4384825
  have hstable : (prefixWord ++ tailWord_4384825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384825).length < 2 ^ (prefixWord ++ tailWord_4384825).sum := by decide
  have hdescent : baseEnd_4384825 < baseStart_4384825 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384855 : List Nat := [1, 1, 3, 2, 2, 1, 3, 4, 2, 1, 3]
def baseStart_4384855 : Nat := 118140960795 + 4384855 * 2 ^ 59
def prefixEnd_4384855 : Nat := 4983230072969 + 3 ^ 40 * 4384855 * 2
def baseEnd_4384855 : Nat := 2251538215270546968346925

theorem tailTrace_4384855 : CollatzResearch.WordTrace tailWord_4384855 prefixEnd_4384855 2251538215270546968346925 := by
  unfold tailWord_4384855
  simp only [CollatzResearch.WordTrace]
  refine ⟨159928800529426683458236019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106619200352951122305490679 159928800529426683458236019)
  ·
    refine ⟨239893200794140025187354029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159928800529426683458236019 239893200794140025187354029)
    ·
      refine ⟨89959950297802509445257761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239893200794140025187354029 89959950297802509445257761)
      ·
        refine ⟨67469962723351882083943321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89959950297802509445257761 67469962723351882083943321)
        ·
          refine ⟨50602472042513911562957491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67469962723351882083943321 50602472042513911562957491)
          ·
            refine ⟨75903708063770867344436237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50602472042513911562957491 75903708063770867344436237)
            ·
              refine ⟨28463890523914075254163589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75903708063770867344436237 28463890523914075254163589)
              ·
                refine ⟨5336979473233889110155673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28463890523914075254163589 5336979473233889110155673)
                ·
                  refine ⟨4002734604925416832616755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5336979473233889110155673 4002734604925416832616755)
                  ·
                    refine ⟨6004101907388125248925133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4002734604925416832616755 6004101907388125248925133)
                    ·
                      refine ⟨2251538215270546968346925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6004101907388125248925133 2251538215270546968346925)
                      ·
                        rfl

theorem cell23_4384855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_4384855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384855 prefixEnd_4384855 := by exact prefixLift 4384855
  have htrace : WordTrace (prefixWord ++ tailWord_4384855) baseStart_4384855 baseEnd_4384855 := by
    simpa [prefixWord, tailWord_4384855, baseEnd_4384855] using wordTrace_append hprefix tailTrace_4384855
  have hstable : (prefixWord ++ tailWord_4384855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384855).length < 2 ^ (prefixWord ++ tailWord_4384855).sum := by decide
  have hdescent : baseEnd_4384855 < baseStart_4384855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384856 : List Nat := [2, 1, 2, 2, 1, 6, 2, 2, 1, 2, 2]
def baseStart_4384856 : Nat := 118140960795 + 4384856 * 2 ^ 59
def prefixEnd_4384856 : Nat := 4983230072969 + 3 ^ 40 * 4384856 * 2
def baseEnd_4384856 : Nat := 2251538728751201464434421

theorem tailTrace_4384856 : CollatzResearch.WordTrace tailWord_4384856 prefixEnd_4384856 2251538728751201464434421 := by
  unfold tailWord_4384856
  simp only [CollatzResearch.WordTrace]
  refine ⟨79964418501211530314511211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106619224668282040419348281 79964418501211530314511211)
  ·
    refine ⟨119946627751817295471766817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79964418501211530314511211 119946627751817295471766817)
    ·
      refine ⟨89959970813862971603825113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119946627751817295471766817 89959970813862971603825113)
      ·
        refine ⟨67469978110397228702868835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89959970813862971603825113 67469978110397228702868835)
        ·
          refine ⟨101204967165595843054303253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67469978110397228702868835 101204967165595843054303253)
          ·
            refine ⟨4743982835887305143170465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 101204967165595843054303253 4743982835887305143170465)
            ·
              refine ⟨3557987126915478857377849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4743982835887305143170465 3557987126915478857377849)
              ·
                refine ⟨2668490345186609143033387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3557987126915478857377849 2668490345186609143033387)
                ·
                  refine ⟨4002735517779913714550081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2668490345186609143033387 4002735517779913714550081)
                  ·
                    refine ⟨3002051638334935285912561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4002735517779913714550081 3002051638334935285912561)
                    ·
                      refine ⟨2251538728751201464434421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3002051638334935285912561 2251538728751201464434421)
                      ·
                        rfl

theorem cell23_4384856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 2, 2, 1, 2, 2].length) (baseStart_4384856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384856 prefixEnd_4384856 := by exact prefixLift 4384856
  have htrace : WordTrace (prefixWord ++ tailWord_4384856) baseStart_4384856 baseEnd_4384856 := by
    simpa [prefixWord, tailWord_4384856, baseEnd_4384856] using wordTrace_append hprefix tailTrace_4384856
  have hstable : (prefixWord ++ tailWord_4384856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384856).length < 2 ^ (prefixWord ++ tailWord_4384856).sum := by decide
  have hdescent : baseEnd_4384856 < baseStart_4384856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384878 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_4384878 : Nat := 118140960795 + 4384878 * 2 ^ 59
def prefixEnd_4384878 : Nat := 4983230072969 + 3 ^ 40 * 4384878 * 2
def baseEnd_4384878 : Nat := 2251550025325600378359319

theorem tailTrace_4384878 : CollatzResearch.WordTrace tailWord_4384878 prefixEnd_4384878 2251550025325600378359319 := by
  unfold tailWord_4384878
  simp only [CollatzResearch.WordTrace]
  refine ⟨19991204926042919798290411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106619759605562238924215525 19991204926042919798290411)
  ·
    refine ⟨29986807389064379697435617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19991204926042919798290411 29986807389064379697435617)
    ·
      refine ⟨22490105541798284773076713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29986807389064379697435617 22490105541798284773076713)
      ·
        refine ⟨16867579156348713579807535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22490105541798284773076713 16867579156348713579807535)
        ·
          refine ⟨25301368734523070369711303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16867579156348713579807535 25301368734523070369711303)
          ·
            refine ⟨37952053101784605554566955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25301368734523070369711303 37952053101784605554566955)
            ·
              refine ⟨56928079652676908331850433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37952053101784605554566955 56928079652676908331850433)
              ·
                refine ⟨42696059739507681248887825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56928079652676908331850433 42696059739507681248887825)
                ·
                  refine ⟨32022044804630760936665869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42696059739507681248887825 32022044804630760936665869)
                  ·
                    refine ⟨12008266801736535351249701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32022044804630760936665869 12008266801736535351249701)
                    ·
                      refine ⟨2251550025325600378359319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12008266801736535351249701 2251550025325600378359319)
                      ·
                        rfl

theorem cell23_4384878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_4384878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384878 prefixEnd_4384878 := by exact prefixLift 4384878
  have htrace : WordTrace (prefixWord ++ tailWord_4384878) baseStart_4384878 baseEnd_4384878 := by
    simpa [prefixWord, tailWord_4384878, baseEnd_4384878] using wordTrace_append hprefix tailTrace_4384878
  have hstable : (prefixWord ++ tailWord_4384878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384878).length < 2 ^ (prefixWord ++ tailWord_4384878).sum := by decide
  have hdescent : baseEnd_4384878 < baseStart_4384878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384899 : List Nat := [1, 1, 1, 3, 3, 5, 2, 1, 1, 3, 2]
def baseStart_4384899 : Nat := 118140960795 + 4384899 * 2 ^ 59
def prefixEnd_4384899 : Nat := 4983230072969 + 3 ^ 40 * 4384899 * 2
def baseEnd_4384899 : Nat := 2251560808419344796196723

theorem tailTrace_4384899 : CollatzResearch.WordTrace tailWord_4384899 prefixEnd_4384899 2251560808419344796196723 := by
  unfold tailWord_4384899
  simp only [CollatzResearch.WordTrace]
  refine ⟨159930405341267278972837751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106620270227511519315225167 159930405341267278972837751)
  ·
    refine ⟨239895608011900918459256627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159930405341267278972837751 239895608011900918459256627)
    ·
      refine ⟨359843412017851377688884941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239895608011900918459256627 359843412017851377688884941)
      ·
        refine ⟨134941279506694266633331853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 359843412017851377688884941 134941279506694266633331853)
        ·
          refine ⟨50602979815010349987499445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134941279506694266633331853 50602979815010349987499445)
          ·
            refine ⟨4744029357657220311328073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50602979815010349987499445 4744029357657220311328073)
            ·
              refine ⟨3558022018242915233496055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4744029357657220311328073 3558022018242915233496055)
              ·
                refine ⟨5337033027364372850244083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3558022018242915233496055 5337033027364372850244083)
                ·
                  refine ⟨8005549541046559275366125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5337033027364372850244083 8005549541046559275366125)
                  ·
                    refine ⟨3002081077892459728262297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8005549541046559275366125 3002081077892459728262297)
                    ·
                      refine ⟨2251560808419344796196723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3002081077892459728262297 2251560808419344796196723)
                      ·
                        rfl

theorem cell23_4384899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 2, 1, 1, 3, 2].length) (baseStart_4384899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384899 prefixEnd_4384899 := by exact prefixLift 4384899
  have htrace : WordTrace (prefixWord ++ tailWord_4384899) baseStart_4384899 baseEnd_4384899 := by
    simpa [prefixWord, tailWord_4384899, baseEnd_4384899] using wordTrace_append hprefix tailTrace_4384899
  have hstable : (prefixWord ++ tailWord_4384899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384899).length < 2 ^ (prefixWord ++ tailWord_4384899).sum := by decide
  have hdescent : baseEnd_4384899 < baseStart_4384899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4384985 : List Nat := [1, 2, 1, 2, 3, 1, 2, 3, 2, 4, 2]
def baseStart_4384985 : Nat := 118140960795 + 4384985 * 2 ^ 59
def prefixEnd_4384985 : Nat := 4983230072969 + 3 ^ 40 * 4384985 * 2
def baseEnd_4384985 : Nat := 2251604967755631459721327

theorem tailTrace_4384985 : CollatzResearch.WordTrace tailWord_4384985 prefixEnd_4384985 2251604967755631459721327 := by
  unfold tailWord_4384985
  simp only [CollatzResearch.WordTrace]
  refine ⟨159933542018955715660468409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106622361345970477106978939 159933542018955715660468409)
  ·
    refine ⟨119950156514216786745351307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159933542018955715660468409 119950156514216786745351307)
    ·
      refine ⟨179925234771325180118026961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119950156514216786745351307 179925234771325180118026961)
      ·
        refine ⟨134943926078493885088520221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179925234771325180118026961 134943926078493885088520221)
        ·
          refine ⟨50603972279435206908195083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 134943926078493885088520221 50603972279435206908195083)
          ·
            refine ⟨75905958419152810362292625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50603972279435206908195083 75905958419152810362292625)
            ·
              refine ⟨56929468814364607771719469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75905958419152810362292625 56929468814364607771719469)
              ·
                refine ⟨21348550805386727914394801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56929468814364607771719469 21348550805386727914394801)
                ·
                  refine ⟨16011413104040045935796101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21348550805386727914394801 16011413104040045935796101)
                  ·
                    refine ⟨3002139957007508612961769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16011413104040045935796101 3002139957007508612961769)
                    ·
                      refine ⟨2251604967755631459721327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3002139957007508612961769 2251604967755631459721327)
                      ·
                        rfl

theorem cell23_4384985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 3, 2, 4, 2].length) (baseStart_4384985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4384985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4384985 prefixEnd_4384985 := by exact prefixLift 4384985
  have htrace : WordTrace (prefixWord ++ tailWord_4384985) baseStart_4384985 baseEnd_4384985 := by
    simpa [prefixWord, tailWord_4384985, baseEnd_4384985] using wordTrace_append hprefix tailTrace_4384985
  have hstable : (prefixWord ++ tailWord_4384985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4384985).length < 2 ^ (prefixWord ++ tailWord_4384985).sum := by decide
  have hdescent : baseEnd_4384985 < baseStart_4384985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4384985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385022 : List Nat := [4, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3]
def baseStart_4385022 : Nat := 118140960795 + 4385022 * 2 ^ 59
def prefixEnd_4385022 : Nat := 4983230072969 + 3 ^ 40 * 4385022 * 2
def baseEnd_4385022 : Nat := 2251623966539847814958657

theorem tailTrace_4385022 : CollatzResearch.WordTrace tailWord_4385022 prefixEnd_4385022 2251623966539847814958657 := by
  unfold tailWord_4385022
  simp only [CollatzResearch.WordTrace]
  refine ⟨19991861439977708872445665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106623261013214447319710213 19991861439977708872445665)
  ·
    refine ⟨14993896079983281654334249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19991861439977708872445665 14993896079983281654334249)
    ·
      refine ⟨11245422059987461240750687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14993896079983281654334249 11245422059987461240750687)
      ·
        refine ⟨16868133089981191861126031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11245422059987461240750687 16868133089981191861126031)
        ·
          refine ⟨25302199634971787791689047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16868133089981191861126031 25302199634971787791689047)
          ·
            refine ⟨37953299452457681687533571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25302199634971787791689047 37953299452457681687533571)
            ·
              refine ⟨56929949178686522531300357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37953299452457681687533571 56929949178686522531300357)
              ·
                refine ⟨10674365471003722974618817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56929949178686522531300357 10674365471003722974618817)
                ·
                  refine ⟨8005774103252792230964113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10674365471003722974618817 8005774103252792230964113)
                  ·
                    refine ⟨6004330577439594173223085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8005774103252792230964113 6004330577439594173223085)
                    ·
                      refine ⟨2251623966539847814958657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6004330577439594173223085 2251623966539847814958657)
                      ·
                        rfl

theorem cell23_4385022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_4385022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385022 prefixEnd_4385022 := by exact prefixLift 4385022
  have htrace : WordTrace (prefixWord ++ tailWord_4385022) baseStart_4385022 baseEnd_4385022 := by
    simpa [prefixWord, tailWord_4385022, baseEnd_4385022] using wordTrace_append hprefix tailTrace_4385022
  have hstable : (prefixWord ++ tailWord_4385022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385022).length < 2 ^ (prefixWord ++ tailWord_4385022).sum := by decide
  have hdescent : baseEnd_4385022 < baseStart_4385022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385025 : List Nat := [1, 2, 4, 1, 1, 2, 4, 2, 6]
def baseStart_4385025 : Nat := 118140960795 + 4385025 * 2 ^ 59
def prefixEnd_4385025 : Nat := 4983230072969 + 3 ^ 40 * 4385025 * 2
def baseEnd_4385025 : Nat := 250180611886867922580127

theorem tailTrace_4385025 : CollatzResearch.WordTrace tailWord_4385025 prefixEnd_4385025 250180611886867922580127 := by
  unfold tailWord_4385025
  simp only [CollatzResearch.WordTrace]
  refine ⟨159935000938810802491924529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106623333959207201661283019 159935000938810802491924529)
  ·
    refine ⟨119951250704108101868943397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159935000938810802491924529 119951250704108101868943397)
    ·
      refine ⟨22490859507020269100426887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119951250704108101868943397 22490859507020269100426887)
      ·
        refine ⟨33736289260530403650640331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22490859507020269100426887 33736289260530403650640331)
        ·
          refine ⟨50604433890795605475960497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33736289260530403650640331 50604433890795605475960497)
          ·
            refine ⟨37953325418096704106970373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50604433890795605475960497 37953325418096704106970373)
            ·
              refine ⟨7116248515893132020056945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37953325418096704106970373 7116248515893132020056945)
              ·
                refine ⟨5337186386919849015042709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7116248515893132020056945 5337186386919849015042709)
                ·
                  refine ⟨250180611886867922580127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5337186386919849015042709 250180611886867922580127)
                  ·
                    rfl

theorem cell23_4385025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 6].length) (baseStart_4385025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385025 prefixEnd_4385025 := by exact prefixLift 4385025
  have htrace : WordTrace (prefixWord ++ tailWord_4385025) baseStart_4385025 baseEnd_4385025 := by
    simpa [prefixWord, tailWord_4385025, baseEnd_4385025] using wordTrace_append hprefix tailTrace_4385025
  have hstable : (prefixWord ++ tailWord_4385025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385025).length < 2 ^ (prefixWord ++ tailWord_4385025).sum := by decide
  have hdescent : baseEnd_4385025 < baseStart_4385025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385048 : List Nat := [2, 1, 2, 3, 1, 2, 1, 1, 2, 1, 7]
def baseStart_4385048 : Nat := 118140960795 + 4385048 * 2 ^ 59
def prefixEnd_4385048 : Nat := 4983230072969 + 3 ^ 40 * 4385048 * 2
def baseEnd_4385048 : Nat := 2251637317036864713233537

theorem tailTrace_4385048 : CollatzResearch.WordTrace tailWord_4385048 prefixEnd_4385048 2251637317036864713233537 := by
  unfold tailWord_4385048
  simp only [CollatzResearch.WordTrace]
  refine ⟨79967919908863738710005899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106623893211818318280007865 79967919908863738710005899)
  ·
    refine ⟨119951879863295608065008849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79967919908863738710005899 119951879863295608065008849)
    ·
      refine ⟨89963909897471706048756637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119951879863295608065008849 89963909897471706048756637)
      ·
        refine ⟨33736466211551889768283739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89963909897471706048756637 33736466211551889768283739)
        ·
          refine ⟨50604699317327834652425609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33736466211551889768283739 50604699317327834652425609)
          ·
            refine ⟨37953524487995875989319207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50604699317327834652425609 37953524487995875989319207)
            ·
              refine ⟨56930286731993813983978811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37953524487995875989319207 56930286731993813983978811)
              ·
                refine ⟨85395430097990720975968217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56930286731993813983978811 85395430097990720975968217)
                ·
                  refine ⟨64046572573493040731976163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85395430097990720975968217 64046572573493040731976163)
                  ·
                    refine ⟨96069858860239561097964245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64046572573493040731976163 96069858860239561097964245)
                    ·
                      refine ⟨2251637317036864713233537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 96069858860239561097964245 2251637317036864713233537)
                      ·
                        rfl

theorem cell23_4385048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_4385048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385048 prefixEnd_4385048 := by exact prefixLift 4385048
  have htrace : WordTrace (prefixWord ++ tailWord_4385048) baseStart_4385048 baseEnd_4385048 := by
    simpa [prefixWord, tailWord_4385048, baseEnd_4385048] using wordTrace_append hprefix tailTrace_4385048
  have hstable : (prefixWord ++ tailWord_4385048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385048).length < 2 ^ (prefixWord ++ tailWord_4385048).sum := by decide
  have hdescent : baseEnd_4385048 < baseStart_4385048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385055 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 3, 5]
def baseStart_4385055 : Nat := 118140960795 + 4385055 * 2 ^ 59
def prefixEnd_4385055 : Nat := 4983230072969 + 3 ^ 40 * 4385055 * 2
def baseEnd_4385055 : Nat := 750546970467148728615335

theorem tailTrace_4385055 : CollatzResearch.WordTrace tailWord_4385055 prefixEnd_4385055 750546970467148728615335 := by
  unfold tailWord_4385055
  simp only [CollatzResearch.WordTrace]
  refine ⟨159936095128702117615516619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106624063419134745077011079 159936095128702117615516619)
  ·
    refine ⟨239904142693053176423274929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159936095128702117615516619 239904142693053176423274929)
    ·
      refine ⟨179928107019789882317456197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239904142693053176423274929 179928107019789882317456197)
      ·
        refine ⟨33736520066210602934523037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179928107019789882317456197 33736520066210602934523037)
        ·
          refine ⟨12651195024828976100446139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33736520066210602934523037 12651195024828976100446139)
          ·
            refine ⟨18976792537243464150669209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12651195024828976100446139 18976792537243464150669209)
            ·
              refine ⟨14232594402932598113001907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18976792537243464150669209 14232594402932598113001907)
              ·
                refine ⟨21348891604398897169502861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14232594402932598113001907 21348891604398897169502861)
                ·
                  refine ⟨8005834351649586438563573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21348891604398897169502861 8005834351649586438563573)
                  ·
                    refine ⟨750546970467148728615335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8005834351649586438563573 750546970467148728615335)
                    ·
                      rfl

theorem cell23_4385055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 5].length) (baseStart_4385055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385055 prefixEnd_4385055 := by exact prefixLift 4385055
  have htrace : WordTrace (prefixWord ++ tailWord_4385055) baseStart_4385055 baseEnd_4385055 := by
    simpa [prefixWord, tailWord_4385055, baseEnd_4385055] using wordTrace_append hprefix tailTrace_4385055
  have hstable : (prefixWord ++ tailWord_4385055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385055).length < 2 ^ (prefixWord ++ tailWord_4385055).sum := by decide
  have hdescent : baseEnd_4385055 < baseStart_4385055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385086 : List Nat := [4, 2, 1, 2, 1, 2, 2, 4, 1, 1, 3]
def baseStart_4385086 : Nat := 118140960795 + 4385086 * 2 ^ 59
def prefixEnd_4385086 : Nat := 4983230072969 + 3 ^ 40 * 4385086 * 2
def baseEnd_4385086 : Nat := 2251656829301735564558363

theorem tailTrace_4385086 : CollatzResearch.WordTrace tailWord_4385086 prefixEnd_4385086 2251656829301735564558363 := by
  unfold tailWord_4385086
  simp only [CollatzResearch.WordTrace]
  refine ⟨19992153223948726238736889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106624817194393206606596741 19992153223948726238736889)
  ·
    refine ⟨14994114917961544679052667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19992153223948726238736889 14994114917961544679052667)
    ·
      refine ⟨22491172376942317018579001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14994114917961544679052667 22491172376942317018579001)
      ·
        refine ⟨16868379282706737763934251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22491172376942317018579001 16868379282706737763934251)
        ·
          refine ⟨25302568924060106645901377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16868379282706737763934251 25302568924060106645901377)
          ·
            refine ⟨18976926693045079984426033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25302568924060106645901377 18976926693045079984426033)
            ·
              refine ⟨14232695019783809988319525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18976926693045079984426033 14232695019783809988319525)
              ·
                refine ⟨2668630316209464372809911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14232695019783809988319525 2668630316209464372809911)
                ·
                  refine ⟨4002945474314196559214867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2668630316209464372809911 4002945474314196559214867)
                  ·
                    refine ⟨6004418211471294838822301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4002945474314196559214867 6004418211471294838822301)
                    ·
                      refine ⟨2251656829301735564558363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6004418211471294838822301 2251656829301735564558363)
                      ·
                        rfl

theorem cell23_4385086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_4385086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385086 prefixEnd_4385086 := by exact prefixLift 4385086
  have htrace : WordTrace (prefixWord ++ tailWord_4385086) baseStart_4385086 baseEnd_4385086 := by
    simpa [prefixWord, tailWord_4385086, baseEnd_4385086] using wordTrace_append hprefix tailTrace_4385086
  have hstable : (prefixWord ++ tailWord_4385086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385086).length < 2 ^ (prefixWord ++ tailWord_4385086).sum := by decide
  have hdescent : baseEnd_4385086 < baseStart_4385086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385095 : List Nat := [1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 5]
def baseStart_4385095 : Nat := 118140960795 + 4385095 * 2 ^ 59
def prefixEnd_4385095 : Nat := 4983230072969 + 3 ^ 40 * 4385095 * 2
def baseEnd_4385095 : Nat := 2251661450627626029345821

theorem tailTrace_4385095 : CollatzResearch.WordTrace tailWord_4385095 prefixEnd_4385095 2251661450627626029345821 := by
  unfold tailWord_4385095
  simp only [CollatzResearch.WordTrace]
  refine ⟨159937554048557204446972739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106625036032371469631315159 159937554048557204446972739)
  ·
    refine ⟨239906331072835806670459109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159937554048557204446972739 239906331072835806670459109)
    ·
      refine ⟨44982437076156713750711083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 239906331072835806670459109 44982437076156713750711083)
      ·
        refine ⟨67473655614235070626066625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44982437076156713750711083 67473655614235070626066625)
        ·
          refine ⟨50605241710676302969549969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67473655614235070626066625 50605241710676302969549969)
          ·
            refine ⟨37953931283007227227162477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50605241710676302969549969 37953931283007227227162477)
            ·
              refine ⟨14232724231127710210185929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37953931283007227227162477 14232724231127710210185929)
              ·
                refine ⟨10674543173345782657639447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14232724231127710210185929 10674543173345782657639447)
                ·
                  refine ⟨16011814760018673986459171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10674543173345782657639447 16011814760018673986459171)
                  ·
                    refine ⟨24017722140028010979688757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16011814760018673986459171 24017722140028010979688757)
                    ·
                      refine ⟨2251661450627626029345821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24017722140028010979688757 2251661450627626029345821)
                      ·
                        rfl

theorem cell23_4385095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_4385095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385095 prefixEnd_4385095 := by exact prefixLift 4385095
  have htrace : WordTrace (prefixWord ++ tailWord_4385095) baseStart_4385095 baseEnd_4385095 := by
    simpa [prefixWord, tailWord_4385095, baseEnd_4385095] using wordTrace_append hprefix tailTrace_4385095
  have hstable : (prefixWord ++ tailWord_4385095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385095).length < 2 ^ (prefixWord ++ tailWord_4385095).sum := by decide
  have hdescent : baseEnd_4385095 < baseStart_4385095 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385105 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 1, 1, 6]
def baseStart_4385105 : Nat := 118140960795 + 4385105 * 2 ^ 59
def prefixEnd_4385105 : Nat := 4983230072969 + 3 ^ 40 * 4385105 * 2
def baseEnd_4385105 : Nat := 2251666585434170990220775

theorem tailTrace_4385105 : CollatzResearch.WordTrace tailWord_4385105 prefixEnd_4385105 2251666585434170990220775 := by
  unfold tailWord_4385105
  simp only [CollatzResearch.WordTrace]
  refine ⟨159937918778520976154836769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106625279185680650769891179 159937918778520976154836769)
  ·
    refine ⟨119953439083890732116127577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159937918778520976154836769 119953439083890732116127577)
    ·
      refine ⟨89965079312918049087095683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119953439083890732116127577 89965079312918049087095683)
      ·
        refine ⟨134947618969377073630643525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89965079312918049087095683 134947618969377073630643525)
        ·
          refine ⟨25302678556758201305745661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134947618969377073630643525 25302678556758201305745661)
          ·
            refine ⟨9488504458784325489654623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25302678556758201305745661 9488504458784325489654623)
            ·
              refine ⟨14232756688176488234481935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9488504458784325489654623 14232756688176488234481935)
              ·
                refine ⟨21349135032264732351722903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14232756688176488234481935 21349135032264732351722903)
                ·
                  refine ⟨32023702548397098527584355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21349135032264732351722903 32023702548397098527584355)
                  ·
                    refine ⟨48035553822595647791376533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32023702548397098527584355 48035553822595647791376533)
                    ·
                      refine ⟨2251666585434170990220775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48035553822595647791376533 2251666585434170990220775)
                      ·
                        rfl

theorem cell23_4385105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_4385105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385105 prefixEnd_4385105 := by exact prefixLift 4385105
  have htrace : WordTrace (prefixWord ++ tailWord_4385105) baseStart_4385105 baseEnd_4385105 := by
    simpa [prefixWord, tailWord_4385105, baseEnd_4385105] using wordTrace_append hprefix tailTrace_4385105
  have hstable : (prefixWord ++ tailWord_4385105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385105).length < 2 ^ (prefixWord ++ tailWord_4385105).sum := by decide
  have hdescent : baseEnd_4385105 < baseStart_4385105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385109 : List Nat := [1, 3, 2, 2, 4, 1, 2, 2, 1, 1, 4]
def baseStart_4385109 : Nat := 118140960795 + 4385109 * 2 ^ 59
def prefixEnd_4385109 : Nat := 4983230072969 + 3 ^ 40 * 4385109 * 2
def baseEnd_4385109 : Nat := 2251668639356788974570757

theorem tailTrace_4385109 : CollatzResearch.WordTrace tailWord_4385109 prefixEnd_4385109 2251668639356788974570757 := by
  unfold tailWord_4385109
  simp only [CollatzResearch.WordTrace]
  refine ⟨159938064670506484837982381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106625376447004323225321587 159938064670506484837982381)
  ·
    refine ⟨59976774251439931814243393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159938064670506484837982381 59976774251439931814243393)
    ·
      refine ⟨44982580688579948860682545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59976774251439931814243393 44982580688579948860682545)
      ·
        refine ⟨33736935516434961645511909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44982580688579948860682545 33736935516434961645511909)
        ·
          refine ⟨6325675409331555308533483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33736935516434961645511909 6325675409331555308533483)
          ·
            refine ⟨9488513113997332962800225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6325675409331555308533483 9488513113997332962800225)
            ·
              refine ⟨7116384835497999722100169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9488513113997332962800225 7116384835497999722100169)
              ·
                refine ⟨5337288626623499791575127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7116384835497999722100169 5337288626623499791575127)
                ·
                  refine ⟨8005932939935249687362691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5337288626623499791575127 8005932939935249687362691)
                  ·
                    refine ⟨12008899409902874531044037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8005932939935249687362691 12008899409902874531044037)
                    ·
                      refine ⟨2251668639356788974570757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12008899409902874531044037 2251668639356788974570757)
                      ·
                        rfl

theorem cell23_4385109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_4385109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385109 prefixEnd_4385109 := by exact prefixLift 4385109
  have htrace : WordTrace (prefixWord ++ tailWord_4385109) baseStart_4385109 baseEnd_4385109 := by
    simpa [prefixWord, tailWord_4385109, baseEnd_4385109] using wordTrace_append hprefix tailTrace_4385109
  have hstable : (prefixWord ++ tailWord_4385109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385109).length < 2 ^ (prefixWord ++ tailWord_4385109).sum := by decide
  have hdescent : baseEnd_4385109 < baseStart_4385109 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385132 : List Nat := [2, 2, 1, 1, 7, 1, 9]
def baseStart_4385132 : Nat := 118140960795 + 4385132 * 2 ^ 59
def prefixEnd_4385132 : Nat := 4983230072969 + 3 ^ 40 * 4385132 * 2
def baseEnd_4385132 : Nat := 27798524066812868945471

theorem tailTrace_4385132 : CollatzResearch.WordTrace tailWord_4385132 prefixEnd_4385132 27798524066812868945471 := by
  unfold tailWord_4385132
  simp only [CollatzResearch.WordTrace]
  refine ⟨79969451774711579883034825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106625935699615439844046433 79969451774711579883034825)
  ·
    refine ⟨59977088831033684912276119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79969451774711579883034825 59977088831033684912276119)
    ·
      refine ⟨89965633246550527368414179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59977088831033684912276119 89965633246550527368414179)
      ·
        refine ⟨134948449869825791052621269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89965633246550527368414179 134948449869825791052621269)
        ·
          refine ⟨3162854293824041977795811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 134948449869825791052621269 3162854293824041977795811)
          ·
            refine ⟨4744281440736062966693717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3162854293824041977795811 4744281440736062966693717)
            ·
              refine ⟨27798524066812868945471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4744281440736062966693717 27798524066812868945471)
              ·
                rfl

theorem cell23_4385132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 9].length) (baseStart_4385132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385132 prefixEnd_4385132 := by exact prefixLift 4385132
  have htrace : WordTrace (prefixWord ++ tailWord_4385132) baseStart_4385132 baseEnd_4385132 := by
    simpa [prefixWord, tailWord_4385132, baseEnd_4385132] using wordTrace_append hprefix tailTrace_4385132
  have hstable : (prefixWord ++ tailWord_4385132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385132).length < 2 ^ (prefixWord ++ tailWord_4385132).sum := by decide
  have hdescent : baseEnd_4385132 < baseStart_4385132 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385159 : List Nat := [1, 1, 4, 2, 2, 1, 3, 3, 2, 1, 3]
def baseStart_4385159 : Nat := 118140960795 + 4385159 * 2 ^ 59
def prefixEnd_4385159 : Nat := 4983230072969 + 3 ^ 40 * 4385159 * 2
def baseEnd_4385159 : Nat := 2251694313389513778945527

theorem tailTrace_4385159 : CollatzResearch.WordTrace tailWord_4385159 prefixEnd_4385159 2251694313389513778945527 := by
  unfold tailWord_4385159
  simp only [CollatzResearch.WordTrace]
  refine ⟨159939888320325343377302531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106626592213550228918201687 159939888320325343377302531)
  ·
    refine ⟨239909832480488015065953797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159939888320325343377302531 239909832480488015065953797)
    ·
      refine ⟨44983093590091502824866337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 239909832480488015065953797 44983093590091502824866337)
      ·
        refine ⟨33737320192568627118649753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44983093590091502824866337 33737320192568627118649753)
        ·
          refine ⟨25302990144426470338987315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33737320192568627118649753 25302990144426470338987315)
          ·
            refine ⟨37954485216639705508480973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25302990144426470338987315 37954485216639705508480973)
            ·
              refine ⟨14232931956239889565680365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37954485216639705508480973 14232931956239889565680365)
              ·
                refine ⟨5337349483589958587130137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14232931956239889565680365 5337349483589958587130137)
                ·
                  refine ⟨4003012112692468940347603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5337349483589958587130137 4003012112692468940347603)
                  ·
                    refine ⟨6004518169038703410521405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4003012112692468940347603 6004518169038703410521405)
                    ·
                      refine ⟨2251694313389513778945527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6004518169038703410521405 2251694313389513778945527)
                      ·
                        rfl

theorem cell23_4385159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_4385159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385159 prefixEnd_4385159 := by exact prefixLift 4385159
  have htrace : WordTrace (prefixWord ++ tailWord_4385159) baseStart_4385159 baseEnd_4385159 := by
    simpa [prefixWord, tailWord_4385159, baseEnd_4385159] using wordTrace_append hprefix tailTrace_4385159
  have hstable : (prefixWord ++ tailWord_4385159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385159).length < 2 ^ (prefixWord ++ tailWord_4385159).sum := by decide
  have hdescent : baseEnd_4385159 < baseStart_4385159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385212 : List Nat := [2, 2, 2, 4, 1, 1, 1, 1, 1, 4, 4]
def baseStart_4385212 : Nat := 118140960795 + 4385212 * 2 ^ 59
def prefixEnd_4385212 : Nat := 4983230072969 + 3 ^ 40 * 4385212 * 2
def baseEnd_4385212 : Nat := 2251721527864202071582783

theorem tailTrace_4385212 : CollatzResearch.WordTrace tailWord_4385212 prefixEnd_4385212 2251721527864202071582783 := by
  unfold tailWord_4385212
  simp only [CollatzResearch.WordTrace]
  refine ⟨79970910694566666714490945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106627880926088888952654593 79970910694566666714490945)
  ·
    refine ⟨59978183020925000035868209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79970910694566666714490945 59978183020925000035868209)
    ·
      refine ⟨44983637265693750026901157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59978183020925000035868209 44983637265693750026901157)
      ·
        refine ⟨8434431987317578130043967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44983637265693750026901157 8434431987317578130043967)
        ·
          refine ⟨12651647980976367195065951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8434431987317578130043967 12651647980976367195065951)
          ·
            refine ⟨18977471971464550792598927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12651647980976367195065951 18977471971464550792598927)
            ·
              refine ⟨28466207957196826188898391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18977471971464550792598927 28466207957196826188898391)
              ·
                refine ⟨42699311935795239283347587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28466207957196826188898391 42699311935795239283347587)
                ·
                  refine ⟨64048967903692858925021381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42699311935795239283347587 64048967903692858925021381)
                  ·
                    refine ⟨12009181481942411048441509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 64048967903692858925021381 12009181481942411048441509)
                    ·
                      refine ⟨2251721527864202071582783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12009181481942411048441509 2251721527864202071582783)
                      ·
                        rfl

theorem cell23_4385212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_4385212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385212 prefixEnd_4385212 := by exact prefixLift 4385212
  have htrace : WordTrace (prefixWord ++ tailWord_4385212) baseStart_4385212 baseEnd_4385212 := by
    simpa [prefixWord, tailWord_4385212, baseEnd_4385212] using wordTrace_append hprefix tailTrace_4385212
  have hstable : (prefixWord ++ tailWord_4385212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385212).length < 2 ^ (prefixWord ++ tailWord_4385212).sum := by decide
  have hdescent : baseEnd_4385212 < baseStart_4385212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385250 : List Nat := [3, 3, 3, 2, 1, 1, 1, 1, 4, 2, 2]
def baseStart_4385250 : Nat := 118140960795 + 4385250 * 2 ^ 59
def prefixEnd_4385250 : Nat := 4983230072969 + 3 ^ 40 * 4385250 * 2
def baseEnd_4385250 : Nat := 2251741040129072922907609

theorem tailTrace_4385250 : CollatzResearch.WordTrace tailWord_4385250 prefixEnd_4385250 2251741040129072922907609 := by
  unfold tailWord_4385250
  simp only [CollatzResearch.WordTrace]
  refine ⟨39985801840748916479716301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106628804908663777279243469 39985801840748916479716301)
  ·
    refine ⟨14994675690280843679893613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39985801840748916479716301 14994675690280843679893613)
    ·
      refine ⟨5623003383855316379960105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14994675690280843679893613 5623003383855316379960105)
      ·
        refine ⟨4217252537891487284970079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5623003383855316379960105 4217252537891487284970079)
        ·
          refine ⟨6325878806837230927455119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4217252537891487284970079 6325878806837230927455119)
          ·
            refine ⟨9488818210255846391182679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6325878806837230927455119 9488818210255846391182679)
            ·
              refine ⟨14233227315383769586774019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9488818210255846391182679 14233227315383769586774019)
              ·
                refine ⟨21349840973075654380161029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14233227315383769586774019 21349840973075654380161029)
                ·
                  refine ⟨4003095182451685196280193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21349840973075654380161029 4003095182451685196280193)
                  ·
                    refine ⟨3002321386838763897210145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4003095182451685196280193 3002321386838763897210145)
                    ·
                      refine ⟨2251741040129072922907609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3002321386838763897210145 2251741040129072922907609)
                      ·
                        rfl

theorem cell23_4385250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_4385250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385250 prefixEnd_4385250 := by exact prefixLift 4385250
  have htrace : WordTrace (prefixWord ++ tailWord_4385250) baseStart_4385250 baseEnd_4385250 := by
    simpa [prefixWord, tailWord_4385250, baseEnd_4385250] using wordTrace_append hprefix tailTrace_4385250
  have hstable : (prefixWord ++ tailWord_4385250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385250).length < 2 ^ (prefixWord ++ tailWord_4385250).sum := by decide
  have hdescent : baseEnd_4385250 < baseStart_4385250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385295 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 8]
def baseStart_4385295 : Nat := 118140960795 + 4385295 * 2 ^ 59
def prefixEnd_4385295 : Nat := 4983230072969 + 3 ^ 40 * 4385295 * 2
def baseEnd_4385295 : Nat := 250196016306502805204989

theorem tailTrace_4385295 : CollatzResearch.WordTrace tailWord_4385295 prefixEnd_4385295 250196016306502805204989 := by
  unfold tailWord_4385295
  simp only [CollatzResearch.WordTrace]
  refine ⟨159944848647832638604253339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106629899098555092402835559 159944848647832638604253339)
  ·
    refine ⟨239917272971748957906380009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159944848647832638604253339 239917272971748957906380009)
    ·
      refine ⟨179937954728811718429785007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239917272971748957906380009 179937954728811718429785007)
      ·
        refine ⟨269906932093217577644677511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179937954728811718429785007 269906932093217577644677511)
        ·
          refine ⟨404860398139826366467016267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269906932093217577644677511 404860398139826366467016267)
          ·
            refine ⟨607290597209739549700524401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404860398139826366467016267 607290597209739549700524401)
            ·
              refine ⟨455467947907304662275393301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 607290597209739549700524401 455467947907304662275393301)
              ·
                refine ⟨21350060058154906044159061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 455467947907304662275393301 21350060058154906044159061)
                ·
                  refine ⟨250196016306502805204989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21350060058154906044159061 250196016306502805204989)
                  ·
                    rfl

theorem cell23_4385295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 8].length) (baseStart_4385295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385295 prefixEnd_4385295 := by exact prefixLift 4385295
  have htrace : WordTrace (prefixWord ++ tailWord_4385295) baseStart_4385295 baseEnd_4385295 := by
    simpa [prefixWord, tailWord_4385295, baseEnd_4385295] using wordTrace_append hprefix tailTrace_4385295
  have hstable : (prefixWord ++ tailWord_4385295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385295).length < 2 ^ (prefixWord ++ tailWord_4385295).sum := by decide
  have hdescent : baseEnd_4385295 < baseStart_4385295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385309 : List Nat := [1, 4, 2, 2, 1, 2, 1, 1, 4, 2, 3]
def baseStart_4385309 : Nat := 118140960795 + 4385309 * 2 ^ 59
def prefixEnd_4385309 : Nat := 4983230072969 + 3 ^ 40 * 4385309 * 2
def baseEnd_4385309 : Nat := 2251771335487688192069837

theorem tailTrace_4385309 : CollatzResearch.WordTrace tailWord_4385309 prefixEnd_4385309 2251771335487688192069837 := by
  unfold tailWord_4385309
  simp only [CollatzResearch.WordTrace]
  refine ⟨159945359269781918995262981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106630239513187945996841987 159945359269781918995262981)
  ·
    refine ⟨29989754863084109811611809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159945359269781918995262981 29989754863084109811611809)
    ·
      refine ⟨22492316147313082358708857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29989754863084109811611809 22492316147313082358708857)
      ·
        refine ⟨16869237110484811769031643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22492316147313082358708857 16869237110484811769031643)
        ·
          refine ⟨25303855665727217653547465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16869237110484811769031643 25303855665727217653547465)
          ·
            refine ⟨18977891749295413240160599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25303855665727217653547465 18977891749295413240160599)
            ·
              refine ⟨28466837623943119860240899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18977891749295413240160599 28466837623943119860240899)
              ·
                refine ⟨42700256435914679790361349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28466837623943119860240899 42700256435914679790361349)
                ·
                  refine ⟨8006298081734002460692753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42700256435914679790361349 8006298081734002460692753)
                  ·
                    refine ⟨6004723561300501845519565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8006298081734002460692753 6004723561300501845519565)
                    ·
                      refine ⟨2251771335487688192069837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6004723561300501845519565 2251771335487688192069837)
                      ·
                        rfl

theorem cell23_4385309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_4385309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385309 prefixEnd_4385309 := by exact prefixLift 4385309
  have htrace : WordTrace (prefixWord ++ tailWord_4385309) baseStart_4385309 baseEnd_4385309 := by
    simpa [prefixWord, tailWord_4385309, baseEnd_4385309] using wordTrace_append hprefix tailTrace_4385309
  have hstable : (prefixWord ++ tailWord_4385309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385309).length < 2 ^ (prefixWord ++ tailWord_4385309).sum := by decide
  have hdescent : baseEnd_4385309 < baseStart_4385309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385329 : List Nat := [1, 2, 2, 3, 1, 1, 6, 1, 6]
def baseStart_4385329 : Nat := 118140960795 + 4385329 * 2 ^ 59
def prefixEnd_4385329 : Nat := 4983230072969 + 3 ^ 40 * 4385329 * 2
def baseEnd_4385329 : Nat := 250197956122308679313305

theorem tailTrace_4385329 : CollatzResearch.WordTrace tailWord_4385329 prefixEnd_4385329 250197956122308679313305 := by
  unfold tailWord_4385329
  simp only [CollatzResearch.WordTrace]
  refine ⟨159946088729709462410991041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106630725819806308273994027 159946088729709462410991041)
  ·
    refine ⟨119959566547282096808243281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159946088729709462410991041 119959566547282096808243281)
    ·
      refine ⟨89969674910461572606182461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119959566547282096808243281 89969674910461572606182461)
      ·
        refine ⟨33738628091423089727318423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 89969674910461572606182461 33738628091423089727318423)
        ·
          refine ⟨50607942137134634590977635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33738628091423089727318423 50607942137134634590977635)
          ·
            refine ⟨75911913205701951886466453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50607942137134634590977635 75911913205701951886466453)
            ·
              refine ⟨3558370931517278994678115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75911913205701951886466453 3558370931517278994678115)
              ·
                refine ⟨5337556397275918492017173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3558370931517278994678115 5337556397275918492017173)
                ·
                  refine ⟨250197956122308679313305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5337556397275918492017173 250197956122308679313305)
                  ·
                    rfl

theorem cell23_4385329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 6].length) (baseStart_4385329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385329 prefixEnd_4385329 := by exact prefixLift 4385329
  have htrace : WordTrace (prefixWord ++ tailWord_4385329) baseStart_4385329 baseEnd_4385329 := by
    simpa [prefixWord, tailWord_4385329, baseEnd_4385329] using wordTrace_append hprefix tailTrace_4385329
  have hstable : (prefixWord ++ tailWord_4385329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385329).length < 2 ^ (prefixWord ++ tailWord_4385329).sum := by decide
  have hdescent : baseEnd_4385329 < baseStart_4385329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385389 : List Nat := [1, 5, 1, 1, 3, 1, 1, 3, 1, 6]
def baseStart_4385389 : Nat := 118140960795 + 4385389 * 2 ^ 59
def prefixEnd_4385389 : Nat := 4983230072969 + 3 ^ 40 * 4385389 * 2
def baseEnd_4385389 : Nat := 750604137980015959689823

theorem tailTrace_4385389 : CollatzResearch.WordTrace tailWord_4385389 prefixEnd_4385389 750604137980015959689823 := by
  unfold tailWord_4385389
  simp only [CollatzResearch.WordTrace]
  refine ⟨159948277109492092658175221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106632184739661395105450147 159948277109492092658175221)
  ·
    refine ⟨14995150979014883686703927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 159948277109492092658175221 14995150979014883686703927)
    ·
      refine ⟨22492726468522325530055891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14995150979014883686703927 22492726468522325530055891)
      ·
        refine ⟨33739089702783488295083837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22492726468522325530055891 33739089702783488295083837)
        ·
          refine ⟨12652158638543808110656439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33739089702783488295083837 12652158638543808110656439)
          ·
            refine ⟨18978237957815712165984659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12652158638543808110656439 18978237957815712165984659)
            ·
              refine ⟨28467356936723568248976989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18978237957815712165984659 28467356936723568248976989)
              ·
                refine ⟨10675258851271338093366371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28467356936723568248976989 10675258851271338093366371)
                ·
                  refine ⟨16012888276907007140049557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10675258851271338093366371 16012888276907007140049557)
                  ·
                    refine ⟨750604137980015959689823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16012888276907007140049557 750604137980015959689823)
                    ·
                      rfl

theorem cell23_4385389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_4385389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385389 prefixEnd_4385389 := by exact prefixLift 4385389
  have htrace : WordTrace (prefixWord ++ tailWord_4385389) baseStart_4385389 baseEnd_4385389 := by
    simpa [prefixWord, tailWord_4385389, baseEnd_4385389] using wordTrace_append hprefix tailTrace_4385389
  have hstable : (prefixWord ++ tailWord_4385389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385389).length < 2 ^ (prefixWord ++ tailWord_4385389).sum := by decide
  have hdescent : baseEnd_4385389 < baseStart_4385389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385399 : List Nat := [1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 3]
def baseStart_4385399 : Nat := 118140960795 + 4385399 * 2 ^ 59
def prefixEnd_4385399 : Nat := 4983230072969 + 3 ^ 40 * 4385399 * 2
def baseEnd_4385399 : Nat := 2251817548746592839944423

theorem tailTrace_4385399 : CollatzResearch.WordTrace tailWord_4385399 prefixEnd_4385399 2251817548746592839944423 := by
  unfold tailWord_4385399
  simp only [CollatzResearch.WordTrace]
  refine ⟨159948641839455864366039251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106632427892970576244026167 159948641839455864366039251)
  ·
    refine ⟨239922962759183796549058877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159948641839455864366039251 239922962759183796549058877)
    ·
      refine ⟨89971111034693923705897079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239922962759183796549058877 89971111034693923705897079)
      ·
        refine ⟨134956666552040885558845619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89971111034693923705897079 134956666552040885558845619)
        ·
          refine ⟨202434999828061328338268429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134956666552040885558845619 202434999828061328338268429)
          ·
            refine ⟨75913124935522998126850661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202434999828061328338268429 75913124935522998126850661)
            ·
              refine ⟨14233710925410562148784499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75913124935522998126850661 14233710925410562148784499)
              ·
                refine ⟨21350566388115843223176749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14233710925410562148784499 21350566388115843223176749)
                ·
                  refine ⟨8006462395543441208691281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21350566388115843223176749 8006462395543441208691281)
                  ·
                    refine ⟨6004846796657580906518461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8006462395543441208691281 6004846796657580906518461)
                    ·
                      refine ⟨2251817548746592839944423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6004846796657580906518461 2251817548746592839944423)
                      ·
                        rfl

theorem cell23_4385399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 3].length) (baseStart_4385399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385399 prefixEnd_4385399 := by exact prefixLift 4385399
  have htrace : WordTrace (prefixWord ++ tailWord_4385399) baseStart_4385399 baseEnd_4385399 := by
    simpa [prefixWord, tailWord_4385399, baseEnd_4385399] using wordTrace_append hprefix tailTrace_4385399
  have hstable : (prefixWord ++ tailWord_4385399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385399).length < 2 ^ (prefixWord ++ tailWord_4385399).sum := by decide
  have hdescent : baseEnd_4385399 < baseStart_4385399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385409 : List Nat := [1, 2, 4, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_4385409 : Nat := 118140960795 + 4385409 * 2 ^ 59
def prefixEnd_4385409 : Nat := 4983230072969 + 3 ^ 40 * 4385409 * 2
def baseEnd_4385409 : Nat := 2251822683553137800819377

theorem tailTrace_4385409 : CollatzResearch.WordTrace tailWord_4385409 prefixEnd_4385409 2251822683553137800819377 := by
  unfold tailWord_4385409
  simp only [CollatzResearch.WordTrace]
  refine ⟨159949006569419636073903281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106632671046279757382602187 159949006569419636073903281)
  ·
    refine ⟨119961754927064727055427461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159949006569419636073903281 119961754927064727055427461)
    ·
      refine ⟨22492829048824636322892649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 119961754927064727055427461 22492829048824636322892649)
      ·
        refine ⟨16869621786618477242169487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22492829048824636322892649 16869621786618477242169487)
        ·
          refine ⟨25304432679927715863254231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16869621786618477242169487 25304432679927715863254231)
          ·
            refine ⟨37956649019891573794881347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25304432679927715863254231 37956649019891573794881347)
            ·
              refine ⟨56934973529837360692322021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37956649019891573794881347 56934973529837360692322021)
              ·
                refine ⟨10675307536844505129810379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56934973529837360692322021 10675307536844505129810379)
                ·
                  refine ⟨16012961305266757694715569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10675307536844505129810379 16012961305266757694715569)
                  ·
                    refine ⟨12009720978950068271036677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16012961305266757694715569 12009720978950068271036677)
                    ·
                      refine ⟨2251822683553137800819377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12009720978950068271036677 2251822683553137800819377)
                      ·
                        rfl

theorem cell23_4385409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_4385409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385409 prefixEnd_4385409 := by exact prefixLift 4385409
  have htrace : WordTrace (prefixWord ++ tailWord_4385409) baseStart_4385409 baseEnd_4385409 := by
    simpa [prefixWord, tailWord_4385409, baseEnd_4385409] using wordTrace_append hprefix tailTrace_4385409
  have hstable : (prefixWord ++ tailWord_4385409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385409).length < 2 ^ (prefixWord ++ tailWord_4385409).sum := by decide
  have hdescent : baseEnd_4385409 < baseStart_4385409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385413 : List Nat := [1, 3, 1, 1, 4, 4, 2, 1, 1, 1, 4]
def baseStart_4385413 : Nat := 118140960795 + 4385413 * 2 ^ 59
def prefixEnd_4385413 : Nat := 4983230072969 + 3 ^ 40 * 4385413 * 2
def baseEnd_4385413 : Nat := 2251824737475755785169359

theorem tailTrace_4385413 : CollatzResearch.WordTrace tailWord_4385413 prefixEnd_4385413 2251824737475755785169359 := by
  unfold tailWord_4385413
  simp only [CollatzResearch.WordTrace]
  refine ⟨159949152461405144757048893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106632768307603429838032595 159949152461405144757048893)
  ·
    refine ⟨59980932173026929283893335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159949152461405144757048893 59980932173026929283893335)
    ·
      refine ⟨89971398259540393925840003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59980932173026929283893335 89971398259540393925840003)
      ·
        refine ⟨134957097389310590888760005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89971398259540393925840003 134957097389310590888760005)
        ·
          refine ⟨25304455760495735791642501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134957097389310590888760005 25304455760495735791642501)
          ·
            refine ⟨4744585455092950460932969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25304455760495735791642501 4744585455092950460932969)
            ·
              refine ⟨3558439091319712845699727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4744585455092950460932969 3558439091319712845699727)
              ·
                refine ⟨5337658636979569268549591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3558439091319712845699727 5337658636979569268549591)
                ·
                  refine ⟨8006487955469353902824387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5337658636979569268549591 8006487955469353902824387)
                  ·
                    refine ⟨12009731933204030854236581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8006487955469353902824387 12009731933204030854236581)
                    ·
                      refine ⟨2251824737475755785169359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12009731933204030854236581 2251824737475755785169359)
                      ·
                        rfl

theorem cell23_4385413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 1, 1, 1, 4].length) (baseStart_4385413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385413 prefixEnd_4385413 := by exact prefixLift 4385413
  have htrace : WordTrace (prefixWord ++ tailWord_4385413) baseStart_4385413 baseEnd_4385413 := by
    simpa [prefixWord, tailWord_4385413, baseEnd_4385413] using wordTrace_append hprefix tailTrace_4385413
  have hstable : (prefixWord ++ tailWord_4385413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385413).length < 2 ^ (prefixWord ++ tailWord_4385413).sum := by decide
  have hdescent : baseEnd_4385413 < baseStart_4385413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385489 : List Nat := [1, 2, 2, 1, 2, 3, 2, 1, 2, 4, 3]
def baseStart_4385489 : Nat := 118140960795 + 4385489 * 2 ^ 59
def prefixEnd_4385489 : Nat := 4983230072969 + 3 ^ 40 * 4385489 * 2
def baseEnd_4385489 : Nat := 2251863762005497487819009

theorem tailTrace_4385489 : CollatzResearch.WordTrace tailWord_4385489 prefixEnd_4385489 2251863762005497487819009 := by
  unfold tailWord_4385489
  simp only [CollatzResearch.WordTrace]
  refine ⟨159951924409129809736815521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106634616272753206491210347 159951924409129809736815521)
  ·
    refine ⟨119963943306847357302611641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159951924409129809736815521 119963943306847357302611641)
    ·
      refine ⟨89972957480135517976958731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119963943306847357302611641 89972957480135517976958731)
      ·
        refine ⟨134959436220203276965438097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89972957480135517976958731 134959436220203276965438097)
        ·
          refine ⟨101219577165152457724078573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134959436220203276965438097 101219577165152457724078573)
          ·
            refine ⟨37957341436932171646529465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101219577165152457724078573 37957341436932171646529465)
            ·
              refine ⟨28468006077699128734897099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37957341436932171646529465 28468006077699128734897099)
              ·
                refine ⟨42702009116548693102345649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28468006077699128734897099 42702009116548693102345649)
                ·
                  refine ⟨32026506837411519826759237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42702009116548693102345649 32026506837411519826759237)
                  ·
                    refine ⟨6004970032014659967517357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32026506837411519826759237 6004970032014659967517357)
                    ·
                      refine ⟨2251863762005497487819009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6004970032014659967517357 2251863762005497487819009)
                      ·
                        rfl

theorem cell23_4385489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 2, 4, 3].length) (baseStart_4385489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385489 prefixEnd_4385489 := by exact prefixLift 4385489
  have htrace : WordTrace (prefixWord ++ tailWord_4385489) baseStart_4385489 baseEnd_4385489 := by
    simpa [prefixWord, tailWord_4385489, baseEnd_4385489] using wordTrace_append hprefix tailTrace_4385489
  have hstable : (prefixWord ++ tailWord_4385489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385489).length < 2 ^ (prefixWord ++ tailWord_4385489).sum := by decide
  have hdescent : baseEnd_4385489 < baseStart_4385489 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385543 : List Nat := [1, 1, 4, 4, 1, 2, 1, 4, 5]
def baseStart_4385543 : Nat := 118140960795 + 4385543 * 2 ^ 59
def prefixEnd_4385543 : Nat := 4983230072969 + 3 ^ 40 * 4385543 * 2
def baseEnd_4385543 : Nat := 250210165551204475171529

theorem tailTrace_4385543 : CollatzResearch.WordTrace tailWord_4385543 prefixEnd_4385543 250210165551204475171529 := by
  unfold tailWord_4385543
  simp only [CollatzResearch.WordTrace]
  refine ⟨159953893950934176959281283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106635929300622784639520855 159953893950934176959281283)
  ·
    refine ⟨239930840926401265438921925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159953893950934176959281283 239930840926401265438921925)
    ·
      refine ⟨44987032673700237269797861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 239930840926401265438921925 44987032673700237269797861)
      ·
        refine ⟨8435068626318794488087099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 44987032673700237269797861 8435068626318794488087099)
        ·
          refine ⟨12652602939478191732130649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8435068626318794488087099 12652602939478191732130649)
          ·
            refine ⟨9489452204608643799097987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12652602939478191732130649 9489452204608643799097987)
            ·
              refine ⟨14234178306912965698646981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9489452204608643799097987 14234178306912965698646981)
              ·
                refine ⟨2668908432546181068496309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14234178306912965698646981 2668908432546181068496309)
                ·
                  refine ⟨250210165551204475171529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2668908432546181068496309 250210165551204475171529)
                  ·
                    rfl

theorem cell23_4385543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 5].length) (baseStart_4385543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385543 prefixEnd_4385543 := by exact prefixLift 4385543
  have htrace : WordTrace (prefixWord ++ tailWord_4385543) baseStart_4385543 baseEnd_4385543 := by
    simpa [prefixWord, tailWord_4385543, baseEnd_4385543] using wordTrace_append hprefix tailTrace_4385543
  have hstable : (prefixWord ++ tailWord_4385543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385543).length < 2 ^ (prefixWord ++ tailWord_4385543).sum := by decide
  have hdescent : baseEnd_4385543 < baseStart_4385543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385546 : List Nat := [3, 1, 2, 2, 1, 2, 1, 1, 1, 7, 2]
def baseStart_4385546 : Nat := 118140960795 + 4385546 * 2 ^ 59
def prefixEnd_4385546 : Nat := 4983230072969 + 3 ^ 40 * 4385546 * 2
def baseEnd_4385546 : Nat := 2251893030402803764806247

theorem tailTrace_4385546 : CollatzResearch.WordTrace tailWord_4385546 prefixEnd_4385546 2251893030402803764806247 := by
  unfold tailWord_4385546
  simp only [CollatzResearch.WordTrace]
  refine ⟨39988500842480827117910123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106636002246615538981093661 39988500842480827117910123)
  ·
    refine ⟨59982751263721240676865185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39988500842480827117910123 59982751263721240676865185)
    ·
      refine ⟨44987063447790930507648889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59982751263721240676865185 44987063447790930507648889)
      ·
        refine ⟨33740297585843197880736667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44987063447790930507648889 33740297585843197880736667)
        ·
          refine ⟨50610446378764796821105001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33740297585843197880736667 50610446378764796821105001)
          ·
            refine ⟨37957834784073597615828751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50610446378764796821105001 37957834784073597615828751)
            ·
              refine ⟨56936752176110396423743127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37957834784073597615828751 56936752176110396423743127)
              ·
                refine ⟨85405128264165594635614691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56936752176110396423743127 85405128264165594635614691)
                ·
                  refine ⟨128107692396248391953422037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85405128264165594635614691 128107692396248391953422037)
                  ·
                    refine ⟨3002524040537071686408329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 128107692396248391953422037 3002524040537071686408329)
                    ·
                      refine ⟨2251893030402803764806247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3002524040537071686408329 2251893030402803764806247)
                      ·
                        rfl

theorem cell23_4385546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_4385546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385546 prefixEnd_4385546 := by exact prefixLift 4385546
  have htrace : WordTrace (prefixWord ++ tailWord_4385546) baseStart_4385546 baseEnd_4385546 := by
    simpa [prefixWord, tailWord_4385546, baseEnd_4385546] using wordTrace_append hprefix tailTrace_4385546
  have hstable : (prefixWord ++ tailWord_4385546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385546).length < 2 ^ (prefixWord ++ tailWord_4385546).sum := by decide
  have hdescent : baseEnd_4385546 < baseStart_4385546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385576 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_4385576 : Nat := 118140960795 + 4385576 * 2 ^ 59
def prefixEnd_4385576 : Nat := 4983230072969 + 3 ^ 40 * 4385576 * 2
def baseEnd_4385576 : Nat := 2251908434822438647431109

theorem tailTrace_4385576 : CollatzResearch.WordTrace tailWord_4385576 prefixEnd_4385576 2251908434822438647431109 := by
  unfold tailWord_4385576
  simp only [CollatzResearch.WordTrace]
  refine ⟨79977548779907311797616291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106636731706543082396821721 79977548779907311797616291)
  ·
    refine ⟨119966323169860967696424437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79977548779907311797616291 119966323169860967696424437)
    ·
      refine ⟨11246842797174465721539791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 119966323169860967696424437 11246842797174465721539791)
      ·
        refine ⟨16870264195761698582309687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11246842797174465721539791 16870264195761698582309687)
        ·
          refine ⟨25305396293642547873464531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16870264195761698582309687 25305396293642547873464531)
          ·
            refine ⟨37958094440463821810196797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25305396293642547873464531 37958094440463821810196797)
            ·
              refine ⟨14234285415173933178823799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 37958094440463821810196797 14234285415173933178823799)
              ·
                refine ⟨21351428122760899768235699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14234285415173933178823799 21351428122760899768235699)
                ·
                  refine ⟨32027142184141349652353549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21351428122760899768235699 32027142184141349652353549)
                  ·
                    refine ⟨12010178319053006119632581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32027142184141349652353549 12010178319053006119632581)
                    ·
                      refine ⟨2251908434822438647431109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12010178319053006119632581 2251908434822438647431109)
                      ·
                        rfl

theorem cell23_4385576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_4385576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385576 prefixEnd_4385576 := by exact prefixLift 4385576
  have htrace : WordTrace (prefixWord ++ tailWord_4385576) baseStart_4385576 baseEnd_4385576 := by
    simpa [prefixWord, tailWord_4385576, baseEnd_4385576] using wordTrace_append hprefix tailTrace_4385576
  have hstable : (prefixWord ++ tailWord_4385576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385576).length < 2 ^ (prefixWord ++ tailWord_4385576).sum := by decide
  have hdescent : baseEnd_4385576 < baseStart_4385576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385586 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 5, 4]
def baseStart_4385586 : Nat := 118140960795 + 4385586 * 2 ^ 59
def prefixEnd_4385586 : Nat := 4983230072969 + 3 ^ 40 * 4385586 * 2
def baseEnd_4385586 : Nat := 750637856542994536102021

theorem tailTrace_4385586 : CollatzResearch.WordTrace tailWord_4385586 prefixEnd_4385586 750637856542994536102021 := by
  unfold tailWord_4385586
  simp only [CollatzResearch.WordTrace]
  refine ⟨39988865572444598825774153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106636974859852263535397741 39988865572444598825774153)
  ·
    refine ⟨29991649179333449119330615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39988865572444598825774153 29991649179333449119330615)
    ·
      refine ⟨44987473769000173678995923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29991649179333449119330615 44987473769000173678995923)
      ·
        refine ⟨67481210653500260518493885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44987473769000173678995923 67481210653500260518493885)
        ·
          refine ⟨25305453995062597694435207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67481210653500260518493885 25305453995062597694435207)
          ·
            refine ⟨37958180992593896541652811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25305453995062597694435207 37958180992593896541652811)
            ·
              refine ⟨56937271488890844812479217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37958180992593896541652811 56937271488890844812479217)
              ·
                refine ⟨42702953616668133609359413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56937271488890844812479217 42702953616668133609359413)
                ·
                  refine ⟨4003401901562637525877445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42702953616668133609359413 4003401901562637525877445)
                  ·
                    refine ⟨750637856542994536102021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4003401901562637525877445 750637856542994536102021)
                    ·
                      rfl

theorem cell23_4385586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 5, 4].length) (baseStart_4385586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385586 prefixEnd_4385586 := by exact prefixLift 4385586
  have htrace : WordTrace (prefixWord ++ tailWord_4385586) baseStart_4385586 baseEnd_4385586 := by
    simpa [prefixWord, tailWord_4385586, baseEnd_4385586] using wordTrace_append hprefix tailTrace_4385586
  have hstable : (prefixWord ++ tailWord_4385586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385586).length < 2 ^ (prefixWord ++ tailWord_4385586).sum := by decide
  have hdescent : baseEnd_4385586 < baseStart_4385586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385596 : List Nat := [2, 2, 2, 2, 1, 1, 1, 3, 4, 2, 3]
def baseStart_4385596 : Nat := 118140960795 + 4385596 * 2 ^ 59
def prefixEnd_4385596 : Nat := 4983230072969 + 3 ^ 40 * 4385596 * 2
def baseEnd_4385596 : Nat := 2251918704435528569181017

theorem tailTrace_4385596 : CollatzResearch.WordTrace tailWord_4385596 prefixEnd_4385596 2251918704435528569181017 := by
  unfold tailWord_4385596
  simp only [CollatzResearch.WordTrace]
  refine ⟨79977913509871083505480321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106637218013161444673973761 79977913509871083505480321)
  ·
    refine ⟨59983435132403312629110241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79977913509871083505480321 59983435132403312629110241)
    ·
      refine ⟨44987576349302484471832681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59983435132403312629110241 44987576349302484471832681)
      ·
        refine ⟨33740682261976863353874511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44987576349302484471832681 33740682261976863353874511)
        ·
          refine ⟨50611023392965295030811767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33740682261976863353874511 50611023392965295030811767)
          ·
            refine ⟨75916535089447942546217651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50611023392965295030811767 75916535089447942546217651)
            ·
              refine ⟨113874802634171913819326477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75916535089447942546217651 113874802634171913819326477)
              ·
                refine ⟨42703050987814467682247429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 113874802634171913819326477 42703050987814467682247429)
                ·
                  refine ⟨8006822060215212690421393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42703050987814467682247429 8006822060215212690421393)
                  ·
                    refine ⟨6005116545161409517816045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8006822060215212690421393 6005116545161409517816045)
                    ·
                      refine ⟨2251918704435528569181017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6005116545161409517816045 2251918704435528569181017)
                      ·
                        rfl

theorem cell23_4385596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_4385596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385596 prefixEnd_4385596 := by exact prefixLift 4385596
  have htrace : WordTrace (prefixWord ++ tailWord_4385596) baseStart_4385596 baseEnd_4385596 := by
    simpa [prefixWord, tailWord_4385596, baseEnd_4385596] using wordTrace_append hprefix tailTrace_4385596
  have hstable : (prefixWord ++ tailWord_4385596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385596).length < 2 ^ (prefixWord ++ tailWord_4385596).sum := by decide
  have hdescent : baseEnd_4385596 < baseStart_4385596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385603 : List Nat := [1, 1, 1, 3, 1, 4, 1, 6, 1, 4]
def baseStart_4385603 : Nat := 118140960795 + 4385603 * 2 ^ 59
def prefixEnd_4385603 : Nat := 4983230072969 + 3 ^ 40 * 4385603 * 2
def baseEnd_4385603 : Nat := 750640766266703347264495

theorem tailTrace_4385603 : CollatzResearch.WordTrace tailWord_4385603 prefixEnd_4385603 750640766266703347264495 := by
  unfold tailWord_4385603
  simp only [CollatzResearch.WordTrace]
  refine ⟨159956082330716807206465463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106637388220477871470976975 159956082330716807206465463)
  ·
    refine ⟨239934123496075210809698195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159956082330716807206465463 239934123496075210809698195)
    ·
      refine ⟨359901185244112816214547293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239934123496075210809698195 359901185244112816214547293)
      ·
        refine ⟨134962944466542306080455235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 359901185244112816214547293 134962944466542306080455235)
        ·
          refine ⟨202444416699813459120682853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134962944466542306080455235 202444416699813459120682853)
          ·
            refine ⟨37958328131215023585128035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 202444416699813459120682853 37958328131215023585128035)
            ·
              refine ⟨56937492196822535377692053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37958328131215023585128035 56937492196822535377692053)
              ·
                refine ⟨2668944946726056345829315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 56937492196822535377692053 2668944946726056345829315)
                ·
                  refine ⟨4003417420089084518743973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2668944946726056345829315 4003417420089084518743973)
                  ·
                    refine ⟨750640766266703347264495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4003417420089084518743973 750640766266703347264495)
                    ·
                      rfl

theorem cell23_4385603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 1, 4].length) (baseStart_4385603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385603 prefixEnd_4385603 := by exact prefixLift 4385603
  have htrace : WordTrace (prefixWord ++ tailWord_4385603) baseStart_4385603 baseEnd_4385603 := by
    simpa [prefixWord, tailWord_4385603, baseEnd_4385603] using wordTrace_append hprefix tailTrace_4385603
  have hstable : (prefixWord ++ tailWord_4385603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385603).length < 2 ^ (prefixWord ++ tailWord_4385603).sum := by decide
  have hdescent : baseEnd_4385603 < baseStart_4385603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385654 : List Nat := [5, 1, 1, 3, 1, 2, 3, 2, 1, 4]
def baseStart_4385654 : Nat := 118140960795 + 4385654 * 2 ^ 59
def prefixEnd_4385654 : Nat := 4983230072969 + 3 ^ 40 * 4385654 * 2
def baseEnd_4385654 : Nat := 750649495437829780751917

theorem tailTrace_4385654 : CollatzResearch.WordTrace tailWord_4385654 prefixEnd_4385654 750649495437829780751917 := by
  unfold tailWord_4385654
  simp only [CollatzResearch.WordTrace]
  refine ⟨9997371403345752682285751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106638628302354695277714677 9997371403345752682285751)
  ·
    refine ⟨14996057105018629023428627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9997371403345752682285751 14996057105018629023428627)
    ·
      refine ⟨22494085657527943535142941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14996057105018629023428627 22494085657527943535142941)
      ·
        refine ⟨8435282121572978825678603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22494085657527943535142941 8435282121572978825678603)
        ·
          refine ⟨12652923182359468238517905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8435282121572978825678603 12652923182359468238517905)
          ·
            refine ⟨9489692386769601178888429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12652923182359468238517905 9489692386769601178888429)
            ·
              refine ⟨3558634645038600442083161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9489692386769601178888429 3558634645038600442083161)
              ·
                refine ⟨2668975983778950331562371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3558634645038600442083161 2668975983778950331562371)
                ·
                  refine ⟨4003463975668425497343557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2668975983778950331562371 4003463975668425497343557)
                  ·
                    refine ⟨750649495437829780751917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4003463975668425497343557 750649495437829780751917)
                    ·
                      rfl

theorem cell23_4385654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 1, 4].length) (baseStart_4385654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385654 prefixEnd_4385654 := by exact prefixLift 4385654
  have htrace : WordTrace (prefixWord ++ tailWord_4385654) baseStart_4385654 baseEnd_4385654 := by
    simpa [prefixWord, tailWord_4385654, baseEnd_4385654] using wordTrace_append hprefix tailTrace_4385654
  have hstable : (prefixWord ++ tailWord_4385654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385654).length < 2 ^ (prefixWord ++ tailWord_4385654).sum := by decide
  have hdescent : baseEnd_4385654 < baseStart_4385654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385660 : List Nat := [2, 2, 2, 1, 1, 1, 1, 8, 1, 1, 3]
def baseStart_4385660 : Nat := 118140960795 + 4385660 * 2 ^ 59
def prefixEnd_4385660 : Nat := 4983230072969 + 3 ^ 40 * 4385660 * 2
def baseEnd_4385660 : Nat := 2251951567197416318780723

theorem tailTrace_4385660 : CollatzResearch.WordTrace tailWord_4385660 prefixEnd_4385660 2251951567197416318780723 := by
  unfold tailWord_4385660
  simp only [CollatzResearch.WordTrace]
  refine ⟨79979080645755152970645217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106638774194340203960860289 79979080645755152970645217)
  ·
    refine ⟨59984310484316364727983913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79979080645755152970645217 59984310484316364727983913)
    ·
      refine ⟨44988232863237273545987935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59984310484316364727983913 44988232863237273545987935)
      ·
        refine ⟨67482349294855910318981903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44988232863237273545987935 67482349294855910318981903)
        ·
          refine ⟨101223523942283865478472855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67482349294855910318981903 101223523942283865478472855)
          ·
            refine ⟨151835285913425798217709283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101223523942283865478472855 151835285913425798217709283)
            ·
              refine ⟨227752928870138697326563925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151835285913425798217709283 227752928870138697326563925)
              ·
                refine ⟨2668979635196937859295671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 227752928870138697326563925 2668979635196937859295671)
                ·
                  refine ⟨4003469452795406788943507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2668979635196937859295671 4003469452795406788943507)
                  ·
                    refine ⟨6005204179193110183415261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4003469452795406788943507 6005204179193110183415261)
                    ·
                      refine ⟨2251951567197416318780723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6005204179193110183415261 2251951567197416318780723)
                      ·
                        rfl

theorem cell23_4385660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 8, 1, 1, 3].length) (baseStart_4385660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385660 prefixEnd_4385660 := by exact prefixLift 4385660
  have htrace : WordTrace (prefixWord ++ tailWord_4385660) baseStart_4385660 baseEnd_4385660 := by
    simpa [prefixWord, tailWord_4385660, baseEnd_4385660] using wordTrace_append hprefix tailTrace_4385660
  have hstable : (prefixWord ++ tailWord_4385660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385660).length < 2 ^ (prefixWord ++ tailWord_4385660).sum := by decide
  have hdescent : baseEnd_4385660 < baseStart_4385660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385696 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 4]
def baseStart_4385696 : Nat := 118140960795 + 4385696 * 2 ^ 59
def prefixEnd_4385696 : Nat := 4983230072969 + 3 ^ 40 * 4385696 * 2
def baseEnd_4385696 : Nat := 2251970052500978177930557

theorem tailTrace_4385696 : CollatzResearch.WordTrace tailWord_4385696 prefixEnd_4385696 2251970052500978177930557 := by
  unfold tailWord_4385696
  simp only [CollatzResearch.WordTrace]
  refine ⟨79979737159689942044800471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106639649546253256059733961 79979737159689942044800471)
  ·
    refine ⟨119969605739534913067200707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79979737159689942044800471 119969605739534913067200707)
    ·
      refine ⟨179954408609302369600801061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119969605739534913067200707 179954408609302369600801061)
      ·
        refine ⟨33741451614244194300150199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 179954408609302369600801061 33741451614244194300150199)
        ·
          refine ⟨50612177421366291450225299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33741451614244194300150199 50612177421366291450225299)
          ·
            refine ⟨75918266132049437175337949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50612177421366291450225299 75918266132049437175337949)
            ·
              refine ⟨28469349799518538940751731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75918266132049437175337949 28469349799518538940751731)
              ·
                refine ⟨42704024699277808411127597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28469349799518538940751731 42704024699277808411127597)
                ·
                  refine ⟨16014009262229178154172849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42704024699277808411127597 16014009262229178154172849)
                  ·
                    refine ⟨12010506946671883615629637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16014009262229178154172849 12010506946671883615629637)
                    ·
                      refine ⟨2251970052500978177930557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12010506946671883615629637 2251970052500978177930557)
                      ·
                        rfl

theorem cell23_4385696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_4385696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385696 prefixEnd_4385696 := by exact prefixLift 4385696
  have htrace : WordTrace (prefixWord ++ tailWord_4385696) baseStart_4385696 baseEnd_4385696 := by
    simpa [prefixWord, tailWord_4385696, baseEnd_4385696] using wordTrace_append hprefix tailTrace_4385696
  have hstable : (prefixWord ++ tailWord_4385696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385696).length < 2 ^ (prefixWord ++ tailWord_4385696).sum := by decide
  have hdescent : baseEnd_4385696 < baseStart_4385696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385700 : List Nat := [2, 3, 1, 2, 1, 2, 5, 1, 1, 1, 4]
def baseStart_4385700 : Nat := 118140960795 + 4385700 * 2 ^ 59
def prefixEnd_4385700 : Nat := 4983230072969 + 3 ^ 40 * 4385700 * 2
def baseEnd_4385700 : Nat := 2251972106423596162280539

theorem tailTrace_4385700 : CollatzResearch.WordTrace tailWord_4385700 prefixEnd_4385700 2251972106423596162280539 := by
  unfold tailWord_4385700
  simp only [CollatzResearch.WordTrace]
  refine ⟨79979810105682696386373277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106639746807576928515164369 79979810105682696386373277)
  ·
    refine ⟨29992428789631011144889979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79979810105682696386373277 29992428789631011144889979)
    ·
      refine ⟨44988643184446516717334969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29992428789631011144889979 44988643184446516717334969)
      ·
        refine ⟨33741482388334887538001227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44988643184446516717334969 33741482388334887538001227)
        ·
          refine ⟨50612223582502331307001841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33741482388334887538001227 50612223582502331307001841)
          ·
            refine ⟨37959167686876748480251381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50612223582502331307001841 37959167686876748480251381)
            ·
              refine ⟨3558671970644695170023567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 37959167686876748480251381 3558671970644695170023567)
              ·
                refine ⟨5338007955967042755035351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3558671970644695170023567 5338007955967042755035351)
                ·
                  refine ⟨8007011933950564132553027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5338007955967042755035351 8007011933950564132553027)
                  ·
                    refine ⟨12010517900925846198829541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8007011933950564132553027 12010517900925846198829541)
                    ·
                      refine ⟨2251972106423596162280539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12010517900925846198829541 2251972106423596162280539)
                      ·
                        rfl

theorem cell23_4385700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_4385700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385700 prefixEnd_4385700 := by exact prefixLift 4385700
  have htrace : WordTrace (prefixWord ++ tailWord_4385700) baseStart_4385700 baseEnd_4385700 := by
    simpa [prefixWord, tailWord_4385700, baseEnd_4385700] using wordTrace_append hprefix tailTrace_4385700
  have hstable : (prefixWord ++ tailWord_4385700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385700).length < 2 ^ (prefixWord ++ tailWord_4385700).sum := by decide
  have hdescent : baseEnd_4385700 < baseStart_4385700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385767 : List Nat := [1, 1, 5, 2, 2, 1, 3, 2, 2, 1, 3]
def baseStart_4385767 : Nat := 118140960795 + 4385767 * 2 ^ 59
def prefixEnd_4385767 : Nat := 4983230072969 + 3 ^ 40 * 4385767 * 2
def baseEnd_4385767 : Nat := 2252006509627447400142731

theorem tailTrace_4385767 : CollatzResearch.WordTrace tailWord_4385767 prefixEnd_4385767 2252006509627447400142731 := by
  unfold tailWord_4385767
  simp only [CollatzResearch.WordTrace]
  refine ⟨159962063902122663215435555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106641375934748442143623703 159962063902122663215435555)
  ·
    refine ⟨239943095853183994823153333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159962063902122663215435555 239943095853183994823153333)
    ·
      refine ⟨22494665236235999514670625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 239943095853183994823153333 22494665236235999514670625)
      ·
        refine ⟨16870998927176999636002969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22494665236235999514670625 16870998927176999636002969)
        ·
          refine ⟨12653249195382749727002227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16870998927176999636002969 12653249195382749727002227)
          ·
            refine ⟨18979873793074124590503341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12653249195382749727002227 18979873793074124590503341)
            ·
              refine ⟨7117452672402796721438753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18979873793074124590503341 7117452672402796721438753)
              ·
                refine ⟨5338089504302097541079065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7117452672402796721438753 5338089504302097541079065)
                ·
                  refine ⟨4003567128226573155809299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5338089504302097541079065 4003567128226573155809299)
                  ·
                    refine ⟨6005350692339859733713949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4003567128226573155809299 6005350692339859733713949)
                    ·
                      refine ⟨2252006509627447400142731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6005350692339859733713949 2252006509627447400142731)
                      ·
                        rfl

theorem cell23_4385767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_4385767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385767 prefixEnd_4385767 := by exact prefixLift 4385767
  have htrace : WordTrace (prefixWord ++ tailWord_4385767) baseStart_4385767 baseEnd_4385767 := by
    simpa [prefixWord, tailWord_4385767, baseEnd_4385767] using wordTrace_append hprefix tailTrace_4385767
  have hstable : (prefixWord ++ tailWord_4385767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385767).length < 2 ^ (prefixWord ++ tailWord_4385767).sum := by decide
  have hdescent : baseEnd_4385767 < baseStart_4385767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385776 : List Nat := [2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 5]
def baseStart_4385776 : Nat := 118140960795 + 4385776 * 2 ^ 59
def prefixEnd_4385776 : Nat := 4983230072969 + 3 ^ 40 * 4385776 * 2
def baseEnd_4385776 : Nat := 2252011130953337864930189

theorem tailTrace_4385776 : CollatzResearch.WordTrace tailWord_4385776 prefixEnd_4385776 2252011130953337864930189 := by
  unfold tailWord_4385776
  simp only [CollatzResearch.WordTrace]
  refine ⟨79981196079545028876256591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106641594772726705168342121 79981196079545028876256591)
  ·
    refine ⟨119971794119317543314384887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79981196079545028876256591 119971794119317543314384887)
    ·
      refine ⟨179957691178976314971577331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119971794119317543314384887 179957691178976314971577331)
      ·
        refine ⟨269936536768464472457365997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179957691178976314971577331 269936536768464472457365997)
        ·
          refine ⟨101226201288174177171512249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 269936536768464472457365997 101226201288174177171512249)
          ·
            refine ⟨75919650966130632878634187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101226201288174177171512249 75919650966130632878634187)
            ·
              refine ⟨113879476449195949317951281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75919650966130632878634187 113879476449195949317951281)
              ·
                refine ⟨85409607336896961988463461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113879476449195949317951281 85409607336896961988463461)
                ·
                  refine ⟨16014301375668180372836899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85409607336896961988463461 16014301375668180372836899)
                  ·
                    refine ⟨24021452063502270559255349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16014301375668180372836899 24021452063502270559255349)
                    ·
                      refine ⟨2252011130953337864930189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24021452063502270559255349 2252011130953337864930189)
                      ·
                        rfl

theorem cell23_4385776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 5].length) (baseStart_4385776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385776 prefixEnd_4385776 := by exact prefixLift 4385776
  have htrace : WordTrace (prefixWord ++ tailWord_4385776) baseStart_4385776 baseEnd_4385776 := by
    simpa [prefixWord, tailWord_4385776, baseEnd_4385776] using wordTrace_append hprefix tailTrace_4385776
  have hstable : (prefixWord ++ tailWord_4385776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385776).length < 2 ^ (prefixWord ++ tailWord_4385776).sum := by decide
  have hdescent : baseEnd_4385776 < baseStart_4385776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385880 : List Nat := [2, 1, 2, 2, 1, 3, 2, 2, 2, 4, 2]
def baseStart_4385880 : Nat := 118140960795 + 4385880 * 2 ^ 59
def prefixEnd_4385880 : Nat := 4983230072969 + 3 ^ 40 * 4385880 * 2
def baseEnd_4385880 : Nat := 2252064532941405458029711

theorem tailTrace_4385880 : CollatzResearch.WordTrace tailWord_4385880 prefixEnd_4385880 2252064532941405458029711 := by
  unfold tailWord_4385880
  simp only [CollatzResearch.WordTrace]
  refine ⟨79983092675356641757149547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106644123567142189009532729 79983092675356641757149547)
  ·
    refine ⟨119974639013034962635724321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79983092675356641757149547 119974639013034962635724321)
    ·
      refine ⟨89980979259776221976793241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 119974639013034962635724321 89980979259776221976793241)
      ·
        refine ⟨67485734444832166482594931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89980979259776221976793241 67485734444832166482594931)
        ·
          refine ⟨101228601667248249723892397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67485734444832166482594931 101228601667248249723892397)
          ·
            refine ⟨37960725625218093646459649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101228601667248249723892397 37960725625218093646459649)
            ·
              refine ⟨28470544218913570234844737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37960725625218093646459649 28470544218913570234844737)
              ·
                refine ⟨21352908164185177676133553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28470544218913570234844737 21352908164185177676133553)
                ·
                  refine ⟨16014681123138883257100165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21352908164185177676133553 16014681123138883257100165)
                  ·
                    refine ⟨3002752710588540610706281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16014681123138883257100165 3002752710588540610706281)
                    ·
                      refine ⟨2252064532941405458029711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3002752710588540610706281 2252064532941405458029711)
                      ·
                        rfl

theorem cell23_4385880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 2, 2, 2, 4, 2].length) (baseStart_4385880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385880 prefixEnd_4385880 := by exact prefixLift 4385880
  have htrace : WordTrace (prefixWord ++ tailWord_4385880) baseStart_4385880 baseEnd_4385880 := by
    simpa [prefixWord, tailWord_4385880, baseEnd_4385880] using wordTrace_append hprefix tailTrace_4385880
  have hstable : (prefixWord ++ tailWord_4385880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385880).length < 2 ^ (prefixWord ++ tailWord_4385880).sum := by decide
  have hdescent : baseEnd_4385880 < baseStart_4385880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385903 : List Nat := [1, 1, 2, 1, 3, 3, 1, 5, 6]
def baseStart_4385903 : Nat := 118140960795 + 4385903 * 2 ^ 59
def prefixEnd_4385903 : Nat := 4983230072969 + 3 ^ 40 * 4385903 * 2
def baseEnd_4385903 : Nat := 250230704777384318671345

theorem tailTrace_4385903 : CollatzResearch.WordTrace tailWord_4385903 prefixEnd_4385903 250230704777384318671345 := by
  unfold tailWord_4385903
  simp only [CollatzResearch.WordTrace]
  refine ⟨159967024229629958442386363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106644682819753305628257575 159967024229629958442386363)
  ·
    refine ⟨239950536344444937663579545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159967024229629958442386363 239950536344444937663579545)
    ·
      refine ⟨179962902258333703247684659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239950536344444937663579545 179962902258333703247684659)
      ·
        refine ⟨269944353387500554871526989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179962902258333703247684659 269944353387500554871526989)
        ·
          refine ⟨101229132520312708076822621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 269944353387500554871526989 101229132520312708076822621)
          ·
            refine ⟨37960924695117265528808483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101229132520312708076822621 37960924695117265528808483)
            ·
              refine ⟨56941387042675898293212725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37960924695117265528808483 56941387042675898293212725)
              ·
                refine ⟨5338255035250865464988693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56941387042675898293212725 5338255035250865464988693)
                ·
                  refine ⟨250230704777384318671345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5338255035250865464988693 250230704777384318671345)
                  ·
                    rfl

theorem cell23_4385903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 6].length) (baseStart_4385903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385903 prefixEnd_4385903 := by exact prefixLift 4385903
  have htrace : WordTrace (prefixWord ++ tailWord_4385903) baseStart_4385903 baseEnd_4385903 := by
    simpa [prefixWord, tailWord_4385903, baseEnd_4385903] using wordTrace_append hprefix tailTrace_4385903
  have hstable : (prefixWord ++ tailWord_4385903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385903).length < 2 ^ (prefixWord ++ tailWord_4385903).sum := by decide
  have hdescent : baseEnd_4385903 < baseStart_4385903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385924 : List Nat := [2, 3, 2, 1, 2, 3, 2, 3, 1, 4]
def baseStart_4385924 : Nat := 118140960795 + 4385924 * 2 ^ 59
def prefixEnd_4385924 : Nat := 4983230072969 + 3 ^ 40 * 4385924 * 2
def baseEnd_4385924 : Nat := 750695708696734428626503

theorem tailTrace_4385924 : CollatzResearch.WordTrace tailWord_4385924 prefixEnd_4385924 750695708696734428626503 := by
  unfold tailWord_4385924
  simp only [CollatzResearch.WordTrace]
  refine ⟨79983895081276939514450413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106645193441702586019267217 79983895081276939514450413)
  ·
    refine ⟨29993960655478852317918905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79983895081276939514450413 29993960655478852317918905)
    ·
      refine ⟨22495470491609139238439179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29993960655478852317918905 22495470491609139238439179)
      ·
        refine ⟨33743205737413708857658769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22495470491609139238439179 33743205737413708857658769)
        ·
          refine ⟨25307404303060281643244077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33743205737413708857658769 25307404303060281643244077)
          ·
            refine ⟨9490276613647605616216529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25307404303060281643244077 9490276613647605616216529)
            ·
              refine ⟨7117707460235704212162397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9490276613647605616216529 7117707460235704212162397)
              ·
                refine ⟨2669140297588389079560899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7117707460235704212162397 2669140297588389079560899)
                ·
                  refine ⟨4003710446382583619341349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2669140297588389079560899 4003710446382583619341349)
                  ·
                    refine ⟨750695708696734428626503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4003710446382583619341349 750695708696734428626503)
                    ·
                      rfl

theorem cell23_4385924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_4385924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385924 prefixEnd_4385924 := by exact prefixLift 4385924
  have htrace : WordTrace (prefixWord ++ tailWord_4385924) baseStart_4385924 baseEnd_4385924 := by
    simpa [prefixWord, tailWord_4385924, baseEnd_4385924] using wordTrace_append hprefix tailTrace_4385924
  have hstable : (prefixWord ++ tailWord_4385924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385924).length < 2 ^ (prefixWord ++ tailWord_4385924).sum := by decide
  have hdescent : baseEnd_4385924 < baseStart_4385924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385954 : List Nat := [3, 3, 1, 3, 2, 1, 3, 1, 6]
def baseStart_4385954 : Nat := 118140960795 + 4385954 * 2 ^ 59
def prefixEnd_4385954 : Nat := 4983230072969 + 3 ^ 40 * 4385954 * 2
def baseEnd_4385954 : Nat := 250233614501093129833819

theorem tailTrace_4385954 : CollatzResearch.WordTrace tailWord_4385954 prefixEnd_4385954 250233614501093129833819 := by
  unfold tailWord_4385954
  simp only [CollatzResearch.WordTrace]
  refine ⟨39992221088111298538123229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106645922901630129434995277 39992221088111298538123229)
  ·
    refine ⟨14997082908041736951796211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39992221088111298538123229 14997082908041736951796211)
    ·
      refine ⟨22495624362062605427694317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14997082908041736951796211 22495624362062605427694317)
      ·
        refine ⟨8435859135773477035385369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22495624362062605427694317 8435859135773477035385369)
        ·
          refine ⟨6326894351830107776539027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8435859135773477035385369 6326894351830107776539027)
          ·
            refine ⟨9490341527745161664808541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6326894351830107776539027 9490341527745161664808541)
            ·
              refine ⟨3558878072904435624303203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9490341527745161664808541 3558878072904435624303203)
              ·
                refine ⟨5338317109356653436454805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3558878072904435624303203 5338317109356653436454805)
                ·
                  refine ⟨250233614501093129833819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5338317109356653436454805 250233614501093129833819)
                  ·
                    rfl

theorem cell23_4385954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_4385954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385954 prefixEnd_4385954 := by exact prefixLift 4385954
  have htrace : WordTrace (prefixWord ++ tailWord_4385954) baseStart_4385954 baseEnd_4385954 := by
    simpa [prefixWord, tailWord_4385954, baseEnd_4385954] using wordTrace_append hprefix tailTrace_4385954
  have hstable : (prefixWord ++ tailWord_4385954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385954).length < 2 ^ (prefixWord ++ tailWord_4385954).sum := by decide
  have hdescent : baseEnd_4385954 < baseStart_4385954 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4385998 : List Nat := [4, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3]
def baseStart_4385998 : Nat := 118140960795 + 4385998 * 2 ^ 59
def prefixEnd_4385998 : Nat := 4983230072969 + 3 ^ 40 * 4385998 * 2
def baseEnd_4385998 : Nat := 2252125123658635996354169

theorem tailTrace_4385998 : CollatzResearch.WordTrace tailWord_4385998 prefixEnd_4385998 2252125123658635996354169 := by
  unfold tailWord_4385998
  simp only [CollatzResearch.WordTrace]
  refine ⟨19996311145535723708386831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106646992776190526444729765 19996311145535723708386831)
  ·
    refine ⟨29994466718303585562580247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19996311145535723708386831 29994466718303585562580247)
    ·
      refine ⟨44991700077455378343870371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29994466718303585562580247 44991700077455378343870371)
      ·
        refine ⟨67487550116183067515805557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44991700077455378343870371 67487550116183067515805557)
        ·
          refine ⟨6326957823392162579606771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67487550116183067515805557 6326957823392162579606771)
          ·
            refine ⟨9490436735088243869410157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6326957823392162579606771 9490436735088243869410157)
            ·
              refine ⟨3558913775658091451028809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9490436735088243869410157 3558913775658091451028809)
              ·
                refine ⟨2669185331743568588271607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3558913775658091451028809 2669185331743568588271607)
                ·
                  refine ⟨4003777997615352882407411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2669185331743568588271607 4003777997615352882407411)
                  ·
                    refine ⟨6005666996423029323611117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4003777997615352882407411 6005666996423029323611117)
                    ·
                      refine ⟨2252125123658635996354169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6005666996423029323611117 2252125123658635996354169)
                      ·
                        rfl

theorem cell23_4385998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 1, 3, 2, 1, 1, 3].length) (baseStart_4385998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4385998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4385998 prefixEnd_4385998 := by exact prefixLift 4385998
  have htrace : WordTrace (prefixWord ++ tailWord_4385998) baseStart_4385998 baseEnd_4385998 := by
    simpa [prefixWord, tailWord_4385998, baseEnd_4385998] using wordTrace_append hprefix tailTrace_4385998
  have hstable : (prefixWord ++ tailWord_4385998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4385998).length < 2 ^ (prefixWord ++ tailWord_4385998).sum := by decide
  have hdescent : baseEnd_4385998 < baseStart_4385998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4385998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386021 : List Nat := [1, 3, 1, 4, 4, 1, 1, 2, 1, 1, 4]
def baseStart_4386021 : Nat := 118140960795 + 4386021 * 2 ^ 59
def prefixEnd_4386021 : Nat := 4983230072969 + 3 ^ 40 * 4386021 * 2
def baseEnd_4386021 : Nat := 2252136933713689406366563

theorem tailTrace_4386021 : CollatzResearch.WordTrace tailWord_4386021 prefixEnd_4386021 2252136933713689406366563 := by
  unfold tailWord_4386021
  simp only [CollatzResearch.WordTrace]
  refine ⟨159971328043202464595181917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106647552028801643063454611 159971328043202464595181917)
  ·
    refine ⟨59989248016200924223193219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159971328043202464595181917 59989248016200924223193219)
    ·
      refine ⟨89983872024301386334789829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59989248016200924223193219 89983872024301386334789829)
      ·
        refine ⟨16871976004556509937773093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 89983872024301386334789829 16871976004556509937773093)
        ·
          refine ⟨3163495500854345613332455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16871976004556509937773093 3163495500854345613332455)
          ·
            refine ⟨4745243251281518419998683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3163495500854345613332455 4745243251281518419998683)
            ·
              refine ⟨7117864876922277629998025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4745243251281518419998683 7117864876922277629998025)
              ·
                refine ⟨5338398657691708222498519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7117864876922277629998025 5338398657691708222498519)
                ·
                  refine ⟨8007597986537562333747779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5338398657691708222498519 8007597986537562333747779)
                  ·
                    refine ⟨12011396979806343500621669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8007597986537562333747779 12011396979806343500621669)
                    ·
                      refine ⟨2252136933713689406366563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12011396979806343500621669 2252136933713689406366563)
                      ·
                        rfl

theorem cell23_4386021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_4386021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386021 prefixEnd_4386021 := by exact prefixLift 4386021
  have htrace : WordTrace (prefixWord ++ tailWord_4386021) baseStart_4386021 baseEnd_4386021 := by
    simpa [prefixWord, tailWord_4386021, baseEnd_4386021] using wordTrace_append hprefix tailTrace_4386021
  have hstable : (prefixWord ++ tailWord_4386021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386021).length < 2 ^ (prefixWord ++ tailWord_4386021).sum := by decide
  have hdescent : baseEnd_4386021 < baseStart_4386021 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386060 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 2, 3, 4]
def baseStart_4386060 : Nat := 118140960795 + 4386060 * 2 ^ 59
def prefixEnd_4386060 : Nat := 4983230072969 + 3 ^ 40 * 4386060 * 2
def baseEnd_4386060 : Nat := 2252156959459214753778883

theorem tailTrace_4386060 : CollatzResearch.WordTrace tailWord_4386060 prefixEnd_4386060 2252156959459214753778883 := by
  unfold tailWord_4386060
  simp only [CollatzResearch.WordTrace]
  refine ⟨79986375245030587127925817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106648500326707449503901089 79986375245030587127925817)
  ·
    refine ⟨59989781433772940345944363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79986375245030587127925817 59989781433772940345944363)
    ·
      refine ⟨89984672150659410518916545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59989781433772940345944363 89984672150659410518916545)
      ·
        refine ⟨67488504112994557889187409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89984672150659410518916545 67488504112994557889187409)
        ·
          refine ⟨50616378084745918416890557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67488504112994557889187409 50616378084745918416890557)
          ·
            refine ⟨18981141781779719406333959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50616378084745918416890557 18981141781779719406333959)
            ·
              refine ⟨28471712672669579109500939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18981141781779719406333959 28471712672669579109500939)
              ·
                refine ⟨42707569009004368664251409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28471712672669579109500939 42707569009004368664251409)
                ·
                  refine ⟨32030676756753276498188557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42707569009004368664251409 32030676756753276498188557)
                  ·
                    refine ⟨12011503783782478686820709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32030676756753276498188557 12011503783782478686820709)
                    ·
                      refine ⟨2252156959459214753778883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12011503783782478686820709 2252156959459214753778883)
                      ·
                        rfl

theorem cell23_4386060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_4386060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386060 prefixEnd_4386060 := by exact prefixLift 4386060
  have htrace : WordTrace (prefixWord ++ tailWord_4386060) baseStart_4386060 baseEnd_4386060 := by
    simpa [prefixWord, tailWord_4386060, baseEnd_4386060] using wordTrace_append hprefix tailTrace_4386060
  have hstable : (prefixWord ++ tailWord_4386060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386060).length < 2 ^ (prefixWord ++ tailWord_4386060).sum := by decide
  have hdescent : baseEnd_4386060 < baseStart_4386060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386098 : List Nat := [3, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2]
def baseStart_4386098 : Nat := 118140960795 + 4386098 * 2 ^ 59
def prefixEnd_4386098 : Nat := 4983230072969 + 3 ^ 40 * 4386098 * 2
def baseEnd_4386098 : Nat := 2252176471724085605103709

theorem tailTrace_4386098 : CollatzResearch.WordTrace tailWord_4386098 prefixEnd_4386098 2252176471724085605103709 := by
  unfold tailWord_4386098
  simp only [CollatzResearch.WordTrace]
  refine ⟨39993534115980876686433737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106649424309282337830489965 39993534115980876686433737)
  ·
    refine ⟨29995150586985657514825303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 39993534115980876686433737 29995150586985657514825303)
    ·
      refine ⟨44992725880478486272237955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29995150586985657514825303 44992725880478486272237955)
      ·
        refine ⟨67489088820717729408356933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44992725880478486272237955 67489088820717729408356933)
        ·
          refine ⟨12654204153884574264066925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67489088820717729408356933 12654204153884574264066925)
          ·
            refine ⟨4745326557706715349025097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12654204153884574264066925 4745326557706715349025097)
            ·
              refine ⟨3558994918280036511768823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4745326557706715349025097 3558994918280036511768823)
              ·
                refine ⟨5338492377420054767653235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3558994918280036511768823 5338492377420054767653235)
                ·
                  refine ⟨8007738566130082151479853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5338492377420054767653235 8007738566130082151479853)
                  ·
                    refine ⟨3002901962298780806804945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8007738566130082151479853 3002901962298780806804945)
                    ·
                      refine ⟨2252176471724085605103709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3002901962298780806804945 2252176471724085605103709)
                      ·
                        rfl

theorem cell23_4386098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 2, 1, 1, 3, 2].length) (baseStart_4386098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386098 prefixEnd_4386098 := by exact prefixLift 4386098
  have htrace : WordTrace (prefixWord ++ tailWord_4386098) baseStart_4386098 baseEnd_4386098 := by
    simpa [prefixWord, tailWord_4386098, baseEnd_4386098] using wordTrace_append hprefix tailTrace_4386098
  have hstable : (prefixWord ++ tailWord_4386098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386098).length < 2 ^ (prefixWord ++ tailWord_4386098).sum := by decide
  have hdescent : baseEnd_4386098 < baseStart_4386098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386111 : List Nat := [1, 1, 2, 2, 4, 2, 3, 2, 2, 2, 2]
def baseStart_4386111 : Nat := 118140960795 + 4386111 * 2 ^ 59
def prefixEnd_4386111 : Nat := 4983230072969 + 3 ^ 40 * 4386111 * 2
def baseEnd_4386111 : Nat := 2252183146972594054241149

theorem tailTrace_4386111 : CollatzResearch.WordTrace tailWord_4386111 prefixEnd_4386111 2252183146972594054241149 := by
  unfold tailWord_4386111
  simp only [CollatzResearch.WordTrace]
  refine ⟨159974610612876409965958187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106649740408584273310638791 159974610612876409965958187)
  ·
    refine ⟨239961915919314614948937281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159974610612876409965958187 239961915919314614948937281)
    ·
      refine ⟨179971436939485961211702961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239961915919314614948937281 179971436939485961211702961)
      ·
        refine ⟨134978577704614470908777221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179971436939485961211702961 134978577704614470908777221)
        ·
          refine ⟨25308483319615213295395729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 134978577704614470908777221 25308483319615213295395729)
          ·
            refine ⟨18981362489711409971546797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25308483319615213295395729 18981362489711409971546797)
            ·
              refine ⟨7118010933641778739330049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18981362489711409971546797 7118010933641778739330049)
              ·
                refine ⟨5338508200231334054497537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7118010933641778739330049 5338508200231334054497537)
                ·
                  refine ⟨4003881150173500540873153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5338508200231334054497537 4003881150173500540873153)
                  ·
                    refine ⟨3002910862630125405654865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4003881150173500540873153 3002910862630125405654865)
                    ·
                      refine ⟨2252183146972594054241149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3002910862630125405654865 2252183146972594054241149)
                      ·
                        rfl

theorem cell23_4386111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 2, 2].length) (baseStart_4386111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386111 prefixEnd_4386111 := by exact prefixLift 4386111
  have htrace : WordTrace (prefixWord ++ tailWord_4386111) baseStart_4386111 baseEnd_4386111 := by
    simpa [prefixWord, tailWord_4386111, baseEnd_4386111] using wordTrace_append hprefix tailTrace_4386111
  have hstable : (prefixWord ++ tailWord_4386111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386111).length < 2 ^ (prefixWord ++ tailWord_4386111).sum := by decide
  have hdescent : baseEnd_4386111 < baseStart_4386111 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386137 : List Nat := [1, 2, 1, 2, 2, 2, 2, 2, 2, 5, 2]
def baseStart_4386137 : Nat := 118140960795 + 4386137 * 2 ^ 59
def prefixEnd_4386137 : Nat := 4983230072969 + 3 ^ 40 * 4386137 * 2
def baseEnd_4386137 : Nat := 2252196497469610952516029

theorem tailTrace_4386137 : CollatzResearch.WordTrace tailWord_4386137 prefixEnd_4386137 2252196497469610952516029 := by
  unfold tailWord_4386137
  simp only [CollatzResearch.WordTrace]
  refine ⟨159975558910782216406404665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106650372607188144270936443 159975558910782216406404665)
  ·
    refine ⟨119981669183086662304803499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159975558910782216406404665 119981669183086662304803499)
    ·
      refine ⟨179972503774629993457205249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119981669183086662304803499 179972503774629993457205249)
      ·
        refine ⟨134979377830972495092903937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 179972503774629993457205249 134979377830972495092903937)
        ·
          refine ⟨101234533373229371319677953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134979377830972495092903937 101234533373229371319677953)
          ·
            refine ⟨75925900029922028489758465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101234533373229371319677953 75925900029922028489758465)
            ·
              refine ⟨56944425022441521367318849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75925900029922028489758465 56944425022441521367318849)
              ·
                refine ⟨42708318766831141025489137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56944425022441521367318849 42708318766831141025489137)
                ·
                  refine ⟨32031239075123355769116853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42708318766831141025489137 32031239075123355769116853)
                  ·
                    refine ⟨3002928663292814603354705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32031239075123355769116853 3002928663292814603354705)
                    ·
                      refine ⟨2252196497469610952516029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3002928663292814603354705 2252196497469610952516029)
                      ·
                        rfl

theorem cell23_4386137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 5, 2].length) (baseStart_4386137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386137 prefixEnd_4386137 := by exact prefixLift 4386137
  have htrace : WordTrace (prefixWord ++ tailWord_4386137) baseStart_4386137 baseEnd_4386137 := by
    simpa [prefixWord, tailWord_4386137, baseEnd_4386137] using wordTrace_append hprefix tailTrace_4386137
  have hstable : (prefixWord ++ tailWord_4386137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386137).length < 2 ^ (prefixWord ++ tailWord_4386137).sum := by decide
  have hdescent : baseEnd_4386137 < baseStart_4386137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386151 : List Nat := [1, 1, 5, 1, 4, 2, 1, 3, 5]
def baseStart_4386151 : Nat := 118140960795 + 4386151 * 2 ^ 59
def prefixEnd_4386151 : Nat := 4983230072969 + 3 ^ 40 * 4386151 * 2
def baseEnd_4386151 : Nat := 250244854022085988637885

theorem tailTrace_4386151 : CollatzResearch.WordTrace tailWord_4386151 prefixEnd_4386151 250244854022085988637885 := by
  unfold tailWord_4386151
  simp only [CollatzResearch.WordTrace]
  refine ⟨159976069532731496797414307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106650713021820997864942871 159976069532731496797414307)
  ·
    refine ⟨239964104299097245196121461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159976069532731496797414307 239964104299097245196121461)
    ·
      refine ⟨22496634778040366737136387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 239964104299097245196121461 22496634778040366737136387)
      ·
        refine ⟨33744952167060550105704581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22496634778040366737136387 33744952167060550105704581)
        ·
          refine ⟨6327178531323853144819609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33744952167060550105704581 6327178531323853144819609)
          ·
            refine ⟨4745383898492889858614707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6327178531323853144819609 4745383898492889858614707)
            ·
              refine ⟨7118075847739334787922061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4745383898492889858614707 7118075847739334787922061)
              ·
                refine ⟨2669278442902250545470773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7118075847739334787922061 2669278442902250545470773)
                ·
                  refine ⟨250244854022085988637885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2669278442902250545470773 250244854022085988637885)
                  ·
                    rfl

theorem cell23_4386151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 5].length) (baseStart_4386151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386151 prefixEnd_4386151 := by exact prefixLift 4386151
  have htrace : WordTrace (prefixWord ++ tailWord_4386151) baseStart_4386151 baseEnd_4386151 := by
    simpa [prefixWord, tailWord_4386151, baseEnd_4386151] using wordTrace_append hprefix tailTrace_4386151
  have hstable : (prefixWord ++ tailWord_4386151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386151).length < 2 ^ (prefixWord ++ tailWord_4386151).sum := by decide
  have hdescent : baseEnd_4386151 < baseStart_4386151 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386167 : List Nat := [1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 4]
def baseStart_4386167 : Nat := 118140960795 + 4386167 * 2 ^ 59
def prefixEnd_4386167 : Nat := 4983230072969 + 3 ^ 40 * 4386167 * 2
def baseEnd_4386167 : Nat := 2252211901889245835140891

theorem tailTrace_4386167 : CollatzResearch.WordTrace tailWord_4386167 prefixEnd_4386167 2252211901889245835140891 := by
  unfold tailWord_4386167
  simp only [CollatzResearch.WordTrace]
  refine ⟨159976653100673531529996755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106651102067115687686664503 159976653100673531529996755)
  ·
    refine ⟨239964979651010297294995133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159976653100673531529996755 239964979651010297294995133)
    ·
      refine ⟨89986867369128861485623175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 239964979651010297294995133 89986867369128861485623175)
      ·
        refine ⟨134980301053693292228434763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89986867369128861485623175 134980301053693292228434763)
        ·
          refine ⟨202470451580539938342652145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134980301053693292228434763 202470451580539938342652145)
          ·
            refine ⟨151852838685404953756989109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202470451580539938342652145 151852838685404953756989109)
            ·
              refine ⟨14236203626756714414717729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 151852838685404953756989109 14236203626756714414717729)
              ·
                refine ⟨10677152720067535811038297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14236203626756714414717729 10677152720067535811038297)
                ·
                  refine ⟨8007864540050651858278723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10677152720067535811038297 8007864540050651858278723)
                  ·
                    refine ⟨12011796810075977787418085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8007864540050651858278723 12011796810075977787418085)
                    ·
                      refine ⟨2252211901889245835140891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12011796810075977787418085 2252211901889245835140891)
                      ·
                        rfl

theorem cell23_4386167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_4386167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386167 prefixEnd_4386167 := by exact prefixLift 4386167
  have htrace : WordTrace (prefixWord ++ tailWord_4386167) baseStart_4386167 baseEnd_4386167 := by
    simpa [prefixWord, tailWord_4386167, baseEnd_4386167] using wordTrace_append hprefix tailTrace_4386167
  have hstable : (prefixWord ++ tailWord_4386167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386167).length < 2 ^ (prefixWord ++ tailWord_4386167).sum := by decide
  have hdescent : baseEnd_4386167 < baseStart_4386167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386170 : List Nat := [3, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5]
def baseStart_4386170 : Nat := 118140960795 + 4386170 * 2 ^ 59
def prefixEnd_4386170 : Nat := 4983230072969 + 3 ^ 40 * 4386170 * 2
def baseEnd_4386170 : Nat := 2252213442331209323403377

theorem tailTrace_4386170 : CollatzResearch.WordTrace tailWord_4386170 prefixEnd_4386170 2252213442331209323403377 := by
  unfold tailWord_4386170
  simp only [CollatzResearch.WordTrace]
  refine ⟨39994190629915665760588991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106651175013108442028237309 39994190629915665760588991)
  ·
    refine ⟨59991285944873498640883487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39994190629915665760588991 59991285944873498640883487)
    ·
      refine ⟨89986928917310247961325231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59991285944873498640883487 89986928917310247961325231)
      ·
        refine ⟨134980393375965371941987847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89986928917310247961325231 134980393375965371941987847)
        ·
          refine ⟨202470590063948057912981771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134980393375965371941987847 202470590063948057912981771)
          ·
            refine ⟨303705885095922086869472657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202470590063948057912981771 303705885095922086869472657)
            ·
              refine ⟨227779413821941565152104493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303705885095922086869472657 227779413821941565152104493)
              ·
                refine ⟨85417280183228086932039185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227779413821941565152104493 85417280183228086932039185)
                ·
                  refine ⟨64062960137421065199029389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85417280183228086932039185 64062960137421065199029389)
                  ·
                    refine ⟨24023610051532899449636021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64062960137421065199029389 24023610051532899449636021)
                    ·
                      refine ⟨2252213442331209323403377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24023610051532899449636021 2252213442331209323403377)
                      ·
                        rfl

theorem cell23_4386170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 2, 3, 5].length) (baseStart_4386170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386170 prefixEnd_4386170 := by exact prefixLift 4386170
  have htrace : WordTrace (prefixWord ++ tailWord_4386170) baseStart_4386170 baseEnd_4386170 := by
    simpa [prefixWord, tailWord_4386170, baseEnd_4386170] using wordTrace_append hprefix tailTrace_4386170
  have hstable : (prefixWord ++ tailWord_4386170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386170).length < 2 ^ (prefixWord ++ tailWord_4386170).sum := by decide
  have hdescent : baseEnd_4386170 < baseStart_4386170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386187 : List Nat := [1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 3]
def baseStart_4386187 : Nat := 118140960795 + 4386187 * 2 ^ 59
def prefixEnd_4386187 : Nat := 4983230072969 + 3 ^ 40 * 4386187 * 2
def baseEnd_4386187 : Nat := 2252222171502335756890799

theorem tailTrace_4386187 : CollatzResearch.WordTrace tailWord_4386187 prefixEnd_4386187 2252222171502335756890799 := by
  unfold tailWord_4386187
  simp only [CollatzResearch.WordTrace]
  refine ⟨159977382560601074945724815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106651588373734049963816543 159977382560601074945724815)
  ·
    refine ⟨239966073840901612418587223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159977382560601074945724815 239966073840901612418587223)
    ·
      refine ⟨359949110761352418627880835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239966073840901612418587223 359949110761352418627880835)
      ·
        refine ⟨539923666142028627941821253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359949110761352418627880835 539923666142028627941821253)
        ·
          refine ⟨101235687401630367739091485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 539923666142028627941821253 101235687401630367739091485)
          ·
            refine ⟨37963382775611387902159307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101235687401630367739091485 37963382775611387902159307)
            ·
              refine ⟨56945074163417081853238961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37963382775611387902159307 56945074163417081853238961)
              ·
                refine ⟨42708805622562811389929221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56945074163417081853238961 42708805622562811389929221)
                ·
                  refine ⟨8007901054230527135611729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42708805622562811389929221 8007901054230527135611729)
                  ·
                    refine ⟨6005925790672895351708797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8007901054230527135611729 6005925790672895351708797)
                    ·
                      refine ⟨2252222171502335756890799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6005925790672895351708797 2252222171502335756890799)
                      ·
                        rfl

theorem cell23_4386187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 2, 4, 2, 3].length) (baseStart_4386187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386187 prefixEnd_4386187 := by exact prefixLift 4386187
  have htrace : WordTrace (prefixWord ++ tailWord_4386187) baseStart_4386187 baseEnd_4386187 := by
    simpa [prefixWord, tailWord_4386187, baseEnd_4386187] using wordTrace_append hprefix tailTrace_4386187
  have hstable : (prefixWord ++ tailWord_4386187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386187).length < 2 ^ (prefixWord ++ tailWord_4386187).sum := by decide
  have hdescent : baseEnd_4386187 < baseStart_4386187 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386221 : List Nat := [1, 5, 2, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_4386221 : Nat := 118140960795 + 4386221 * 2 ^ 59
def prefixEnd_4386221 : Nat := 4983230072969 + 3 ^ 40 * 4386221 * 2
def baseEnd_4386221 : Nat := 2252239629844588623865643

theorem tailTrace_4386221 : CollatzResearch.WordTrace tailWord_4386221 prefixEnd_4386221 2252239629844588623865643 := by
  unfold tailWord_4386221
  simp only [CollatzResearch.WordTrace]
  refine ⟨159978622642477898752462517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106652415094985265834975011 159978622642477898752462517)
  ·
    refine ⟨14997995872732303008043361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 159978622642477898752462517 14997995872732303008043361)
    ·
      refine ⟨11248496904549227256032521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14997995872732303008043361 11248496904549227256032521)
      ·
        refine ⟨8436372678411920442024391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11248496904549227256032521 8436372678411920442024391)
        ·
          refine ⟨12654559017617880663036587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8436372678411920442024391 12654559017617880663036587)
          ·
            refine ⟨18981838526426820994554881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12654559017617880663036587 18981838526426820994554881)
            ·
              refine ⟨14236378894820115745916161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18981838526426820994554881 14236378894820115745916161)
              ·
                refine ⟨10677284171115086809437121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14236378894820115745916161 10677284171115086809437121)
                ·
                  refine ⟨8007963128336315107077841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10677284171115086809437121 8007963128336315107077841)
                  ·
                    refine ⟨6005972346252236330308381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8007963128336315107077841 6005972346252236330308381)
                    ·
                      refine ⟨2252239629844588623865643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6005972346252236330308381 2252239629844588623865643)
                      ·
                        rfl

theorem cell23_4386221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_4386221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386221 prefixEnd_4386221 := by exact prefixLift 4386221
  have htrace : WordTrace (prefixWord ++ tailWord_4386221) baseStart_4386221 baseEnd_4386221 := by
    simpa [prefixWord, tailWord_4386221, baseEnd_4386221] using wordTrace_append hprefix tailTrace_4386221
  have hstable : (prefixWord ++ tailWord_4386221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386221).length < 2 ^ (prefixWord ++ tailWord_4386221).sum := by decide
  have hdescent : baseEnd_4386221 < baseStart_4386221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386237 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 5, 5]
def baseStart_4386237 : Nat := 118140960795 + 4386237 * 2 ^ 59
def prefixEnd_4386237 : Nat := 4983230072969 + 3 ^ 40 * 4386237 * 2
def baseEnd_4386237 : Nat := 750749281845020187088523

theorem tailTrace_4386237 : CollatzResearch.WordTrace tailWord_4386237 prefixEnd_4386237 750749281845020187088523 := by
  unfold tailWord_4386237
  simp only [CollatzResearch.WordTrace]
  refine ⟨159979206210419933485044965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106652804140279955656696643 159979206210419933485044965)
  ·
    refine ⟨29996101164453737528445931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 159979206210419933485044965 29996101164453737528445931)
    ·
      refine ⟨44994151746680606292668897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 29996101164453737528445931 44994151746680606292668897)
      ·
        refine ⟨33745613810010454719501673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44994151746680606292668897 33745613810010454719501673)
        ·
          refine ⟨25309210357507841039626255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33745613810010454719501673 25309210357507841039626255)
          ·
            refine ⟨37963815536261761559439383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25309210357507841039626255 37963815536261761559439383)
            ·
              refine ⟨56945723304392642339159075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37963815536261761559439383 56945723304392642339159075)
              ·
                refine ⟨85418584956588963508738613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 56945723304392642339159075 85418584956588963508738613)
                ·
                  refine ⟨8007992339680215328944245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85418584956588963508738613 8007992339680215328944245)
                  ·
                    refine ⟨750749281845020187088523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8007992339680215328944245 750749281845020187088523)
                    ·
                      rfl

theorem cell23_4386237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_4386237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386237 prefixEnd_4386237 := by exact prefixLift 4386237
  have htrace : WordTrace (prefixWord ++ tailWord_4386237) baseStart_4386237 baseEnd_4386237 := by
    simpa [prefixWord, tailWord_4386237, baseEnd_4386237] using wordTrace_append hprefix tailTrace_4386237
  have hstable : (prefixWord ++ tailWord_4386237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386237).length < 2 ^ (prefixWord ++ tailWord_4386237).sum := by decide
  have hdescent : baseEnd_4386237 < baseStart_4386237 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386267 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 10, 4]
def baseStart_4386267 : Nat := 118140960795 + 4386267 * 2 ^ 59
def prefixEnd_4386267 : Nat := 4983230072969 + 3 ^ 40 * 4386267 * 2
def baseEnd_4386267 : Nat := 750754416651565147963477

theorem tailTrace_4386267 : CollatzResearch.WordTrace tailWord_4386267 prefixEnd_4386267 750754416651565147963477 := by
  unfold tailWord_4386267
  simp only [CollatzResearch.WordTrace]
  refine ⟨159980300400311248608637055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106653533600207499072424703 159980300400311248608637055)
  ·
    refine ⟨239970450600466872912955583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159980300400311248608637055 239970450600466872912955583)
    ·
      refine ⟨359955675900700309369433375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239970450600466872912955583 359955675900700309369433375)
      ·
        refine ⟨539933513851050464054150063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359955675900700309369433375 539933513851050464054150063)
        ·
          refine ⟨809900270776575696081225095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 539933513851050464054150063 809900270776575696081225095)
          ·
            refine ⟨1214850406164863544121837643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 809900270776575696081225095 1214850406164863544121837643)
            ·
              refine ⟨1822275609247295316182756465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214850406164863544121837643 1822275609247295316182756465)
              ·
                refine ⟨1366706706935471487137067349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1822275609247295316182756465 1366706706935471487137067349)
                ·
                  refine ⟨4004023555475014122471877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 1366706706935471487137067349 4004023555475014122471877)
                  ·
                    refine ⟨750754416651565147963477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4004023555475014122471877 750754416651565147963477)
                    ·
                      rfl

theorem cell23_4386267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 4].length) (baseStart_4386267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386267 prefixEnd_4386267 := by exact prefixLift 4386267
  have htrace : WordTrace (prefixWord ++ tailWord_4386267) baseStart_4386267 baseEnd_4386267 := by
    simpa [prefixWord, tailWord_4386267, baseEnd_4386267] using wordTrace_append hprefix tailTrace_4386267
  have hstable : (prefixWord ++ tailWord_4386267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386267).length < 2 ^ (prefixWord ++ tailWord_4386267).sum := by decide
  have hdescent : baseEnd_4386267 < baseStart_4386267 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386284 : List Nat := [2, 2, 1, 1, 2, 1, 2, 6, 2, 4]
def baseStart_4386284 : Nat := 118140960795 + 4386284 * 2 ^ 59
def prefixEnd_4386284 : Nat := 4983230072969 + 3 ^ 40 * 4386284 * 2
def baseEnd_4386284 : Nat := 750757326375273959125951

theorem tailTrace_4386284 : CollatzResearch.WordTrace tailWord_4386284 prefixEnd_4386284 750757326375273959125951 := by
  unfold tailWord_4386284
  simp only [CollatzResearch.WordTrace]
  refine ⟨79990460220624830256002953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106653946960833107008003937 79990460220624830256002953)
  ·
    refine ⟨59992845165468622692002215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79990460220624830256002953 59992845165468622692002215)
    ·
      refine ⟨89989267748202934038003323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59992845165468622692002215 89989267748202934038003323)
      ·
        refine ⟨134983901622304401057004985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89989267748202934038003323 134983901622304401057004985)
        ·
          refine ⟨101237926216728300792753739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134983901622304401057004985 101237926216728300792753739)
          ·
            refine ⟨151856889325092451189130609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101237926216728300792753739 151856889325092451189130609)
            ·
              refine ⟨113892666993819338391847957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151856889325092451189130609 113892666993819338391847957)
              ·
                refine ⟨5338718765335281487117873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 113892666993819338391847957 5338718765335281487117873)
                ·
                  refine ⟨4004039074001461115338405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5338718765335281487117873 4004039074001461115338405)
                  ·
                    refine ⟨750757326375273959125951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4004039074001461115338405 750757326375273959125951)
                    ·
                      rfl

theorem cell23_4386284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 4].length) (baseStart_4386284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386284 prefixEnd_4386284 := by exact prefixLift 4386284
  have htrace : WordTrace (prefixWord ++ tailWord_4386284) baseStart_4386284 baseEnd_4386284 := by
    simpa [prefixWord, tailWord_4386284, baseEnd_4386284] using wordTrace_append hprefix tailTrace_4386284
  have hstable : (prefixWord ++ tailWord_4386284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386284).length < 2 ^ (prefixWord ++ tailWord_4386284).sum := by decide
  have hdescent : baseEnd_4386284 < baseStart_4386284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386287 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 4]
def baseStart_4386287 : Nat := 118140960795 + 4386287 * 2 ^ 59
def prefixEnd_4386287 : Nat := 4983230072969 + 3 ^ 40 * 4386287 * 2
def baseEnd_4386287 : Nat := 2252273519567785365640339

theorem tailTrace_4386287 : CollatzResearch.WordTrace tailWord_4386287 prefixEnd_4386287 2252273519567785365640339 := by
  unfold tailWord_4386287
  simp only [CollatzResearch.WordTrace]
  refine ⟨159981029860238792024365115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106654019906825861349576743 159981029860238792024365115)
  ·
    refine ⟨239971544790358188036547673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159981029860238792024365115 239971544790358188036547673)
    ·
      refine ⟨179978658592768641027410755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239971544790358188036547673 179978658592768641027410755)
      ·
        refine ⟨269967987889152961541116133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179978658592768641027410755 269967987889152961541116133)
        ·
          refine ⟨50618997729216180288959275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 269967987889152961541116133 50618997729216180288959275)
          ·
            refine ⟨75928496593824270433438913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50618997729216180288959275 75928496593824270433438913)
            ·
              refine ⟨56946372445368202825079185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75928496593824270433438913 56946372445368202825079185)
              ·
                refine ⟨42709779334026152118809389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56946372445368202825079185 42709779334026152118809389)
                ·
                  refine ⟨16016167250259807044553521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42709779334026152118809389 16016167250259807044553521)
                  ·
                    refine ⟨12012125437694855283415141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16016167250259807044553521 12012125437694855283415141)
                    ·
                      refine ⟨2252273519567785365640339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12012125437694855283415141 2252273519567785365640339)
                      ·
                        rfl

theorem cell23_4386287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 3, 2, 4].length) (baseStart_4386287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386287 prefixEnd_4386287 := by exact prefixLift 4386287
  have htrace : WordTrace (prefixWord ++ tailWord_4386287) baseStart_4386287 baseEnd_4386287 := by
    simpa [prefixWord, tailWord_4386287, baseEnd_4386287] using wordTrace_append hprefix tailTrace_4386287
  have hstable : (prefixWord ++ tailWord_4386287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386287).length < 2 ^ (prefixWord ++ tailWord_4386287).sum := by decide
  have hdescent : baseEnd_4386287 < baseStart_4386287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386294 : List Nat := [5, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_4386294 : Nat := 118140960795 + 4386294 * 2 ^ 59
def prefixEnd_4386294 : Nat := 4983230072969 + 3 ^ 40 * 4386294 * 2
def baseEnd_4386294 : Nat := 2252277113932366838252807

theorem tailTrace_4386294 : CollatzResearch.WordTrace tailWord_4386294 prefixEnd_4386294 2252277113932366838252807 := by
  unfold tailWord_4386294
  simp only [CollatzResearch.WordTrace]
  refine ⟨9998830323200839513741871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106654190114142288146579957 9998830323200839513741871)
  ·
    refine ⟨14998245484801259270612807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9998830323200839513741871 14998245484801259270612807)
    ·
      refine ⟨22497368227201888905919211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14998245484801259270612807 22497368227201888905919211)
      ·
        refine ⟨33746052340802833358878817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22497368227201888905919211 33746052340802833358878817)
        ·
          refine ⟨25309539255602125019159113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33746052340802833358878817 25309539255602125019159113)
          ·
            refine ⟨18982154441701593764369335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25309539255602125019159113 18982154441701593764369335)
            ·
              refine ⟨28473231662552390646554003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18982154441701593764369335 28473231662552390646554003)
              ·
                refine ⟨42709847493828585969831005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28473231662552390646554003 42709847493828585969831005)
                ·
                  refine ⟨16016192810185719738686627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42709847493828585969831005 16016192810185719738686627)
                  ·
                    refine ⟨24024289215278579608029941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16016192810185719738686627 24024289215278579608029941)
                    ·
                      refine ⟨2252277113932366838252807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24024289215278579608029941 2252277113932366838252807)
                      ·
                        rfl

theorem cell23_4386294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_4386294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386294 prefixEnd_4386294 := by exact prefixLift 4386294
  have htrace : WordTrace (prefixWord ++ tailWord_4386294) baseStart_4386294 baseEnd_4386294 := by
    simpa [prefixWord, tailWord_4386294, baseEnd_4386294] using wordTrace_append hprefix tailTrace_4386294
  have hstable : (prefixWord ++ tailWord_4386294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386294).length < 2 ^ (prefixWord ++ tailWord_4386294).sum := by decide
  have hdescent : baseEnd_4386294 < baseStart_4386294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386308 : List Nat := [2, 3, 2, 3, 2, 1, 2, 2, 1, 1, 4]
def baseStart_4386308 : Nat := 118140960795 + 4386308 * 2 ^ 59
def prefixEnd_4386308 : Nat := 4983230072969 + 3 ^ 40 * 4386308 * 2
def baseEnd_4386308 : Nat := 2252284302661529783477743

theorem tailTrace_4386308 : CollatzResearch.WordTrace tailWord_4386308 prefixEnd_4386308 2252284302661529783477743 := by
  unfold tailWord_4386308
  simp only [CollatzResearch.WordTrace]
  refine ⟨79990897896581356305439789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106654530528775141740586385 79990897896581356305439789)
  ·
    refine ⟨29996586711218008614539921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 79990897896581356305439789 29996586711218008614539921)
    ·
      refine ⟨22497440033413506460904941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 29996586711218008614539921 22497440033413506460904941)
      ·
        refine ⟨8436540012530064922839353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22497440033413506460904941 8436540012530064922839353)
        ·
          refine ⟨6327405009397548692129515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8436540012530064922839353 6327405009397548692129515)
          ·
            refine ⟨9491107514096323038194273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6327405009397548692129515 9491107514096323038194273)
            ·
              refine ⟨7118330635572242278645705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9491107514096323038194273 7118330635572242278645705)
              ·
                refine ⟨5338747976679181708984279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7118330635572242278645705 5338747976679181708984279)
                ·
                  refine ⟨8008121965018772563476419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5338747976679181708984279 8008121965018772563476419)
                  ·
                    refine ⟨12012182947528158845214629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8008121965018772563476419 12012182947528158845214629)
                    ·
                      refine ⟨2252284302661529783477743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12012182947528158845214629 2252284302661529783477743)
                      ·
                        rfl

theorem cell23_4386308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_4386308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386308 prefixEnd_4386308 := by exact prefixLift 4386308
  have htrace : WordTrace (prefixWord ++ tailWord_4386308) baseStart_4386308 baseEnd_4386308 := by
    simpa [prefixWord, tailWord_4386308, baseEnd_4386308] using wordTrace_append hprefix tailTrace_4386308
  have hstable : (prefixWord ++ tailWord_4386308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386308).length < 2 ^ (prefixWord ++ tailWord_4386308).sum := by decide
  have hdescent : baseEnd_4386308 < baseStart_4386308 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386311 : List Nat := [1, 1, 4, 3, 2, 1, 1, 4, 1, 2, 3]
def baseStart_4386311 : Nat := 118140960795 + 4386311 * 2 ^ 59
def prefixEnd_4386311 : Nat := 4983230072969 + 3 ^ 40 * 4386311 * 2
def baseEnd_4386311 : Nat := 2252285843103493271740229

theorem tailTrace_4386311 : CollatzResearch.WordTrace tailWord_4386311 prefixEnd_4386311 2252285843103493271740229 := by
  unfold tailWord_4386311
  simp only [CollatzResearch.WordTrace]
  refine ⟨159981905212151844123238787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106654603474767896082159191 159981905212151844123238787)
  ·
    refine ⟨239972857818227766184858181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159981905212151844123238787 239972857818227766184858181)
    ·
      refine ⟨44994910840917706159660909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 239972857818227766184858181 44994910840917706159660909)
      ·
        refine ⟨16873091565344139809872841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44994910840917706159660909 16873091565344139809872841)
        ·
          refine ⟨12654818674008104857404631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16873091565344139809872841 12654818674008104857404631)
          ·
            refine ⟨18982228011012157286106947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12654818674008104857404631 18982228011012157286106947)
            ·
              refine ⟨28473342016518235929160421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18982228011012157286106947 28473342016518235929160421)
              ·
                refine ⟨5338751628097169236717579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28473342016518235929160421 5338751628097169236717579)
                ·
                  refine ⟨8008127442145753855076369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5338751628097169236717579 8008127442145753855076369)
                  ·
                    refine ⟨6006095581609315391307277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8008127442145753855076369 6006095581609315391307277)
                    ·
                      refine ⟨2252285843103493271740229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6006095581609315391307277 2252285843103493271740229)
                      ·
                        rfl

theorem cell23_4386311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_4386311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386311 prefixEnd_4386311 := by exact prefixLift 4386311
  have htrace : WordTrace (prefixWord ++ tailWord_4386311) baseStart_4386311 baseEnd_4386311 := by
    simpa [prefixWord, tailWord_4386311, baseEnd_4386311] using wordTrace_append hprefix tailTrace_4386311
  have hstable : (prefixWord ++ tailWord_4386311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386311).length < 2 ^ (prefixWord ++ tailWord_4386311).sum := by decide
  have hdescent : baseEnd_4386311 < baseStart_4386311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386314 : List Nat := [3, 1, 2, 2, 2, 2, 4, 7]
def baseStart_4386314 : Nat := 118140960795 + 4386314 * 2 ^ 59
def prefixEnd_4386314 : Nat := 4983230072969 + 3 ^ 40 * 4386314 * 2
def baseEnd_4386314 : Nat := 83418051242424324444545

theorem tailTrace_4386314 : CollatzResearch.WordTrace tailWord_4386314 prefixEnd_4386314 83418051242424324444545 := by
  unfold tailWord_4386314
  simp only [CollatzResearch.WordTrace]
  refine ⟨39995503657785243908899499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106654676420760650423731997 39995503657785243908899499)
  ·
    refine ⟨59993255486677865863349249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39995503657785243908899499 59993255486677865863349249)
    ·
      refine ⟨44994941615008399397511937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59993255486677865863349249 44994941615008399397511937)
      ·
        refine ⟨33746206211256299548133953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44994941615008399397511937 33746206211256299548133953)
        ·
          refine ⟨25309654658442224661100465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33746206211256299548133953 25309654658442224661100465)
          ·
            refine ⟨18982240993831668495825349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25309654658442224661100465 18982240993831668495825349)
            ·
              refine ⟨3559170186343437842967253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18982240993831668495825349 3559170186343437842967253)
              ·
                refine ⟨83418051242424324444545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3559170186343437842967253 83418051242424324444545)
                ·
                  rfl

theorem cell23_4386314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 7].length) (baseStart_4386314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386314 prefixEnd_4386314 := by exact prefixLift 4386314
  have htrace : WordTrace (prefixWord ++ tailWord_4386314) baseStart_4386314 baseEnd_4386314 := by
    simpa [prefixWord, tailWord_4386314, baseEnd_4386314] using wordTrace_append hprefix tailTrace_4386314
  have hstable : (prefixWord ++ tailWord_4386314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386314).length < 2 ^ (prefixWord ++ tailWord_4386314).sum := by decide
  have hdescent : baseEnd_4386314 < baseStart_4386314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386325 : List Nat := [1, 3, 2, 1, 3, 2, 3, 3, 1, 2, 2]
def baseStart_4386325 : Nat := 118140960795 + 4386325 * 2 ^ 59
def prefixEnd_4386325 : Nat := 4983230072969 + 3 ^ 40 * 4386325 * 2
def baseEnd_4386325 : Nat := 2252293031832656216965165

theorem tailTrace_4386325 : CollatzResearch.WordTrace tailWord_4386325 prefixEnd_4386325 2252293031832656216965165 := by
  unfold tailWord_4386325
  simp only [CollatzResearch.WordTrace]
  refine ⟨159982415834101124514248429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106654943889400749676165619 159982415834101124514248429)
  ·
    refine ⟨59993405937787921692843161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159982415834101124514248429 59993405937787921692843161)
    ·
      refine ⟨44995054453340941269632371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59993405937787921692843161 44995054453340941269632371)
      ·
        refine ⟨67492581680011411904448557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 44995054453340941269632371 67492581680011411904448557)
        ·
          refine ⟨25309718130004279464168209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67492581680011411904448557 25309718130004279464168209)
          ·
            refine ⟨18982288597503209598126157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25309718130004279464168209 18982288597503209598126157)
            ·
              refine ⟨7118358224063703599297309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18982288597503209598126157 7118358224063703599297309)
              ·
                refine ⟨2669384334023888849736491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7118358224063703599297309 2669384334023888849736491)
                ·
                  refine ⟨4004076501035833274604737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2669384334023888849736491 4004076501035833274604737)
                  ·
                    refine ⟨3003057375776874955953553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4004076501035833274604737 3003057375776874955953553)
                    ·
                      refine ⟨2252293031832656216965165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3003057375776874955953553 2252293031832656216965165)
                      ·
                        rfl

theorem cell23_4386325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 3, 3, 1, 2, 2].length) (baseStart_4386325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386325 prefixEnd_4386325 := by exact prefixLift 4386325
  have htrace : WordTrace (prefixWord ++ tailWord_4386325) baseStart_4386325 baseEnd_4386325 := by
    simpa [prefixWord, tailWord_4386325, baseEnd_4386325] using wordTrace_append hprefix tailTrace_4386325
  have hstable : (prefixWord ++ tailWord_4386325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386325).length < 2 ^ (prefixWord ++ tailWord_4386325).sum := by decide
  have hdescent : baseEnd_4386325 < baseStart_4386325 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386341 : List Nat := [1, 3, 1, 2, 2, 1, 1, 6, 2, 1, 3]
def baseStart_4386341 : Nat := 118140960795 + 4386341 * 2 ^ 59
def prefixEnd_4386341 : Nat := 4983230072969 + 3 ^ 40 * 4386341 * 2
def baseEnd_4386341 : Nat := 2252301247523128154365091

theorem tailTrace_4386341 : CollatzResearch.WordTrace tailWord_4386341 prefixEnd_4386341 2252301247523128154365091 := by
  unfold tailWord_4386341
  simp only [CollatzResearch.WordTrace]
  refine ⟨159982999402043159246830877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106655332934695439497887251 159982999402043159246830877)
  ·
    refine ⟨59993624775766184717561579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159982999402043159246830877 59993624775766184717561579)
    ·
      refine ⟨89990437163649277076342369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59993624775766184717561579 89990437163649277076342369)
      ·
        refine ⟨67492827872736957807256777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89990437163649277076342369 67492827872736957807256777)
        ·
          refine ⟨50619620904552718355442583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67492827872736957807256777 50619620904552718355442583)
          ·
            refine ⟨75929431356829077533163875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50619620904552718355442583 75929431356829077533163875)
            ·
              refine ⟨113894147035243616299745813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 75929431356829077533163875 113894147035243616299745813)
              ·
                refine ⟨5338788142277044514050585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 113894147035243616299745813 5338788142277044514050585)
                ·
                  refine ⟨4004091106707783385537939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5338788142277044514050585 4004091106707783385537939)
                  ·
                    refine ⟨6006136660061675078306909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4004091106707783385537939 6006136660061675078306909)
                    ·
                      refine ⟨2252301247523128154365091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6006136660061675078306909 2252301247523128154365091)
                      ·
                        rfl

theorem cell23_4386341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_4386341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386341 prefixEnd_4386341 := by exact prefixLift 4386341
  have htrace : WordTrace (prefixWord ++ tailWord_4386341) baseStart_4386341 baseEnd_4386341 := by
    simpa [prefixWord, tailWord_4386341, baseEnd_4386341] using wordTrace_append hprefix tailTrace_4386341
  have hstable : (prefixWord ++ tailWord_4386341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386341).length < 2 ^ (prefixWord ++ tailWord_4386341).sum := by decide
  have hdescent : baseEnd_4386341 < baseStart_4386341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386421 : List Nat := [1, 3, 4, 2, 1, 2, 1, 2, 7]
def baseStart_4386421 : Nat := 118140960795 + 4386421 * 2 ^ 59
def prefixEnd_4386421 : Nat := 4983230072969 + 3 ^ 40 * 4386421 * 2
def baseEnd_4386421 : Nat := 250260258441720871262747

theorem tailTrace_4386421 : CollatzResearch.WordTrace tailWord_4386421 prefixEnd_4386421 250260258441720871262747 := by
  unfold tailWord_4386421
  simp only [CollatzResearch.WordTrace]
  refine ⟨159985917241753332909743117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106657278161168888606495411 159985917241753332909743117)
  ·
    refine ⟨59994718965657499841153669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159985917241753332909743117 59994718965657499841153669)
    ·
      refine ⟨11249009806060781220216313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59994718965657499841153669 11249009806060781220216313)
      ·
        refine ⟨8436757354545585915162235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11249009806060781220216313 8436757354545585915162235)
        ·
          refine ⟨12655136031818378872743353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8436757354545585915162235 12655136031818378872743353)
          ·
            refine ⟨9491352023863784154557515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12655136031818378872743353 9491352023863784154557515)
            ·
              refine ⟨14237028035795676231836273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9491352023863784154557515 14237028035795676231836273)
              ·
                refine ⟨10677771026846757173877205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14237028035795676231836273 10677771026846757173877205)
                ·
                  refine ⟨250260258441720871262747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10677771026846757173877205 250260258441720871262747)
                  ·
                    rfl

theorem cell23_4386421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 7].length) (baseStart_4386421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386421 prefixEnd_4386421 := by exact prefixLift 4386421
  have htrace : WordTrace (prefixWord ++ tailWord_4386421) baseStart_4386421 baseEnd_4386421 := by
    simpa [prefixWord, tailWord_4386421, baseEnd_4386421] using wordTrace_append hprefix tailTrace_4386421
  have hstable : (prefixWord ++ tailWord_4386421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386421).length < 2 ^ (prefixWord ++ tailWord_4386421).sum := by decide
  have hdescent : baseEnd_4386421 < baseStart_4386421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386538 : List Nat := [3, 1, 3, 1, 1, 1, 2, 4, 3, 1, 3]
def baseStart_4386538 : Nat := 118140960795 + 4386538 * 2 ^ 59
def prefixEnd_4386538 : Nat := 4983230072969 + 3 ^ 40 * 4386538 * 2
def baseEnd_4386538 : Nat := 2252402403212063883601685

theorem tailTrace_4386538 : CollatzResearch.WordTrace tailWord_4386538 prefixEnd_4386538 2252402403212063883601685 := by
  unfold tailWord_4386538
  simp only [CollatzResearch.WordTrace]
  refine ⟨39997546145582365472938067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106660123054886307927834845 39997546145582365472938067)
  ·
    refine ⟨59996319218373548209407101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 39997546145582365472938067 59996319218373548209407101)
    ·
      refine ⟨22498619706890080578527663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59996319218373548209407101 22498619706890080578527663)
      ·
        refine ⟨33747929560335120867791495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22498619706890080578527663 33747929560335120867791495)
        ·
          refine ⟨50621894340502681301687243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33747929560335120867791495 50621894340502681301687243)
          ·
            refine ⟨75932841510754021952530865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50621894340502681301687243 75932841510754021952530865)
            ·
              refine ⟨56949631133065516464398149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75932841510754021952530865 56949631133065516464398149)
              ·
                refine ⟨10678055837449784337074653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56949631133065516464398149 10678055837449784337074653)
                ·
                  refine ⟨4004270939043669126402995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10678055837449784337074653 4004270939043669126402995)
                  ·
                    refine ⟨6006406408565503689604493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4004270939043669126402995 6006406408565503689604493)
                    ·
                      refine ⟨2252402403212063883601685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6006406408565503689604493 2252402403212063883601685)
                      ·
                        rfl

theorem cell23_4386538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_4386538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386538 prefixEnd_4386538 := by exact prefixLift 4386538
  have htrace : WordTrace (prefixWord ++ tailWord_4386538) baseStart_4386538 baseEnd_4386538 := by
    simpa [prefixWord, tailWord_4386538, baseEnd_4386538] using wordTrace_append hprefix tailTrace_4386538
  have hstable : (prefixWord ++ tailWord_4386538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386538).length < 2 ^ (prefixWord ++ tailWord_4386538).sum := by decide
  have hdescent : baseEnd_4386538 < baseStart_4386538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386571 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 4, 4]
def baseStart_4386571 : Nat := 118140960795 + 4386571 * 2 ^ 59
def prefixEnd_4386571 : Nat := 4983230072969 + 3 ^ 40 * 4386571 * 2
def baseEnd_4386571 : Nat := 750806449357887418163011

theorem tailTrace_4386571 : CollatzResearch.WordTrace tailWord_4386571 prefixEnd_4386571 750806449357887418163011 := by
  unfold tailWord_4386571
  simp only [CollatzResearch.WordTrace]
  refine ⟨159991388191209908527703567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106660925460806605685135711 159991388191209908527703567)
  ·
    refine ⟨239987082286814862791555351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159991388191209908527703567 239987082286814862791555351)
    ·
      refine ⟨359980623430222294187333027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239987082286814862791555351 359980623430222294187333027)
      ·
        refine ⟨539970935145333441280999541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 359980623430222294187333027 539970935145333441280999541)
        ·
          refine ⟨50622275169875010120093707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 539970935145333441280999541 50622275169875010120093707)
          ·
            refine ⟨75933412754812515180140561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50622275169875010120093707 75933412754812515180140561)
            ·
              refine ⟨56950059566109386385105421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75933412754812515180140561 56950059566109386385105421)
              ·
                refine ⟨21356272337291019894414533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56950059566109386385105421 21356272337291019894414533)
                ·
                  refine ⟨4004301063242066230202725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21356272337291019894414533 4004301063242066230202725)
                  ·
                    refine ⟨750806449357887418163011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4004301063242066230202725 750806449357887418163011)
                    ·
                      rfl

theorem cell23_4386571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 4].length) (baseStart_4386571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386571 prefixEnd_4386571 := by exact prefixLift 4386571
  have htrace : WordTrace (prefixWord ++ tailWord_4386571) baseStart_4386571 baseEnd_4386571 := by
    simpa [prefixWord, tailWord_4386571, baseEnd_4386571] using wordTrace_append hprefix tailTrace_4386571
  have hstable : (prefixWord ++ tailWord_4386571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386571).length < 2 ^ (prefixWord ++ tailWord_4386571).sum := by decide
  have hdescent : baseEnd_4386571 < baseStart_4386571 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386572 : List Nat := [2, 2, 1, 2, 2, 1, 6, 2, 1, 1, 3]
def baseStart_4386572 : Nat := 118140960795 + 4386572 * 2 ^ 59
def prefixEnd_4386572 : Nat := 4983230072969 + 3 ^ 40 * 4386572 * 2
def baseEnd_4386572 : Nat := 2252419861554316750576529

theorem tailTrace_4386572 : CollatzResearch.WordTrace tailWord_4386572 prefixEnd_4386572 2252419861554316750576529 := by
  unfold tailWord_4386572
  simp only [CollatzResearch.WordTrace]
  refine ⟨79995712332103142849244985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106660949776137523798993313 79995712332103142849244985)
  ·
    refine ⟨59996784249077357136933739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79995712332103142849244985 59996784249077357136933739)
    ·
      refine ⟨89995176373616035705400609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 59996784249077357136933739 89995176373616035705400609)
      ·
        refine ⟨67496382280212026779050457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 89995176373616035705400609 67496382280212026779050457)
        ·
          refine ⟨50622286710159020084287843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67496382280212026779050457 50622286710159020084287843)
          ·
            refine ⟨75933430065238530126431765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50622286710159020084287843 75933430065238530126431765)
            ·
              refine ⟨3559379534308056099676489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 75933430065238530126431765 3559379534308056099676489)
              ·
                refine ⟨2669534650731042074757367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3559379534308056099676489 2669534650731042074757367)
                ·
                  refine ⟨4004301976096563112136051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2669534650731042074757367 4004301976096563112136051)
                  ·
                    refine ⟨6006452964144844668204077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4004301976096563112136051 6006452964144844668204077)
                    ·
                      refine ⟨2252419861554316750576529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6006452964144844668204077 2252419861554316750576529)
                      ·
                        rfl

theorem cell23_4386572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 6, 2, 1, 1, 3].length) (baseStart_4386572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386572 prefixEnd_4386572 := by exact prefixLift 4386572
  have htrace : WordTrace (prefixWord ++ tailWord_4386572) baseStart_4386572 baseEnd_4386572 := by
    simpa [prefixWord, tailWord_4386572, baseEnd_4386572] using wordTrace_append hprefix tailTrace_4386572
  have hstable : (prefixWord ++ tailWord_4386572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386572).length < 2 ^ (prefixWord ++ tailWord_4386572).sum := by decide
  have hdescent : baseEnd_4386572 < baseStart_4386572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386588 : List Nat := [2, 2, 3, 1, 1, 2, 1, 5, 2, 4]
def baseStart_4386588 : Nat := 118140960795 + 4386588 * 2 ^ 59
def prefixEnd_4386588 : Nat := 4983230072969 + 3 ^ 40 * 4386588 * 2
def baseEnd_4386588 : Nat := 750809359081596229325485

theorem tailTrace_4386588 : CollatzResearch.WordTrace tailWord_4386588 prefixEnd_4386588 750809359081596229325485 := by
  unfold tailWord_4386588
  simp only [CollatzResearch.WordTrace]
  refine ⟨79996004116074160215536209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106661338821432213620714945 79996004116074160215536209)
  ·
    refine ⟨59997003087055620161652157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79996004116074160215536209 59997003087055620161652157)
    ·
      refine ⟨22498876157645857560619559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 59997003087055620161652157 22498876157645857560619559)
      ·
        refine ⟨33748314236468786340929339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22498876157645857560619559 33748314236468786340929339)
        ·
          refine ⟨50622471354703179511394009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33748314236468786340929339 50622471354703179511394009)
          ·
            refine ⟨37966853516027384633545507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50622471354703179511394009 37966853516027384633545507)
            ·
              refine ⟨56950280274041076950318261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37966853516027384633545507 56950280274041076950318261)
              ·
                refine ⟨5339088775691350964092337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 56950280274041076950318261 5339088775691350964092337)
                ·
                  refine ⟨4004316581768513223069253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5339088775691350964092337 4004316581768513223069253)
                  ·
                    refine ⟨750809359081596229325485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4004316581768513223069253 750809359081596229325485)
                    ·
                      rfl

theorem cell23_4386588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_4386588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386588 prefixEnd_4386588 := by exact prefixLift 4386588
  have htrace : WordTrace (prefixWord ++ tailWord_4386588) baseStart_4386588 baseEnd_4386588 := by
    simpa [prefixWord, tailWord_4386588, baseEnd_4386588] using wordTrace_append hprefix tailTrace_4386588
  have hstable : (prefixWord ++ tailWord_4386588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386588).length < 2 ^ (prefixWord ++ tailWord_4386588).sum := by decide
  have hdescent : baseEnd_4386588 < baseStart_4386588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386612 : List Nat := [2, 5, 1, 1, 2, 1, 4, 1, 1, 1, 4]
def baseStart_4386612 : Nat := 118140960795 + 4386612 * 2 ^ 59
def prefixEnd_4386612 : Nat := 4983230072969 + 3 ^ 40 * 4386612 * 2
def baseEnd_4386612 : Nat := 2252440400780496594076345

theorem tailTrace_4386612 : CollatzResearch.WordTrace tailWord_4386612 prefixEnd_4386612 2252440400780496594076345 := by
  unfold tailWord_4386612
  simp only [CollatzResearch.WordTrace]
  refine ⟨79996441792030686264973045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106661922389374248353297393 79996441792030686264973045)
  ·
    refine ⟨7499666418002876837341223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 79996441792030686264973045 7499666418002876837341223)
    ·
      refine ⟨11249499627004315256011835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7499666418002876837341223 11249499627004315256011835)
      ·
        refine ⟨16874249440506472884017753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11249499627004315256011835 16874249440506472884017753)
        ·
          refine ⟨12655687080379854663013315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16874249440506472884017753 12655687080379854663013315)
          ·
            refine ⟨18983530620569781994519973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12655687080379854663013315 18983530620569781994519973)
            ·
              refine ⟨3559411991356834123972495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18983530620569781994519973 3559411991356834123972495)
              ·
                refine ⟨5339117987035251185958743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3559411991356834123972495 5339117987035251185958743)
                ·
                  refine ⟨8008676980552876778938115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5339117987035251185958743 8008676980552876778938115)
                  ·
                    refine ⟨12013015470829315168407173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8008676980552876778938115 12013015470829315168407173)
                    ·
                      refine ⟨2252440400780496594076345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12013015470829315168407173 2252440400780496594076345)
                      ·
                        rfl

theorem cell23_4386612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_4386612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386612 prefixEnd_4386612 := by exact prefixLift 4386612
  have htrace : WordTrace (prefixWord ++ tailWord_4386612) baseStart_4386612 baseEnd_4386612 := by
    simpa [prefixWord, tailWord_4386612, baseEnd_4386612] using wordTrace_append hprefix tailTrace_4386612
  have hstable : (prefixWord ++ tailWord_4386612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386612).length < 2 ^ (prefixWord ++ tailWord_4386612).sum := by decide
  have hdescent : baseEnd_4386612 < baseStart_4386612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386622 : List Nat := [4, 2, 1, 2, 2, 3, 1, 2, 2, 4]
def baseStart_4386622 : Nat := 118140960795 + 4386622 * 2 ^ 59
def prefixEnd_4386622 : Nat := 4983230072969 + 3 ^ 40 * 4386622 * 2
def baseEnd_4386622 : Nat := 750815178529013851650433

theorem tailTrace_4386622 : CollatzResearch.WordTrace tailWord_4386622 prefixEnd_4386622 750815178529013851650433 := by
  unfold tailWord_4386622
  simp only [CollatzResearch.WordTrace]
  refine ⟨19999156039253143029726265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106662165542683429491873413 19999156039253143029726265)
  ·
    refine ⟨14999367029439857272294699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19999156039253143029726265 14999367029439857272294699)
    ·
      refine ⟨22499050544159785908442049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14999367029439857272294699 22499050544159785908442049)
      ·
        refine ⟨16874287908119839431331537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22499050544159785908442049 16874287908119839431331537)
        ·
          refine ⟨12655715931089879573498653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16874287908119839431331537 12655715931089879573498653)
          ·
            refine ⟨4745893474158704840061995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12655715931089879573498653 4745893474158704840061995)
            ·
              refine ⟨7118840211238057260092993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4745893474158704840061995 7118840211238057260092993)
              ·
                refine ⟨5339130158428542945069745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7118840211238057260092993 5339130158428542945069745)
                ·
                  refine ⟨4004347618821407208802309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5339130158428542945069745 4004347618821407208802309)
                  ·
                    refine ⟨750815178529013851650433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4004347618821407208802309 750815178529013851650433)
                    ·
                      rfl

theorem cell23_4386622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 2, 4].length) (baseStart_4386622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386622 prefixEnd_4386622 := by exact prefixLift 4386622
  have htrace : WordTrace (prefixWord ++ tailWord_4386622) baseStart_4386622 baseEnd_4386622 := by
    simpa [prefixWord, tailWord_4386622, baseEnd_4386622] using wordTrace_append hprefix tailTrace_4386622
  have hstable : (prefixWord ++ tailWord_4386622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386622).length < 2 ^ (prefixWord ++ tailWord_4386622).sum := by decide
  have hdescent : baseEnd_4386622 < baseStart_4386622 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386645 : List Nat := [1, 3, 2, 2, 2, 4, 1, 1, 1, 3, 3]
def baseStart_4386645 : Nat := 118140960795 + 4386645 * 2 ^ 59
def prefixEnd_4386645 : Nat := 4983230072969 + 3 ^ 40 * 4386645 * 2
def baseEnd_4386645 : Nat := 2252457345642094964963693

theorem tailTrace_4386645 : CollatzResearch.WordTrace tailWord_4386645 prefixEnd_4386645 2252457345642094964963693 := by
  unfold tailWord_4386645
  simp only [CollatzResearch.WordTrace]
  refine ⟨159994087192941819165897389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106662724795294546110598259 159994087192941819165897389)
  ·
    refine ⟨59997782697353182187211521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 159994087192941819165897389 59997782697353182187211521)
    ·
      refine ⟨44998337023014886640408641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 59997782697353182187211521 44998337023014886640408641)
      ·
        refine ⟨33748752767261164980306481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 44998337023014886640408641 33748752767261164980306481)
        ·
          refine ⟨25311564575445873735229861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33748752767261164980306481 25311564575445873735229861)
          ·
            refine ⟨4745918357896101325355599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25311564575445873735229861 4745918357896101325355599)
            ·
              refine ⟨7118877536844151988033399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4745918357896101325355599 7118877536844151988033399)
              ·
                refine ⟨10678316305266227982050099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7118877536844151988033399 10678316305266227982050099)
                ·
                  refine ⟨16017474457899341973075149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10678316305266227982050099 16017474457899341973075149)
                  ·
                    refine ⟨6006552921712253239903181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16017474457899341973075149 6006552921712253239903181)
                    ·
                      refine ⟨2252457345642094964963693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6006552921712253239903181 2252457345642094964963693)
                      ·
                        rfl

theorem cell23_4386645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_4386645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386645 prefixEnd_4386645 := by exact prefixLift 4386645
  have htrace : WordTrace (prefixWord ++ tailWord_4386645) baseStart_4386645 baseEnd_4386645 := by
    simpa [prefixWord, tailWord_4386645, baseEnd_4386645] using wordTrace_append hprefix tailTrace_4386645
  have hstable : (prefixWord ++ tailWord_4386645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386645).length < 2 ^ (prefixWord ++ tailWord_4386645).sum := by decide
  have hdescent : baseEnd_4386645 < baseStart_4386645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386652 : List Nat := [2, 2, 4, 2, 3, 1, 2, 7]
def baseStart_4386652 : Nat := 118140960795 + 4386652 * 2 ^ 59
def prefixEnd_4386652 : Nat := 4983230072969 + 3 ^ 40 * 4386652 * 2
def baseEnd_4386652 : Nat := 83424479259506534725043

theorem tailTrace_4386652 : CollatzResearch.WordTrace tailWord_4386652 prefixEnd_4386652 83424479259506534725043 := by
  unfold tailWord_4386652
  simp only [CollatzResearch.WordTrace]
  refine ⟨79997171251958229680701105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106662895002610972907601473 79997171251958229680701105)
  ·
    refine ⟨59997878438968672260525829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 79997171251958229680701105 59997878438968672260525829)
    ·
      refine ⟨11249602207306626048848593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 59997878438968672260525829 11249602207306626048848593)
      ·
        refine ⟨8437201655479969536636445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11249602207306626048848593 8437201655479969536636445)
        ·
          refine ⟨3163950620804988576238667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8437201655479969536636445 3163950620804988576238667)
          ·
            refine ⟨4745925931207482864358001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3163950620804988576238667 4745925931207482864358001)
            ·
              refine ⟨3559444448405612148268501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4745925931207482864358001 3559444448405612148268501)
              ·
                refine ⟨83424479259506534725043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3559444448405612148268501 83424479259506534725043)
                ·
                  rfl

theorem cell23_4386652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 7].length) (baseStart_4386652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386652 prefixEnd_4386652 := by exact prefixLift 4386652
  have htrace : WordTrace (prefixWord ++ tailWord_4386652) baseStart_4386652 baseEnd_4386652 := by
    simpa [prefixWord, tailWord_4386652, baseEnd_4386652] using wordTrace_append hprefix tailTrace_4386652
  have hstable : (prefixWord ++ tailWord_4386652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386652).length < 2 ^ (prefixWord ++ tailWord_4386652).sum := by decide
  have hdescent : baseEnd_4386652 < baseStart_4386652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386655 : List Nat := [1, 1, 2, 3, 1, 4, 1, 4, 1, 3, 2]
def baseStart_4386655 : Nat := 118140960795 + 4386655 * 2 ^ 59
def prefixEnd_4386655 : Nat := 4983230072969 + 3 ^ 40 * 4386655 * 2
def baseEnd_4386655 : Nat := 2252462480448639925838647

theorem tailTrace_4386655 : CollatzResearch.WordTrace tailWord_4386655 prefixEnd_4386655 2252462480448639925838647 := by
  unfold tailWord_4386655
  simp only [CollatzResearch.WordTrace]
  refine ⟨159994451922905590873761419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106662967948603727249174279 159994451922905590873761419)
  ·
    refine ⟨239991677884358386310642129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159994451922905590873761419 239991677884358386310642129)
    ·
      refine ⟨179993758413268789732981597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239991677884358386310642129 179993758413268789732981597)
      ·
        refine ⟨67497659404975796149868099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 179993758413268789732981597 67497659404975796149868099)
        ·
          refine ⟨101246489107463694224802149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67497659404975796149868099 101246489107463694224802149)
          ·
            refine ⟨18983716707649442667150403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101246489107463694224802149 18983716707649442667150403)
            ·
              refine ⟨28475575061474164000725605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18983716707649442667150403 28475575061474164000725605)
              ·
                refine ⟨5339170324026405750136051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28475575061474164000725605 5339170324026405750136051)
                ·
                  refine ⟨8008755486039608625204077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5339170324026405750136051 8008755486039608625204077)
                  ·
                    refine ⟨3003283307264853234451529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8008755486039608625204077 3003283307264853234451529)
                    ·
                      refine ⟨2252462480448639925838647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3003283307264853234451529 2252462480448639925838647)
                      ·
                        rfl

theorem cell23_4386655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 3, 2].length) (baseStart_4386655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386655 prefixEnd_4386655 := by exact prefixLift 4386655
  have htrace : WordTrace (prefixWord ++ tailWord_4386655) baseStart_4386655 baseEnd_4386655 := by
    simpa [prefixWord, tailWord_4386655, baseEnd_4386655] using wordTrace_append hprefix tailTrace_4386655
  have hstable : (prefixWord ++ tailWord_4386655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386655).length < 2 ^ (prefixWord ++ tailWord_4386655).sum := by decide
  have hdescent : baseEnd_4386655 < baseStart_4386655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386658 : List Nat := [3, 3, 2, 1, 2, 1, 1, 1, 2, 2, 5]
def baseStart_4386658 : Nat := 118140960795 + 4386658 * 2 ^ 59
def prefixEnd_4386658 : Nat := 4983230072969 + 3 ^ 40 * 4386658 * 2
def baseEnd_4386658 : Nat := 2252464020890603414101133

theorem tailTrace_4386658 : CollatzResearch.WordTrace tailWord_4386658 prefixEnd_4386658 2252464020890603414101133 := by
  unfold tailWord_4386658
  simp only [CollatzResearch.WordTrace]
  refine ⟨39998640335473680596530157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106663040894596481590747085 39998640335473680596530157)
  ·
    refine ⟨14999490125802630223698809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 39998640335473680596530157 14999490125802630223698809)
    ·
      refine ⟨11249617594351972667774107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14999490125802630223698809 11249617594351972667774107)
      ·
        refine ⟨16874426391527959001661161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11249617594351972667774107 16874426391527959001661161)
        ·
          refine ⟨12655819793645969251245871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16874426391527959001661161 12655819793645969251245871)
          ·
            refine ⟨18983729690468953876868807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12655819793645969251245871 18983729690468953876868807)
            ·
              refine ⟨28475594535703430815303211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18983729690468953876868807 28475594535703430815303211)
              ·
                refine ⟨42713391803555146222954817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28475594535703430815303211 42713391803555146222954817)
                ·
                  refine ⟨32035043852666359667216113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42713391803555146222954817 32035043852666359667216113)
                  ·
                    refine ⟨24026282889499769750412085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32035043852666359667216113 24026282889499769750412085)
                    ·
                      refine ⟨2252464020890603414101133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24026282889499769750412085 2252464020890603414101133)
                      ·
                        rfl

theorem cell23_4386658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_4386658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386658 prefixEnd_4386658 := by exact prefixLift 4386658
  have htrace : WordTrace (prefixWord ++ tailWord_4386658) baseStart_4386658 baseEnd_4386658 := by
    simpa [prefixWord, tailWord_4386658, baseEnd_4386658] using wordTrace_append hprefix tailTrace_4386658
  have hstable : (prefixWord ++ tailWord_4386658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386658).length < 2 ^ (prefixWord ++ tailWord_4386658).sum := by decide
  have hdescent : baseEnd_4386658 < baseStart_4386658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386671 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 3]
def baseStart_4386671 : Nat := 118140960795 + 4386671 * 2 ^ 59
def prefixEnd_4386671 : Nat := 4983230072969 + 3 ^ 40 * 4386671 * 2
def baseEnd_4386671 : Nat := 2252470696139111863238573

theorem tailTrace_4386671 : CollatzResearch.WordTrace tailWord_4386671 prefixEnd_4386671 2252470696139111863238573 := by
  unfold tailWord_4386671
  simp only [CollatzResearch.WordTrace]
  refine ⟨159995035490847625606343867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106663356993898417070895911 159995035490847625606343867)
  ·
    refine ⟨239992553236271438409515801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 159995035490847625606343867 239992553236271438409515801)
    ·
      refine ⟨179994414927203578807136851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 239992553236271438409515801 179994414927203578807136851)
      ·
        refine ⟨269991622390805368210705277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179994414927203578807136851 269991622390805368210705277)
        ·
          refine ⟨101246858396552013079014479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 269991622390805368210705277 101246858396552013079014479)
          ·
            refine ⟨151870287594828019618521719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101246858396552013079014479 151870287594828019618521719)
            ·
              refine ⟨227805431392242029427782579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151870287594828019618521719 227805431392242029427782579)
              ·
                refine ⟨341708147088363044141673869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227805431392242029427782579 341708147088363044141673869)
                ·
                  refine ⟨128140555158136141553127701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 341708147088363044141673869 128140555158136141553127701)
                  ·
                    refine ⟨6006588523037631635302861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 128140555158136141553127701 6006588523037631635302861)
                    ·
                      refine ⟨2252470696139111863238573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6006588523037631635302861 2252470696139111863238573)
                      ·
                        rfl

theorem cell23_4386671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 3, 6, 3].length) (baseStart_4386671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386671 prefixEnd_4386671 := by exact prefixLift 4386671
  have htrace : WordTrace (prefixWord ++ tailWord_4386671) baseStart_4386671 baseEnd_4386671 := by
    simpa [prefixWord, tailWord_4386671, baseEnd_4386671] using wordTrace_append hprefix tailTrace_4386671
  have hstable : (prefixWord ++ tailWord_4386671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386671).length < 2 ^ (prefixWord ++ tailWord_4386671).sum := by decide
  have hdescent : baseEnd_4386671 < baseStart_4386671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386696 : List Nat := [2, 1, 3, 3, 4, 1, 2, 1, 2, 1, 3]
def baseStart_4386696 : Nat := 118140960795 + 4386696 * 2 ^ 59
def prefixEnd_4386696 : Nat := 4983230072969 + 3 ^ 40 * 4386696 * 2
def baseEnd_4386696 : Nat := 2252483533155474265425959

theorem tailTrace_4386696 : CollatzResearch.WordTrace tailWord_4386696 prefixEnd_4386696 2252483533155474265425959 := by
  unfold tailWord_4386696
  simp only [CollatzResearch.WordTrace]
  refine ⟨79997973657878527438001971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106663964877171369917335961 79997973657878527438001971)
  ·
    refine ⟨119996960486817791157002957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79997973657878527438001971 119996960486817791157002957)
    ·
      refine ⟨44998860182556671683876109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 119996960486817791157002957 44998860182556671683876109)
      ·
        refine ⟨16874572568458751881453541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 44998860182556671683876109 16874572568458751881453541)
        ·
          refine ⟨3163982356586015977772539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16874572568458751881453541 3163982356586015977772539)
          ·
            refine ⟨4745973534879023966658809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3163982356586015977772539 4745973534879023966658809)
            ·
              refine ⟨3559480151159267974994107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4745973534879023966658809 3559480151159267974994107)
              ·
                refine ⟨5339220226738901962491161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3559480151159267974994107 5339220226738901962491161)
                ·
                  refine ⟨4004415170054176471868371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5339220226738901962491161 4004415170054176471868371)
                  ·
                    refine ⟨6006622755081264707802557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4004415170054176471868371 6006622755081264707802557)
                    ·
                      refine ⟨2252483533155474265425959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6006622755081264707802557 2252483533155474265425959)
                      ·
                        rfl

theorem cell23_4386696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_4386696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386696 prefixEnd_4386696 := by exact prefixLift 4386696
  have htrace : WordTrace (prefixWord ++ tailWord_4386696) baseStart_4386696 baseEnd_4386696 := by
    simpa [prefixWord, tailWord_4386696, baseEnd_4386696] using wordTrace_append hprefix tailTrace_4386696
  have hstable : (prefixWord ++ tailWord_4386696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386696).length < 2 ^ (prefixWord ++ tailWord_4386696).sum := by decide
  have hdescent : baseEnd_4386696 < baseStart_4386696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386761 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 1, 5, 5]
def baseStart_4386761 : Nat := 118140960795 + 4386761 * 2 ^ 59
def prefixEnd_4386761 : Nat := 4983230072969 + 3 ^ 40 * 4386761 * 2
def baseEnd_4386761 : Nat := 2252516909398016511113159

theorem tailTrace_4386761 : CollatzResearch.WordTrace tailWord_4386761 prefixEnd_4386761 2252516909398016511113159 := by
  unfold tailWord_4386761
  simp only [CollatzResearch.WordTrace]
  refine ⟨159998318060521570977120137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106665545373681047318080091 159998318060521570977120137)
  ·
    refine ⟨119998738545391178232840103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 159998318060521570977120137 119998738545391178232840103)
    ·
      refine ⟨179998107818086767349260155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119998738545391178232840103 179998107818086767349260155)
      ·
        refine ⟨269997161727130151023890233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179998107818086767349260155 269997161727130151023890233)
        ·
          refine ⟨202497871295347613267917675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269997161727130151023890233 202497871295347613267917675)
          ·
            refine ⟨303746806943021419901876513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202497871295347613267917675 303746806943021419901876513)
            ·
              refine ⟨227810105207266064926407385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303746806943021419901876513 227810105207266064926407385)
              ·
                refine ⟨170857578905449548694805539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227810105207266064926407385 170857578905449548694805539)
                ·
                  refine ⟨256286368358174323042208309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170857578905449548694805539 256286368358174323042208309)
                  ·
                    refine ⟨24026847033578842785207029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 256286368358174323042208309 24026847033578842785207029)
                    ·
                      refine ⟨2252516909398016511113159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24026847033578842785207029 2252516909398016511113159)
                      ·
                        rfl

theorem cell23_4386761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_4386761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386761 prefixEnd_4386761 := by exact prefixLift 4386761
  have htrace : WordTrace (prefixWord ++ tailWord_4386761) baseStart_4386761 baseEnd_4386761 := by
    simpa [prefixWord, tailWord_4386761, baseEnd_4386761] using wordTrace_append hprefix tailTrace_4386761
  have hstable : (prefixWord ++ tailWord_4386761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386761).length < 2 ^ (prefixWord ++ tailWord_4386761).sum := by decide
  have hdescent : baseEnd_4386761 < baseStart_4386761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386768 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 5, 4]
def baseStart_4386768 : Nat := 118140960795 + 4386768 * 2 ^ 59
def prefixEnd_4386768 : Nat := 4983230072969 + 3 ^ 40 * 4386768 * 2
def baseEnd_4386768 : Nat := 750840167920865994575209

theorem tailTrace_4386768 : CollatzResearch.WordTrace tailWord_4386768 prefixEnd_4386768 750840167920865994575209 := by
  unfold tailWord_4386768
  simp only [CollatzResearch.WordTrace]
  refine ⟨79999286685748105586312479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106665715580997474115083305 79999286685748105586312479)
  ·
    refine ⟨119998930028622158379468719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 79999286685748105586312479 119998930028622158379468719)
    ·
      refine ⟨179998395042933237569203079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119998930028622158379468719 179998395042933237569203079)
      ·
        refine ⟨269997592564399856353804619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 179998395042933237569203079 269997592564399856353804619)
        ·
          refine ⟨404996388846599784530706929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269997592564399856353804619 404996388846599784530706929)
          ·
            refine ⟨303747291634949838398030197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 404996388846599784530706929 303747291634949838398030197)
            ·
              refine ⟨28476308590776547349815331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 303747291634949838398030197 28476308590776547349815331)
              ·
                refine ⟨42714462886164821024722997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28476308590776547349815331 42714462886164821024722997)
                ·
                  refine ⟨4004480895577951971067781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42714462886164821024722997 4004480895577951971067781)
                  ·
                    refine ⟨750840167920865994575209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4004480895577951971067781 750840167920865994575209)
                    ·
                      rfl

theorem cell23_4386768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 5, 4].length) (baseStart_4386768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386768 prefixEnd_4386768 := by exact prefixLift 4386768
  have htrace : WordTrace (prefixWord ++ tailWord_4386768) baseStart_4386768 baseEnd_4386768 := by
    simpa [prefixWord, tailWord_4386768, baseEnd_4386768] using wordTrace_append hprefix tailTrace_4386768
  have hstable : (prefixWord ++ tailWord_4386768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386768).length < 2 ^ (prefixWord ++ tailWord_4386768).sum := by decide
  have hdescent : baseEnd_4386768 < baseStart_4386768 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386835 : List Nat := [1, 1, 1, 2, 1, 4, 4, 1, 1, 5, 2]
def baseStart_4386835 : Nat := 118140960795 + 4386835 * 2 ^ 59
def prefixEnd_4386835 : Nat := 4983230072969 + 3 ^ 40 * 4386835 * 2
def baseEnd_4386835 : Nat := 2252554906966449221587819

theorem tailTrace_4386835 : CollatzResearch.WordTrace tailWord_4386835 prefixEnd_4386835 2252554906966449221587819 := by
  unfold tailWord_4386835
  simp only [CollatzResearch.WordTrace]
  refine ⟨160001017062253481615313959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106667344708168987743542639 160001017062253481615313959)
  ·
    refine ⟨240001525593380222422970939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160001017062253481615313959 240001525593380222422970939)
    ·
      refine ⟨360002288390070333634456409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240001525593380222422970939 360002288390070333634456409)
      ·
        refine ⟨270001716292552750225842307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 360002288390070333634456409 270001716292552750225842307)
        ·
          refine ⟨405002574438829125338763461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270001716292552750225842307 405002574438829125338763461)
          ·
            refine ⟨75937982707280461001018149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 405002574438829125338763461 75937982707280461001018149)
            ·
              refine ⟨14238371757615086437690903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 75937982707280461001018149 14238371757615086437690903)
              ·
                refine ⟨21357557636422629656536355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14238371757615086437690903 21357557636422629656536355)
                ·
                  refine ⟨32036336454633944484804533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21357557636422629656536355 32036336454633944484804533)
                  ·
                    refine ⟨3003406542621932295450425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32036336454633944484804533 3003406542621932295450425)
                    ·
                      refine ⟨2252554906966449221587819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3003406542621932295450425 2252554906966449221587819)
                      ·
                        rfl

theorem cell23_4386835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 5, 2].length) (baseStart_4386835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386835 prefixEnd_4386835 := by exact prefixLift 4386835
  have htrace : WordTrace (prefixWord ++ tailWord_4386835) baseStart_4386835 baseEnd_4386835 := by
    simpa [prefixWord, tailWord_4386835, baseEnd_4386835] using wordTrace_append hprefix tailTrace_4386835
  have hstable : (prefixWord ++ tailWord_4386835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386835).length < 2 ^ (prefixWord ++ tailWord_4386835).sum := by decide
  have hdescent : baseEnd_4386835 < baseStart_4386835 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386875 : List Nat := [1, 1, 1, 1, 1, 2, 1, 9, 2, 4]
def baseStart_4386875 : Nat := 118140960795 + 4386875 * 2 ^ 59
def prefixEnd_4386875 : Nat := 4983230072969 + 3 ^ 40 * 4386875 * 2
def baseEnd_4386875 : Nat := 750858482064209688362545

theorem tailTrace_4386875 : CollatzResearch.WordTrace tailWord_4386875 prefixEnd_4386875 750858482064209688362545 := by
  unfold tailWord_4386875
  simp only [CollatzResearch.WordTrace]
  refine ⟨160002475982108568446770079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106668317321405712297846719 160002475982108568446770079)
  ·
    refine ⟨240003713973162852670155119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160002475982108568446770079 240003713973162852670155119)
    ·
      refine ⟨360005570959744279005232679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240003713973162852670155119 360005570959744279005232679)
      ·
        refine ⟨540008356439616418507849019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360005570959744279005232679 540008356439616418507849019)
        ·
          refine ⟨810012534659424627761773529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540008356439616418507849019 810012534659424627761773529)
          ·
            refine ⟨607509400994568470821330147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 810012534659424627761773529 607509400994568470821330147)
            ·
              refine ⟨911264101491852706231995221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 607509400994568470821330147 911264101491852706231995221)
              ·
                refine ⟨5339438094678824450578097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 911264101491852706231995221 5339438094678824450578097)
                ·
                  refine ⟨4004578571009118337933573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5339438094678824450578097 4004578571009118337933573)
                  ·
                    refine ⟨750858482064209688362545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4004578571009118337933573 750858482064209688362545)
                    ·
                      rfl

theorem cell23_4386875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 4].length) (baseStart_4386875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386875 prefixEnd_4386875 := by exact prefixLift 4386875
  have htrace : WordTrace (prefixWord ++ tailWord_4386875) baseStart_4386875 baseEnd_4386875 := by
    simpa [prefixWord, tailWord_4386875, baseEnd_4386875] using wordTrace_append hprefix tailTrace_4386875
  have hstable : (prefixWord ++ tailWord_4386875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386875).length < 2 ^ (prefixWord ++ tailWord_4386875).sum := by decide
  have hdescent : baseEnd_4386875 < baseStart_4386875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386886 : List Nat := [6, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2]
def baseStart_4386886 : Nat := 118140960795 + 4386886 * 2 ^ 59
def prefixEnd_4386886 : Nat := 4983230072969 + 3 ^ 40 * 4386886 * 2
def baseEnd_4386886 : Nat := 2252581094479828522050085

theorem tailTrace_4386886 : CollatzResearch.WordTrace tailWord_4386886 prefixEnd_4386886 2252581094479828522050085 := by
  unfold tailWord_4386886
  simp only [CollatzResearch.WordTrace]
  refine ⟨5000089912033397416419391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 106668584790045811550280341 5000089912033397416419391)
  ·
    refine ⟨7500134868050096124629087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5000089912033397416419391 7500134868050096124629087)
    ·
      refine ⟨11250202302075144186943631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7500134868050096124629087 11250202302075144186943631)
      ·
        refine ⟨16875303453112716280415447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11250202302075144186943631 16875303453112716280415447)
        ·
          refine ⟨25312955179669074420623171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16875303453112716280415447 25312955179669074420623171)
          ·
            refine ⟨37969432769503611630934757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25312955179669074420623171 37969432769503611630934757)
            ·
              refine ⟨7119268644281927180800267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 37969432769503611630934757 7119268644281927180800267)
              ·
                refine ⟨10678902966422890771200401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7119268644281927180800267 10678902966422890771200401)
                ·
                  refine ⟨8009177224817168078400301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10678902966422890771200401 8009177224817168078400301)
                  ·
                    refine ⟨3003441459306438029400113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8009177224817168078400301 3003441459306438029400113)
                    ·
                      refine ⟨2252581094479828522050085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3003441459306438029400113 2252581094479828522050085)
                      ·
                        rfl

theorem cell23_4386886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2].length) (baseStart_4386886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386886 prefixEnd_4386886 := by exact prefixLift 4386886
  have htrace : WordTrace (prefixWord ++ tailWord_4386886) baseStart_4386886 baseEnd_4386886 := by
    simpa [prefixWord, tailWord_4386886, baseEnd_4386886] using wordTrace_append hprefix tailTrace_4386886
  have hstable : (prefixWord ++ tailWord_4386886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386886).length < 2 ^ (prefixWord ++ tailWord_4386886).sum := by decide
  have hdescent : baseEnd_4386886 < baseStart_4386886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386909 : List Nat := [1, 4, 4, 1, 1, 1, 1, 4, 2, 4]
def baseStart_4386909 : Nat := 118140960795 + 4386909 * 2 ^ 59
def prefixEnd_4386909 : Nat := 4983230072969 + 3 ^ 40 * 4386909 * 2
def baseEnd_4386909 : Nat := 750864301511627310687493

theorem tailTrace_4386909 : CollatzResearch.WordTrace tailWord_4386909 prefixEnd_4386909 750864301511627310687493 := by
  unfold tailWord_4386909
  simp only [CollatzResearch.WordTrace]
  refine ⟨160003716063985392253507781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106669144042656928169005187 160003716063985392253507781)
  ·
    refine ⟨30000696761997261047532709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160003716063985392253507781 30000696761997261047532709)
    ·
      refine ⟨5625130642874486446412383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30000696761997261047532709 5625130642874486446412383)
      ·
        refine ⟨8437695964311729669618575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5625130642874486446412383 8437695964311729669618575)
        ·
          refine ⟨12656543946467594504427863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8437695964311729669618575 12656543946467594504427863)
          ·
            refine ⟨18984815919701391756641795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12656543946467594504427863 18984815919701391756641795)
            ·
              refine ⟨28477223879552087634962693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18984815919701391756641795 28477223879552087634962693)
              ·
                refine ⟨5339479477416016431555505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28477223879552087634962693 5339479477416016431555505)
                ·
                  refine ⟨4004609608062012323666629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5339479477416016431555505 4004609608062012323666629)
                  ·
                    refine ⟨750864301511627310687493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4004609608062012323666629 750864301511627310687493)
                    ·
                      rfl

theorem cell23_4386909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_4386909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386909 prefixEnd_4386909 := by exact prefixLift 4386909
  have htrace : WordTrace (prefixWord ++ tailWord_4386909) baseStart_4386909 baseEnd_4386909 := by
    simpa [prefixWord, tailWord_4386909, baseEnd_4386909] using wordTrace_append hprefix tailTrace_4386909
  have hstable : (prefixWord ++ tailWord_4386909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386909).length < 2 ^ (prefixWord ++ tailWord_4386909).sum := by decide
  have hdescent : baseEnd_4386909 < baseStart_4386909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386910 : List Nat := [4, 4, 1, 1, 2, 1, 1, 4, 1, 1, 3]
def baseStart_4386910 : Nat := 118140960795 + 4386910 * 2 ^ 59
def prefixEnd_4386910 : Nat := 4983230072969 + 3 ^ 40 * 4386910 * 2
def baseEnd_4386910 : Nat := 2252593418015536428149975

theorem tailTrace_4386910 : CollatzResearch.WordTrace tailWord_4386910 prefixEnd_4386910 2252593418015536428149975 := by
  unfold tailWord_4386910
  simp only [CollatzResearch.WordTrace]
  refine ⟨20000469067122721178036773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106669168357987846282862789 20000469067122721178036773)
  ·
    refine ⟨3750087950085510220881895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20000469067122721178036773 3750087950085510220881895)
    ·
      refine ⟨5625131925128265331322843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3750087950085510220881895 5625131925128265331322843)
      ·
        refine ⟨8437697887692397996984265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5625131925128265331322843 8437697887692397996984265)
        ·
          refine ⟨6328273415769298497738199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8437697887692397996984265 6328273415769298497738199)
          ·
            refine ⟨9492410123653947746607299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6328273415769298497738199 9492410123653947746607299)
            ·
              refine ⟨14238615185480921619910949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9492410123653947746607299 14238615185480921619910949)
              ·
                refine ⟨2669740347277672803733303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14238615185480921619910949 2669740347277672803733303)
                ·
                  refine ⟨4004610520916509205599955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2669740347277672803733303 4004610520916509205599955)
                  ·
                    refine ⟨6006915781374763808399933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4004610520916509205599955 6006915781374763808399933)
                    ·
                      refine ⟨2252593418015536428149975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6006915781374763808399933 2252593418015536428149975)
                      ·
                        rfl

theorem cell23_4386910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_4386910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386910 prefixEnd_4386910 := by exact prefixLift 4386910
  have htrace : WordTrace (prefixWord ++ tailWord_4386910) baseStart_4386910 baseEnd_4386910 := by
    simpa [prefixWord, tailWord_4386910, baseEnd_4386910] using wordTrace_append hprefix tailTrace_4386910
  have hstable : (prefixWord ++ tailWord_4386910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386910).length < 2 ^ (prefixWord ++ tailWord_4386910).sum := by decide
  have hdescent : baseEnd_4386910 < baseStart_4386910 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386922 : List Nat := [3, 1, 3, 2, 3, 2, 1, 8]
def baseStart_4386922 : Nat := 118140960795 + 4386922 * 2 ^ 59
def prefixEnd_4386922 : Nat := 4983230072969 + 3 ^ 40 * 4386922 * 2
def baseEnd_4386922 : Nat := 83429614066051495599997

theorem tailTrace_4386922 : CollatzResearch.WordTrace tailWord_4386922 prefixEnd_4386922 83429614066051495599997 := by
  unfold tailWord_4386922
  simp only [CollatzResearch.WordTrace]
  refine ⟨40001047553234573868432755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 106669460141958863649154013 40001047553234573868432755)
  ·
    refine ⟨60001571329851860802649133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40001047553234573868432755 60001571329851860802649133)
    ·
      refine ⟨22500589248694447800993425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60001571329851860802649133 22500589248694447800993425)
      ·
        refine ⟨16875441936520835850745069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22500589248694447800993425 16875441936520835850745069)
        ·
          refine ⟨6328290726195313444029401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16875441936520835850745069 6328290726195313444029401)
          ·
            refine ⟨4746218044646485083022051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6328290726195313444029401 4746218044646485083022051)
            ·
              refine ⟨7119327066969727624533077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4746218044646485083022051 7119327066969727624533077)
              ·
                refine ⟨83429614066051495599997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7119327066969727624533077 83429614066051495599997)
                ·
                  rfl

theorem cell23_4386922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 8].length) (baseStart_4386922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386922 prefixEnd_4386922 := by exact prefixLift 4386922
  have htrace : WordTrace (prefixWord ++ tailWord_4386922) baseStart_4386922 baseEnd_4386922 := by
    simpa [prefixWord, tailWord_4386922, baseEnd_4386922] using wordTrace_append hprefix tailTrace_4386922
  have hstable : (prefixWord ++ tailWord_4386922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386922).length < 2 ^ (prefixWord ++ tailWord_4386922).sum := by decide
  have hdescent : baseEnd_4386922 < baseStart_4386922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4386983 : List Nat := [1, 1, 6, 2, 2, 1, 3, 1, 2, 1, 3]
def baseStart_4386983 : Nat := 118140960795 + 4386983 * 2 ^ 59
def prefixEnd_4386983 : Nat := 4983230072969 + 3 ^ 40 * 4386983 * 2
def baseEnd_4386983 : Nat := 2252630902103314642537139

theorem tailTrace_4386983 : CollatzResearch.WordTrace tailWord_4386983 prefixEnd_4386983 2252630902103314642537139 := by
  unfold tailWord_4386983
  simp only [CollatzResearch.WordTrace]
  refine ⟨160006415065717302891701603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106670943377144868594467735 160006415065717302891701603)
  ·
    refine ⟨240009622598575954337552405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160006415065717302891701603 240009622598575954337552405)
    ·
      refine ⟨11250451059308247859572769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 240009622598575954337552405 11250451059308247859572769)
      ·
        refine ⟨8437838294481185894679577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11250451059308247859572769 8437838294481185894679577)
        ·
          refine ⟨6328378720860889421009683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8437838294481185894679577 6328378720860889421009683)
          ·
            refine ⟨9492568081291334131514525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6328378720860889421009683 9492568081291334131514525)
            ·
              refine ⟨3559713030484250299317947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9492568081291334131514525 3559713030484250299317947)
              ·
                refine ⟨5339569545726375448976921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3559713030484250299317947 5339569545726375448976921)
                ·
                  refine ⟨4004677159294781586732691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5339569545726375448976921 4004677159294781586732691)
                  ·
                    refine ⟨6007015738942172380099037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4004677159294781586732691 6007015738942172380099037)
                    ·
                      refine ⟨2252630902103314642537139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6007015738942172380099037 2252630902103314642537139)
                      ·
                        rfl

theorem cell23_4386983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_4386983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4386983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4386983 prefixEnd_4386983 := by exact prefixLift 4386983
  have htrace : WordTrace (prefixWord ++ tailWord_4386983) baseStart_4386983 baseEnd_4386983 := by
    simpa [prefixWord, tailWord_4386983, baseEnd_4386983] using wordTrace_append hprefix tailTrace_4386983
  have hstable : (prefixWord ++ tailWord_4386983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4386983).length < 2 ^ (prefixWord ++ tailWord_4386983).sum := by decide
  have hdescent : baseEnd_4386983 < baseStart_4386983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4386983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387009 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_4387009 : Nat := 118140960795 + 4387009 * 2 ^ 59
def prefixEnd_4387009 : Nat := 4983230072969 + 3 ^ 40 * 4387009 * 2
def baseEnd_4387009 : Nat := 2252644252600331540812019

theorem tailTrace_4387009 : CollatzResearch.WordTrace tailWord_4387009 prefixEnd_4387009 2252644252600331540812019 := by
  unfold tailWord_4387009
  simp only [CollatzResearch.WordTrace]
  refine ⟨160007363363623109332148081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106671575575748739554765387 160007363363623109332148081)
  ·
    refine ⟨120005522522717331999111061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160007363363623109332148081 120005522522717331999111061)
    ·
      refine ⟨5625258868252374937458331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 120005522522717331999111061 5625258868252374937458331)
      ·
        refine ⟨8437888302378562406187497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5625258868252374937458331 8437888302378562406187497)
        ·
          refine ⟨6328416226783921804640623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8437888302378562406187497 6328416226783921804640623)
          ·
            refine ⟨9492624340175882706960935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6328416226783921804640623 9492624340175882706960935)
            ·
              refine ⟨14238936510263824060441403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9492624340175882706960935 14238936510263824060441403)
              ·
                refine ⟨21358404765395736090662105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14238936510263824060441403 21358404765395736090662105)
                ·
                  refine ⟨16018803574046802067996579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21358404765395736090662105 16018803574046802067996579)
                  ·
                    refine ⟨24028205361070203101994869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16018803574046802067996579 24028205361070203101994869)
                    ·
                      refine ⟨2252644252600331540812019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24028205361070203101994869 2252644252600331540812019)
                      ·
                        rfl

theorem cell23_4387009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_4387009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387009 prefixEnd_4387009 := by exact prefixLift 4387009
  have htrace : WordTrace (prefixWord ++ tailWord_4387009) baseStart_4387009 baseEnd_4387009 := by
    simpa [prefixWord, tailWord_4387009, baseEnd_4387009] using wordTrace_append hprefix tailTrace_4387009
  have hstable : (prefixWord ++ tailWord_4387009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387009).length < 2 ^ (prefixWord ++ tailWord_4387009).sum := by decide
  have hdescent : baseEnd_4387009 < baseStart_4387009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387025 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 4, 5]
def baseStart_4387025 : Nat := 118140960795 + 4387025 * 2 ^ 59
def prefixEnd_4387025 : Nat := 4983230072969 + 3 ^ 40 * 4387025 * 2
def baseEnd_4387025 : Nat := 750884156096934492737315

theorem tailTrace_4387025 : CollatzResearch.WordTrace tailWord_4387025 prefixEnd_4387025 750884156096934492737315 := by
  unfold tailWord_4387025
  simp only [CollatzResearch.WordTrace]
  refine ⟨160007946931565144064730529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106671964621043429376487019 160007946931565144064730529)
  ·
    refine ⟨120005960198673858048547897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160007946931565144064730529 120005960198673858048547897)
    ·
      refine ⟨90004470149005393536410923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120005960198673858048547897 90004470149005393536410923)
      ·
        refine ⟨135006705223508090304616385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90004470149005393536410923 135006705223508090304616385)
        ·
          refine ⟨101255028917631067728462289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135006705223508090304616385 101255028917631067728462289)
          ·
            refine ⟨75941271688223300796346717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101255028917631067728462289 75941271688223300796346717)
            ·
              refine ⟨28477976883083737798630019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 75941271688223300796346717 28477976883083737798630019)
              ·
                refine ⟨42716965324625606697945029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28477976883083737798630019 42716965324625606697945029)
                ·
                  refine ⟨8009430998367301255864693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42716965324625606697945029 8009430998367301255864693)
                  ·
                    refine ⟨750884156096934492737315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8009430998367301255864693 750884156096934492737315)
                    ·
                      rfl

theorem cell23_4387025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_4387025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387025 prefixEnd_4387025 := by exact prefixLift 4387025
  have htrace : WordTrace (prefixWord ++ tailWord_4387025) baseStart_4387025 baseEnd_4387025 := by
    simpa [prefixWord, tailWord_4387025, baseEnd_4387025] using wordTrace_append hprefix tailTrace_4387025
  have hstable : (prefixWord ++ tailWord_4387025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387025).length < 2 ^ (prefixWord ++ tailWord_4387025).sum := by decide
  have hdescent : baseEnd_4387025 < baseStart_4387025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387029 : List Nat := [1, 3, 2, 4, 2, 2, 1, 1, 7]
def baseStart_4387029 : Nat := 118140960795 + 4387029 * 2 ^ 59
def prefixEnd_4387029 : Nat := 4983230072969 + 3 ^ 40 * 4387029 * 2
def baseEnd_4387029 : Nat := 250294946912602384729103

theorem tailTrace_4387029 : CollatzResearch.WordTrace tailWord_4387029 prefixEnd_4387029 250294946912602384729103 := by
  unfold tailWord_4387029
  simp only [CollatzResearch.WordTrace]
  refine ⟨160008092823550652747876141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106672061882367101831917427 160008092823550652747876141)
  ·
    refine ⟨60003034808831494780453553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160008092823550652747876141 60003034808831494780453553)
    ·
      refine ⟨45002276106623621085340165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60003034808831494780453553 45002276106623621085340165)
      ·
        refine ⟨8437926769991928953501281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45002276106623621085340165 8437926769991928953501281)
        ·
          refine ⟨6328445077493946715125961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8437926769991928953501281 6328445077493946715125961)
          ·
            refine ⟨4746333808120460036344471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6328445077493946715125961 4746333808120460036344471)
            ·
              refine ⟨7119500712180690054516707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4746333808120460036344471 7119500712180690054516707)
              ·
                refine ⟨10679251068271035081775061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7119500712180690054516707 10679251068271035081775061)
                ·
                  refine ⟨250294946912602384729103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10679251068271035081775061 250294946912602384729103)
                  ·
                    rfl

theorem cell23_4387029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 7].length) (baseStart_4387029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387029 prefixEnd_4387029 := by exact prefixLift 4387029
  have htrace : WordTrace (prefixWord ++ tailWord_4387029) baseStart_4387029 baseEnd_4387029 := by
    simpa [prefixWord, tailWord_4387029, baseEnd_4387029] using wordTrace_append hprefix tailTrace_4387029
  have hstable : (prefixWord ++ tailWord_4387029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387029).length < 2 ^ (prefixWord ++ tailWord_4387029).sum := by decide
  have hdescent : baseEnd_4387029 < baseStart_4387029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387062 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_4387062 : Nat := 118140960795 + 4387062 * 2 ^ 59
def prefixEnd_4387062 : Nat := 4983230072969 + 3 ^ 40 * 4387062 * 2
def baseEnd_4387062 : Nat := 2252671467075019833449275

theorem tailTrace_4387062 : CollatzResearch.WordTrace tailWord_4387062 prefixEnd_4387062 2252671467075019833449275 := by
  unfold tailWord_4387062
  simp only [CollatzResearch.WordTrace]
  refine ⟨10000581027026943711489215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106672864288287399589218293 10000581027026943711489215)
  ·
    refine ⟨15000871540540415567233823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10000581027026943711489215 15000871540540415567233823)
    ·
      refine ⟨22501307310810623350850735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15000871540540415567233823 22501307310810623350850735)
      ·
        refine ⟨33751960966215935026276103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22501307310810623350850735 33751960966215935026276103)
        ·
          refine ⟨50627941449323902539414155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33751960966215935026276103 50627941449323902539414155)
          ·
            refine ⟨75941912173985853809121233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50627941449323902539414155 75941912173985853809121233)
            ·
              refine ⟨56956434130489390356840925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75941912173985853809121233 56956434130489390356840925)
              ·
                refine ⟨21358662798933521383815347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56956434130489390356840925 21358662798933521383815347)
                ·
                  refine ⟨32037994198400282075723021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21358662798933521383815347 32037994198400282075723021)
                  ·
                    refine ⟨12014247824400105778396133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32037994198400282075723021 12014247824400105778396133)
                    ·
                      refine ⟨2252671467075019833449275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12014247824400105778396133 2252671467075019833449275)
                      ·
                        rfl

theorem cell23_4387062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_4387062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387062 prefixEnd_4387062 := by exact prefixLift 4387062
  have htrace : WordTrace (prefixWord ++ tailWord_4387062) baseStart_4387062 baseEnd_4387062 := by
    simpa [prefixWord, tailWord_4387062, baseEnd_4387062] using wordTrace_append hprefix tailTrace_4387062
  have hstable : (prefixWord ++ tailWord_4387062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387062).length < 2 ^ (prefixWord ++ tailWord_4387062).sum := by decide
  have hdescent : baseEnd_4387062 < baseStart_4387062 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387075 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 6]
def baseStart_4387075 : Nat := 118140960795 + 4387075 * 2 ^ 59
def prefixEnd_4387075 : Nat := 4983230072969 + 3 ^ 40 * 4387075 * 2
def baseEnd_4387075 : Nat := 2252678142323528282586715

theorem tailTrace_4387075 : CollatzResearch.WordTrace tailWord_4387075 prefixEnd_4387075 2252678142323528282586715 := by
  unfold tailWord_4387075
  simp only [CollatzResearch.WordTrace]
  refine ⟨160009770581384002604050679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106673180387589335069367119 160009770581384002604050679)
  ·
    refine ⟨240014655872076003906076019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160009770581384002604050679 240014655872076003906076019)
    ·
      refine ⟨360021983808114005859114029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240014655872076003906076019 360021983808114005859114029)
      ·
        refine ⟨135008243928042752197167761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 360021983808114005859114029 135008243928042752197167761)
        ·
          refine ⟨101256182946032064147875821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135008243928042752197167761 101256182946032064147875821)
          ·
            refine ⟨37971068604762024055453433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101256182946032064147875821 37971068604762024055453433)
            ·
              refine ⟨28478301453571518041590075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37971068604762024055453433 28478301453571518041590075)
              ·
                refine ⟨42717452180357277062385113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28478301453571518041590075 42717452180357277062385113)
                ·
                  refine ⟨32038089135267957796788835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42717452180357277062385113 32038089135267957796788835)
                  ·
                    refine ⟨48057133702901936695183253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32038089135267957796788835 48057133702901936695183253)
                    ·
                      refine ⟨2252678142323528282586715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48057133702901936695183253 2252678142323528282586715)
                      ·
                        rfl

theorem cell23_4387075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_4387075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387075 prefixEnd_4387075 := by exact prefixLift 4387075
  have htrace : WordTrace (prefixWord ++ tailWord_4387075) baseStart_4387075 baseEnd_4387075 := by
    simpa [prefixWord, tailWord_4387075, baseEnd_4387075] using wordTrace_append hprefix tailTrace_4387075
  have hstable : (prefixWord ++ tailWord_4387075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387075).length < 2 ^ (prefixWord ++ tailWord_4387075).sum := by decide
  have hdescent : baseEnd_4387075 < baseStart_4387075 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387139 : List Nat := [1, 1, 1, 3, 1, 3, 2, 4, 2, 3, 2]
def baseStart_4387139 : Nat := 118140960795 + 4387139 * 2 ^ 59
def prefixEnd_4387139 : Nat := 4983230072969 + 3 ^ 40 * 4387139 * 2
def baseEnd_4387139 : Nat := 2252711005085416032186421

theorem tailTrace_4387139 : CollatzResearch.WordTrace tailWord_4387139 prefixEnd_4387139 2252711005085416032186421 := by
  unfold tailWord_4387139
  simp only [CollatzResearch.WordTrace]
  refine ⟨160012104853152141534380471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106674736568768094356253647 160012104853152141534380471)
  ·
    refine ⟨240018157279728212301570707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160012104853152141534380471 240018157279728212301570707)
    ·
      refine ⟨360027235919592318452356061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240018157279728212301570707 360027235919592318452356061)
      ·
        refine ⟨135010213469847119419633523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 360027235919592318452356061 135010213469847119419633523)
        ·
          refine ⟨202515320204770679129450285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135010213469847119419633523 202515320204770679129450285)
          ·
            refine ⟨75943245076789004673543857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202515320204770679129450285 75943245076789004673543857)
            ·
              refine ⟨56957433807591753505157893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 75943245076789004673543857 56957433807591753505157893)
              ·
                refine ⟨10679518838923453782217105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 56957433807591753505157893 10679518838923453782217105)
                ·
                  refine ⟨8009639129192590336662829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10679518838923453782217105 8009639129192590336662829)
                  ·
                    refine ⟨3003614673447221376248561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8009639129192590336662829 3003614673447221376248561)
                    ·
                      refine ⟨2252711005085416032186421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3003614673447221376248561 2252711005085416032186421)
                      ·
                        rfl

theorem cell23_4387139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 3, 2].length) (baseStart_4387139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387139 prefixEnd_4387139 := by exact prefixLift 4387139
  have htrace : WordTrace (prefixWord ++ tailWord_4387139) baseStart_4387139 baseEnd_4387139 := by
    simpa [prefixWord, tailWord_4387139, baseEnd_4387139] using wordTrace_append hprefix tailTrace_4387139
  have hstable : (prefixWord ++ tailWord_4387139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387139).length < 2 ^ (prefixWord ++ tailWord_4387139).sum := by decide
  have hdescent : baseEnd_4387139 < baseStart_4387139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387172 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 3, 1, 5]
def baseStart_4387172 : Nat := 118140960795 + 4387172 * 2 ^ 59
def prefixEnd_4387172 : Nat := 4983230072969 + 3 ^ 40 * 4387172 * 2
def baseEnd_4387172 : Nat := 2252727949947014403073769

theorem tailTrace_4387172 : CollatzResearch.WordTrace tailWord_4387172 prefixEnd_4387172 2252727949947014403073769 := by
  unfold tailWord_4387172
  simp only [CollatzResearch.WordTrace]
  refine ⟨80006654231016294085165885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106675538974688392113554513 80006654231016294085165885)
  ·
    refine ⟨30002495336631110281937207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80006654231016294085165885 30002495336631110281937207)
    ·
      refine ⟨45003743004946665422905811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30002495336631110281937207 45003743004946665422905811)
      ·
        refine ⟨67505614507419998134358717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45003743004946665422905811 67505614507419998134358717)
        ·
          refine ⟨25314605440282499300384519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67505614507419998134358717 25314605440282499300384519)
          ·
            refine ⟨37971908160423748950576779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25314605440282499300384519 37971908160423748950576779)
            ·
              refine ⟨56957862240635623425865169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37971908160423748950576779 56957862240635623425865169)
              ·
                refine ⟨42718396680476717569398877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 56957862240635623425865169 42718396680476717569398877)
                ·
                  refine ⟨16019398755178769088524579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42718396680476717569398877 16019398755178769088524579)
                  ·
                    refine ⟨24029098132768153632786869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16019398755178769088524579 24029098132768153632786869)
                    ·
                      refine ⟨2252727949947014403073769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24029098132768153632786869 2252727949947014403073769)
                      ·
                        rfl

theorem cell23_4387172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 3, 1, 5].length) (baseStart_4387172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387172 prefixEnd_4387172 := by exact prefixLift 4387172
  have htrace : WordTrace (prefixWord ++ tailWord_4387172) baseStart_4387172 baseEnd_4387172 := by
    simpa [prefixWord, tailWord_4387172, baseEnd_4387172] using wordTrace_append hprefix tailTrace_4387172
  have hstable : (prefixWord ++ tailWord_4387172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387172).length < 2 ^ (prefixWord ++ tailWord_4387172).sum := by decide
  have hdescent : baseEnd_4387172 < baseStart_4387172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387180 : List Nat := [2, 2, 1, 1, 6, 2, 1, 3, 1, 1, 3]
def baseStart_4387180 : Nat := 118140960795 + 4387180 * 2 ^ 59
def prefixEnd_4387180 : Nat := 4983230072969 + 3 ^ 40 * 4387180 * 2
def baseEnd_4387180 : Nat := 2252732057792250371773733

theorem tailTrace_4387180 : CollatzResearch.WordTrace tailWord_4387180 prefixEnd_4387180 2252732057792250371773733 := by
  unfold tailWord_4387180
  simp only [CollatzResearch.WordTrace]
  refine ⟨80006800123001802768311497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106675733497335737024415329 80006800123001802768311497)
  ·
    refine ⟨60005100092251352076233623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80006800123001802768311497 60005100092251352076233623)
    ·
      refine ⟨90007650138377028114350435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60005100092251352076233623 90007650138377028114350435)
      ·
        refine ⟨135011475207565542171525653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90007650138377028114350435 135011475207565542171525653)
        ·
          refine ⟨6328662900354634789290265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 135011475207565542171525653 6328662900354634789290265)
          ·
            refine ⟨4746497175265976091967699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6328662900354634789290265 4746497175265976091967699)
            ·
              refine ⟨7119745762898964137951549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4746497175265976091967699 7119745762898964137951549)
              ·
                refine ⟨2669904661087111551731831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7119745762898964137951549 2669904661087111551731831)
                ·
                  refine ⟨4004856991630667327597747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2669904661087111551731831 4004856991630667327597747)
                  ·
                    refine ⟨6007285487446000991396621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4004856991630667327597747 6007285487446000991396621)
                    ·
                      refine ⟨2252732057792250371773733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6007285487446000991396621 2252732057792250371773733)
                      ·
                        rfl

theorem cell23_4387180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3, 1, 1, 3].length) (baseStart_4387180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387180 prefixEnd_4387180 := by exact prefixLift 4387180
  have htrace : WordTrace (prefixWord ++ tailWord_4387180) baseStart_4387180 baseEnd_4387180 := by
    simpa [prefixWord, tailWord_4387180, baseEnd_4387180] using wordTrace_append hprefix tailTrace_4387180
  have hstable : (prefixWord ++ tailWord_4387180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387180).length < 2 ^ (prefixWord ++ tailWord_4387180).sum := by decide
  have hdescent : baseEnd_4387180 < baseStart_4387180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387189 : List Nat := [1, 3, 4, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_4387189 : Nat := 118140960795 + 4387189 * 2 ^ 59
def prefixEnd_4387189 : Nat := 4983230072969 + 3 ^ 40 * 4387189 * 2
def baseEnd_4387189 : Nat := 2252736679118140836561191

theorem tailTrace_4387189 : CollatzResearch.WordTrace tailWord_4387189 prefixEnd_4387189 2252736679118140836561191 := by
  unfold tailWord_4387189
  simp only [CollatzResearch.WordTrace]
  refine ⟨160013928502971000073700621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106675952335314000049133747 160013928502971000073700621)
  ·
    refine ⟨60005223188614125027637733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160013928502971000073700621 60005223188614125027637733)
    ·
      refine ⟨11250979347865148442682075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60005223188614125027637733 11250979347865148442682075)
      ·
        refine ⟨16876469021797722664023113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11250979347865148442682075 16876469021797722664023113)
        ·
          refine ⟨12657351766348291998017335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16876469021797722664023113 12657351766348291998017335)
          ·
            refine ⟨18986027649522437997026003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12657351766348291998017335 18986027649522437997026003)
            ·
              refine ⟨28479041474283656995539005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18986027649522437997026003 28479041474283656995539005)
              ·
                refine ⟨10679640552856371373327127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28479041474283656995539005 10679640552856371373327127)
                ·
                  refine ⟨16019460829284557059990691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10679640552856371373327127 16019460829284557059990691)
                  ·
                    refine ⟨24029191243926835589986037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16019460829284557059990691 24029191243926835589986037)
                    ·
                      refine ⟨2252736679118140836561191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24029191243926835589986037 2252736679118140836561191)
                      ·
                        rfl

theorem cell23_4387189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_4387189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387189 prefixEnd_4387189 := by exact prefixLift 4387189
  have htrace : WordTrace (prefixWord ++ tailWord_4387189) baseStart_4387189 baseEnd_4387189 := by
    simpa [prefixWord, tailWord_4387189, baseEnd_4387189] using wordTrace_append hprefix tailTrace_4387189
  have hstable : (prefixWord ++ tailWord_4387189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387189).length < 2 ^ (prefixWord ++ tailWord_4387189).sum := by decide
  have hdescent : baseEnd_4387189 < baseStart_4387189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387190 : List Nat := [5, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2]
def baseStart_4387190 : Nat := 118140960795 + 4387190 * 2 ^ 59
def prefixEnd_4387190 : Nat := 4983230072969 + 3 ^ 40 * 4387190 * 2
def baseEnd_4387190 : Nat := 2252737192598795332648687

theorem tailTrace_4387190 : CollatzResearch.WordTrace tailWord_4387190 prefixEnd_4387190 2252737192598795332648687 := by
  unfold tailWord_4387190
  simp only [CollatzResearch.WordTrace]
  refine ⟨10000872810997961077780439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 106675976650644918162991349 10000872810997961077780439)
  ·
    refine ⟨15001309216496941616670659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10000872810997961077780439 15001309216496941616670659)
    ·
      refine ⟨22501963824745412425005989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15001309216496941616670659 22501963824745412425005989)
      ·
        refine ⟨4219118217139764829688623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22501963824745412425005989 4219118217139764829688623)
        ·
          refine ⟨6328677325709647244532935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4219118217139764829688623 6328677325709647244532935)
          ·
            refine ⟨9493015988564470866799403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6328677325709647244532935 9493015988564470866799403)
            ·
              refine ⟨14239523982846706300199105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9493015988564470866799403 14239523982846706300199105)
              ·
                refine ⟨10679642987135029725149329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14239523982846706300199105 10679642987135029725149329)
                ·
                  refine ⟨8009732240351272293861997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10679642987135029725149329 8009732240351272293861997)
                  ·
                    refine ⟨3003649590131727110198249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8009732240351272293861997 3003649590131727110198249)
                    ·
                      refine ⟨2252737192598795332648687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3003649590131727110198249 2252737192598795332648687)
                      ·
                        rfl

theorem cell23_4387190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_4387190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387190 prefixEnd_4387190 := by exact prefixLift 4387190
  have htrace : WordTrace (prefixWord ++ tailWord_4387190) baseStart_4387190 baseEnd_4387190 := by
    simpa [prefixWord, tailWord_4387190, baseEnd_4387190] using wordTrace_append hprefix tailTrace_4387190
  have hstable : (prefixWord ++ tailWord_4387190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387190).length < 2 ^ (prefixWord ++ tailWord_4387190).sum := by decide
  have hdescent : baseEnd_4387190 < baseStart_4387190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387220 : List Nat := [2, 4, 2, 1, 4, 1, 1, 2, 1, 1, 4]
def baseStart_4387220 : Nat := 118140960795 + 4387220 * 2 ^ 59
def prefixEnd_4387220 : Nat := 4983230072969 + 3 ^ 40 * 4387220 * 2
def baseEnd_4387220 : Nat := 2252752597018430215273549

theorem tailTrace_4387220 : CollatzResearch.WordTrace tailWord_4387220 prefixEnd_4387220 2252752597018430215273549 := by
  unfold tailWord_4387220
  simp only [CollatzResearch.WordTrace]
  refine ⟨80007529582929346184039557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106676706110572461578719409 80007529582929346184039557)
  ·
    refine ⟨15001411796799252409507417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80007529582929346184039557 15001411796799252409507417)
    ·
      refine ⟨11251058847599439307130563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15001411796799252409507417 11251058847599439307130563)
      ·
        refine ⟨16876588271399158960695845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11251058847599439307130563 16876588271399158960695845)
        ·
          refine ⟨3164360300887342305130471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16876588271399158960695845 3164360300887342305130471)
          ·
            refine ⟨4746540451331013457695707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3164360300887342305130471 4746540451331013457695707)
            ·
              refine ⟨7119810676996520186543561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4746540451331013457695707 7119810676996520186543561)
              ·
                refine ⟨5339858007747390139907671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7119810676996520186543561 5339858007747390139907671)
                ·
                  refine ⟨8009787011621085209861507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5339858007747390139907671 8009787011621085209861507)
                  ·
                    refine ⟨12014680517431627814792261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8009787011621085209861507 12014680517431627814792261)
                    ·
                      refine ⟨2252752597018430215273549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12014680517431627814792261 2252752597018430215273549)
                      ·
                        rfl

theorem cell23_4387220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_4387220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387220 prefixEnd_4387220 := by exact prefixLift 4387220
  have htrace : WordTrace (prefixWord ++ tailWord_4387220) baseStart_4387220 baseEnd_4387220 := by
    simpa [prefixWord, tailWord_4387220, baseEnd_4387220] using wordTrace_append hprefix tailTrace_4387220
  have hstable : (prefixWord ++ tailWord_4387220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387220).length < 2 ^ (prefixWord ++ tailWord_4387220).sum := by decide
  have hdescent : baseEnd_4387220 < baseStart_4387220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387240 : List Nat := [2, 1, 6, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_4387240 : Nat := 118140960795 + 4387240 * 2 ^ 59
def prefixEnd_4387240 : Nat := 4983230072969 + 3 ^ 40 * 4387240 * 2
def baseEnd_4387240 : Nat := 2252762866631520137023457

theorem tailTrace_4387240 : CollatzResearch.WordTrace tailWord_4387240 prefixEnd_4387240 2252762866631520137023457 := by
  unfold tailWord_4387240
  simp only [CollatzResearch.WordTrace]
  refine ⟨80007894312893117891903587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106677192417190823855871449 80007894312893117891903587)
  ·
    refine ⟨120011841469339676837855381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80007894312893117891903587 120011841469339676837855381)
    ·
      refine ⟨5625555068875297351774471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 120011841469339676837855381 5625555068875297351774471)
      ·
        refine ⟨8438332603312946027661707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5625555068875297351774471 8438332603312946027661707)
        ·
          refine ⟨12657498904969419041492561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8438332603312946027661707 12657498904969419041492561)
          ·
            refine ⟨9493124178727064281119421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12657498904969419041492561 9493124178727064281119421)
            ·
              refine ⟨3559921567022649105419783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9493124178727064281119421 3559921567022649105419783)
              ·
                refine ⟨5339882350533973658129675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3559921567022649105419783 5339882350533973658129675)
                ·
                  refine ⟨8009823525800960487194513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5339882350533973658129675 8009823525800960487194513)
                  ·
                    refine ⟨6007367644350720365395885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8009823525800960487194513 6007367644350720365395885)
                    ·
                      refine ⟨2252762866631520137023457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6007367644350720365395885 2252762866631520137023457)
                      ·
                        rfl

theorem cell23_4387240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_4387240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387240 prefixEnd_4387240 := by exact prefixLift 4387240
  have htrace : WordTrace (prefixWord ++ tailWord_4387240) baseStart_4387240 baseEnd_4387240 := by
    simpa [prefixWord, tailWord_4387240, baseEnd_4387240] using wordTrace_append hprefix tailTrace_4387240
  have hstable : (prefixWord ++ tailWord_4387240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387240).length < 2 ^ (prefixWord ++ tailWord_4387240).sum := by decide
  have hdescent : baseEnd_4387240 < baseStart_4387240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387293 : List Nat := [1, 4, 3, 1, 1, 1, 2, 2, 4, 2, 2]
def baseStart_4387293 : Nat := 118140960795 + 4387293 * 2 ^ 59
def prefixEnd_4387293 : Nat := 4983230072969 + 3 ^ 40 * 4387293 * 2
def baseEnd_4387293 : Nat := 2252790081106208429660713

theorem tailTrace_4387293 : CollatzResearch.WordTrace tailWord_4387293 prefixEnd_4387293 2252790081106208429660713 := by
  unfold tailWord_4387293
  simp only [CollatzResearch.WordTrace]
  refine ⟨160017721694594225835486533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106678481129729483890324355 160017721694594225835486533)
  ·
    refine ⟨30003322817736417344153725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160017721694594225835486533 30003322817736417344153725)
    ·
      refine ⟨11251246056651156504057647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30003322817736417344153725 11251246056651156504057647)
      ·
        refine ⟨16876869084976734756086471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11251246056651156504057647 16876869084976734756086471)
        ·
          refine ⟨25315303627465102134129707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16876869084976734756086471 25315303627465102134129707)
          ·
            refine ⟨37972955441197653201194561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25315303627465102134129707 37972955441197653201194561)
            ·
              refine ⟨28479716580898239900895921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 37972955441197653201194561 28479716580898239900895921)
              ·
                refine ⟨21359787435673679925671941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28479716580898239900895921 21359787435673679925671941)
                ·
                  refine ⟨4004960144188814986063489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21359787435673679925671941 4004960144188814986063489)
                  ·
                    refine ⟨3003720108141611239547617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4004960144188814986063489 3003720108141611239547617)
                    ·
                      refine ⟨2252790081106208429660713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3003720108141611239547617 2252790081106208429660713)
                      ·
                        rfl

theorem cell23_4387293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_4387293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387293 prefixEnd_4387293 := by exact prefixLift 4387293
  have htrace : WordTrace (prefixWord ++ tailWord_4387293) baseStart_4387293 baseEnd_4387293 := by
    simpa [prefixWord, tailWord_4387293, baseEnd_4387293] using wordTrace_append hprefix tailTrace_4387293
  have hstable : (prefixWord ++ tailWord_4387293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387293).length < 2 ^ (prefixWord ++ tailWord_4387293).sum := by decide
  have hdescent : baseEnd_4387293 < baseStart_4387293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387310 : List Nat := [4, 1, 2, 1, 2, 2, 3, 2, 2, 2, 2]
def baseStart_4387310 : Nat := 118140960795 + 4387310 * 2 ^ 59
def prefixEnd_4387310 : Nat := 4983230072969 + 3 ^ 40 * 4387310 * 2
def baseEnd_4387310 : Nat := 2252798810277334863148135

theorem tailTrace_4387310 : CollatzResearch.WordTrace tailWord_4387310 prefixEnd_4387310 2252798810277334863148135 := by
  unfold tailWord_4387310
  simp only [CollatzResearch.WordTrace]
  refine ⟨20002292716941579717356923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 106678894490355091825903589 20002292716941579717356923)
  ·
    refine ⟨30003439075412369576035385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20002292716941579717356923 30003439075412369576035385)
    ·
      refine ⟨22502579306559277182026539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30003439075412369576035385 22502579306559277182026539)
      ·
        refine ⟨33753868959838915773039809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22502579306559277182026539 33753868959838915773039809)
        ·
          refine ⟨25315401719879186829779857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33753868959838915773039809 25315401719879186829779857)
          ·
            refine ⟨18986551289909390122334893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25315401719879186829779857 18986551289909390122334893)
            ·
              refine ⟨7119956733716021295875585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18986551289909390122334893 7119956733716021295875585)
              ·
                refine ⟨5339967550287015971906689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7119956733716021295875585 5339967550287015971906689)
                ·
                  refine ⟨4004975662715261978930017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5339967550287015971906689 4004975662715261978930017)
                  ·
                    refine ⟨3003731747036446484197513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4004975662715261978930017 3003731747036446484197513)
                    ·
                      refine ⟨2252798810277334863148135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3003731747036446484197513 2252798810277334863148135)
                      ·
                        rfl

theorem cell23_4387310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_4387310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387310 prefixEnd_4387310 := by exact prefixLift 4387310
  have htrace : WordTrace (prefixWord ++ tailWord_4387310) baseStart_4387310 baseEnd_4387310 := by
    simpa [prefixWord, tailWord_4387310, baseEnd_4387310] using wordTrace_append hprefix tailTrace_4387310
  have hstable : (prefixWord ++ tailWord_4387310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387310).length < 2 ^ (prefixWord ++ tailWord_4387310).sum := by decide
  have hdescent : baseEnd_4387310 < baseStart_4387310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387329 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 1, 7]
def baseStart_4387329 : Nat := 118140960795 + 4387329 * 2 ^ 59
def prefixEnd_4387329 : Nat := 4983230072969 + 3 ^ 40 * 4387329 * 2
def baseEnd_4387329 : Nat := 750936188803256762936849

theorem tailTrace_4387329 : CollatzResearch.WordTrace tailWord_4387329 prefixEnd_4387329 750936188803256762936849 := by
  unfold tailWord_4387329
  simp only [CollatzResearch.WordTrace]
  refine ⟨160019034722463803983797041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106679356481642535989198027 160019034722463803983797041)
  ·
    refine ⟨120014276041847852987847781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160019034722463803983797041 120014276041847852987847781)
    ·
      refine ⟨22502676757846472435221459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120014276041847852987847781 22502676757846472435221459)
      ·
        refine ⟨33754015136769708652832189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22502676757846472435221459 33754015136769708652832189)
        ·
          refine ⟨12657755676288640744812071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33754015136769708652832189 12657755676288640744812071)
          ·
            refine ⟨18986633514432961117218107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12657755676288640744812071 18986633514432961117218107)
            ·
              refine ⟨28479950271649441675827161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18986633514432961117218107 28479950271649441675827161)
              ·
                refine ⟨21359962703737081256870371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28479950271649441675827161 21359962703737081256870371)
                ·
                  refine ⟨32039944055605621885305557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21359962703737081256870371 32039944055605621885305557)
                  ·
                    refine ⟨750936188803256762936849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32039944055605621885305557 750936188803256762936849)
                    ·
                      rfl

theorem cell23_4387329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_4387329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387329 prefixEnd_4387329 := by exact prefixLift 4387329
  have htrace : WordTrace (prefixWord ++ tailWord_4387329) baseStart_4387329 baseEnd_4387329 := by
    simpa [prefixWord, tailWord_4387329, baseEnd_4387329] using wordTrace_append hprefix tailTrace_4387329
  have hstable : (prefixWord ++ tailWord_4387329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387329).length < 2 ^ (prefixWord ++ tailWord_4387329).sum := by decide
  have hdescent : baseEnd_4387329 < baseStart_4387329 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387349 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 1, 3, 4]
def baseStart_4387349 : Nat := 118140960795 + 4387349 * 2 ^ 59
def prefixEnd_4387349 : Nat := 4983230072969 + 3 ^ 40 * 4387349 * 2
def baseEnd_4387349 : Nat := 2252818836022860210560455

theorem tailTrace_4387349 : CollatzResearch.WordTrace tailWord_4387349 prefixEnd_4387349 2252818836022860210560455 := by
  unfold tailWord_4387349
  simp only [CollatzResearch.WordTrace]
  refine ⟨160019764182391347399525101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106679842788260898266350067 160019764182391347399525101)
  ·
    refine ⟨60007411568396755274821913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160019764182391347399525101 60007411568396755274821913)
    ·
      refine ⟨45005558676297566456116435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60007411568396755274821913 45005558676297566456116435)
      ·
        refine ⟨67508338014446349684174653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45005558676297566456116435 67508338014446349684174653)
        ·
          refine ⟨25315626755417381131565495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67508338014446349684174653 25315626755417381131565495)
          ·
            refine ⟨37973440133126071697348243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25315626755417381131565495 37973440133126071697348243)
            ·
              refine ⟨56960160199689107546022365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 37973440133126071697348243 56960160199689107546022365)
              ·
                refine ⟨21360060074883415329758387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 56960160199689107546022365 21360060074883415329758387)
                ·
                  refine ⟨32040090112325122994637581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21360060074883415329758387 32040090112325122994637581)
                  ·
                    refine ⟨12015033792121921122989093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32040090112325122994637581 12015033792121921122989093)
                    ·
                      refine ⟨2252818836022860210560455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12015033792121921122989093 2252818836022860210560455)
                      ·
                        rfl

theorem cell23_4387349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_4387349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387349 prefixEnd_4387349 := by exact prefixLift 4387349
  have htrace : WordTrace (prefixWord ++ tailWord_4387349) baseStart_4387349 baseEnd_4387349 := by
    simpa [prefixWord, tailWord_4387349, baseEnd_4387349] using wordTrace_append hprefix tailTrace_4387349
  have hstable : (prefixWord ++ tailWord_4387349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387349).length < 2 ^ (prefixWord ++ tailWord_4387349).sum := by decide
  have hdescent : baseEnd_4387349 < baseStart_4387349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387367 : List Nat := [1, 1, 7, 2, 1, 1, 3, 2, 5]
def baseStart_4387367 : Nat := 118140960795 + 4387367 * 2 ^ 59
def prefixEnd_4387367 : Nat := 4983230072969 + 3 ^ 40 * 4387367 * 2
def baseEnd_4387367 : Nat := 250314230963849015570597

theorem tailTrace_4387367 : CollatzResearch.WordTrace tailWord_4387367 prefixEnd_4387367 250314230963849015570597 := by
  unfold tailWord_4387367
  simp only [CollatzResearch.WordTrace]
  refine ⟨160020420696326136473680355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 106680280464217424315786903 160020420696326136473680355)
  ·
    refine ⟨240030631044489204710520533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160020420696326136473680355 240030631044489204710520533)
    ·
      refine ⟨5625717915105215735402825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 240030631044489204710520533 5625717915105215735402825)
      ·
        refine ⟨4219288436328911801552119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5625717915105215735402825 4219288436328911801552119)
        ·
          refine ⟨6328932654493367702328179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4219288436328911801552119 6328932654493367702328179)
          ·
            refine ⟨9493398981740051553492269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6328932654493367702328179 9493398981740051553492269)
            ·
              refine ⟨3560024618152519332559601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9493398981740051553492269 3560024618152519332559601)
              ·
                refine ⟨2670018463614389499419701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3560024618152519332559601 2670018463614389499419701)
                ·
                  refine ⟨250314230963849015570597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2670018463614389499419701 250314230963849015570597)
                  ·
                    rfl

theorem cell23_4387367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 5].length) (baseStart_4387367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387367 prefixEnd_4387367 := by exact prefixLift 4387367
  have htrace : WordTrace (prefixWord ++ tailWord_4387367) baseStart_4387367 baseEnd_4387367 := by
    simpa [prefixWord, tailWord_4387367, baseEnd_4387367] using wordTrace_append hprefix tailTrace_4387367
  have hstable : (prefixWord ++ tailWord_4387367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387367).length < 2 ^ (prefixWord ++ tailWord_4387367).sum := by decide
  have hdescent : baseEnd_4387367 < baseStart_4387367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387376 : List Nat := [2, 1, 1, 1, 2, 3, 5, 1, 3, 4]
def baseStart_4387376 : Nat := 118140960795 + 4387376 * 2 ^ 59
def prefixEnd_4387376 : Nat := 4983230072969 + 3 ^ 40 * 4387376 * 2
def baseEnd_4387376 : Nat := 750944233333510534974277

theorem tailTrace_4387376 : CollatzResearch.WordTrace tailWord_4387376 prefixEnd_4387376 750944233333510534974277 := by
  unfold tailWord_4387376
  simp only [CollatzResearch.WordTrace]
  refine ⟨80010374476646765505378991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106680499302195687340505321 80010374476646765505378991)
  ·
    refine ⟨120015561714970148258068487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80010374476646765505378991 120015561714970148258068487)
    ·
      refine ⟨180023342572455222387102731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120015561714970148258068487 180023342572455222387102731)
      ·
        refine ⟨270035013858682833580654097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180023342572455222387102731 270035013858682833580654097)
        ·
          refine ⟨202526260394012125185490573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270035013858682833580654097 202526260394012125185490573)
          ·
            refine ⟨75947347647754546944558965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 202526260394012125185490573 75947347647754546944558965)
            ·
              refine ⟨7120063841976988776052403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 75947347647754546944558965 7120063841976988776052403)
              ·
                refine ⟨10680095762965483164078605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7120063841976988776052403 10680095762965483164078605)
                ·
                  refine ⟨4005035911112056186529477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10680095762965483164078605 4005035911112056186529477)
                  ·
                    refine ⟨750944233333510534974277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4005035911112056186529477 750944233333510534974277)
                    ·
                      rfl

theorem cell23_4387376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 3, 4].length) (baseStart_4387376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387376 prefixEnd_4387376 := by exact prefixLift 4387376
  have htrace : WordTrace (prefixWord ++ tailWord_4387376) baseStart_4387376 baseEnd_4387376 := by
    simpa [prefixWord, tailWord_4387376, baseEnd_4387376] using wordTrace_append hprefix tailTrace_4387376
  have hstable : (prefixWord ++ tailWord_4387376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387376).length < 2 ^ (prefixWord ++ tailWord_4387376).sum := by decide
  have hdescent : baseEnd_4387376 < baseStart_4387376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387456 : List Nat := [2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 4]
def baseStart_4387456 : Nat := 118140960795 + 4387456 * 2 ^ 59
def prefixEnd_4387456 : Nat := 4983230072969 + 3 ^ 40 * 4387456 * 2
def baseEnd_4387456 : Nat := 2252873778452891291922463

theorem tailTrace_4387456 : CollatzResearch.WordTrace tailWord_4387456 prefixEnd_4387456 2252873778452891291922463 := by
  unfold tailWord_4387456
  simp only [CollatzResearch.WordTrace]
  refine ⟨80011833396501852336835111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106682444528669136449113481 80011833396501852336835111)
  ·
    refine ⟨120017750094752778505252667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80011833396501852336835111 120017750094752778505252667)
    ·
      refine ⟨180026625142129167757879001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120017750094752778505252667 180026625142129167757879001)
      ·
        refine ⟨135019968856596875818409251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180026625142129167757879001 135019968856596875818409251)
        ·
          refine ⟨202529953284895313727613877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135019968856596875818409251 202529953284895313727613877)
          ·
            refine ⟨18987183120458935661963801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 202529953284895313727613877 18987183120458935661963801)
            ·
              refine ⟨14240387340344201746472851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18987183120458935661963801 14240387340344201746472851)
              ·
                refine ⟨21360581010516302619709277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14240387340344201746472851 21360581010516302619709277)
                ·
                  refine ⟨8010217878943613482390979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21360581010516302619709277 8010217878943613482390979)
                  ·
                    refine ⟨12015326818415420223586469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8010217878943613482390979 12015326818415420223586469)
                    ·
                      refine ⟨2252873778452891291922463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12015326818415420223586469 2252873778452891291922463)
                      ·
                        rfl

theorem cell23_4387456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 4].length) (baseStart_4387456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387456 prefixEnd_4387456 := by exact prefixLift 4387456
  have htrace : WordTrace (prefixWord ++ tailWord_4387456) baseStart_4387456 baseEnd_4387456 := by
    simpa [prefixWord, tailWord_4387456, baseEnd_4387456] using wordTrace_append hprefix tailTrace_4387456
  have hstable : (prefixWord ++ tailWord_4387456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387456).length < 2 ^ (prefixWord ++ tailWord_4387456).sum := by decide
  have hdescent : baseEnd_4387456 < baseStart_4387456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4387460 : List Nat := [2, 3, 2, 1, 3, 1, 3, 1, 2, 3, 2]
def baseStart_4387460 : Nat := 118140960795 + 4387460 * 2 ^ 59
def prefixEnd_4387460 : Nat := 4983230072969 + 3 ^ 40 * 4387460 * 2
def baseEnd_4387460 : Nat := 2252875832375509276272445

theorem tailTrace_4387460 : CollatzResearch.WordTrace tailWord_4387460 prefixEnd_4387460 2252875832375509276272445 := by
  unfold tailWord_4387460
  simp only [CollatzResearch.WordTrace]
  refine ⟨80011906342494606678407917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 106682541789992808904543889 80011906342494606678407917)
  ·
    refine ⟨30004464878435477504402969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80011906342494606678407917 30004464878435477504402969)
    ·
      refine ⟨22503348658826608128302227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30004464878435477504402969 22503348658826608128302227)
      ·
        refine ⟨33755022988239912192453341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22503348658826608128302227 33755022988239912192453341)
        ·
          refine ⟨12658133620589967072170003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33755022988239912192453341 12658133620589967072170003)
          ·
            refine ⟨18987200430884950608255005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12658133620589967072170003 18987200430884950608255005)
            ·
              refine ⟨7120200161581856478095627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18987200430884950608255005 7120200161581856478095627)
              ·
                refine ⟨10680300242372784717143441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7120200161581856478095627 10680300242372784717143441)
                ·
                  refine ⟨8010225181779588537857581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10680300242372784717143441 8010225181779588537857581)
                  ·
                    refine ⟨3003834443167345701696593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8010225181779588537857581 3003834443167345701696593)
                    ·
                      refine ⟨2252875832375509276272445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3003834443167345701696593 2252875832375509276272445)
                      ·
                        rfl

theorem cell23_4387460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 3, 1, 2, 3, 2].length) (baseStart_4387460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4387460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4387460 prefixEnd_4387460 := by exact prefixLift 4387460
  have htrace : WordTrace (prefixWord ++ tailWord_4387460) baseStart_4387460 baseEnd_4387460 := by
    simpa [prefixWord, tailWord_4387460, baseEnd_4387460] using wordTrace_append hprefix tailTrace_4387460
  have hstable : (prefixWord ++ tailWord_4387460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4387460).length < 2 ^ (prefixWord ++ tailWord_4387460).sum := by decide
  have hdescent : baseEnd_4387460 < baseStart_4387460 := by decide
  rcases family_descends (prefixWord ++ tailWord_4387460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
