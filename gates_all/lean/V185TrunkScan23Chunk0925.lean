import V185TrunkScan23Chunk0924

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5474440 : List Nat := [2, 1, 3, 4, 1, 1, 3, 1, 2, 3, 2]
def baseStart_5474440 : Nat := 118140960795 + 5474440 * 2 ^ 59
def prefixEnd_5474440 : Nat := 4983230072969 + 3 ^ 40 * 5474440 * 2
def baseEnd_5474440 : Nat := 2811019034199666462023515

theorem tailTrace_5474440 : CollatzResearch.WordTrace tailWord_5474440 prefixEnd_5474440 2811019034199666462023515 := by
  unfold tailWord_5474440
  simp only [CollatzResearch.WordTrace]
  refine ⟨99834615143523157380574387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133112820191364209840765849 99834615143523157380574387)
  ·
    refine ⟨149751922715284736070861581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99834615143523157380574387 149751922715284736070861581)
    ·
      refine ⟨56156971018231776026573093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149751922715284736070861581 56156971018231776026573093)
      ·
        refine ⟨10529432065918458004982455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56156971018231776026573093 10529432065918458004982455)
        ·
          refine ⟨15794148098877687007473683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10529432065918458004982455 15794148098877687007473683)
          ·
            refine ⟨23691222148316530511210525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15794148098877687007473683 23691222148316530511210525)
            ·
              refine ⟨8884208305618698941703947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23691222148316530511210525 8884208305618698941703947)
              ·
                refine ⟨13326312458428048412555921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8884208305618698941703947 13326312458428048412555921)
                ·
                  refine ⟨9994734343821036309416941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13326312458428048412555921 9994734343821036309416941)
                  ·
                    refine ⟨3748025378932888616031353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9994734343821036309416941 3748025378932888616031353)
                    ·
                      refine ⟨2811019034199666462023515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3748025378932888616031353 2811019034199666462023515)
                      ·
                        rfl

theorem cell23_5474440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_5474440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474440 prefixEnd_5474440 := by exact prefixLift 5474440
  have htrace : WordTrace (prefixWord ++ tailWord_5474440) baseStart_5474440 baseEnd_5474440 := by
    simpa [prefixWord, tailWord_5474440, baseEnd_5474440] using wordTrace_append hprefix tailTrace_5474440
  have hstable : (prefixWord ++ tailWord_5474440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474440).length < 2 ^ (prefixWord ++ tailWord_5474440).sum := by decide
  have hdescent : baseEnd_5474440 < baseStart_5474440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474453 : List Nat := [1, 3, 2, 1, 1, 1, 3, 2, 5, 2, 2]
def baseStart_5474453 : Nat := 118140960795 + 5474453 * 2 ^ 59
def prefixEnd_5474453 : Nat := 4983230072969 + 3 ^ 40 * 5474453 * 2
def baseEnd_5474453 : Nat := 2811025709448174911160955

theorem tailTrace_5474453 : CollatzResearch.WordTrace tailWord_5474453 prefixEnd_5474453 2811025709448174911160955 := by
  unfold tailWord_5474453
  simp only [CollatzResearch.WordTrace]
  refine ⟨199669704435999217981372013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133113136290666145320914675 199669704435999217981372013)
  ·
    refine ⟨74876139163499706743014505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199669704435999217981372013 74876139163499706743014505)
    ·
      refine ⟨56157104372624780057260879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74876139163499706743014505 56157104372624780057260879)
      ·
        refine ⟨84235656558937170085891319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56157104372624780057260879 84235656558937170085891319)
        ·
          refine ⟨126353484838405755128836979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84235656558937170085891319 126353484838405755128836979)
          ·
            refine ⟨189530227257608632693255469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126353484838405755128836979 189530227257608632693255469)
            ·
              refine ⟨71073835221603237259970801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189530227257608632693255469 71073835221603237259970801)
              ·
                refine ⟨53305376416202427944978101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71073835221603237259970801 53305376416202427944978101)
                ·
                  refine ⟨4997379039018977619841697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53305376416202427944978101 4997379039018977619841697)
                  ·
                    refine ⟨3748034279264233214881273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4997379039018977619841697 3748034279264233214881273)
                    ·
                      refine ⟨2811025709448174911160955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3748034279264233214881273 2811025709448174911160955)
                      ·
                        rfl

theorem cell23_5474453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 2, 5, 2, 2].length) (baseStart_5474453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474453 prefixEnd_5474453 := by exact prefixLift 5474453
  have htrace : WordTrace (prefixWord ++ tailWord_5474453) baseStart_5474453 baseEnd_5474453 := by
    simpa [prefixWord, tailWord_5474453, baseEnd_5474453] using wordTrace_append hprefix tailTrace_5474453
  have hstable : (prefixWord ++ tailWord_5474453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474453).length < 2 ^ (prefixWord ++ tailWord_5474453).sum := by decide
  have hdescent : baseEnd_5474453 < baseStart_5474453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474463 : List Nat := [1, 1, 2, 6, 1, 2, 1, 1, 4, 4]
def baseStart_5474463 : Nat := 118140960795 + 5474463 * 2 ^ 59
def prefixEnd_5474463 : Nat := 4983230072969 + 3 ^ 40 * 5474463 * 2
def baseEnd_5474463 : Nat := 937010281418239957345303

theorem tailTrace_5474463 : CollatzResearch.WordTrace tailWord_5474463 prefixEnd_5474463 937010281418239957345303 := by
  unfold tailWord_5474463
  simp only [CollatzResearch.WordTrace]
  refine ⟨199670069165962989689236043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133113379443975326459490695 199670069165962989689236043)
  ·
    refine ⟨299505103748944484533854065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199670069165962989689236043 299505103748944484533854065)
    ·
      refine ⟨224628827811708363400390549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299505103748944484533854065 224628827811708363400390549)
      ·
        refine ⟨10529476303673829534393307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 224628827811708363400390549 10529476303673829534393307)
        ·
          refine ⟨15794214455510744301589961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10529476303673829534393307 15794214455510744301589961)
          ·
            refine ⟨11845660841633058226192471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15794214455510744301589961 11845660841633058226192471)
            ·
              refine ⟨17768491262449587339288707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11845660841633058226192471 17768491262449587339288707)
              ·
                refine ⟨26652736893674381008933061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17768491262449587339288707 26652736893674381008933061)
                ·
                  refine ⟨4997388167563946439174949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26652736893674381008933061 4997388167563946439174949)
                  ·
                    refine ⟨937010281418239957345303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4997388167563946439174949 937010281418239957345303)
                    ·
                      rfl

theorem cell23_5474463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 1, 4, 4].length) (baseStart_5474463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474463 prefixEnd_5474463 := by exact prefixLift 5474463
  have htrace : WordTrace (prefixWord ++ tailWord_5474463) baseStart_5474463 baseEnd_5474463 := by
    simpa [prefixWord, tailWord_5474463, baseEnd_5474463] using wordTrace_append hprefix tailTrace_5474463
  have hstable : (prefixWord ++ tailWord_5474463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474463).length < 2 ^ (prefixWord ++ tailWord_5474463).sum := by decide
  have hdescent : baseEnd_5474463 < baseStart_5474463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474484 : List Nat := [2, 5, 3, 1, 1, 1, 2, 2, 1, 5]
def baseStart_5474484 : Nat := 118140960795 + 5474484 * 2 ^ 59
def prefixEnd_5474484 : Nat := 4983230072969 + 3 ^ 40 * 5474484 * 2
def baseEnd_5474484 : Nat := 937013875782821429957771

theorem tailTrace_5474484 : CollatzResearch.WordTrace tailWord_5474484 prefixEnd_5474484 937013875782821429957771 := by
  unfold tailWord_5474484
  simp only [CollatzResearch.WordTrace]
  refine ⟨99835417549443455137875253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133113890065924606850500337 99835417549443455137875253)
  ·
    refine ⟨9359570395260323919175805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99835417549443455137875253 9359570395260323919175805)
    ·
      refine ⟨3509838898222621469690927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9359570395260323919175805 3509838898222621469690927)
      ·
        refine ⟨5264758347333932204536391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3509838898222621469690927 5264758347333932204536391)
        ·
          refine ⟨7897137521000898306804587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5264758347333932204536391 7897137521000898306804587)
          ·
            refine ⟨11845706281501347460206881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7897137521000898306804587 11845706281501347460206881)
            ·
              refine ⟨8884279711126010595155161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11845706281501347460206881 8884279711126010595155161)
              ·
                refine ⟨6663209783344507946366371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8884279711126010595155161 6663209783344507946366371)
                ·
                  refine ⟨9994814675016761919549557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6663209783344507946366371 9994814675016761919549557)
                  ·
                    refine ⟨937013875782821429957771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9994814675016761919549557 937013875782821429957771)
                    ·
                      rfl

theorem cell23_5474484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_5474484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474484 prefixEnd_5474484 := by exact prefixLift 5474484
  have htrace : WordTrace (prefixWord ++ tailWord_5474484) baseStart_5474484 baseEnd_5474484 := by
    simpa [prefixWord, tailWord_5474484, baseEnd_5474484] using wordTrace_append hprefix tailTrace_5474484
  have hstable : (prefixWord ++ tailWord_5474484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474484).length < 2 ^ (prefixWord ++ tailWord_5474484).sum := by decide
  have hdescent : baseEnd_5474484 < baseStart_5474484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474564 : List Nat := [2, 3, 2, 2, 3, 1, 3, 1, 1, 3, 2]
def baseStart_5474564 : Nat := 118140960795 + 5474564 * 2 ^ 59
def prefixEnd_5474564 : Nat := 4983230072969 + 3 ^ 40 * 5474564 * 2
def baseEnd_5474564 : Nat := 2811082705800823976872945

theorem tailTrace_5474564 : CollatzResearch.WordTrace tailWord_5474564 prefixEnd_5474564 2811082705800823976872945 := by
  unfold tailWord_5474564
  simp only [CollatzResearch.WordTrace]
  refine ⟨99836876469298541969331373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133115835292398055959108497 99836876469298541969331373)
  ·
    refine ⟨37438828675986953238499265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99836876469298541969331373 37438828675986953238499265)
    ·
      refine ⟨28079121506990214928874449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37438828675986953238499265 28079121506990214928874449)
      ·
        refine ⟨21059341130242661196655837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28079121506990214928874449 21059341130242661196655837)
        ·
          refine ⟨7897252923840997948745939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21059341130242661196655837 7897252923840997948745939)
          ·
            refine ⟨11845879385761496923118909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7897252923840997948745939 11845879385761496923118909)
            ·
              refine ⟨4442204769660561346169591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11845879385761496923118909 4442204769660561346169591)
              ·
                refine ⟨6663307154490842019254387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4442204769660561346169591 6663307154490842019254387)
                ·
                  refine ⟨9994960731736263028881581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6663307154490842019254387 9994960731736263028881581)
                  ·
                    refine ⟨3748110274401098635830593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9994960731736263028881581 3748110274401098635830593)
                    ·
                      refine ⟨2811082705800823976872945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3748110274401098635830593 2811082705800823976872945)
                      ·
                        rfl

theorem cell23_5474564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_5474564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474564 prefixEnd_5474564 := by exact prefixLift 5474564
  have htrace : WordTrace (prefixWord ++ tailWord_5474564) baseStart_5474564 baseEnd_5474564 := by
    simpa [prefixWord, tailWord_5474564, baseEnd_5474564] using wordTrace_append hprefix tailTrace_5474564
  have hstable : (prefixWord ++ tailWord_5474564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474564).length < 2 ^ (prefixWord ++ tailWord_5474564).sum := by decide
  have hdescent : baseEnd_5474564 < baseStart_5474564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474577 : List Nat := [1, 2, 2, 1, 1, 6, 2, 2, 2, 2, 2]
def baseStart_5474577 : Nat := 118140960795 + 5474577 * 2 ^ 59
def prefixEnd_5474577 : Nat := 4983230072969 + 3 ^ 40 * 5474577 * 2
def baseEnd_5474577 : Nat := 2811089381049332426010385

theorem tailTrace_5474577 : CollatzResearch.WordTrace tailWord_5474577 prefixEnd_5474577 2811089381049332426010385 := by
  unfold tailWord_5474577
  simp only [CollatzResearch.WordTrace]
  refine ⟨199674227087549987158885985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133116151391699991439257323 199674227087549987158885985)
  ·
    refine ⟨149755670315662490369164489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199674227087549987158885985 149755670315662490369164489)
    ·
      refine ⟨112316752736746867776873367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149755670315662490369164489 112316752736746867776873367)
      ·
        refine ⟨168475129105120301665310051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112316752736746867776873367 168475129105120301665310051)
        ·
          refine ⟨252712693657680452497965077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168475129105120301665310051 252712693657680452497965077)
          ·
            refine ⟨11845907515203771210842113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 252712693657680452497965077 11845907515203771210842113)
            ·
              refine ⟨8884430636402828408131585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11845907515203771210842113 8884430636402828408131585)
              ·
                refine ⟨6663322977302121306098689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8884430636402828408131585 6663322977302121306098689)
                ·
                  refine ⟨4997492232976590979574017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6663322977302121306098689 4997492232976590979574017)
                  ·
                    refine ⟨3748119174732443234680513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4997492232976590979574017 3748119174732443234680513)
                    ·
                      refine ⟨2811089381049332426010385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3748119174732443234680513 2811089381049332426010385)
                      ·
                        rfl

theorem cell23_5474577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 6, 2, 2, 2, 2, 2].length) (baseStart_5474577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474577 prefixEnd_5474577 := by exact prefixLift 5474577
  have htrace : WordTrace (prefixWord ++ tailWord_5474577) baseStart_5474577 baseEnd_5474577 := by
    simpa [prefixWord, tailWord_5474577, baseEnd_5474577] using wordTrace_append hprefix tailTrace_5474577
  have hstable : (prefixWord ++ tailWord_5474577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474577).length < 2 ^ (prefixWord ++ tailWord_5474577).sum := by decide
  have hdescent : baseEnd_5474577 < baseStart_5474577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474590 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_5474590 : Nat := 118140960795 + 5474590 * 2 ^ 59
def prefixEnd_5474590 : Nat := 4983230072969 + 3 ^ 40 * 5474590 * 2
def baseEnd_5474590 : Nat := 2811096056297840875147825

theorem tailTrace_5474590 : CollatzResearch.WordTrace tailWord_5474590 prefixEnd_5474590 2811096056297840875147825 := by
  unfold tailWord_5474590
  simp only [CollatzResearch.WordTrace]
  refine ⟨24959337654562861297388653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133116467491001926919406149 24959337654562861297388653)
  ·
    refine ⟨9359751620461072986520745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24959337654562861297388653 9359751620461072986520745)
    ·
      refine ⟨7019813715345804739890559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9359751620461072986520745 7019813715345804739890559)
      ·
        refine ⟨10529720573018707109835839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7019813715345804739890559 10529720573018707109835839)
        ·
          refine ⟨15794580859528060664753759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10529720573018707109835839 15794580859528060664753759)
          ·
            refine ⟨23691871289292090997130639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15794580859528060664753759 23691871289292090997130639)
            ·
              refine ⟨35537806933938136495695959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23691871289292090997130639 35537806933938136495695959)
              ·
                refine ⟨53306710400907204743543939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35537806933938136495695959 53306710400907204743543939)
                ·
                  refine ⟨79960065601360807115315909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53306710400907204743543939 79960065601360807115315909)
                  ·
                    refine ⟨14992512300255151334121733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79960065601360807115315909 14992512300255151334121733)
                    ·
                      refine ⟨2811096056297840875147825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14992512300255151334121733 2811096056297840875147825)
                      ·
                        rfl

theorem cell23_5474590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_5474590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474590 prefixEnd_5474590 := by exact prefixLift 5474590
  have htrace : WordTrace (prefixWord ++ tailWord_5474590) baseStart_5474590 baseEnd_5474590 := by
    simpa [prefixWord, tailWord_5474590, baseEnd_5474590] using wordTrace_append hprefix tailTrace_5474590
  have hstable : (prefixWord ++ tailWord_5474590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474590).length < 2 ^ (prefixWord ++ tailWord_5474590).sum := by decide
  have hdescent : baseEnd_5474590 < baseStart_5474590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474628 : List Nat := [2, 3, 4, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_5474628 : Nat := 118140960795 + 5474628 * 2 ^ 59
def prefixEnd_5474628 : Nat := 4983230072969 + 3 ^ 40 * 5474628 * 2
def baseEnd_5474628 : Nat := 2811115568562711726472651

theorem tailTrace_5474628 : CollatzResearch.WordTrace tailWord_5474628 prefixEnd_5474628 2811115568562711726472651 := by
  unfold tailWord_5474628
  simp only [CollatzResearch.WordTrace]
  refine ⟨99838043605182611434496269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133117391473576815245995025 99838043605182611434496269)
  ·
    refine ⟨37439266351943479287936101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99838043605182611434496269 37439266351943479287936101)
    ·
      refine ⟨7019862440989402366488019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37439266351943479287936101 7019862440989402366488019)
      ·
        refine ⟨10529793661484103549732029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7019862440989402366488019 10529793661484103549732029)
        ·
          refine ⟨3948672623056538831149511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10529793661484103549732029 3948672623056538831149511)
          ·
            refine ⟨5923008934584808246724267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3948672623056538831149511 5923008934584808246724267)
            ·
              refine ⟨8884513401877212370086401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5923008934584808246724267 8884513401877212370086401)
              ·
                refine ⟨6663385051407909277564801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8884513401877212370086401 6663385051407909277564801)
                ·
                  refine ⟨4997538788555931958173601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6663385051407909277564801 4997538788555931958173601)
                  ·
                    refine ⟨3748154091416948968630201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4997538788555931958173601 3748154091416948968630201)
                    ·
                      refine ⟨2811115568562711726472651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3748154091416948968630201 2811115568562711726472651)
                      ·
                        rfl

theorem cell23_5474628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_5474628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474628 prefixEnd_5474628 := by exact prefixLift 5474628
  have htrace : WordTrace (prefixWord ++ tailWord_5474628) baseStart_5474628 baseEnd_5474628 := by
    simpa [prefixWord, tailWord_5474628, baseEnd_5474628] using wordTrace_append hprefix tailTrace_5474628
  have hstable : (prefixWord ++ tailWord_5474628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474628).length < 2 ^ (prefixWord ++ tailWord_5474628).sum := by decide
  have hdescent : baseEnd_5474628 < baseStart_5474628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474720 : List Nat := [2, 1, 1, 4, 1, 3, 3, 2, 1, 5]
def baseStart_5474720 : Nat := 118140960795 + 5474720 * 2 ^ 59
def prefixEnd_5474720 : Nat := 4983230072969 + 3 ^ 40 * 5474720 * 2
def baseEnd_5474720 : Nat := 937054269594308455507409

theorem tailTrace_5474720 : CollatzResearch.WordTrace tailWord_5474720 prefixEnd_5474720 937054269594308455507409 := by
  unfold tailWord_5474720
  simp only [CollatzResearch.WordTrace]
  refine ⟨99839721363015961290670807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133119628484021281720894409 99839721363015961290670807)
  ·
    refine ⟨149759582044523941936006211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99839721363015961290670807 149759582044523941936006211)
    ·
      refine ⟨224639373066785912904009317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149759582044523941936006211 224639373066785912904009317)
      ·
        refine ⟨42119882450022358669501747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224639373066785912904009317 42119882450022358669501747)
        ·
          refine ⟨63179823675033538004252621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42119882450022358669501747 63179823675033538004252621)
          ·
            refine ⟨23692433878137576751594733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63179823675033538004252621 23692433878137576751594733)
            ·
              refine ⟨8884662704301591281848025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23692433878137576751594733 8884662704301591281848025)
              ·
                refine ⟨6663497028226193461386019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8884662704301591281848025 6663497028226193461386019)
                ·
                  refine ⟨9995245542339290192079029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6663497028226193461386019 9995245542339290192079029)
                  ·
                    refine ⟨937054269594308455507409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9995245542339290192079029 937054269594308455507409)
                    ·
                      rfl

theorem cell23_5474720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 3, 2, 1, 5].length) (baseStart_5474720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474720 prefixEnd_5474720 := by exact prefixLift 5474720
  have htrace : WordTrace (prefixWord ++ tailWord_5474720) baseStart_5474720 baseEnd_5474720 := by
    simpa [prefixWord, tailWord_5474720, baseEnd_5474720] using wordTrace_append hprefix tailTrace_5474720
  have hstable : (prefixWord ++ tailWord_5474720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474720).length < 2 ^ (prefixWord ++ tailWord_5474720).sum := by decide
  have hdescent : baseEnd_5474720 < baseStart_5474720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474727 : List Nat := [1, 1, 6, 1, 1, 2, 1, 3, 2, 3, 2]
def baseStart_5474727 : Nat := 118140960795 + 5474727 * 2 ^ 59
def prefixEnd_5474727 : Nat := 4983230072969 + 3 ^ 40 * 5474727 * 2
def baseEnd_5474727 : Nat := 2811166403147506839134695

theorem tailTrace_5474727 : CollatzResearch.WordTrace tailWord_5474727 prefixEnd_5474727 2811166403147506839134695 := by
  unfold tailWord_5474727
  simp only [CollatzResearch.WordTrace]
  refine ⟨199679698037006562776846435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133119798691337708517897623 199679698037006562776846435)
  ·
    refine ⟨299519547055509844165269653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199679698037006562776846435 299519547055509844165269653)
    ·
      refine ⟨14039978768227023945247015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 299519547055509844165269653 14039978768227023945247015)
      ·
        refine ⟨21059968152340535917870523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14039978768227023945247015 21059968152340535917870523)
        ·
          refine ⟨31589952228510803876805785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21059968152340535917870523 31589952228510803876805785)
          ·
            refine ⟨23692464171383102907604339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31589952228510803876805785 23692464171383102907604339)
            ·
              refine ⟨35538696257074654361406509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23692464171383102907604339 35538696257074654361406509)
              ·
                refine ⟨13327011096402995385527441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35538696257074654361406509 13327011096402995385527441)
                ·
                  refine ⟨9995258322302246539145581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13327011096402995385527441 9995258322302246539145581)
                  ·
                    refine ⟨3748221870863342452179593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9995258322302246539145581 3748221870863342452179593)
                    ·
                      refine ⟨2811166403147506839134695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3748221870863342452179593 2811166403147506839134695)
                      ·
                        rfl

theorem cell23_5474727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 3, 2, 3, 2].length) (baseStart_5474727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474727 prefixEnd_5474727 := by exact prefixLift 5474727
  have htrace : WordTrace (prefixWord ++ tailWord_5474727) baseStart_5474727 baseEnd_5474727 := by
    simpa [prefixWord, tailWord_5474727, baseEnd_5474727] using wordTrace_append hprefix tailTrace_5474727
  have hstable : (prefixWord ++ tailWord_5474727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474727).length < 2 ^ (prefixWord ++ tailWord_5474727).sum := by decide
  have hdescent : baseEnd_5474727 < baseStart_5474727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474737 : List Nat := [1, 2, 2, 4, 1, 3, 3, 1, 1, 5]
def baseStart_5474737 : Nat := 118140960795 + 5474737 * 2 ^ 59
def prefixEnd_5474737 : Nat := 4983230072969 + 3 ^ 40 * 5474737 * 2
def baseEnd_5474737 : Nat := 937057179318017266669883

theorem tailTrace_5474737 : CollatzResearch.WordTrace tailWord_5474737 prefixEnd_5474737 937057179318017266669883 := by
  unfold tailWord_5474737
  simp only [CollatzResearch.WordTrace]
  refine ⟨199680062766970334484710465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133120041844646889656473643 199680062766970334484710465)
  ·
    refine ⟨149760047075227750863532849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199680062766970334484710465 149760047075227750863532849)
    ·
      refine ⟨112320035306420813147649637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149760047075227750863532849 112320035306420813147649637)
      ·
        refine ⟨21060006619953902465184307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112320035306420813147649637 21060006619953902465184307)
        ·
          refine ⟨31590009929930853697776461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21060006619953902465184307 31590009929930853697776461)
          ·
            refine ⟨11846253723724070136666173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31590009929930853697776461 11846253723724070136666173)
            ·
              refine ⟨4442345146396526301249815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11846253723724070136666173 4442345146396526301249815)
              ·
                refine ⟨6663517719594789451874723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4442345146396526301249815 6663517719594789451874723)
                ·
                  refine ⟨9995276579392184177812085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6663517719594789451874723 9995276579392184177812085)
                  ·
                    refine ⟨937057179318017266669883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9995276579392184177812085 937057179318017266669883)
                    ·
                      rfl

theorem cell23_5474737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 3, 1, 1, 5].length) (baseStart_5474737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474737 prefixEnd_5474737 := by exact prefixLift 5474737
  have htrace : WordTrace (prefixWord ++ tailWord_5474737) baseStart_5474737 baseEnd_5474737 := by
    simpa [prefixWord, tailWord_5474737, baseEnd_5474737] using wordTrace_append hprefix tailTrace_5474737
  have hstable : (prefixWord ++ tailWord_5474737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474737).length < 2 ^ (prefixWord ++ tailWord_5474737).sum := by decide
  have hdescent : baseEnd_5474737 < baseStart_5474737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474750 : List Nat := [4, 2, 1, 1, 1, 1, 2, 3, 4, 4]
def baseStart_5474750 : Nat := 118140960795 + 5474750 * 2 ^ 59
def prefixEnd_5474750 : Nat := 4983230072969 + 3 ^ 40 * 5474750 * 2
def baseEnd_5474750 : Nat := 937059404400853416382363

theorem tailTrace_5474750 : CollatzResearch.WordTrace tailWord_5474750 prefixEnd_5474750 937059404400853416382363 := by
  unfold tailWord_5474750
  simp only [CollatzResearch.WordTrace]
  refine ⟨24960067114490404713116713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133120357943948825136622469 24960067114490404713116713)
  ·
    refine ⟨18720050335867803534837535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24960067114490404713116713 18720050335867803534837535)
    ·
      refine ⟨28080075503801705302256303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18720050335867803534837535 28080075503801705302256303)
      ·
        refine ⟨42120113255702557953384455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28080075503801705302256303 42120113255702557953384455)
        ·
          refine ⟨63180169883553836930076683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42120113255702557953384455 63180169883553836930076683)
          ·
            refine ⟨94770254825330755395115025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63180169883553836930076683 94770254825330755395115025)
            ·
              refine ⟨71077691118998066546336269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94770254825330755395115025 71077691118998066546336269)
              ·
                refine ⟨26654134169624274954876101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71077691118998066546336269 26654134169624274954876101)
                ·
                  refine ⟨4997650156804551554039269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26654134169624274954876101 4997650156804551554039269)
                  ·
                    refine ⟨937059404400853416382363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4997650156804551554039269 937059404400853416382363)
                    ·
                      rfl

theorem cell23_5474750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_5474750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474750 prefixEnd_5474750 := by exact prefixLift 5474750
  have htrace : WordTrace (prefixWord ++ tailWord_5474750) baseStart_5474750 baseEnd_5474750 := by
    simpa [prefixWord, tailWord_5474750, baseEnd_5474750] using wordTrace_append hprefix tailTrace_5474750
  have hstable : (prefixWord ++ tailWord_5474750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474750).length < 2 ^ (prefixWord ++ tailWord_5474750).sum := by decide
  have hdescent : baseEnd_5474750 < baseStart_5474750 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474760 : List Nat := [2, 1, 3, 1, 3, 2, 1, 2, 3, 2, 3]
def baseStart_5474760 : Nat := 118140960795 + 5474760 * 2 ^ 59
def prefixEnd_5474760 : Nat := 4983230072969 + 3 ^ 40 * 5474760 * 2
def baseEnd_5474760 : Nat := 2811183348009105210022043

theorem tailTrace_5474760 : CollatzResearch.WordTrace tailWord_5474760 prefixEnd_5474760 2811183348009105210022043 := by
  unfold tailWord_5474760
  simp only [CollatzResearch.WordTrace]
  refine ⟨99840450822943504706398867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133120601097258006275198489 99840450822943504706398867)
  ·
    refine ⟨149760676234415257059598301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99840450822943504706398867 149760676234415257059598301)
    ·
      refine ⟨56160253587905721397349363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149760676234415257059598301 56160253587905721397349363)
      ·
        refine ⟨84240380381858582096024045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56160253587905721397349363 84240380381858582096024045)
        ·
          refine ⟨31590142643196968286009017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84240380381858582096024045 31590142643196968286009017)
          ·
            refine ⟨23692606982397726214506763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31590142643196968286009017 23692606982397726214506763)
            ·
              refine ⟨35538910473596589321760145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23692606982397726214506763 35538910473596589321760145)
              ·
                refine ⟨26654182855197441991320109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35538910473596589321760145 26654182855197441991320109)
                ·
                  refine ⟨9995318570699040746745041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26654182855197441991320109 9995318570699040746745041)
                  ·
                    refine ⟨7496488928024280560058781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9995318570699040746745041 7496488928024280560058781)
                    ·
                      refine ⟨2811183348009105210022043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7496488928024280560058781 2811183348009105210022043)
                      ·
                        rfl

theorem cell23_5474760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_5474760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474760 prefixEnd_5474760 := by exact prefixLift 5474760
  have htrace : WordTrace (prefixWord ++ tailWord_5474760) baseStart_5474760 baseEnd_5474760 := by
    simpa [prefixWord, tailWord_5474760, baseEnd_5474760] using wordTrace_append hprefix tailTrace_5474760
  have hstable : (prefixWord ++ tailWord_5474760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474760).length < 2 ^ (prefixWord ++ tailWord_5474760).sum := by decide
  have hdescent : baseEnd_5474760 < baseStart_5474760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474791 : List Nat := [1, 1, 5, 2, 1, 1, 4, 3, 1, 2, 2]
def baseStart_5474791 : Nat := 118140960795 + 5474791 * 2 ^ 59
def prefixEnd_5474791 : Nat := 4983230072969 + 3 ^ 40 * 5474791 * 2
def baseEnd_5474791 : Nat := 2811199265909394588734401

theorem tailTrace_5474791 : CollatzResearch.WordTrace tailWord_5474791 prefixEnd_5474791 2811199265909394588734401 := by
  unfold tailWord_5474791
  simp only [CollatzResearch.WordTrace]
  refine ⟨199682032308774701707176227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133121354872516467804784151 199682032308774701707176227)
  ·
    refine ⟨299523048463162052560764341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199682032308774701707176227 299523048463162052560764341)
    ·
      refine ⟨28080285793421442427571657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 299523048463162052560764341 28080285793421442427571657)
      ·
        refine ⟨21060214345066081820678743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28080285793421442427571657 21060214345066081820678743)
        ·
          refine ⟨31590321517599122731018115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21060214345066081820678743 31590321517599122731018115)
          ·
            refine ⟨47385482276398684096527173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31590321517599122731018115 47385482276398684096527173)
            ·
              refine ⟨8884777926824753268098845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47385482276398684096527173 8884777926824753268098845)
              ·
                refine ⟨3331791722559282475537067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8884777926824753268098845 3331791722559282475537067)
                ·
                  refine ⟨4997687583838923713305601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3331791722559282475537067 4997687583838923713305601)
                  ·
                    refine ⟨3748265687879192784979201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4997687583838923713305601 3748265687879192784979201)
                    ·
                      refine ⟨2811199265909394588734401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3748265687879192784979201 2811199265909394588734401)
                      ·
                        rfl

theorem cell23_5474791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_5474791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474791 prefixEnd_5474791 := by exact prefixLift 5474791
  have htrace : WordTrace (prefixWord ++ tailWord_5474791) baseStart_5474791 baseEnd_5474791 := by
    simpa [prefixWord, tailWord_5474791, baseEnd_5474791] using wordTrace_append hprefix tailTrace_5474791
  have hstable : (prefixWord ++ tailWord_5474791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474791).length < 2 ^ (prefixWord ++ tailWord_5474791).sum := by decide
  have hdescent : baseEnd_5474791 < baseStart_5474791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474794 : List Nat := [3, 1, 3, 1, 3, 1, 4, 1, 1, 2, 3]
def baseStart_5474794 : Nat := 118140960795 + 5474794 * 2 ^ 59
def prefixEnd_5474794 : Nat := 4983230072969 + 3 ^ 40 * 5474794 * 2
def baseEnd_5474794 : Nat := 2811200806351358076996887

theorem tailTrace_5474794 : CollatzResearch.WordTrace tailWord_5474794 prefixEnd_5474794 2811200806351358076996887 := by
  unfold tailWord_5474794
  simp only [CollatzResearch.WordTrace]
  refine ⟨49920535431940958304883859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133121427818509222146356957 49920535431940958304883859)
  ·
    refine ⟨74880803147911437457325789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49920535431940958304883859 74880803147911437457325789)
    ·
      refine ⟨28080301180466789046497171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74880803147911437457325789 28080301180466789046497171)
      ·
        refine ⟨42120451770700183569745757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28080301180466789046497171 42120451770700183569745757)
        ·
          refine ⟨15795169414012568838654659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42120451770700183569745757 15795169414012568838654659)
          ·
            refine ⟨23692754121018853257981989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15795169414012568838654659 23692754121018853257981989)
            ·
              refine ⟨4442391397691034985871623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23692754121018853257981989 4442391397691034985871623)
              ·
                refine ⟨6663587096536552478807435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4442391397691034985871623 6663587096536552478807435)
                ·
                  refine ⟨9995380644804828718211153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6663587096536552478807435 9995380644804828718211153)
                  ·
                    refine ⟨7496535483603621538658365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9995380644804828718211153 7496535483603621538658365)
                    ·
                      refine ⟨2811200806351358076996887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7496535483603621538658365 2811200806351358076996887)
                      ·
                        rfl

theorem cell23_5474794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_5474794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474794 prefixEnd_5474794 := by exact prefixLift 5474794
  have htrace : WordTrace (prefixWord ++ tailWord_5474794) baseStart_5474794 baseEnd_5474794 := by
    simpa [prefixWord, tailWord_5474794, baseEnd_5474794] using wordTrace_append hprefix tailTrace_5474794
  have hstable : (prefixWord ++ tailWord_5474794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474794).length < 2 ^ (prefixWord ++ tailWord_5474794).sum := by decide
  have hdescent : baseEnd_5474794 < baseStart_5474794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474850 : List Nat := [3, 3, 1, 1, 1, 1, 1, 2, 1, 6, 3]
def baseStart_5474850 : Nat := 118140960795 + 5474850 * 2 ^ 59
def prefixEnd_5474850 : Nat := 4983230072969 + 3 ^ 40 * 5474850 * 2
def baseEnd_5474850 : Nat := 2811229561268009857896629

theorem tailTrace_5474850 : CollatzResearch.WordTrace tailWord_5474850 prefixEnd_5474850 2811229561268009857896629 := by
  unfold tailWord_5474850
  simp only [CollatzResearch.WordTrace]
  refine ⟨49921046053890238695893501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133122789477040636522382669 49921046053890238695893501)
  ·
    refine ⟨18720392270208839510960063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49921046053890238695893501 18720392270208839510960063)
    ·
      refine ⟨28080588405313259266440095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18720392270208839510960063 28080588405313259266440095)
      ·
        refine ⟨42120882607969888899660143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28080588405313259266440095 42120882607969888899660143)
        ·
          refine ⟨63181323911954833349490215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42120882607969888899660143 63181323911954833349490215)
          ·
            refine ⟨94771985867932250024235323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63181323911954833349490215 94771985867932250024235323)
            ·
              refine ⟨142157978801898375036352985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94771985867932250024235323 142157978801898375036352985)
              ·
                refine ⟨106618484101423781277264739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142157978801898375036352985 106618484101423781277264739)
                ·
                  refine ⟨159927726152135671915897109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106618484101423781277264739 159927726152135671915897109)
                  ·
                    refine ⟨7496612163381359621057677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 159927726152135671915897109 7496612163381359621057677)
                    ·
                      refine ⟨2811229561268009857896629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7496612163381359621057677 2811229561268009857896629)
                      ·
                        rfl

theorem cell23_5474850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_5474850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474850 prefixEnd_5474850 := by exact prefixLift 5474850
  have htrace : WordTrace (prefixWord ++ tailWord_5474850) baseStart_5474850 baseEnd_5474850 := by
    simpa [prefixWord, tailWord_5474850, baseEnd_5474850] using wordTrace_append hprefix tailTrace_5474850
  have hstable : (prefixWord ++ tailWord_5474850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474850).length < 2 ^ (prefixWord ++ tailWord_5474850).sum := by decide
  have hdescent : baseEnd_5474850 < baseStart_5474850 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474853 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 9]
def baseStart_5474853 : Nat := 118140960795 + 5474853 * 2 ^ 59
def prefixEnd_5474853 : Nat := 4983230072969 + 3 ^ 40 * 5474853 * 2
def baseEnd_5474853 : Nat := 312359011301108149573235

theorem tailTrace_5474853 : CollatzResearch.WordTrace tailWord_5474853 prefixEnd_5474853 312359011301108149573235 := by
  unfold tailWord_5474853
  simp only [CollatzResearch.WordTrace]
  refine ⟨199684293634550086295933213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133122862423033390863955475 199684293634550086295933213)
  ·
    refine ⟨74881610112956282360974955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199684293634550086295933213 74881610112956282360974955)
    ·
      refine ⟨112322415169434423541462433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74881610112956282360974955 112322415169434423541462433)
      ·
        refine ⟨84241811377075817656096825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112322415169434423541462433 84241811377075817656096825)
        ·
          refine ⟨63181358532806863242072619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84241811377075817656096825 63181358532806863242072619)
          ·
            refine ⟨94772037799210294863108929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63181358532806863242072619 94772037799210294863108929)
            ·
              refine ⟨71079028349407721147331697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94772037799210294863108929 71079028349407721147331697)
              ·
                refine ⟨53309271262055790860498773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71079028349407721147331697 53309271262055790860498773)
                ·
                  refine ⟨312359011301108149573235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53309271262055790860498773 312359011301108149573235)
                  ·
                    rfl

theorem cell23_5474853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 9].length) (baseStart_5474853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474853 prefixEnd_5474853 := by exact prefixLift 5474853
  have htrace : WordTrace (prefixWord ++ tailWord_5474853) baseStart_5474853 baseEnd_5474853 := by
    simpa [prefixWord, tailWord_5474853, baseEnd_5474853] using wordTrace_append hprefix tailTrace_5474853
  have hstable : (prefixWord ++ tailWord_5474853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474853).length < 2 ^ (prefixWord ++ tailWord_5474853).sum := by decide
  have hdescent : baseEnd_5474853 < baseStart_5474853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474880 : List Nat := [2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 3]
def baseStart_5474880 : Nat := 118140960795 + 5474880 * 2 ^ 59
def prefixEnd_5474880 : Nat := 4983230072969 + 3 ^ 40 * 5474880 * 2
def baseEnd_5474880 : Nat := 2811244965687644740521491

theorem tailTrace_5474880 : CollatzResearch.WordTrace tailWord_5474880 prefixEnd_5474880 2811244965687644740521491 := by
  unfold tailWord_5474880
  simp only [CollatzResearch.WordTrace]
  refine ⟨99842639202726134953583047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133123518936968179938110729 99842639202726134953583047)
  ·
    refine ⟨149763958804089202430374571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99842639202726134953583047 149763958804089202430374571)
    ·
      refine ⟨224645938206133803645561857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149763958804089202430374571 224645938206133803645561857)
      ·
        refine ⟨168484453654600352734171393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224645938206133803645561857 168484453654600352734171393)
        ·
          refine ⟨126363340240950264550628545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168484453654600352734171393 126363340240950264550628545)
          ·
            refine ⟨94772505180712698412971409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126363340240950264550628545 94772505180712698412971409)
            ·
              refine ⟨71079378885534523809728557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94772505180712698412971409 71079378885534523809728557)
              ·
                refine ⟨26654767082075446428648209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71079378885534523809728557 26654767082075446428648209)
                ·
                  refine ⟨19991075311556584821486157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26654767082075446428648209 19991075311556584821486157)
                  ·
                    refine ⟨7496653241833719308057309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19991075311556584821486157 7496653241833719308057309)
                    ·
                      refine ⟨2811244965687644740521491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7496653241833719308057309 2811244965687644740521491)
                      ·
                        rfl

theorem cell23_5474880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 3].length) (baseStart_5474880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474880 prefixEnd_5474880 := by exact prefixLift 5474880
  have htrace : WordTrace (prefixWord ++ tailWord_5474880) baseStart_5474880 baseEnd_5474880 := by
    simpa [prefixWord, tailWord_5474880, baseEnd_5474880] using wordTrace_append hprefix tailTrace_5474880
  have hstable : (prefixWord ++ tailWord_5474880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474880).length < 2 ^ (prefixWord ++ tailWord_5474880).sum := by decide
  have hdescent : baseEnd_5474880 < baseStart_5474880 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474881 : List Nat := [1, 2, 5, 1, 1, 3, 1, 3, 2, 2, 2]
def baseStart_5474881 : Nat := 118140960795 + 5474881 * 2 ^ 59
def prefixEnd_5474881 : Nat := 4983230072969 + 3 ^ 40 * 5474881 * 2
def baseEnd_5474881 : Nat := 2811245479168299236608987

theorem tailTrace_5474881 : CollatzResearch.WordTrace tailWord_5474881 prefixEnd_5474881 2811245479168299236608987 := by
  unfold tailWord_5474881
  simp only [CollatzResearch.WordTrace]
  refine ⟨199685314878448647077952497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133123543252299098051968331 199685314878448647077952497)
  ·
    refine ⟨149763986158836485308464373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199685314878448647077952497 149763986158836485308464373)
    ·
      refine ⟨14040373702390920497668535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149763986158836485308464373 14040373702390920497668535)
      ·
        refine ⟨21060560553586380746502803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14040373702390920497668535 21060560553586380746502803)
        ·
          refine ⟨31590840830379571119754205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21060560553586380746502803 31590840830379571119754205)
          ·
            refine ⟨11846565311392339169907827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31590840830379571119754205 11846565311392339169907827)
            ·
              refine ⟨17769847967088508754861741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11846565311392339169907827 17769847967088508754861741)
              ·
                refine ⟨6663692987658190783073153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17769847967088508754861741 6663692987658190783073153)
                ·
                  refine ⟨4997769740743643087304865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6663692987658190783073153 4997769740743643087304865)
                  ·
                    refine ⟨3748327305557732315478649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4997769740743643087304865 3748327305557732315478649)
                    ·
                      refine ⟨2811245479168299236608987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3748327305557732315478649 2811245479168299236608987)
                      ·
                        rfl

theorem cell23_5474881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_5474881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474881 prefixEnd_5474881 := by exact prefixLift 5474881
  have htrace : WordTrace (prefixWord ++ tailWord_5474881) baseStart_5474881 baseEnd_5474881 := by
    simpa [prefixWord, tailWord_5474881, baseEnd_5474881] using wordTrace_append hprefix tailTrace_5474881
  have hstable : (prefixWord ++ tailWord_5474881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474881).length < 2 ^ (prefixWord ++ tailWord_5474881).sum := by decide
  have hdescent : baseEnd_5474881 < baseStart_5474881 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474883 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 3, 7]
def baseStart_5474883 : Nat := 118140960795 + 5474883 * 2 ^ 59
def prefixEnd_5474883 : Nat := 4983230072969 + 3 ^ 40 * 5474883 * 2
def baseEnd_5474883 : Nat := 937082168709869409594659

theorem tailTrace_5474883 : CollatzResearch.WordTrace tailWord_5474883 prefixEnd_5474883 937082168709869409594659 := by
  unfold tailWord_5474883
  simp only [CollatzResearch.WordTrace]
  refine ⟨199685387824441401419525303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133123591882960934279683535 199685387824441401419525303)
  ·
    refine ⟨299528081736662102129287955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199685387824441401419525303 299528081736662102129287955)
    ·
      refine ⟨449292122604993153193931933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299528081736662102129287955 449292122604993153193931933)
      ·
        refine ⟨168484545976872432447724475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 449292122604993153193931933 168484545976872432447724475)
        ·
          refine ⟨252726818965308648671586713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168484545976872432447724475 252726818965308648671586713)
          ·
            refine ⟨189545114223981486503690035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252726818965308648671586713 189545114223981486503690035)
            ·
              refine ⟨284317671335972229755535053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189545114223981486503690035 284317671335972229755535053)
              ·
                refine ⟨106619126750989586158325645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 284317671335972229755535053 106619126750989586158325645)
                ·
                  refine ⟨39982172531621094809372117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106619126750989586158325645 39982172531621094809372117)
                  ·
                    refine ⟨937082168709869409594659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39982172531621094809372117 937082168709869409594659)
                    ·
                      rfl

theorem cell23_5474883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 3, 7].length) (baseStart_5474883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474883 prefixEnd_5474883 := by exact prefixLift 5474883
  have htrace : WordTrace (prefixWord ++ tailWord_5474883) baseStart_5474883 baseEnd_5474883 := by
    simpa [prefixWord, tailWord_5474883, baseEnd_5474883] using wordTrace_append hprefix tailTrace_5474883
  have hstable : (prefixWord ++ tailWord_5474883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474883).length < 2 ^ (prefixWord ++ tailWord_5474883).sum := by decide
  have hdescent : baseEnd_5474883 < baseStart_5474883 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474937 : List Nat := [1, 2, 1, 3, 3, 2, 1, 1, 1, 6, 2]
def baseStart_5474937 : Nat := 118140960795 + 5474937 * 2 ^ 59
def prefixEnd_5474937 : Nat := 4983230072969 + 3 ^ 40 * 5474937 * 2
def baseEnd_5474937 : Nat := 2811274234084951017508729

theorem tailTrace_5474937 : CollatzResearch.WordTrace tailWord_5474937 prefixEnd_5474937 2811274234084951017508729 := by
  unfold tailWord_5474937
  simp only [CollatzResearch.WordTrace]
  refine ⟨199687357366245768641991065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133124904910830512427994043 199687357366245768641991065)
  ·
    refine ⟨149765518024684326481493299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199687357366245768641991065 149765518024684326481493299)
    ·
      refine ⟨224648277037026489722239949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149765518024684326481493299 224648277037026489722239949)
      ·
        refine ⟨84243103888884933645839981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224648277037026489722239949 84243103888884933645839981)
        ·
          refine ⟨31591163958331850117189993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84243103888884933645839981 31591163958331850117189993)
          ·
            refine ⟨23693372968748887587892495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31591163958331850117189993 23693372968748887587892495)
            ·
              refine ⟨35540059453123331381838743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23693372968748887587892495 35540059453123331381838743)
              ·
                refine ⟨53310089179684997072758115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35540059453123331381838743 53310089179684997072758115)
                ·
                  refine ⟨79965133769527495609137173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53310089179684997072758115 79965133769527495609137173)
                  ·
                    refine ⟨3748365645446601356678305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79965133769527495609137173 3748365645446601356678305)
                    ·
                      refine ⟨2811274234084951017508729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3748365645446601356678305 2811274234084951017508729)
                      ·
                        rfl

theorem cell23_5474937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 1, 1, 6, 2].length) (baseStart_5474937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474937 prefixEnd_5474937 := by exact prefixLift 5474937
  have htrace : WordTrace (prefixWord ++ tailWord_5474937) baseStart_5474937 baseEnd_5474937 := by
    simpa [prefixWord, tailWord_5474937, baseEnd_5474937] using wordTrace_append hprefix tailTrace_5474937
  have hstable : (prefixWord ++ tailWord_5474937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474937).length < 2 ^ (prefixWord ++ tailWord_5474937).sum := by decide
  have hdescent : baseEnd_5474937 < baseStart_5474937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474974 : List Nat := [4, 3, 1, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_5474974 : Nat := 118140960795 + 5474974 * 2 ^ 59
def prefixEnd_5474974 : Nat := 4983230072969 + 3 ^ 40 * 5474974 * 2
def baseEnd_5474974 : Nat := 2811293232869167372746059

theorem tailTrace_5474974 : CollatzResearch.WordTrace tailWord_5474974 prefixEnd_5474974 2811293232869167372746059 := by
  unfold tailWord_5474974
  simp only [CollatzResearch.WordTrace]
  refine ⟨24961088358388965495135997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133125804578074482640725317 24961088358388965495135997)
  ·
    refine ⟨9360408134395862060675999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24961088358388965495135997 9360408134395862060675999)
    ·
      refine ⟨14040612201593793091013999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9360408134395862060675999 14040612201593793091013999)
      ·
        refine ⟨21060918302390689636520999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14040612201593793091013999 21060918302390689636520999)
        ·
          refine ⟨31591377453586034454781499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21060918302390689636520999 31591377453586034454781499)
          ·
            refine ⟨47387066180379051682172249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31591377453586034454781499 47387066180379051682172249)
            ·
              refine ⟨35540299635284288761629187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47387066180379051682172249 35540299635284288761629187)
              ·
                refine ⟨53310449452926433142443781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35540299635284288761629187 53310449452926433142443781)
                ·
                  refine ⟨9995709272423706214208209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53310449452926433142443781 9995709272423706214208209)
                  ·
                    refine ⟨7496781954317779660656157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9995709272423706214208209 7496781954317779660656157)
                    ·
                      refine ⟨2811293232869167372746059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7496781954317779660656157 2811293232869167372746059)
                      ·
                        rfl

theorem cell23_5474974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_5474974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474974 prefixEnd_5474974 := by exact prefixLift 5474974
  have htrace : WordTrace (prefixWord ++ tailWord_5474974) baseStart_5474974 baseEnd_5474974 := by
    simpa [prefixWord, tailWord_5474974, baseEnd_5474974] using wordTrace_append hprefix tailTrace_5474974
  have hstable : (prefixWord ++ tailWord_5474974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474974).length < 2 ^ (prefixWord ++ tailWord_5474974).sum := by decide
  have hdescent : baseEnd_5474974 < baseStart_5474974 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474977 : List Nat := [1, 2, 3, 3, 3, 1, 1, 1, 8]
def baseStart_5474977 : Nat := 118140960795 + 5474977 * 2 ^ 59
def prefixEnd_5474977 : Nat := 4983230072969 + 3 ^ 40 * 5474977 * 2
def baseEnd_5474977 : Nat := 312366085923458984556505

theorem tailTrace_5474977 : CollatzResearch.WordTrace tailWord_5474977 prefixEnd_5474977 312366085923458984556505 := by
  unfold tailWord_5474977
  simp only [CollatzResearch.WordTrace]
  refine ⟨199688816286100855473447185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133125877524067236982298123 199688816286100855473447185)
  ·
    refine ⟨149766612214575641605085389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199688816286100855473447185 149766612214575641605085389)
    ·
      refine ⟨56162479580465865601907021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149766612214575641605085389 56162479580465865601907021)
      ·
        refine ⟨21060929842674699600715133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56162479580465865601907021 21060929842674699600715133)
        ·
          refine ⟨7897848691003012350268175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21060929842674699600715133 7897848691003012350268175)
          ·
            refine ⟨11846773036504518525402263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7897848691003012350268175 11846773036504518525402263)
            ·
              refine ⟨17770159554756777788103395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11846773036504518525402263 17770159554756777788103395)
              ·
                refine ⟨26655239332135166682155093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17770159554756777788103395 26655239332135166682155093)
                ·
                  refine ⟨312366085923458984556505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26655239332135166682155093 312366085923458984556505)
                  ·
                    rfl

theorem cell23_5474977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 1, 1, 8].length) (baseStart_5474977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474977 prefixEnd_5474977 := by exact prefixLift 5474977
  have htrace : WordTrace (prefixWord ++ tailWord_5474977) baseStart_5474977 baseEnd_5474977 := by
    simpa [prefixWord, tailWord_5474977, baseEnd_5474977] using wordTrace_append hprefix tailTrace_5474977
  have hstable : (prefixWord ++ tailWord_5474977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474977).length < 2 ^ (prefixWord ++ tailWord_5474977).sum := by decide
  have hdescent : baseEnd_5474977 < baseStart_5474977 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5474980 : List Nat := [2, 3, 1, 2, 2, 1, 1, 1, 1, 1, 8]
def baseStart_5474980 : Nat := 118140960795 + 5474980 * 2 ^ 59
def prefixEnd_5474980 : Nat := 4983230072969 + 3 ^ 40 * 5474980 * 2
def baseEnd_5474980 : Nat := 2811296313753094349271031

theorem tailTrace_5474980 : CollatzResearch.WordTrace tailWord_5474980 prefixEnd_5474980 2811296313753094349271031 := by
  unfold tailWord_5474980
  simp only [CollatzResearch.WordTrace]
  refine ⟨99844462852544993492903197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133125950470059991323870929 99844462852544993492903197)
  ·
    refine ⟨37441673569704372559838699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99844462852544993492903197 37441673569704372559838699)
    ·
      refine ⟨56162510354556558839758049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37441673569704372559838699 56162510354556558839758049)
      ·
        refine ⟨42121882765917419129818537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56162510354556558839758049 42121882765917419129818537)
        ·
          refine ⟨31591412074438064347363903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42121882765917419129818537 31591412074438064347363903)
          ·
            refine ⟨47387118111657096521045855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31591412074438064347363903 47387118111657096521045855)
            ·
              refine ⟨71080677167485644781568783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47387118111657096521045855 71080677167485644781568783)
              ·
                refine ⟨106621015751228467172353175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71080677167485644781568783 106621015751228467172353175)
                ·
                  refine ⟨159931523626842700758529763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106621015751228467172353175 159931523626842700758529763)
                  ·
                    refine ⟨239897285440264051137794645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 159931523626842700758529763 239897285440264051137794645)
                    ·
                      refine ⟨2811296313753094349271031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 239897285440264051137794645 2811296313753094349271031)
                      ·
                        rfl

theorem cell23_5474980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_5474980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5474980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5474980 prefixEnd_5474980 := by exact prefixLift 5474980
  have htrace : WordTrace (prefixWord ++ tailWord_5474980) baseStart_5474980 baseEnd_5474980 := by
    simpa [prefixWord, tailWord_5474980, baseEnd_5474980] using wordTrace_append hprefix tailTrace_5474980
  have hstable : (prefixWord ++ tailWord_5474980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5474980).length < 2 ^ (prefixWord ++ tailWord_5474980).sum := by decide
  have hdescent : baseEnd_5474980 < baseStart_5474980 := by decide
  rcases family_descends (prefixWord ++ tailWord_5474980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475004 : List Nat := [2, 2, 2, 3, 1, 1, 1, 4, 3, 1, 3]
def baseStart_5475004 : Nat := 118140960795 + 5475004 * 2 ^ 59
def prefixEnd_5475004 : Nat := 4983230072969 + 3 ^ 40 * 5475004 * 2
def baseEnd_5475004 : Nat := 2811308637288802255370921

theorem tailTrace_5475004 : CollatzResearch.WordTrace tailWord_5475004 prefixEnd_5475004 2811308637288802255370921 := by
  unfold tailWord_5475004
  simp only [CollatzResearch.WordTrace]
  refine ⟨99844900528501519542340033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133126534038002026056453377 99844900528501519542340033)
  ·
    refine ⟨74883675396376139656755025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99844900528501519542340033 74883675396376139656755025)
    ·
      refine ⟨56162756547282104742566269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74883675396376139656755025 56162756547282104742566269)
      ·
        refine ⟨21061033705230789278462351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56162756547282104742566269 21061033705230789278462351)
        ·
          refine ⟨31591550557846183917693527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21061033705230789278462351 31591550557846183917693527)
          ·
            refine ⟨47387325836769275876540291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31591550557846183917693527 47387325836769275876540291)
            ·
              refine ⟨71080988755153913814810437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47387325836769275876540291 71080988755153913814810437)
              ·
                refine ⟨13327685391591358840276957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71080988755153913814810437 13327685391591358840276957)
                ·
                  refine ⟨4997882021846759565103859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13327685391591358840276957 4997882021846759565103859)
                  ·
                    refine ⟨7496823032770139347655789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4997882021846759565103859 7496823032770139347655789)
                    ·
                      refine ⟨2811308637288802255370921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7496823032770139347655789 2811308637288802255370921)
                      ·
                        rfl

theorem cell23_5475004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 3, 1, 3].length) (baseStart_5475004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475004 prefixEnd_5475004 := by exact prefixLift 5475004
  have htrace : WordTrace (prefixWord ++ tailWord_5475004) baseStart_5475004 baseEnd_5475004 := by
    simpa [prefixWord, tailWord_5475004, baseEnd_5475004] using wordTrace_append hprefix tailTrace_5475004
  have hstable : (prefixWord ++ tailWord_5475004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475004).length < 2 ^ (prefixWord ++ tailWord_5475004).sum := by decide
  have hdescent : baseEnd_5475004 < baseStart_5475004 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475007 : List Nat := [1, 1, 2, 2, 2, 4, 1, 4, 1, 5]
def baseStart_5475007 : Nat := 118140960795 + 5475007 * 2 ^ 59
def prefixEnd_5475007 : Nat := 4983230072969 + 3 ^ 40 * 5475007 * 2
def baseEnd_5475007 : Nat := 937103392576921914544469

theorem tailTrace_5475007 : CollatzResearch.WordTrace tailWord_5475007 prefixEnd_5475007 937103392576921914544469 := by
  unfold tailWord_5475007
  simp only [CollatzResearch.WordTrace]
  refine ⟨199689910475992170597039275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133126606983994780398026183 199689910475992170597039275)
  ·
    refine ⟨299534865713988255895558913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199689910475992170597039275 299534865713988255895558913)
    ·
      refine ⟨224651149285491191921669185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299534865713988255895558913 224651149285491191921669185)
      ·
        refine ⟨168488361964118393941251889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224651149285491191921669185 168488361964118393941251889)
        ·
          refine ⟨126366271473088795455938917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168488361964118393941251889 126366271473088795455938917)
          ·
            refine ⟨23693675901204149147988547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126366271473088795455938917 23693675901204149147988547)
            ·
              refine ⟨35540513851806223721982821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23693675901204149147988547 35540513851806223721982821)
              ·
                refine ⟨6663846347213666947871779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35540513851806223721982821 6663846347213666947871779)
                ·
                  refine ⟨9995769520820500421807669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6663846347213666947871779 9995769520820500421807669)
                  ·
                    refine ⟨937103392576921914544469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9995769520820500421807669 937103392576921914544469)
                    ·
                      rfl

theorem cell23_5475007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 4, 1, 5].length) (baseStart_5475007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475007 prefixEnd_5475007 := by exact prefixLift 5475007
  have htrace : WordTrace (prefixWord ++ tailWord_5475007) baseStart_5475007 baseEnd_5475007 := by
    simpa [prefixWord, tailWord_5475007, baseEnd_5475007] using wordTrace_append hprefix tailTrace_5475007
  have hstable : (prefixWord ++ tailWord_5475007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475007).length < 2 ^ (prefixWord ++ tailWord_5475007).sum := by decide
  have hdescent : baseEnd_5475007 < baseStart_5475007 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475057 : List Nat := [1, 2, 2, 2, 2, 2, 2, 3, 1, 2, 4]
def baseStart_5475057 : Nat := 118140960795 + 5475057 * 2 ^ 59
def prefixEnd_5475057 : Nat := 4983230072969 + 3 ^ 40 * 5475057 * 2
def baseEnd_5475057 : Nat := 2811335851763490548008177

theorem tailTrace_5475057 : CollatzResearch.WordTrace tailWord_5475057 prefixEnd_5475057 2811335851763490548008177 := by
  unfold tailWord_5475057
  simp only [CollatzResearch.WordTrace]
  refine ⟨199691734125811029136359425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133127822750540686090906283 199691734125811029136359425)
  ·
    refine ⟨149768800594358271852269569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199691734125811029136359425 149768800594358271852269569)
    ·
      refine ⟨112326600445768703889202177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149768800594358271852269569 112326600445768703889202177)
      ·
        refine ⟨84244950334326527916901633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112326600445768703889202177 84244950334326527916901633)
        ·
          refine ⟨63183712750744895937676225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84244950334326527916901633 63183712750744895937676225)
          ·
            refine ⟨47387784563058671953257169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63183712750744895937676225 47387784563058671953257169)
            ·
              refine ⟨35540838422294003964942877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47387784563058671953257169 35540838422294003964942877)
              ·
                refine ⟨13327814408360251486853579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35540838422294003964942877 13327814408360251486853579)
                ·
                  refine ⟨19991721612540377230280369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13327814408360251486853579 19991721612540377230280369)
                  ·
                    refine ⟨14993791209405282922710277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19991721612540377230280369 14993791209405282922710277)
                    ·
                      refine ⟨2811335851763490548008177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14993791209405282922710277 2811335851763490548008177)
                      ·
                        rfl

theorem cell23_5475057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_5475057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475057 prefixEnd_5475057 := by exact prefixLift 5475057
  have htrace : WordTrace (prefixWord ++ tailWord_5475057) baseStart_5475057 baseEnd_5475057 := by
    simpa [prefixWord, tailWord_5475057, baseEnd_5475057] using wordTrace_append hprefix tailTrace_5475057
  have hstable : (prefixWord ++ tailWord_5475057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475057).length < 2 ^ (prefixWord ++ tailWord_5475057).sum := by decide
  have hdescent : baseEnd_5475057 < baseStart_5475057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475074 : List Nat := [3, 4, 1, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_5475074 : Nat := 118140960795 + 5475074 * 2 ^ 59
def prefixEnd_5475074 : Nat := 4983230072969 + 3 ^ 40 * 5475074 * 2
def baseEnd_5475074 : Nat := 2811344580934616981495599

theorem tailTrace_5475074 : CollatzResearch.WordTrace tailWord_5475074 prefixEnd_5475074 2811344580934616981495599 := by
  unfold tailWord_5475074
  simp only [CollatzResearch.WordTrace]
  refine ⟨49923088541687360259932069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133128236111166294026485517 49923088541687360259932069)
  ·
    refine ⟨9360579101566380048737263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49923088541687360259932069 9360579101566380048737263)
    ·
      refine ⟨14040868652349570073105895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9360579101566380048737263 14040868652349570073105895)
      ·
        refine ⟨21061302978524355109658843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14040868652349570073105895 21061302978524355109658843)
        ·
          refine ⟨31591954467786532664488265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21061302978524355109658843 31591954467786532664488265)
          ·
            refine ⟨23693965850839899498366199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31591954467786532664488265 23693965850839899498366199)
            ·
              refine ⟨35540948776259849247549299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23693965850839899498366199 35540948776259849247549299)
              ·
                refine ⟨53311423164389773871323949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35540948776259849247549299 53311423164389773871323949)
                ·
                  refine ⟨19991783686646165201746481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53311423164389773871323949 19991783686646165201746481)
                  ·
                    refine ⟨14993837764984623901309861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19991783686646165201746481 14993837764984623901309861)
                    ·
                      refine ⟨2811344580934616981495599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14993837764984623901309861 2811344580934616981495599)
                      ·
                        rfl

theorem cell23_5475074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_5475074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475074 prefixEnd_5475074 := by exact prefixLift 5475074
  have htrace : WordTrace (prefixWord ++ tailWord_5475074) baseStart_5475074 baseEnd_5475074 := by
    simpa [prefixWord, tailWord_5475074, baseEnd_5475074] using wordTrace_append hprefix tailTrace_5475074
  have hstable : (prefixWord ++ tailWord_5475074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475074).length < 2 ^ (prefixWord ++ tailWord_5475074).sum := by decide
  have hdescent : baseEnd_5475074 < baseStart_5475074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475095 : List Nat := [1, 1, 3, 4, 3, 1, 1, 4, 1, 2, 2]
def baseStart_5475095 : Nat := 118140960795 + 5475095 * 2 ^ 59
def prefixEnd_5475095 : Nat := 4983230072969 + 3 ^ 40 * 5475095 * 2
def baseEnd_5475095 : Nat := 2811355364028361399333003

theorem tailTrace_5475095 : CollatzResearch.WordTrace tailWord_5475095 prefixEnd_5475095 2811355364028361399333003 := by
  unfold tailWord_5475095
  simp only [CollatzResearch.WordTrace]
  refine ⟨199693120099673361626242739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133128746733115574417495159 199693120099673361626242739)
  ·
    refine ⟨299539680149510042439364109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199693120099673361626242739 299539680149510042439364109)
    ·
      refine ⟨112327380056066265914761541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299539680149510042439364109 112327380056066265914761541)
      ·
        refine ⟨21061383760512424859017789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 112327380056066265914761541 21061383760512424859017789)
        ·
          refine ⟨7898018910192159322131671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21061383760512424859017789 7898018910192159322131671)
          ·
            refine ⟨11847028365288238983197507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7898018910192159322131671 11847028365288238983197507)
            ·
              refine ⟨17770542547932358474796261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11847028365288238983197507 17770542547932358474796261)
              ·
                refine ⟨3331976727737317214024299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17770542547932358474796261 3331976727737317214024299)
                ·
                  refine ⟨4997965091605975821036449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3331976727737317214024299 4997965091605975821036449)
                  ·
                    refine ⟨3748473818704481865777337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4997965091605975821036449 3748473818704481865777337)
                    ·
                      refine ⟨2811355364028361399333003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3748473818704481865777337 2811355364028361399333003)
                      ·
                        rfl

theorem cell23_5475095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_5475095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475095 prefixEnd_5475095 := by exact prefixLift 5475095
  have htrace : WordTrace (prefixWord ++ tailWord_5475095) baseStart_5475095 baseEnd_5475095 := by
    simpa [prefixWord, tailWord_5475095, baseEnd_5475095] using wordTrace_append hprefix tailTrace_5475095
  have hstable : (prefixWord ++ tailWord_5475095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475095).length < 2 ^ (prefixWord ++ tailWord_5475095).sum := by decide
  have hdescent : baseEnd_5475095 < baseStart_5475095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475101 : List Nat := [1, 4, 2, 4, 1, 2, 1, 8]
def baseStart_5475101 : Nat := 118140960795 + 5475101 * 2 ^ 59
def prefixEnd_5475101 : Nat := 4983230072969 + 3 ^ 40 * 5475101 * 2
def baseEnd_5475101 : Nat := 104124386848603273179925

theorem tailTrace_5475101 : CollatzResearch.WordTrace tailWord_5475101 prefixEnd_5475101 104124386848603273179925 := by
  unfold tailWord_5475101
  simp only [CollatzResearch.WordTrace]
  refine ⟨199693338937651624650961157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133128892625101083100640771 199693338937651624650961157)
  ·
    refine ⟨37442501050809679622055217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199693338937651624650961157 37442501050809679622055217)
    ·
      refine ⟨28081875788107259716541413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37442501050809679622055217 28081875788107259716541413)
      ·
        refine ⟨5265351710270111196851515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28081875788107259716541413 5265351710270111196851515)
        ·
          refine ⟨7898027565405166795277273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5265351710270111196851515 7898027565405166795277273)
          ·
            refine ⟨5923520674053875096457955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7898027565405166795277273 5923520674053875096457955)
            ·
              refine ⟨8885281011080812644686933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5923520674053875096457955 8885281011080812644686933)
              ·
                refine ⟨104124386848603273179925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8885281011080812644686933 104124386848603273179925)
                ·
                  rfl

theorem cell23_5475101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 8].length) (baseStart_5475101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475101 prefixEnd_5475101 := by exact prefixLift 5475101
  have htrace : WordTrace (prefixWord ++ tailWord_5475101) baseStart_5475101 baseEnd_5475101 := by
    simpa [prefixWord, tailWord_5475101, baseEnd_5475101] using wordTrace_append hprefix tailTrace_5475101
  have hstable : (prefixWord ++ tailWord_5475101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475101).length < 2 ^ (prefixWord ++ tailWord_5475101).sum := by decide
  have hdescent : baseEnd_5475101 < baseStart_5475101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475121 : List Nat := [1, 2, 2, 3, 2, 1, 2, 4, 1, 3, 2]
def baseStart_5475121 : Nat := 118140960795 + 5475121 * 2 ^ 59
def prefixEnd_5475121 : Nat := 4983230072969 + 3 ^ 40 * 5475121 * 2
def baseEnd_5475121 : Nat := 2811368714525378297607883

theorem tailTrace_5475121 : CollatzResearch.WordTrace tailWord_5475121 prefixEnd_5475121 2811368714525378297607883 := by
  unfold tailWord_5475121
  simp only [CollatzResearch.WordTrace]
  refine ⟨199694068397579168066689217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133129378931719445377792811 199694068397579168066689217)
  ·
    refine ⟨149770551298184376050016913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199694068397579168066689217 149770551298184376050016913)
    ·
      refine ⟨112327913473638282037512685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149770551298184376050016913 112327913473638282037512685)
      ·
        refine ⟨42122967552614355764067257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112327913473638282037512685 42122967552614355764067257)
        ·
          refine ⟨31592225664460766823050443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42122967552614355764067257 31592225664460766823050443)
          ·
            refine ⟨47388338496691150234575665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31592225664460766823050443 47388338496691150234575665)
            ·
              refine ⟨35541253872518362675931749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47388338496691150234575665 35541253872518362675931749)
              ·
                refine ⟨6663985101097193001737203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35541253872518362675931749 6663985101097193001737203)
                ·
                  refine ⟨9995977651645789502605805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6663985101097193001737203 9995977651645789502605805)
                  ·
                    refine ⟨3748491619367171063477177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9995977651645789502605805 3748491619367171063477177)
                    ·
                      refine ⟨2811368714525378297607883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3748491619367171063477177 2811368714525378297607883)
                      ·
                        rfl

theorem cell23_5475121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 2, 4, 1, 3, 2].length) (baseStart_5475121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475121 prefixEnd_5475121 := by exact prefixLift 5475121
  have htrace : WordTrace (prefixWord ++ tailWord_5475121) baseStart_5475121 baseEnd_5475121 := by
    simpa [prefixWord, tailWord_5475121, baseEnd_5475121] using wordTrace_append hprefix tailTrace_5475121
  have hstable : (prefixWord ++ tailWord_5475121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475121).length < 2 ^ (prefixWord ++ tailWord_5475121).sum := by decide
  have hdescent : baseEnd_5475121 < baseStart_5475121 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475187 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 1, 7]
def baseStart_5475187 : Nat := 118140960795 + 5475187 * 2 ^ 59
def prefixEnd_5475187 : Nat := 4983230072969 + 3 ^ 40 * 5475187 * 2
def baseEnd_5475187 : Nat := 937134201416191679794193

theorem tailTrace_5475187 : CollatzResearch.WordTrace tailWord_5475187 prefixEnd_5475187 937134201416191679794193 := by
  unfold tailWord_5475187
  simp only [CollatzResearch.WordTrace]
  refine ⟨199696475615340061338591815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133130983743560040892394543 199696475615340061338591815)
  ·
    refine ⟨299544713423010092007887723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199696475615340061338591815 299544713423010092007887723)
    ·
      refine ⟨449317070134515138011831585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299544713423010092007887723 449317070134515138011831585)
      ·
        refine ⟨336987802600886353508873689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 449317070134515138011831585 336987802600886353508873689)
        ·
          refine ⟨252740851950664765131655267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336987802600886353508873689 252740851950664765131655267)
          ·
            refine ⟨379111277925997147697482901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252740851950664765131655267 379111277925997147697482901)
            ·
              refine ⟨17770841152781116298319511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 379111277925997147697482901 17770841152781116298319511)
              ·
                refine ⟨26656261729171674447479267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17770841152781116298319511 26656261729171674447479267)
                ·
                  refine ⟨39984392593757511671218901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26656261729171674447479267 39984392593757511671218901)
                  ·
                    refine ⟨937134201416191679794193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39984392593757511671218901 937134201416191679794193)
                    ·
                      rfl

theorem cell23_5475187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 1, 7].length) (baseStart_5475187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475187 prefixEnd_5475187 := by exact prefixLift 5475187
  have htrace : WordTrace (prefixWord ++ tailWord_5475187) baseStart_5475187 baseEnd_5475187 := by
    simpa [prefixWord, tailWord_5475187, baseEnd_5475187] using wordTrace_append hprefix tailTrace_5475187
  have hstable : (prefixWord ++ tailWord_5475187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475187).length < 2 ^ (prefixWord ++ tailWord_5475187).sum := by decide
  have hdescent : baseEnd_5475187 < baseStart_5475187 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475194 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2]
def baseStart_5475194 : Nat := 118140960795 + 5475194 * 2 ^ 59
def prefixEnd_5475194 : Nat := 4983230072969 + 3 ^ 40 * 5475194 * 2
def baseEnd_5475194 : Nat := 2811406198613156511995047

theorem tailTrace_5475194 : CollatzResearch.WordTrace tailWord_5475194 prefixEnd_5475194 2811406198613156511995047 := by
  unfold tailWord_5475194
  simp only [CollatzResearch.WordTrace]
  refine ⟨49924182731578675383524159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133131153950876467689397757 49924182731578675383524159)
  ·
    refine ⟨74886274097368013075286239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49924182731578675383524159 74886274097368013075286239)
    ·
      refine ⟨112329411146052019612929359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74886274097368013075286239 112329411146052019612929359)
      ·
        refine ⟨168494116719078029419394039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112329411146052019612929359 168494116719078029419394039)
        ·
          refine ⟨252741175078617044129091059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168494116719078029419394039 252741175078617044129091059)
          ·
            refine ⟨379111762617925566193636589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252741175078617044129091059 379111762617925566193636589)
            ·
              refine ⟨142166910981722087322613721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 379111762617925566193636589 142166910981722087322613721)
              ·
                refine ⟨106625183236291565491960291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142166910981722087322613721 106625183236291565491960291)
                ·
                  refine ⟨159937774854437348237940437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106625183236291565491960291 159937774854437348237940437)
                  ·
                    refine ⟨3748541598150875349326729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 159937774854437348237940437 3748541598150875349326729)
                    ·
                      refine ⟨2811406198613156511995047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3748541598150875349326729 2811406198613156511995047)
                      ·
                        rfl

theorem cell23_5475194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 1, 7, 2].length) (baseStart_5475194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475194 prefixEnd_5475194 := by exact prefixLift 5475194
  have htrace : WordTrace (prefixWord ++ tailWord_5475194) baseStart_5475194 baseEnd_5475194 := by
    simpa [prefixWord, tailWord_5475194, baseEnd_5475194] using wordTrace_append hprefix tailTrace_5475194
  have hstable : (prefixWord ++ tailWord_5475194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475194).length < 2 ^ (prefixWord ++ tailWord_5475194).sum := by decide
  have hdescent : baseEnd_5475194 < baseStart_5475194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475208 : List Nat := [2, 1, 3, 3, 2, 2, 3, 2, 5]
def baseStart_5475208 : Nat := 118140960795 + 5475208 * 2 ^ 59
def prefixEnd_5475208 : Nat := 4983230072969 + 3 ^ 40 * 5475208 * 2
def baseEnd_5475208 : Nat := 312379265260257717468887

theorem tailTrace_5475208 : CollatzResearch.WordTrace tailWord_5475208 prefixEnd_5475208 312379265260257717468887 := by
  unfold tailWord_5475208
  simp only [CollatzResearch.WordTrace]
  refine ⟨99848620774131990962553139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133131494365509321283404185 99848620774131990962553139)
  ·
    refine ⟨149772931161197986443829709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99848620774131990962553139 149772931161197986443829709)
    ·
      refine ⟨56164849185449244916436141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149772931161197986443829709 56164849185449244916436141)
      ·
        refine ⟨21061818444543466843663553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56164849185449244916436141 21061818444543466843663553)
        ·
          refine ⟨15796363833407600132747665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21061818444543466843663553 15796363833407600132747665)
          ·
            refine ⟨11847272875055700099560749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15796363833407600132747665 11847272875055700099560749)
            ·
              refine ⟨4442727328145887537335281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11847272875055700099560749 4442727328145887537335281)
              ·
                refine ⟨3332045496109415653001461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4442727328145887537335281 3332045496109415653001461)
                ·
                  refine ⟨312379265260257717468887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3332045496109415653001461 312379265260257717468887)
                  ·
                    rfl

theorem cell23_5475208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 2, 5].length) (baseStart_5475208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475208 prefixEnd_5475208 := by exact prefixLift 5475208
  have htrace : WordTrace (prefixWord ++ tailWord_5475208) baseStart_5475208 baseEnd_5475208 := by
    simpa [prefixWord, tailWord_5475208, baseEnd_5475208] using wordTrace_append hprefix tailTrace_5475208
  have hstable : (prefixWord ++ tailWord_5475208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475208).length < 2 ^ (prefixWord ++ tailWord_5475208).sum := by decide
  have hdescent : baseEnd_5475208 < baseStart_5475208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475237 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 3, 3, 6]
def baseStart_5475237 : Nat := 118140960795 + 5475237 * 2 ^ 59
def prefixEnd_5475237 : Nat := 4983230072969 + 3 ^ 40 * 5475237 * 2
def baseEnd_5475237 : Nat := 2811428278281299843757349

theorem tailTrace_5475237 : CollatzResearch.WordTrace tailWord_5475237 prefixEnd_5475237 2811428278281299843757349 := by
  unfold tailWord_5475237
  simp only [CollatzResearch.WordTrace]
  refine ⟨199698299265158919877911965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133132199510105946585274643 199698299265158919877911965)
  ·
    refine ⟨74886862224434594954216987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199698299265158919877911965 74886862224434594954216987)
    ·
      refine ⟨112330293336651892431325481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74886862224434594954216987 112330293336651892431325481)
      ·
        refine ⟨84247720002488919323494111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112330293336651892431325481 84247720002488919323494111)
        ·
          refine ⟨126371580003733378985241167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84247720002488919323494111 126371580003733378985241167)
          ·
            refine ⟨189557370005600068477861751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126371580003733378985241167 189557370005600068477861751)
            ·
              refine ⟨284336055008400102716792627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189557370005600068477861751 284336055008400102716792627)
              ·
                refine ⟨426504082512600154075188941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284336055008400102716792627 426504082512600154075188941)
                ·
                  refine ⟨159939030942225057778195853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 426504082512600154075188941 159939030942225057778195853)
                  ·
                    refine ⟨59977136603334396666823445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159939030942225057778195853 59977136603334396666823445)
                    ·
                      refine ⟨2811428278281299843757349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59977136603334396666823445 2811428278281299843757349)
                      ·
                        rfl

theorem cell23_5475237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_5475237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475237 prefixEnd_5475237 := by exact prefixLift 5475237
  have htrace : WordTrace (prefixWord ++ tailWord_5475237) baseStart_5475237 baseEnd_5475237 := by
    simpa [prefixWord, tailWord_5475237, baseEnd_5475237] using wordTrace_append hprefix tailTrace_5475237
  have hstable : (prefixWord ++ tailWord_5475237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475237).length < 2 ^ (prefixWord ++ tailWord_5475237).sum := by decide
  have hdescent : baseEnd_5475237 < baseStart_5475237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475244 : List Nat := [2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 3]
def baseStart_5475244 : Nat := 118140960795 + 5475244 * 2 ^ 59
def prefixEnd_5475244 : Nat := 4983230072969 + 3 ^ 40 * 5475244 * 2
def baseEnd_5475244 : Nat := 2811431872645881316369817

theorem tailTrace_5475244 : CollatzResearch.WordTrace tailWord_5475244 prefixEnd_5475244 2811431872645881316369817 := by
  unfold tailWord_5475244
  simp only [CollatzResearch.WordTrace]
  refine ⟨99849277288066780036708393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133132369717422373382277857 99849277288066780036708393)
  ·
    refine ⟨74886957966050085027531295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99849277288066780036708393 74886957966050085027531295)
    ·
      refine ⟨112330436949075127541296943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74886957966050085027531295 112330436949075127541296943)
      ·
        refine ⟨168495655423612691311945415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112330436949075127541296943 168495655423612691311945415)
        ·
          refine ⟨252743483135419036967918123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168495655423612691311945415 252743483135419036967918123)
          ·
            refine ⟨379115224703128555451877185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252743483135419036967918123 379115224703128555451877185)
            ·
              refine ⟨284336418527346416588907889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379115224703128555451877185 284336418527346416588907889)
              ·
                refine ⟨213252313895509812441680917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284336418527346416588907889 213252313895509812441680917)
                ·
                  refine ⟨9996202213852022458203793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 213252313895509812441680917 9996202213852022458203793)
                  ·
                    refine ⟨7497151660389016843652845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9996202213852022458203793 7497151660389016843652845)
                    ·
                      refine ⟨2811431872645881316369817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7497151660389016843652845 2811431872645881316369817)
                      ·
                        rfl

theorem cell23_5475244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 3].length) (baseStart_5475244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475244 prefixEnd_5475244 := by exact prefixLift 5475244
  have htrace : WordTrace (prefixWord ++ tailWord_5475244) baseStart_5475244 baseEnd_5475244 := by
    simpa [prefixWord, tailWord_5475244, baseEnd_5475244] using wordTrace_append hprefix tailTrace_5475244
  have hstable : (prefixWord ++ tailWord_5475244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475244).length < 2 ^ (prefixWord ++ tailWord_5475244).sum := by decide
  have hdescent : baseEnd_5475244 < baseStart_5475244 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475247 : List Nat := [1, 1, 2, 1, 2, 2, 2, 4, 8]
def baseStart_5475247 : Nat := 118140960795 + 5475247 * 2 ^ 59
def prefixEnd_5475247 : Nat := 4983230072969 + 3 ^ 40 * 5475247 * 2
def baseEnd_5475247 : Nat := 312381490343093867181367

theorem tailTrace_5475247 : CollatzResearch.WordTrace tailWord_5475247 prefixEnd_5475247 312381490343093867181367 := by
  unfold tailWord_5475247
  simp only [CollatzResearch.WordTrace]
  refine ⟨199698663995122691585775995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133132442663415127723850663 199698663995122691585775995)
  ·
    refine ⟨299547995992684037378663993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199698663995122691585775995 299547995992684037378663993)
    ·
      refine ⟨224660996994513028033997995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299547995992684037378663993 224660996994513028033997995)
      ·
        refine ⟨336991495491769542050996993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224660996994513028033997995 336991495491769542050996993)
        ·
          refine ⟨252743621618827156538247745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 336991495491769542050996993 252743621618827156538247745)
          ·
            refine ⟨189557716214120367403685809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252743621618827156538247745 189557716214120367403685809)
            ·
              refine ⟨142168287160590275552764357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189557716214120367403685809 142168287160590275552764357)
              ·
                refine ⟨26656553842610676666143317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142168287160590275552764357 26656553842610676666143317)
                ·
                  refine ⟨312381490343093867181367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26656553842610676666143317 312381490343093867181367)
                  ·
                    rfl

theorem cell23_5475247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 4, 8].length) (baseStart_5475247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475247 prefixEnd_5475247 := by exact prefixLift 5475247
  have htrace : WordTrace (prefixWord ++ tailWord_5475247) baseStart_5475247 baseEnd_5475247 := by
    simpa [prefixWord, tailWord_5475247, baseEnd_5475247] using wordTrace_append hprefix tailTrace_5475247
  have hstable : (prefixWord ++ tailWord_5475247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475247).length < 2 ^ (prefixWord ++ tailWord_5475247).sum := by decide
  have hdescent : baseEnd_5475247 < baseStart_5475247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475264 : List Nat := [2, 1, 1, 2, 3, 3, 1, 4, 6]
def baseStart_5475264 : Nat := 118140960795 + 5475264 * 2 ^ 59
def prefixEnd_5475264 : Nat := 4983230072969 + 3 ^ 40 * 5475264 * 2
def baseEnd_5475264 : Nat := 312382460250996804235525

theorem tailTrace_5475264 : CollatzResearch.WordTrace tailWord_5475264 prefixEnd_5475264 312382460250996804235525 := by
  unfold tailWord_5475264
  simp only [CollatzResearch.WordTrace]
  refine ⟨99849642018030551744572423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133132856024040735659429897 99849642018030551744572423)
  ·
    refine ⟨149774463027045827616858635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99849642018030551744572423 149774463027045827616858635)
    ·
      refine ⟨224661694540568741425287953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149774463027045827616858635 224661694540568741425287953)
      ·
        refine ⟨168496270905426556068965965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224661694540568741425287953 168496270905426556068965965)
        ·
          refine ⟨63186101589534958525862237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168496270905426556068965965 63186101589534958525862237)
          ·
            refine ⟨23694788096075609447198339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63186101589534958525862237 23694788096075609447198339)
            ·
              refine ⟨35542182144113414170797509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23694788096075609447198339 35542182144113414170797509)
              ·
                refine ⟨6664159152021265157024533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35542182144113414170797509 6664159152021265157024533)
                ·
                  refine ⟨312382460250996804235525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6664159152021265157024533 312382460250996804235525)
                  ·
                    rfl

theorem cell23_5475264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 1, 4, 6].length) (baseStart_5475264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475264 prefixEnd_5475264 := by exact prefixLift 5475264
  have htrace : WordTrace (prefixWord ++ tailWord_5475264) baseStart_5475264 baseEnd_5475264 := by
    simpa [prefixWord, tailWord_5475264, baseEnd_5475264] using wordTrace_append hprefix tailTrace_5475264
  have hstable : (prefixWord ++ tailWord_5475264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475264).length < 2 ^ (prefixWord ++ tailWord_5475264).sum := by decide
  have hdescent : baseEnd_5475264 < baseStart_5475264 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475267 : List Nat := [1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 8]
def baseStart_5475267 : Nat := 118140960795 + 5475267 * 2 ^ 59
def prefixEnd_5475267 : Nat := 4983230072969 + 3 ^ 40 * 5475267 * 2
def baseEnd_5475267 : Nat := 2811443682700934726382211

theorem tailTrace_5475267 : CollatzResearch.WordTrace tailWord_5475267 prefixEnd_5475267 2811443682700934726382211 := by
  unfold tailWord_5475267
  simp only [CollatzResearch.WordTrace]
  refine ⟨199699393455050235001504055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133132928970033490001002703 199699393455050235001504055)
  ·
    refine ⟨299549090182575352502256083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199699393455050235001504055 299549090182575352502256083)
    ·
      refine ⟨449323635273863028753384125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299549090182575352502256083 449323635273863028753384125)
      ·
        refine ⟨168496363227698635782519047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 449323635273863028753384125 168496363227698635782519047)
        ·
          refine ⟨252744544841547953673778571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168496363227698635782519047 252744544841547953673778571)
          ·
            refine ⟨379116817262321930510667857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252744544841547953673778571 379116817262321930510667857)
            ·
              refine ⟨284337612946741447883000893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379116817262321930510667857 284337612946741447883000893)
              ·
                refine ⟨106626604855028042956125335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 284337612946741447883000893 106626604855028042956125335)
                ·
                  refine ⟨159939907282542064434188003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106626604855028042956125335 159939907282542064434188003)
                  ·
                    refine ⟨239909860923813096651282005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 159939907282542064434188003 239909860923813096651282005)
                    ·
                      refine ⟨2811443682700934726382211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 239909860923813096651282005 2811443682700934726382211)
                      ·
                        rfl

theorem cell23_5475267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 1, 8].length) (baseStart_5475267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475267 prefixEnd_5475267 := by exact prefixLift 5475267
  have htrace : WordTrace (prefixWord ++ tailWord_5475267) baseStart_5475267 baseEnd_5475267 := by
    simpa [prefixWord, tailWord_5475267, baseEnd_5475267] using wordTrace_append hprefix tailTrace_5475267
  have hstable : (prefixWord ++ tailWord_5475267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475267).length < 2 ^ (prefixWord ++ tailWord_5475267).sum := by decide
  have hdescent : baseEnd_5475267 < baseStart_5475267 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475274 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 2, 5, 3]
def baseStart_5475274 : Nat := 118140960795 + 5475274 * 2 ^ 59
def prefixEnd_5475274 : Nat := 4983230072969 + 3 ^ 40 * 5475274 * 2
def baseEnd_5475274 : Nat := 2811447277065516198994679

theorem tailTrace_5475274 : CollatzResearch.WordTrace tailWord_5475274 prefixEnd_5475274 2811447277065516198994679 := by
  unfold tailWord_5475274
  simp only [CollatzResearch.WordTrace]
  refine ⟨49924912191506218799252219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133133099177349916798005917 49924912191506218799252219)
  ·
    refine ⟨74887368287259328198878329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49924912191506218799252219 74887368287259328198878329)
    ·
      refine ⟨56165526215444496149158747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74887368287259328198878329 56165526215444496149158747)
      ·
        refine ⟨84248289323166744223738121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56165526215444496149158747 84248289323166744223738121)
        ·
          refine ⟨63186216992375058167803591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84248289323166744223738121 63186216992375058167803591)
          ·
            refine ⟨94779325488562587251705387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63186216992375058167803591 94779325488562587251705387)
            ·
              refine ⟨142168988232843880877558081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94779325488562587251705387 142168988232843880877558081)
              ·
                refine ⟨106626741174632910658168561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142168988232843880877558081 106626741174632910658168561)
                ·
                  refine ⟨79970055880974682993626421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106626741174632910658168561 79970055880974682993626421)
                  ·
                    refine ⟨7497192738841376530652477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79970055880974682993626421 7497192738841376530652477)
                    ·
                      refine ⟨2811447277065516198994679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7497192738841376530652477 2811447277065516198994679)
                      ·
                        rfl

theorem cell23_5475274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 2, 5, 3].length) (baseStart_5475274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475274 prefixEnd_5475274 := by exact prefixLift 5475274
  have htrace : WordTrace (prefixWord ++ tailWord_5475274) baseStart_5475274 baseEnd_5475274 := by
    simpa [prefixWord, tailWord_5475274, baseEnd_5475274] using wordTrace_append hprefix tailTrace_5475274
  have hstable : (prefixWord ++ tailWord_5475274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475274).length < 2 ^ (prefixWord ++ tailWord_5475274).sum := by decide
  have hdescent : baseEnd_5475274 < baseStart_5475274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475295 : List Nat := [1, 1, 2, 3, 6, 1, 1, 1, 2, 2, 3]
def baseStart_5475295 : Nat := 118140960795 + 5475295 * 2 ^ 59
def prefixEnd_5475295 : Nat := 4983230072969 + 3 ^ 40 * 5475295 * 2
def baseEnd_5475295 : Nat := 2811458060159260616832083

theorem tailTrace_5475295 : CollatzResearch.WordTrace tailWord_5475295 prefixEnd_5475295 2811458060159260616832083 := by
  unfold tailWord_5475295
  simp only [CollatzResearch.WordTrace]
  refine ⟨199700414698948795783523339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133133609799299197189015559 199700414698948795783523339)
  ·
    refine ⟨299550622048423193675285009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199700414698948795783523339 299550622048423193675285009)
    ·
      refine ⟨224662966536317395256463757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299550622048423193675285009 224662966536317395256463757)
      ·
        refine ⟨84248612451119023221173909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224662966536317395256463757 84248612451119023221173909)
        ·
          refine ⟨3949153708646204213492527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 84248612451119023221173909 3949153708646204213492527)
          ·
            refine ⟨5923730562969306320238791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3949153708646204213492527 5923730562969306320238791)
            ·
              refine ⟨8885595844453959480358187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5923730562969306320238791 8885595844453959480358187)
              ·
                refine ⟨13328393766680939220537281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8885595844453959480358187 13328393766680939220537281)
                ·
                  refine ⟨9996295325010704415402961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13328393766680939220537281 9996295325010704415402961)
                  ·
                    refine ⟨7497221493758028311552221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9996295325010704415402961 7497221493758028311552221)
                    ·
                      refine ⟨2811458060159260616832083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7497221493758028311552221 2811458060159260616832083)
                      ·
                        rfl

theorem cell23_5475295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 1, 2, 2, 3].length) (baseStart_5475295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475295 prefixEnd_5475295 := by exact prefixLift 5475295
  have htrace : WordTrace (prefixWord ++ tailWord_5475295) baseStart_5475295 baseEnd_5475295 := by
    simpa [prefixWord, tailWord_5475295, baseEnd_5475295] using wordTrace_append hprefix tailTrace_5475295
  have hstable : (prefixWord ++ tailWord_5475295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475295).length < 2 ^ (prefixWord ++ tailWord_5475295).sum := by decide
  have hdescent : baseEnd_5475295 < baseStart_5475295 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475311 : List Nat := [1, 1, 2, 1, 4, 4, 1, 3, 1, 5]
def baseStart_5475311 : Nat := 118140960795 + 5475311 * 2 ^ 59
def prefixEnd_5475311 : Nat := 4983230072969 + 3 ^ 40 * 5475311 * 2
def baseEnd_5475311 : Nat := 937155425283244184744003

theorem tailTrace_5475311 : CollatzResearch.WordTrace tailWord_5475311 prefixEnd_5475311 937155425283244184744003 := by
  unfold tailWord_5475311
  simp only [CollatzResearch.WordTrace]
  refine ⟨199700998266890830516105787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133133998844593887010737191 199700998266890830516105787)
  ·
    refine ⟨299551497400336245774158681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199700998266890830516105787 299551497400336245774158681)
    ·
      refine ⟨224663623050252184330619011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299551497400336245774158681 224663623050252184330619011)
      ·
        refine ⟨336995434575378276495928517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224663623050252184330619011 336995434575378276495928517)
        ·
          refine ⟨63186643982883426842986597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 336995434575378276495928517 63186643982883426842986597)
          ·
            refine ⟨11847495746790642533059987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63186643982883426842986597 11847495746790642533059987)
            ·
              refine ⟨17771243620185963799589981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11847495746790642533059987 17771243620185963799589981)
              ·
                refine ⟨6664216357569736424846243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17771243620185963799589981 6664216357569736424846243)
                ·
                  refine ⟨9996324536354604637269365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6664216357569736424846243 9996324536354604637269365)
                  ·
                    refine ⟨937155425283244184744003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9996324536354604637269365 937155425283244184744003)
                    ·
                      rfl

theorem cell23_5475311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 3, 1, 5].length) (baseStart_5475311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475311 prefixEnd_5475311 := by exact prefixLift 5475311
  have htrace : WordTrace (prefixWord ++ tailWord_5475311) baseStart_5475311 baseEnd_5475311 := by
    simpa [prefixWord, tailWord_5475311, baseEnd_5475311] using wordTrace_append hprefix tailTrace_5475311
  have hstable : (prefixWord ++ tailWord_5475311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475311).length < 2 ^ (prefixWord ++ tailWord_5475311).sum := by decide
  have hdescent : baseEnd_5475311 < baseStart_5475311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475354 : List Nat := [3, 1, 1, 3, 1, 2, 3, 9]
def baseStart_5475354 : Nat := 118140960795 + 5475354 * 2 ^ 59
def prefixEnd_5475354 : Nat := 4983230072969 + 3 ^ 40 * 5475354 * 2
def baseEnd_5475354 : Nat := 104129198352513921703493

theorem tailTrace_5475354 : CollatzResearch.WordTrace tailWord_5475354 prefixEnd_5475354 104129198352513921703493 := by
  unfold tailWord_5475354
  simp only [CollatzResearch.WordTrace]
  refine ⟨49925641651433762214980279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133135044403823365906614077 49925641651433762214980279)
  ·
    refine ⟨74888462477150643322470419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49925641651433762214980279 74888462477150643322470419)
    ·
      refine ⟨112332693715725964983705629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74888462477150643322470419 112332693715725964983705629)
      ·
        refine ⟨42124760143397236868889611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112332693715725964983705629 42124760143397236868889611)
        ·
          refine ⟨63187140215095855303334417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42124760143397236868889611 63187140215095855303334417)
          ·
            refine ⟨47390355161321891477500813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63187140215095855303334417 47390355161321891477500813)
            ·
              refine ⟨17771383185495709304062805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47390355161321891477500813 17771383185495709304062805)
              ·
                refine ⟨104129198352513921703493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17771383185495709304062805 104129198352513921703493)
                ·
                  rfl

theorem cell23_5475354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 9].length) (baseStart_5475354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475354 prefixEnd_5475354 := by exact prefixLift 5475354
  have htrace : WordTrace (prefixWord ++ tailWord_5475354) baseStart_5475354 baseEnd_5475354 := by
    simpa [prefixWord, tailWord_5475354, baseEnd_5475354] using wordTrace_append hprefix tailTrace_5475354
  have hstable : (prefixWord ++ tailWord_5475354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475354).length < 2 ^ (prefixWord ++ tailWord_5475354).sum := by decide
  have hdescent : baseEnd_5475354 < baseStart_5475354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475382 : List Nat := [5, 1, 2, 1, 1, 2, 3, 1, 3, 2, 2]
def baseStart_5475382 : Nat := 118140960795 + 5475382 * 2 ^ 59
def prefixEnd_5475382 : Nat := 4983230072969 + 3 ^ 40 * 5475382 * 2
def baseEnd_5475382 : Nat := 2811502732976201776444183

theorem tailTrace_5475382 : CollatzResearch.WordTrace tailWord_5475382 prefixEnd_5475382 2811502732976201776444183 := by
  unfold tailWord_5475382
  simp only [CollatzResearch.WordTrace]
  refine ⟨12481474240602100602621275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133135725233089073094626933 12481474240602100602621275)
  ·
    refine ⟨18722211360903150903931913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12481474240602100602621275 18722211360903150903931913)
    ·
      refine ⟨14041658520677363177948935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18722211360903150903931913 14041658520677363177948935)
      ·
        refine ⟨21062487781016044766923403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14041658520677363177948935 21062487781016044766923403)
        ·
          refine ⟨31593731671524067150385105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21062487781016044766923403 31593731671524067150385105)
          ·
            refine ⟨23695298753643050362788829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31593731671524067150385105 23695298753643050362788829)
            ·
              refine ⟨8885737032616143886045811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23695298753643050362788829 8885737032616143886045811)
              ·
                refine ⟨13328605548924215829068717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8885737032616143886045811 13328605548924215829068717)
                ·
                  refine ⟨4998227080846580935900769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13328605548924215829068717 4998227080846580935900769)
                  ·
                    refine ⟨3748670310634935701925577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4998227080846580935900769 3748670310634935701925577)
                    ·
                      refine ⟨2811502732976201776444183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3748670310634935701925577 2811502732976201776444183)
                      ·
                        rfl

theorem cell23_5475382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_5475382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475382 prefixEnd_5475382 := by exact prefixLift 5475382
  have htrace : WordTrace (prefixWord ++ tailWord_5475382) baseStart_5475382 baseEnd_5475382 := by
    simpa [prefixWord, tailWord_5475382, baseEnd_5475382] using wordTrace_append hprefix tailTrace_5475382
  have hstable : (prefixWord ++ tailWord_5475382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475382).length < 2 ^ (prefixWord ++ tailWord_5475382).sum := by decide
  have hdescent : baseEnd_5475382 < baseStart_5475382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475391 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 2, 7, 2]
def baseStart_5475391 : Nat := 118140960795 + 5475391 * 2 ^ 59
def prefixEnd_5475391 : Nat := 4983230072969 + 3 ^ 40 * 5475391 * 2
def baseEnd_5475391 : Nat := 2811507354302092241231641

theorem tailTrace_5475391 : CollatzResearch.WordTrace tailWord_5475391 prefixEnd_5475391 2811507354302092241231641 := by
  unfold tailWord_5475391
  simp only [CollatzResearch.WordTrace]
  refine ⟨199703916106601004179018027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133135944071067336119345351 199703916106601004179018027)
  ·
    refine ⟨299555874159901506268527041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199703916106601004179018027 299555874159901506268527041)
    ·
      refine ⟨224666905619926129701395281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299555874159901506268527041 224666905619926129701395281)
      ·
        refine ⟨168500179214944597276046461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224666905619926129701395281 168500179214944597276046461)
        ·
          refine ⟨63187567205604223978517423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168500179214944597276046461 63187567205604223978517423)
          ·
            refine ⟨94781350808406335967776135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63187567205604223978517423 94781350808406335967776135)
            ·
              refine ⟨142172026212609503951664203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94781350808406335967776135 142172026212609503951664203)
              ·
                refine ⟨213258039318914255927496305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142172026212609503951664203 213258039318914255927496305)
                ·
                  refine ⟨159943529489185691945622229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213258039318914255927496305 159943529489185691945622229)
                  ·
                    refine ⟨3748676472402789654975521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 159943529489185691945622229 3748676472402789654975521)
                    ·
                      refine ⟨2811507354302092241231641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3748676472402789654975521 2811507354302092241231641)
                      ·
                        rfl

theorem cell23_5475391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 2, 7, 2].length) (baseStart_5475391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475391 prefixEnd_5475391 := by exact prefixLift 5475391
  have htrace : WordTrace (prefixWord ++ tailWord_5475391) baseStart_5475391 baseEnd_5475391 := by
    simpa [prefixWord, tailWord_5475391, baseEnd_5475391] using wordTrace_append hprefix tailTrace_5475391
  have hstable : (prefixWord ++ tailWord_5475391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475391).length < 2 ^ (prefixWord ++ tailWord_5475391).sum := by decide
  have hdescent : baseEnd_5475391 < baseStart_5475391 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475404 : List Nat := [2, 2, 1, 3, 1, 1, 1, 1, 1, 2, 8]
def baseStart_5475404 : Nat := 118140960795 + 5475404 * 2 ^ 59
def prefixEnd_5475404 : Nat := 4983230072969 + 3 ^ 40 * 5475404 * 2
def baseEnd_5475404 : Nat := 2811514029550600690369081

theorem tailTrace_5475404 : CollatzResearch.WordTrace tailWord_5475404 prefixEnd_5475404 2811514029550600690369081 := by
  unfold tailWord_5475404
  simp only [CollatzResearch.WordTrace]
  refine ⟨99852195127776953699620633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133136260170369271599494177 99852195127776953699620633)
  ·
    refine ⟨74889146345832715274715475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99852195127776953699620633 74889146345832715274715475)
    ·
      refine ⟨112333719518749072912073213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74889146345832715274715475 112333719518749072912073213)
      ·
        refine ⟨42125144819530902342027455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112333719518749072912073213 42125144819530902342027455)
        ·
          refine ⟨63187717229296353513041183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42125144819530902342027455 63187717229296353513041183)
          ·
            refine ⟨94781575843944530269561775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63187717229296353513041183 94781575843944530269561775)
            ·
              refine ⟨142172363765916795404342663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94781575843944530269561775 142172363765916795404342663)
              ·
                refine ⟨213258545648875193106513995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142172363765916795404342663 213258545648875193106513995)
                ·
                  refine ⟨319887818473312789659770993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213258545648875193106513995 319887818473312789659770993)
                  ·
                    refine ⟨239915863854984592244828245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 319887818473312789659770993 239915863854984592244828245)
                    ·
                      refine ⟨2811514029550600690369081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 239915863854984592244828245 2811514029550600690369081)
                      ·
                        rfl

theorem cell23_5475404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_5475404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475404 prefixEnd_5475404 := by exact prefixLift 5475404
  have htrace : WordTrace (prefixWord ++ tailWord_5475404) baseStart_5475404 baseEnd_5475404 := by
    simpa [prefixWord, tailWord_5475404, baseEnd_5475404] using wordTrace_append hprefix tailTrace_5475404
  have hstable : (prefixWord ++ tailWord_5475404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475404).length < 2 ^ (prefixWord ++ tailWord_5475404).sum := by decide
  have hdescent : baseEnd_5475404 < baseStart_5475404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475491 : List Nat := [1, 1, 1, 4, 1, 1, 1, 6, 2, 5]
def baseStart_5475491 : Nat := 118140960795 + 5475491 * 2 ^ 59
def prefixEnd_5475491 : Nat := 4983230072969 + 3 ^ 40 * 5475491 * 2
def baseEnd_5475491 : Nat := 937186234122513949993727

theorem tailTrace_5475491 : CollatzResearch.WordTrace tailWord_5475491 prefixEnd_5475491 937186234122513949993727 := by
  unfold tailWord_5475491
  simp only [CollatzResearch.WordTrace]
  refine ⟨199707563406238721257658327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133138375604159147505105551 199707563406238721257658327)
  ·
    refine ⟨299561345109358081886487491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199707563406238721257658327 299561345109358081886487491)
    ·
      refine ⟨449342017664037122829731237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299561345109358081886487491 449342017664037122829731237)
      ·
        refine ⟨84251628312006960530574607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 449342017664037122829731237 84251628312006960530574607)
        ·
          refine ⟨126377442468010440795861911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84251628312006960530574607 126377442468010440795861911)
          ·
            refine ⟨189566163702015661193792867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126377442468010440795861911 189566163702015661193792867)
            ·
              refine ⟨284349245553023491790689301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189566163702015661193792867 284349245553023491790689301)
              ·
                refine ⟨13328870885297976177688561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 284349245553023491790689301 13328870885297976177688561)
                ·
                  refine ⟨9996653163973482133266421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13328870885297976177688561 9996653163973482133266421)
                  ·
                    refine ⟨937186234122513949993727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9996653163973482133266421 937186234122513949993727)
                    ·
                      rfl

theorem cell23_5475491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 6, 2, 5].length) (baseStart_5475491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475491 prefixEnd_5475491 := by exact prefixLift 5475491
  have htrace : WordTrace (prefixWord ++ tailWord_5475491) baseStart_5475491 baseEnd_5475491 := by
    simpa [prefixWord, tailWord_5475491, baseEnd_5475491] using wordTrace_append hprefix tailTrace_5475491
  have hstable : (prefixWord ++ tailWord_5475491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475491).length < 2 ^ (prefixWord ++ tailWord_5475491).sum := by decide
  have hdescent : baseEnd_5475491 < baseStart_5475491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475495 : List Nat := [1, 1, 6, 2, 1, 1, 2, 4, 5]
def baseStart_5475495 : Nat := 118140960795 + 5475495 * 2 ^ 59
def prefixEnd_5475495 : Nat := 4983230072969 + 3 ^ 40 * 5475495 * 2
def baseEnd_5475495 : Nat := 312395639587795537147907

theorem tailTrace_5475495 : CollatzResearch.WordTrace tailWord_5475495 prefixEnd_5475495 312395639587795537147907 := by
  unfold tailWord_5475495
  simp only [CollatzResearch.WordTrace]
  refine ⟨199707709298224229940803939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133138472865482819960535959 199707709298224229940803939)
  ·
    refine ⟨299561563947336344911205909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199707709298224229940803939 299561563947336344911205909)
    ·
      refine ⟨14041948310031391167712777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 299561563947336344911205909 14041948310031391167712777)
      ·
        refine ⟨10531461232523543375784583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14041948310031391167712777 10531461232523543375784583)
        ·
          refine ⟨15797191848785315063676875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10531461232523543375784583 15797191848785315063676875)
          ·
            refine ⟨23695787773177972595515313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15797191848785315063676875 23695787773177972595515313)
            ·
              refine ⟨17771840829883479446636485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23695787773177972595515313 17771840829883479446636485)
              ·
                refine ⟨3332220155603152396244341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17771840829883479446636485 3332220155603152396244341)
                ·
                  refine ⟨312395639587795537147907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3332220155603152396244341 312395639587795537147907)
                  ·
                    rfl

theorem cell23_5475495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 4, 5].length) (baseStart_5475495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475495 prefixEnd_5475495 := by exact prefixLift 5475495
  have htrace : WordTrace (prefixWord ++ tailWord_5475495) baseStart_5475495 baseEnd_5475495 := by
    simpa [prefixWord, tailWord_5475495, baseEnd_5475495] using wordTrace_append hprefix tailTrace_5475495
  have hstable : (prefixWord ++ tailWord_5475495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475495).length < 2 ^ (prefixWord ++ tailWord_5475495).sum := by decide
  have hdescent : baseEnd_5475495 < baseStart_5475495 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475511 : List Nat := [1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 4]
def baseStart_5475511 : Nat := 118140960795 + 5475511 * 2 ^ 59
def prefixEnd_5475511 : Nat := 4983230072969 + 3 ^ 40 * 5475511 * 2
def baseEnd_5475511 : Nat := 2811568971980631771731089

theorem tailTrace_5475511 : CollatzResearch.WordTrace tailWord_5475511 prefixEnd_5475511 2811568971980631771731089 := by
  unfold tailWord_5475511
  simp only [CollatzResearch.WordTrace]
  refine ⟨199708292866166264673386387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133138861910777509782257591 199708292866166264673386387)
  ·
    refine ⟨299562439299249397010079581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199708292866166264673386387 299562439299249397010079581)
    ·
      refine ⟨112335914737218523878779843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299562439299249397010079581 112335914737218523878779843)
      ·
        refine ⟨168503872105827785818169765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112335914737218523878779843 168503872105827785818169765)
        ·
          refine ⟨31594476019842709840906831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168503872105827785818169765 31594476019842709840906831)
          ·
            refine ⟨47391714029764064761360247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31594476019842709840906831 47391714029764064761360247)
            ·
              refine ⟨71087571044646097142040371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47391714029764064761360247 71087571044646097142040371)
              ·
                refine ⟨106631356566969145713060557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71087571044646097142040371 106631356566969145713060557)
                ·
                  refine ⟨39986758712613429642397709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 106631356566969145713060557 39986758712613429642397709)
                  ·
                    refine ⟨14995034517230036115899141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39986758712613429642397709 14995034517230036115899141)
                    ·
                      refine ⟨2811568971980631771731089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14995034517230036115899141 2811568971980631771731089)
                      ·
                        rfl

theorem cell23_5475511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_5475511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475511 prefixEnd_5475511 := by exact prefixLift 5475511
  have htrace : WordTrace (prefixWord ++ tailWord_5475511) baseStart_5475511 baseEnd_5475511 := by
    simpa [prefixWord, tailWord_5475511, baseEnd_5475511] using wordTrace_append hprefix tailTrace_5475511
  have hstable : (prefixWord ++ tailWord_5475511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475511).length < 2 ^ (prefixWord ++ tailWord_5475511).sum := by decide
  have hdescent : baseEnd_5475511 < baseStart_5475511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475528 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 1, 6, 2]
def baseStart_5475528 : Nat := 118140960795 + 5475528 * 2 ^ 59
def prefixEnd_5475528 : Nat := 4983230072969 + 3 ^ 40 * 5475528 * 2
def baseEnd_5475528 : Nat := 2811577701151758205218511

theorem tailTrace_5475528 : CollatzResearch.WordTrace tailWord_5475528 prefixEnd_5475528 2811577701151758205218511 := by
  unfold tailWord_5475528
  simp only [CollatzResearch.WordTrace]
  refine ⟨99854456453552338288377619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133139275271403117717836825 99854456453552338288377619)
  ·
    refine ⟨149781684680328507432566429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99854456453552338288377619 149781684680328507432566429)
    ·
      refine ⟨56168131755123190287212411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149781684680328507432566429 56168131755123190287212411)
      ·
        refine ⟨84252197632684785430818617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56168131755123190287212411 84252197632684785430818617)
        ·
          refine ⟨63189148224513589073113963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84252197632684785430818617 63189148224513589073113963)
          ·
            refine ⟨94783722336770383609670945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63189148224513589073113963 94783722336770383609670945)
            ·
              refine ⟨71087791752577787707253209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94783722336770383609670945 71087791752577787707253209)
              ·
                refine ⟨53315843814433340780439907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71087791752577787707253209 53315843814433340780439907)
                ·
                  refine ⟨79973765721650011170659861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53315843814433340780439907 79973765721650011170659861)
                  ·
                    refine ⟨3748770268202344273624681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79973765721650011170659861 3748770268202344273624681)
                    ·
                      refine ⟨2811577701151758205218511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3748770268202344273624681 2811577701151758205218511)
                      ·
                        rfl

theorem cell23_5475528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 1, 6, 2].length) (baseStart_5475528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475528 prefixEnd_5475528 := by exact prefixLift 5475528
  have htrace : WordTrace (prefixWord ++ tailWord_5475528) baseStart_5475528 baseEnd_5475528 := by
    simpa [prefixWord, tailWord_5475528, baseEnd_5475528] using wordTrace_append hprefix tailTrace_5475528
  have hstable : (prefixWord ++ tailWord_5475528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475528).length < 2 ^ (prefixWord ++ tailWord_5475528).sum := by decide
  have hdescent : baseEnd_5475528 < baseStart_5475528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475542 : List Nat := [5, 2, 1, 2, 2, 1, 1, 2, 2, 5]
def baseStart_5475542 : Nat := 118140960795 + 5475542 * 2 ^ 59
def prefixEnd_5475542 : Nat := 4983230072969 + 3 ^ 40 * 5475542 * 2
def baseEnd_5475542 : Nat := 937194963293640383481149

theorem tailTrace_5475542 : CollatzResearch.WordTrace tailWord_5475542 prefixEnd_5475542 937194963293640383481149 := by
  unfold tailWord_5475542
  simp only [CollatzResearch.WordTrace]
  refine ⟨12481838970565872310485305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133139615686035971311843253 12481838970565872310485305)
  ·
    refine ⟨9361379227924404232863979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12481838970565872310485305 9361379227924404232863979)
    ·
      refine ⟨14042068841886606349295969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9361379227924404232863979 14042068841886606349295969)
      ·
        refine ⟨10531551631414954761971977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14042068841886606349295969 10531551631414954761971977)
        ·
          refine ⟨7898663723561216071478983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10531551631414954761971977 7898663723561216071478983)
          ·
            refine ⟨11847995585341824107218475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7898663723561216071478983 11847995585341824107218475)
            ·
              refine ⟨17771993378012736160827713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11847995585341824107218475 17771993378012736160827713)
              ·
                refine ⟨13328995033509552120620785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17771993378012736160827713 13328995033509552120620785)
                ·
                  refine ⟨9996746275132164090465589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13328995033509552120620785 9996746275132164090465589)
                  ·
                    refine ⟨937194963293640383481149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9996746275132164090465589 937194963293640383481149)
                    ·
                      rfl

theorem cell23_5475542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 2, 2, 5].length) (baseStart_5475542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475542 prefixEnd_5475542 := by exact prefixLift 5475542
  have htrace : WordTrace (prefixWord ++ tailWord_5475542) baseStart_5475542 baseEnd_5475542 := by
    simpa [prefixWord, tailWord_5475542, baseEnd_5475542] using wordTrace_append hprefix tailTrace_5475542
  have hstable : (prefixWord ++ tailWord_5475542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475542).length < 2 ^ (prefixWord ++ tailWord_5475542).sum := by decide
  have hdescent : baseEnd_5475542 < baseStart_5475542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475551 : List Nat := [1, 1, 2, 3, 2, 1, 4, 1, 8]
def baseStart_5475551 : Nat := 118140960795 + 5475551 * 2 ^ 59
def prefixEnd_5475551 : Nat := 4983230072969 + 3 ^ 40 * 5475551 * 2
def baseEnd_5475551 : Nat := 312398834578534623914545

theorem tailTrace_5475551 : CollatzResearch.WordTrace tailWord_5475551 prefixEnd_5475551 312398834578534623914545 := by
  unfold tailWord_5475551
  simp only [CollatzResearch.WordTrace]
  refine ⟨199709751786021351504842507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133139834524014234336561671 199709751786021351504842507)
  ·
    refine ⟨299564627679032027257263761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199709751786021351504842507 299564627679032027257263761)
    ·
      refine ⟨224673470759274020442947821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299564627679032027257263761 224673470759274020442947821)
      ·
        refine ⟨84252551534727757666105433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224673470759274020442947821 84252551534727757666105433)
        ·
          refine ⟨63189413651045818249579075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84252551534727757666105433 63189413651045818249579075)
          ·
            refine ⟨94784120476568727374368613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63189413651045818249579075 94784120476568727374368613)
            ·
              refine ⟨17772022589356636382694115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94784120476568727374368613 17772022589356636382694115)
              ·
                refine ⟨26658033884034954574041173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17772022589356636382694115 26658033884034954574041173)
                ·
                  refine ⟨312398834578534623914545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26658033884034954574041173 312398834578534623914545)
                  ·
                    rfl

theorem cell23_5475551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 8].length) (baseStart_5475551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475551 prefixEnd_5475551 := by exact prefixLift 5475551
  have htrace : WordTrace (prefixWord ++ tailWord_5475551) baseStart_5475551 baseEnd_5475551 := by
    simpa [prefixWord, tailWord_5475551, baseEnd_5475551] using wordTrace_append hprefix tailTrace_5475551
  have hstable : (prefixWord ++ tailWord_5475551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475551).length < 2 ^ (prefixWord ++ tailWord_5475551).sum := by decide
  have hdescent : baseEnd_5475551 < baseStart_5475551 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475582 : List Nat := [4, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_5475582 : Nat := 118140960795 + 5475582 * 2 ^ 59
def prefixEnd_5475582 : Nat := 4983230072969 + 3 ^ 40 * 5475582 * 2
def baseEnd_5475582 : Nat := 2811605429107100993943263

theorem tailTrace_5475582 : CollatzResearch.WordTrace tailWord_5475582 prefixEnd_5475582 2811605429107100993943263 := by
  unfold tailWord_5475582
  simp only [CollatzResearch.WordTrace]
  refine ⟨24963860306113630474902625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133140588299272695866147333 24963860306113630474902625)
  ·
    refine ⟨18722895229585222856176969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24963860306113630474902625 18722895229585222856176969)
    ·
      refine ⟨14042171422188917142132727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18722895229585222856176969 14042171422188917142132727)
      ·
        refine ⟨21063257133283375713199091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14042171422188917142132727 21063257133283375713199091)
        ·
          refine ⟨31594885699925063569798637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21063257133283375713199091 31594885699925063569798637)
          ·
            refine ⟨11848082137471898838674489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31594885699925063569798637 11848082137471898838674489)
            ·
              refine ⟨8886061603103924129005867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11848082137471898838674489 8886061603103924129005867)
              ·
                refine ⟨13329092404655886193508801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8886061603103924129005867 13329092404655886193508801)
                ·
                  refine ⟨9996819303491914645131601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13329092404655886193508801 9996819303491914645131601)
                  ·
                    refine ⟨7497614477618935983848701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9996819303491914645131601 7497614477618935983848701)
                    ·
                      refine ⟨2811605429107100993943263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7497614477618935983848701 2811605429107100993943263)
                      ·
                        rfl

theorem cell23_5475582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_5475582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475582 prefixEnd_5475582 := by exact prefixLift 5475582
  have htrace : WordTrace (prefixWord ++ tailWord_5475582) baseStart_5475582 baseEnd_5475582 := by
    simpa [prefixWord, tailWord_5475582, baseEnd_5475582] using wordTrace_append hprefix tailTrace_5475582
  have hstable : (prefixWord ++ tailWord_5475582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475582).length < 2 ^ (prefixWord ++ tailWord_5475582).sum := by decide
  have hdescent : baseEnd_5475582 < baseStart_5475582 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475611 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 5, 6]
def baseStart_5475611 : Nat := 118140960795 + 5475611 * 2 ^ 59
def prefixEnd_5475611 : Nat := 4983230072969 + 3 ^ 40 * 5475611 * 2
def baseEnd_5475611 : Nat := 937206773348693793493543

theorem tailTrace_5475611 : CollatzResearch.WordTrace tailWord_5475611 prefixEnd_5475611 937206773348693793493543 := by
  unfold tailWord_5475611
  simp only [CollatzResearch.WordTrace]
  refine ⟨199711940165803981752026687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133141293443869321168017791 199711940165803981752026687)
  ·
    refine ⟨299567910248705972628040031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199711940165803981752026687 299567910248705972628040031)
    ·
      refine ⟨449351865373058958942060047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299567910248705972628040031 449351865373058958942060047)
      ·
        refine ⟨674027798059588438413090071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449351865373058958942060047 674027798059588438413090071)
        ·
          refine ⟨1011041697089382657619635107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 674027798059588438413090071 1011041697089382657619635107)
          ·
            refine ⟨1516562545634073986429452661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1011041697089382657619635107 1516562545634073986429452661)
            ·
              refine ⟨142177738653194436227761187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1516562545634073986429452661 142177738653194436227761187)
              ·
                refine ⟨213266607979791654341641781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142177738653194436227761187 213266607979791654341641781)
                ·
                  refine ⟨19993744498105467594528917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 213266607979791654341641781 19993744498105467594528917)
                  ·
                    refine ⟨937206773348693793493543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19993744498105467594528917 937206773348693793493543)
                    ·
                      rfl

theorem cell23_5475611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 5, 6].length) (baseStart_5475611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475611 prefixEnd_5475611 := by exact prefixLift 5475611
  have htrace : WordTrace (prefixWord ++ tailWord_5475611) baseStart_5475611 baseEnd_5475611 := by
    simpa [prefixWord, tailWord_5475611, baseEnd_5475611] using wordTrace_append hprefix tailTrace_5475611
  have hstable : (prefixWord ++ tailWord_5475611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475611).length < 2 ^ (prefixWord ++ tailWord_5475611).sum := by decide
  have hdescent : baseEnd_5475611 < baseStart_5475611 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475628 : List Nat := [2, 2, 1, 1, 1, 3, 1, 2, 6, 4]
def baseStart_5475628 : Nat := 118140960795 + 5475628 * 2 ^ 59
def prefixEnd_5475628 : Nat := 4983230072969 + 3 ^ 40 * 5475628 * 2
def baseEnd_5475628 : Nat := 937209683072402604656017

theorem tailTrace_5475628 : CollatzResearch.WordTrace tailWord_5475628 prefixEnd_5475628 937209683072402604656017 := by
  unfold tailWord_5475628
  simp only [CollatzResearch.WordTrace]
  refine ⟨99856280103371196827697769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133141706804494929103597025 99856280103371196827697769)
  ·
    refine ⟨74892210077528397620773327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99856280103371196827697769 74892210077528397620773327)
    ·
      refine ⟨112338315116292596431159991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74892210077528397620773327 112338315116292596431159991)
      ·
        refine ⟨168507472674438894646739987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112338315116292596431159991 168507472674438894646739987)
        ·
          refine ⟨252761209011658341970109981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168507472674438894646739987 252761209011658341970109981)
          ·
            refine ⟨94785453379371878238791243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252761209011658341970109981 94785453379371878238791243)
            ·
              refine ⟨142178180069057817358186865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94785453379371878238791243 142178180069057817358186865)
              ·
                refine ⟨106633635051793363018640149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142178180069057817358186865 106633635051793363018640149)
                ·
                  refine ⟨4998451643052813891498757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106633635051793363018640149 4998451643052813891498757)
                  ·
                    refine ⟨937209683072402604656017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4998451643052813891498757 937209683072402604656017)
                    ·
                      rfl

theorem cell23_5475628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 4].length) (baseStart_5475628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475628 prefixEnd_5475628 := by exact prefixLift 5475628
  have htrace : WordTrace (prefixWord ++ tailWord_5475628) baseStart_5475628 baseEnd_5475628 := by
    simpa [prefixWord, tailWord_5475628, baseEnd_5475628] using wordTrace_append hprefix tailTrace_5475628
  have hstable : (prefixWord ++ tailWord_5475628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475628).length < 2 ^ (prefixWord ++ tailWord_5475628).sum := by decide
  have hdescent : baseEnd_5475628 < baseStart_5475628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475629 : List Nat := [1, 5, 3, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_5475629 : Nat := 118140960795 + 5475629 * 2 ^ 59
def prefixEnd_5475629 : Nat := 4983230072969 + 3 ^ 40 * 5475629 * 2
def baseEnd_5475629 : Nat := 2811629562697862310055547

theorem tailTrace_5475629 : CollatzResearch.WordTrace tailWord_5475629 prefixEnd_5475629 2811629562697862310055547 := by
  unfold tailWord_5475629
  simp only [CollatzResearch.WordTrace]
  refine ⟨199712596679738770826181941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133141731119825847217454627 199712596679738770826181941)
  ·
    refine ⟨18723055938725509764954557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 199712596679738770826181941 18723055938725509764954557)
    ·
      refine ⟨7021145977022066161857959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18723055938725509764954557 7021145977022066161857959)
      ·
        refine ⟨10531718965533099242786939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7021145977022066161857959 10531718965533099242786939)
        ·
          refine ⟨15797578448299648864180409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10531718965533099242786939 15797578448299648864180409)
          ·
            refine ⟨11848183836224736648135307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15797578448299648864180409 11848183836224736648135307)
            ·
              refine ⟨17772275754337104972202961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11848183836224736648135307 17772275754337104972202961)
              ·
                refine ⟨13329206815752828729152221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17772275754337104972202961 13329206815752828729152221)
                ·
                  refine ⟨4998452555907310773432083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13329206815752828729152221 4998452555907310773432083)
                  ·
                    refine ⟨7497678833860966160148125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4998452555907310773432083 7497678833860966160148125)
                    ·
                      refine ⟨2811629562697862310055547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7497678833860966160148125 2811629562697862310055547)
                      ·
                        rfl

theorem cell23_5475629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_5475629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475629 prefixEnd_5475629 := by exact prefixLift 5475629
  have htrace : WordTrace (prefixWord ++ tailWord_5475629) baseStart_5475629 baseEnd_5475629 := by
    simpa [prefixWord, tailWord_5475629, baseEnd_5475629] using wordTrace_append hprefix tailTrace_5475629
  have hstable : (prefixWord ++ tailWord_5475629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475629).length < 2 ^ (prefixWord ++ tailWord_5475629).sum := by decide
  have hdescent : baseEnd_5475629 < baseStart_5475629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475648 : List Nat := [2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 4]
def baseStart_5475648 : Nat := 118140960795 + 5475648 * 2 ^ 59
def prefixEnd_5475648 : Nat := 4983230072969 + 3 ^ 40 * 5475648 * 2
def baseEnd_5475648 : Nat := 2811639318830297735717959

theorem tailTrace_5475648 : CollatzResearch.WordTrace tailWord_5475648 prefixEnd_5475648 2811639318830297735717959 := by
  unfold tailWord_5475648
  simp only [CollatzResearch.WordTrace]
  refine ⟨99856644833334968535561799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133142193111113291380749065 99856644833334968535561799)
  ·
    refine ⟨149784967250002452803342699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99856644833334968535561799 149784967250002452803342699)
    ·
      refine ⟨224677450875003679205014049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149784967250002452803342699 224677450875003679205014049)
      ·
        refine ⟨168508088156252759403760537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224677450875003679205014049 168508088156252759403760537)
        ·
          refine ⟨126381066117189569552820403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168508088156252759403760537 126381066117189569552820403)
          ·
            refine ⟨189571599175784354329230605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126381066117189569552820403 189571599175784354329230605)
            ·
              refine ⟨71089349690919132873461477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189571599175784354329230605 71089349690919132873461477)
              ·
                refine ⟨13329253067047337413774027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71089349690919132873461477 13329253067047337413774027)
                ·
                  refine ⟨19993879600571006120661041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13329253067047337413774027 19993879600571006120661041)
                  ·
                    refine ⟨14995409700428254590495781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19993879600571006120661041 14995409700428254590495781)
                    ·
                      refine ⟨2811639318830297735717959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14995409700428254590495781 2811639318830297735717959)
                      ·
                        rfl

theorem cell23_5475648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 4, 1, 2, 4].length) (baseStart_5475648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475648 prefixEnd_5475648 := by exact prefixLift 5475648
  have htrace : WordTrace (prefixWord ++ tailWord_5475648) baseStart_5475648 baseEnd_5475648 := by
    simpa [prefixWord, tailWord_5475648, baseEnd_5475648] using wordTrace_append hprefix tailTrace_5475648
  have hstable : (prefixWord ++ tailWord_5475648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475648).length < 2 ^ (prefixWord ++ tailWord_5475648).sum := by decide
  have hdescent : baseEnd_5475648 < baseStart_5475648 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475649 : List Nat := [1, 2, 5, 2, 1, 3, 2, 1, 1, 5]
def baseStart_5475649 : Nat := 118140960795 + 5475649 * 2 ^ 59
def prefixEnd_5475649 : Nat := 4983230072969 + 3 ^ 40 * 5475649 * 2
def baseEnd_5475649 : Nat := 937213277436984077268485

theorem tailTrace_5475649 : CollatzResearch.WordTrace tailWord_5475649 prefixEnd_5475649 937213277436984077268485 := by
  unfold tailWord_5475649
  simp only [CollatzResearch.WordTrace]
  refine ⟨199713326139666314241910001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133142217426444209494606667 199713326139666314241910001)
  ·
    refine ⟨149784994604749735681432501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199713326139666314241910001 149784994604749735681432501)
    ·
      refine ⟨14042343244195287720134297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149784994604749735681432501 14042343244195287720134297)
      ·
        refine ⟨10531757433146465790100723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14042343244195287720134297 10531757433146465790100723)
        ·
          refine ⟨15797636149719698685151085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10531757433146465790100723 15797636149719698685151085)
          ·
            refine ⟨5924113556144887006931657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15797636149719698685151085 5924113556144887006931657)
            ·
              refine ⟨4443085167108665255198743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5924113556144887006931657 4443085167108665255198743)
              ·
                refine ⟨6664627750662997882798115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4443085167108665255198743 6664627750662997882798115)
                ·
                  refine ⟨9996941625994496824197173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6664627750662997882798115 9996941625994496824197173)
                  ·
                    refine ⟨937213277436984077268485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9996941625994496824197173 937213277436984077268485)
                    ·
                      rfl

theorem cell23_5475649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 2, 1, 1, 5].length) (baseStart_5475649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475649 prefixEnd_5475649 := by exact prefixLift 5475649
  have htrace : WordTrace (prefixWord ++ tailWord_5475649) baseStart_5475649 baseEnd_5475649 := by
    simpa [prefixWord, tailWord_5475649, baseEnd_5475649] using wordTrace_append hprefix tailTrace_5475649
  have hstable : (prefixWord ++ tailWord_5475649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475649).length < 2 ^ (prefixWord ++ tailWord_5475649).sum := by decide
  have hdescent : baseEnd_5475649 < baseStart_5475649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475669 : List Nat := [1, 3, 2, 2, 3, 2, 2, 1, 3, 2, 2]
def baseStart_5475669 : Nat := 118140960795 + 5475669 * 2 ^ 59
def prefixEnd_5475669 : Nat := 4983230072969 + 3 ^ 40 * 5475669 * 2
def baseEnd_5475669 : Nat := 2811650101924042153555363

theorem tailTrace_5475669 : CollatzResearch.WordTrace tailWord_5475669 prefixEnd_5475669 2811650101924042153555363 := by
  unfold tailWord_5475669
  simp only [CollatzResearch.WordTrace]
  refine ⟨199714055599593857657638061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133142703733062571771758707 199714055599593857657638061)
  ·
    refine ⟨74892770849847696621614273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199714055599593857657638061 74892770849847696621614273)
    ·
      refine ⟨56169578137385772466210705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74892770849847696621614273 56169578137385772466210705)
      ·
        refine ⟨42127183603039329349658029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56169578137385772466210705 42127183603039329349658029)
        ·
          refine ⟨15797693851139748506121761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42127183603039329349658029 15797693851139748506121761)
          ·
            refine ⟨11848270388354811379591321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15797693851139748506121761 11848270388354811379591321)
            ·
              refine ⟨8886202791266108534693491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11848270388354811379591321 8886202791266108534693491)
              ·
                refine ⟨13329304186899162802040237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8886202791266108534693491 13329304186899162802040237)
                ·
                  refine ⟨4998489070087186050765089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13329304186899162802040237 4998489070087186050765089)
                  ·
                    refine ⟨3748866802565389538073817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4998489070087186050765089 3748866802565389538073817)
                    ·
                      refine ⟨2811650101924042153555363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3748866802565389538073817 2811650101924042153555363)
                      ·
                        rfl

theorem cell23_5475669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 1, 3, 2, 2].length) (baseStart_5475669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475669 prefixEnd_5475669 := by exact prefixLift 5475669
  have htrace : WordTrace (prefixWord ++ tailWord_5475669) baseStart_5475669 baseEnd_5475669 := by
    simpa [prefixWord, tailWord_5475669, baseEnd_5475669] using wordTrace_append hprefix tailTrace_5475669
  have hstable : (prefixWord ++ tailWord_5475669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475669).length < 2 ^ (prefixWord ++ tailWord_5475669).sum := by decide
  have hdescent : baseEnd_5475669 < baseStart_5475669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475698 : List Nat := [3, 2, 1, 2, 1, 2, 1, 1, 1, 4, 5]
def baseStart_5475698 : Nat := 118140960795 + 5475698 * 2 ^ 59
def prefixEnd_5475698 : Nat := 4983230072969 + 3 ^ 40 * 5475698 * 2
def baseEnd_5475698 : Nat := 2811664992863022540092729

theorem tailTrace_5475698 : CollatzResearch.WordTrace tailWord_5475698 prefixEnd_5475698 2811664992863022540092729 := by
  unfold tailWord_5475698
  simp only [CollatzResearch.WordTrace]
  refine ⟨49928778329122198902610937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133143408877659197073629165 49928778329122198902610937)
  ·
    refine ⟨37446583746841649176958203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49928778329122198902610937 37446583746841649176958203)
    ·
      refine ⟨56169875620262473765437305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37446583746841649176958203 56169875620262473765437305)
      ·
        refine ⟨42127406715196855324077979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56169875620262473765437305 42127406715196855324077979)
        ·
          refine ⟨63191110072795282986116969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42127406715196855324077979 63191110072795282986116969)
          ·
            refine ⟨47393332554596462239587727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63191110072795282986116969 47393332554596462239587727)
            ·
              refine ⟨71089998831894693359381591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47393332554596462239587727 71089998831894693359381591)
              ·
                refine ⟨106634998247842040039072387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71089998831894693359381591 106634998247842040039072387)
                ·
                  refine ⟨159952497371763060058608581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106634998247842040039072387 159952497371763060058608581)
                  ·
                    refine ⟨29991093257205573760989109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 159952497371763060058608581 29991093257205573760989109)
                    ·
                      refine ⟨2811664992863022540092729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29991093257205573760989109 2811664992863022540092729)
                      ·
                        rfl

theorem cell23_5475698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_5475698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475698 prefixEnd_5475698 := by exact prefixLift 5475698
  have htrace : WordTrace (prefixWord ++ tailWord_5475698) baseStart_5475698 baseEnd_5475698 := by
    simpa [prefixWord, tailWord_5475698, baseEnd_5475698] using wordTrace_append hprefix tailTrace_5475698
  have hstable : (prefixWord ++ tailWord_5475698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475698).length < 2 ^ (prefixWord ++ tailWord_5475698).sum := by decide
  have hdescent : baseEnd_5475698 < baseStart_5475698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475746 : List Nat := [3, 3, 1, 2, 1, 4, 1, 2, 1, 3, 2]
def baseStart_5475746 : Nat := 118140960795 + 5475746 * 2 ^ 59
def prefixEnd_5475746 : Nat := 4983230072969 + 3 ^ 40 * 5475746 * 2
def baseEnd_5475746 : Nat := 2811689639934438352292509

theorem tailTrace_5475746 : CollatzResearch.WordTrace tailWord_5475746 prefixEnd_5475746 2811689639934438352292509 := by
  unfold tailWord_5475746
  simp only [CollatzResearch.WordTrace]
  refine ⟨49929216005078724952047773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133144576013543266538794061 49929216005078724952047773)
  ·
    refine ⟨18723456001904521857017915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49929216005078724952047773 18723456001904521857017915)
    ·
      refine ⟨28085184002856782785526873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18723456001904521857017915 28085184002856782785526873)
      ·
        refine ⟨21063888002142587089145155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28085184002856782785526873 21063888002142587089145155)
        ·
          refine ⟨31595832003213880633717733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21063888002142587089145155 31595832003213880633717733)
          ·
            refine ⟨5924218500602602618822075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31595832003213880633717733 5924218500602602618822075)
            ·
              refine ⟨8886327750903903928233113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5924218500602602618822075 8886327750903903928233113)
              ·
                refine ⟨6664745813177927946174835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8886327750903903928233113 6664745813177927946174835)
                ·
                  refine ⟨9997118719766891919262253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6664745813177927946174835 9997118719766891919262253)
                  ·
                    refine ⟨3748919519912584469723345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9997118719766891919262253 3748919519912584469723345)
                    ·
                      refine ⟨2811689639934438352292509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3748919519912584469723345 2811689639934438352292509)
                      ·
                        rfl

theorem cell23_5475746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_5475746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475746 prefixEnd_5475746 := by exact prefixLift 5475746
  have htrace : WordTrace (prefixWord ++ tailWord_5475746) baseStart_5475746 baseEnd_5475746 := by
    simpa [prefixWord, tailWord_5475746, baseEnd_5475746] using wordTrace_append hprefix tailTrace_5475746
  have hstable : (prefixWord ++ tailWord_5475746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475746).length < 2 ^ (prefixWord ++ tailWord_5475746).sum := by decide
  have hdescent : baseEnd_5475746 < baseStart_5475746 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475748 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 9]
def baseStart_5475748 : Nat := 118140960795 + 5475748 * 2 ^ 59
def prefixEnd_5475748 : Nat := 4983230072969 + 3 ^ 40 * 5475748 * 2
def baseEnd_5475748 : Nat := 312410074099527482718611

theorem tailTrace_5475748 : CollatzResearch.WordTrace tailWord_5475748 prefixEnd_5475748 312410074099527482718611 := by
  unfold tailWord_5475748
  simp only [CollatzResearch.WordTrace]
  refine ⟨99858468483153827074881949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133144624644205102766509265 99858468483153827074881949)
  ·
    refine ⟨37446925681182685153080731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99858468483153827074881949 37446925681182685153080731)
    ·
      refine ⟨56170388521774027729621097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37446925681182685153080731 56170388521774027729621097)
      ·
        refine ⟨42127791391330520797215823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56170388521774027729621097 42127791391330520797215823)
        ·
          refine ⟨63191687086995781195823735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42127791391330520797215823 63191687086995781195823735)
          ·
            refine ⟨94787530630493671793735603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63191687086995781195823735 94787530630493671793735603)
            ·
              refine ⟨142181295945740507690603405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94787530630493671793735603 142181295945740507690603405)
              ·
                refine ⟨53317985979652690383976277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142181295945740507690603405 53317985979652690383976277)
                ·
                  refine ⟨312410074099527482718611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53317985979652690383976277 312410074099527482718611)
                  ·
                    rfl

theorem cell23_5475748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_5475748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475748 prefixEnd_5475748 := by exact prefixLift 5475748
  have htrace : WordTrace (prefixWord ++ tailWord_5475748) baseStart_5475748 baseEnd_5475748 := by
    simpa [prefixWord, tailWord_5475748, baseEnd_5475748] using wordTrace_append hprefix tailTrace_5475748
  have hstable : (prefixWord ++ tailWord_5475748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475748).length < 2 ^ (prefixWord ++ tailWord_5475748).sum := by decide
  have hdescent : baseEnd_5475748 < baseStart_5475748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475808 : List Nat := [2, 1, 1, 3, 1, 1, 2, 1, 1, 10]
def baseStart_5475808 : Nat := 118140960795 + 5475808 * 2 ^ 59
def prefixEnd_5475808 : Nat := 4983230072969 + 3 ^ 40 * 5475808 * 2
def baseEnd_5475808 : Nat := 937240491911672369905741

theorem tailTrace_5475808 : CollatzResearch.WordTrace tailWord_5475808 prefixEnd_5475808 937240491911672369905741 := by
  unfold tailWord_5475808
  simp only [CollatzResearch.WordTrace]
  refine ⟨99859562673045142198474039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133146083564060189597965385 99859562673045142198474039)
  ·
    refine ⟨149789344009567713297711059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99859562673045142198474039 149789344009567713297711059)
    ·
      refine ⟨224684016014351569946566589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149789344009567713297711059 224684016014351569946566589)
      ·
        refine ⟨84256506005381838729962471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224684016014351569946566589 84256506005381838729962471)
        ·
          refine ⟨126384759008072758094943707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84256506005381838729962471 126384759008072758094943707)
          ·
            refine ⟨189577138512109137142415561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126384759008072758094943707 189577138512109137142415561)
            ·
              refine ⟨142182853884081852856811671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189577138512109137142415561 142182853884081852856811671)
              ·
                refine ⟨213274280826122779285217507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142182853884081852856811671 213274280826122779285217507)
                ·
                  refine ⟨319911421239184168927826261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213274280826122779285217507 319911421239184168927826261)
                  ·
                    refine ⟨937240491911672369905741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 319911421239184168927826261 937240491911672369905741)
                    ·
                      rfl

theorem cell23_5475808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 1, 1, 10].length) (baseStart_5475808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475808 prefixEnd_5475808 := by exact prefixLift 5475808
  have htrace : WordTrace (prefixWord ++ tailWord_5475808) baseStart_5475808 baseEnd_5475808 := by
    simpa [prefixWord, tailWord_5475808, baseEnd_5475808] using wordTrace_append hprefix tailTrace_5475808
  have hstable : (prefixWord ++ tailWord_5475808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475808).length < 2 ^ (prefixWord ++ tailWord_5475808).sum := by decide
  have hdescent : baseEnd_5475808 < baseStart_5475808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475832 : List Nat := [2, 1, 2, 1, 1, 5, 1, 2, 2, 4, 2]
def baseStart_5475832 : Nat := 118140960795 + 5475832 * 2 ^ 59
def prefixEnd_5475832 : Nat := 4983230072969 + 3 ^ 40 * 5475832 * 2
def baseEnd_5475832 : Nat := 2811733799270725015817113

theorem tailTrace_5475832 : CollatzResearch.WordTrace tailWord_5475832 prefixEnd_5475832 2811733799270725015817113 := by
  unfold tailWord_5475832
  simp only [CollatzResearch.WordTrace]
  refine ⟨99860000349001668247910875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133146667132002224330547833 99860000349001668247910875)
  ·
    refine ⟨149790000523502502371866313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99860000349001668247910875 149790000523502502371866313)
    ·
      refine ⟨112342500392626876778899735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149790000523502502371866313 112342500392626876778899735)
      ·
        refine ⟨168513750588940315168349603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112342500392626876778899735 168513750588940315168349603)
        ·
          refine ⟨252770625883410472752524405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168513750588940315168349603 252770625883410472752524405)
          ·
            refine ⟨23697246176569731820549163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 252770625883410472752524405 23697246176569731820549163)
            ·
              refine ⟨35545869264854597730823745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23697246176569731820549163 35545869264854597730823745)
              ·
                refine ⟨26659401948640948298117809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35545869264854597730823745 26659401948640948298117809)
                ·
                  refine ⟨19994551461480711223588357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26659401948640948298117809 19994551461480711223588357)
                  ·
                    refine ⟨3748978399027633354422817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19994551461480711223588357 3748978399027633354422817)
                    ·
                      refine ⟨2811733799270725015817113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3748978399027633354422817 2811733799270725015817113)
                      ·
                        rfl

theorem cell23_5475832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 2, 2, 4, 2].length) (baseStart_5475832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475832 prefixEnd_5475832 := by exact prefixLift 5475832
  have htrace : WordTrace (prefixWord ++ tailWord_5475832) baseStart_5475832 baseEnd_5475832 := by
    simpa [prefixWord, tailWord_5475832, baseEnd_5475832] using wordTrace_append hprefix tailTrace_5475832
  have hstable : (prefixWord ++ tailWord_5475832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475832).length < 2 ^ (prefixWord ++ tailWord_5475832).sum := by decide
  have hdescent : baseEnd_5475832 < baseStart_5475832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475915 : List Nat := [1, 1, 1, 1, 3, 1, 3, 5, 1, 6]
def baseStart_5475915 : Nat := 118140960795 + 5475915 * 2 ^ 59
def prefixEnd_5475915 : Nat := 4983230072969 + 3 ^ 40 * 5475915 * 2
def baseEnd_5475915 : Nat := 937258806055016063693077

theorem tailTrace_5475915 : CollatzResearch.WordTrace tailWord_5475915 prefixEnd_5475915 937258806055016063693077 := by
  unfold tailWord_5475915
  simp only [CollatzResearch.WordTrace]
  refine ⟨199723027956702641671093199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133148685304468427780728799 199723027956702641671093199)
  ·
    refine ⟨299584541935053962506639799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199723027956702641671093199 299584541935053962506639799)
    ·
      refine ⟨449376812902580943759959699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299584541935053962506639799 449376812902580943759959699)
      ·
        refine ⟨674065219353871415639939549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449376812902580943759959699 674065219353871415639939549)
        ·
          refine ⟨252774457257701780864977331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 674065219353871415639939549 252774457257701780864977331)
          ·
            refine ⟨379161685886552671297465997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252774457257701780864977331 379161685886552671297465997)
            ·
              refine ⟨142185632207457251736549749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 379161685886552671297465997 142185632207457251736549749)
              ·
                refine ⟨13329903019449117350301539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 142185632207457251736549749 13329903019449117350301539)
                ·
                  refine ⟨19994854529173676025452309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13329903019449117350301539 19994854529173676025452309)
                  ·
                    refine ⟨937258806055016063693077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19994854529173676025452309 937258806055016063693077)
                    ·
                      rfl

theorem cell23_5475915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 1, 6].length) (baseStart_5475915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475915 prefixEnd_5475915 := by exact prefixLift 5475915
  have htrace : WordTrace (prefixWord ++ tailWord_5475915) baseStart_5475915 baseEnd_5475915 := by
    simpa [prefixWord, tailWord_5475915, baseEnd_5475915] using wordTrace_append hprefix tailTrace_5475915
  have hstable : (prefixWord ++ tailWord_5475915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475915).length < 2 ^ (prefixWord ++ tailWord_5475915).sum := by decide
  have hdescent : baseEnd_5475915 < baseStart_5475915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475932 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 3, 6]
def baseStart_5475932 : Nat := 118140960795 + 5475932 * 2 ^ 59
def prefixEnd_5475932 : Nat := 4983230072969 + 3 ^ 40 * 5475932 * 2
def baseEnd_5475932 : Nat := 937261715778724874855551

theorem tailTrace_5475932 : CollatzResearch.WordTrace tailWord_5475932 prefixEnd_5475932 937261715778724874855551 := by
  unfold tailWord_5475932
  simp only [CollatzResearch.WordTrace]
  refine ⟨99861823998820526787231025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133149098665094035716308033 99861823998820526787231025)
  ·
    refine ⟨74896367999115395090423269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99861823998820526787231025 74896367999115395090423269)
    ·
      refine ⟨14043068999834136579454363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74896367999115395090423269 14043068999834136579454363)
      ·
        refine ⟨21064603499751204869181545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14043068999834136579454363 21064603499751204869181545)
        ·
          refine ⟨15798452624813403651886159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21064603499751204869181545 15798452624813403651886159)
          ·
            refine ⟨23697678937220105477829239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15798452624813403651886159 23697678937220105477829239)
            ·
              refine ⟨35546518405830158216743859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23697678937220105477829239 35546518405830158216743859)
              ·
                refine ⟨53319777608745237325115789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35546518405830158216743859 53319777608745237325115789)
                ·
                  refine ⟨19994916603279463996918421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53319777608745237325115789 19994916603279463996918421)
                  ·
                    refine ⟨937261715778724874855551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19994916603279463996918421 937261715778724874855551)
                    ·
                      rfl

theorem cell23_5475932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_5475932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475932 prefixEnd_5475932 := by exact prefixLift 5475932
  have htrace : WordTrace (prefixWord ++ tailWord_5475932) baseStart_5475932 baseEnd_5475932 := by
    simpa [prefixWord, tailWord_5475932, baseEnd_5475932] using wordTrace_append hprefix tailTrace_5475932
  have hstable : (prefixWord ++ tailWord_5475932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475932).length < 2 ^ (prefixWord ++ tailWord_5475932).sum := by decide
  have hdescent : baseEnd_5475932 < baseStart_5475932 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5475969 : List Nat := [1, 2, 4, 2, 1, 3, 2, 1, 1, 2, 4]
def baseStart_5475969 : Nat := 118140960795 + 5475969 * 2 ^ 59
def prefixEnd_5475969 : Nat := 4983230072969 + 3 ^ 40 * 5475969 * 2
def baseEnd_5475969 : Nat := 2811804146120390979803983

theorem tailTrace_5475969 : CollatzResearch.WordTrace tailWord_5475969 prefixEnd_5475969 2811804146120390979803983 := by
  unfold tailWord_5475969
  simp only [CollatzResearch.WordTrace]
  refine ⟨199724997498507008893558961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133149998332338005929039307 199724997498507008893558961)
  ·
    refine ⟨149793748123880256670169221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199724997498507008893558961 149793748123880256670169221)
    ·
      refine ⟨28086327773227548125656729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149793748123880256670169221 28086327773227548125656729)
      ·
        refine ⟨21064745829920661094242547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28086327773227548125656729 21064745829920661094242547)
        ·
          refine ⟨31597118744880991641363821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21064745829920661094242547 31597118744880991641363821)
          ·
            refine ⟨11848919529330371865511433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31597118744880991641363821 11848919529330371865511433)
            ·
              refine ⟨8886689646997778899133575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11848919529330371865511433 8886689646997778899133575)
              ·
                refine ⟨13330034470496668348700363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8886689646997778899133575 13330034470496668348700363)
                ·
                  refine ⟨19995051705745002523050545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13330034470496668348700363 19995051705745002523050545)
                  ·
                    refine ⟨14996288779308751892287909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19995051705745002523050545 14996288779308751892287909)
                    ·
                      refine ⟨2811804146120390979803983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14996288779308751892287909 2811804146120390979803983)
                      ·
                        rfl

theorem cell23_5475969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_5475969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5475969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5475969 prefixEnd_5475969 := by exact prefixLift 5475969
  have htrace : WordTrace (prefixWord ++ tailWord_5475969) baseStart_5475969 baseEnd_5475969 := by
    simpa [prefixWord, tailWord_5475969, baseEnd_5475969] using wordTrace_append hprefix tailTrace_5475969
  have hstable : (prefixWord ++ tailWord_5475969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5475969).length < 2 ^ (prefixWord ++ tailWord_5475969).sum := by decide
  have hdescent : baseEnd_5475969 < baseStart_5475969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5475969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476023 : List Nat := [1, 1, 3, 1, 5, 2, 3, 1, 2, 1, 3]
def baseStart_5476023 : Nat := 118140960795 + 5476023 * 2 ^ 59
def prefixEnd_5476023 : Nat := 4983230072969 + 3 ^ 40 * 5476023 * 2
def baseEnd_5476023 : Nat := 2811831874075733768528735

theorem tailTrace_5476023 : CollatzResearch.WordTrace tailWord_5476023 prefixEnd_5476023 2811831874075733768528735 := by
  unfold tailWord_5476023
  simp only [CollatzResearch.WordTrace]
  refine ⟨199726967040311376116024723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133151311360207584077349815 199726967040311376116024723)
  ·
    refine ⟨299590450560467064174037085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199726967040311376116024723 299590450560467064174037085)
    ·
      refine ⟨112346418960175149065263907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299590450560467064174037085 112346418960175149065263907)
      ·
        refine ⟨168519628440262723597895861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112346418960175149065263907 168519628440262723597895861)
        ·
          refine ⟨15798715166274630337302737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 168519628440262723597895861 15798715166274630337302737)
          ·
            refine ⟨11849036374705972752977053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15798715166274630337302737 11849036374705972752977053)
            ·
              refine ⟨4443388640514739782366395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11849036374705972752977053 4443388640514739782366395)
              ·
                refine ⟨6665082960772109673549593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4443388640514739782366395 6665082960772109673549593)
                ·
                  refine ⟨4998812220579082255162195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6665082960772109673549593 4998812220579082255162195)
                  ·
                    refine ⟨7498218330868623382743293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4998812220579082255162195 7498218330868623382743293)
                    ·
                      refine ⟨2811831874075733768528735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7498218330868623382743293 2811831874075733768528735)
                      ·
                        rfl

theorem cell23_5476023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 3, 1, 2, 1, 3].length) (baseStart_5476023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476023 prefixEnd_5476023 := by exact prefixLift 5476023
  have htrace : WordTrace (prefixWord ++ tailWord_5476023) baseStart_5476023 baseEnd_5476023 := by
    simpa [prefixWord, tailWord_5476023, baseEnd_5476023] using wordTrace_append hprefix tailTrace_5476023
  have hstable : (prefixWord ++ tailWord_5476023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476023).length < 2 ^ (prefixWord ++ tailWord_5476023).sum := by decide
  have hdescent : baseEnd_5476023 < baseStart_5476023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476032 : List Nat := [2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 5]
def baseStart_5476032 : Nat := 118140960795 + 5476032 * 2 ^ 59
def prefixEnd_5476032 : Nat := 4983230072969 + 3 ^ 40 * 5476032 * 2
def baseEnd_5476032 : Nat := 2811836495401624233316193

theorem tailTrace_5476032 : CollatzResearch.WordTrace tailWord_5476032 prefixEnd_5476032 2811836495401624233316193 := by
  unfold tailWord_5476032
  simp only [CollatzResearch.WordTrace]
  refine ⟨99863647648639385326551175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133151530198185847102068233 99863647648639385326551175)
  ·
    refine ⟨149795471472959077989826763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99863647648639385326551175 149795471472959077989826763)
    ·
      refine ⟨224693207209438616984740145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149795471472959077989826763 224693207209438616984740145)
      ·
        refine ⟨168519905407078962738555109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224693207209438616984740145 168519905407078962738555109)
        ·
          refine ⟨31597482263827305513479083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168519905407078962738555109 31597482263827305513479083)
          ·
            refine ⟨47396223395740958270218625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31597482263827305513479083 47396223395740958270218625)
            ·
              refine ⟨35547167546805718702663969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47396223395740958270218625 35547167546805718702663969)
              ·
                refine ⟨26660375660104289026997977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35547167546805718702663969 26660375660104289026997977)
                ·
                  refine ⟨19995281745078216770248483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26660375660104289026997977 19995281745078216770248483)
                  ·
                    refine ⟨29992922617617325155372725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19995281745078216770248483 29992922617617325155372725)
                    ·
                      refine ⟨2811836495401624233316193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29992922617617325155372725 2811836495401624233316193)
                      ·
                        rfl

theorem cell23_5476032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 5].length) (baseStart_5476032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476032 prefixEnd_5476032 := by exact prefixLift 5476032
  have htrace : WordTrace (prefixWord ++ tailWord_5476032) baseStart_5476032 baseEnd_5476032 := by
    simpa [prefixWord, tailWord_5476032, baseEnd_5476032] using wordTrace_append hprefix tailTrace_5476032
  have hstable : (prefixWord ++ tailWord_5476032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476032).length < 2 ^ (prefixWord ++ tailWord_5476032).sum := by decide
  have hdescent : baseEnd_5476032 < baseStart_5476032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476046 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2]
def baseStart_5476046 : Nat := 118140960795 + 5476046 * 2 ^ 59
def prefixEnd_5476046 : Nat := 4983230072969 + 3 ^ 40 * 5476046 * 2
def baseEnd_5476046 : Nat := 2811843684130787178541129

theorem tailTrace_5476046 : CollatzResearch.WordTrace tailWord_5476046 prefixEnd_5476046 2811843684130787178541129 := by
  unfold tailWord_5476046
  simp only [CollatzResearch.WordTrace]
  refine ⟨24965975739903506380513999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133151870612818700696074661 24965975739903506380513999)
  ·
    refine ⟨37448963609855259570770999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24965975739903506380513999 37448963609855259570770999)
    ·
      refine ⟨56173445414782889356156499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37448963609855259570770999 56173445414782889356156499)
      ·
        refine ⟨84260168122174334034234749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56173445414782889356156499 84260168122174334034234749)
        ·
          refine ⟨31597563045815375262838031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84260168122174334034234749 31597563045815375262838031)
          ·
            refine ⟨47396344568723062894257047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31597563045815375262838031 47396344568723062894257047)
            ·
              refine ⟨71094516853084594341385571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47396344568723062894257047 71094516853084594341385571)
              ·
                refine ⟨106641775279626891512078357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71094516853084594341385571 106641775279626891512078357)
                ·
                  refine ⟨4998833216232510539628673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 106641775279626891512078357 4998833216232510539628673)
                  ·
                    refine ⟨3749124912174382904721505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4998833216232510539628673 3749124912174382904721505)
                    ·
                      refine ⟨2811843684130787178541129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3749124912174382904721505 2811843684130787178541129)
                      ·
                        rfl

theorem cell23_5476046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 6, 2, 2].length) (baseStart_5476046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476046 prefixEnd_5476046 := by exact prefixLift 5476046
  have htrace : WordTrace (prefixWord ++ tailWord_5476046) baseStart_5476046 baseEnd_5476046 := by
    simpa [prefixWord, tailWord_5476046, baseEnd_5476046] using wordTrace_append hprefix tailTrace_5476046
  have hstable : (prefixWord ++ tailWord_5476046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476046).length < 2 ^ (prefixWord ++ tailWord_5476046).sum := by decide
  have hdescent : baseEnd_5476046 < baseStart_5476046 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476092 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 1, 1, 7]
def baseStart_5476092 : Nat := 118140960795 + 5476092 * 2 ^ 59
def prefixEnd_5476092 : Nat := 4983230072969 + 3 ^ 40 * 5476092 * 2
def baseEnd_5476092 : Nat := 2811867304240893998565917

theorem tailTrace_5476092 : CollatzResearch.WordTrace tailWord_5476092 prefixEnd_5476092 2811867304240893998565917 := by
  unfold tailWord_5476092
  simp only [CollatzResearch.WordTrace]
  refine ⟨99864741838530700450143265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133152989118040933933524353 99864741838530700450143265)
  ·
    refine ⟨74898556378898025337607449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99864741838530700450143265 74898556378898025337607449)
    ·
      refine ⟨56173917284173519003205587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74898556378898025337607449 56173917284173519003205587)
      ·
        refine ⟨84260875926260278504808381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56173917284173519003205587 84260875926260278504808381)
        ·
          refine ⟨31597828472347604439303143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84260875926260278504808381 31597828472347604439303143)
          ·
            refine ⟨47396742708521406658954715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31597828472347604439303143 47396742708521406658954715)
            ·
              refine ⟨71095114062782109988432073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47396742708521406658954715 71095114062782109988432073)
              ·
                refine ⟨53321335547086582491324055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71095114062782109988432073 53321335547086582491324055)
                ·
                  refine ⟨79982003320629873736986083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53321335547086582491324055 79982003320629873736986083)
                  ·
                    refine ⟨119973004980944810605479125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79982003320629873736986083 119973004980944810605479125)
                    ·
                      refine ⟨2811867304240893998565917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119973004980944810605479125 2811867304240893998565917)
                      ·
                        rfl

theorem cell23_5476092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_5476092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476092 prefixEnd_5476092 := by exact prefixLift 5476092
  have htrace : WordTrace (prefixWord ++ tailWord_5476092) baseStart_5476092 baseEnd_5476092 := by
    simpa [prefixWord, tailWord_5476092, baseEnd_5476092] using wordTrace_append hprefix tailTrace_5476092
  have hstable : (prefixWord ++ tailWord_5476092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476092).length < 2 ^ (prefixWord ++ tailWord_5476092).sum := by decide
  have hdescent : baseEnd_5476092 < baseStart_5476092 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476136 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 1, 6, 2]
def baseStart_5476136 : Nat := 118140960795 + 5476136 * 2 ^ 59
def prefixEnd_5476136 : Nat := 4983230072969 + 3 ^ 40 * 5476136 * 2
def baseEnd_5476136 : Nat := 2811889897389691826415715

theorem tailTrace_5476136 : CollatzResearch.WordTrace tailWord_5476136 prefixEnd_5476136 2811889897389691826415715 := by
  unfold tailWord_5476136
  simp only [CollatzResearch.WordTrace]
  refine ⟨99865544244450998207444131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133154058992601330943258841 99865544244450998207444131)
  ·
    refine ⟨149798316366676497311166197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99865544244450998207444131 149798316366676497311166197)
    ·
      refine ⟨14043592159375921622921831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 149798316366676497311166197 14043592159375921622921831)
      ·
        refine ⟨21065388239063882434382747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14043592159375921622921831 21065388239063882434382747)
        ·
          refine ⟨31598082358595823651574121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21065388239063882434382747 31598082358595823651574121)
          ·
            refine ⟨23698561768946867738680591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31598082358595823651574121 23698561768946867738680591)
            ·
              refine ⟨35547842653420301608020887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23698561768946867738680591 35547842653420301608020887)
              ·
                refine ⟨53321763980130452412031331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35547842653420301608020887 53321763980130452412031331)
                ·
                  refine ⟨79982645970195678618046997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53321763980130452412031331 79982645970195678618046997)
                  ·
                    refine ⟨3749186529852922435220953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79982645970195678618046997 3749186529852922435220953)
                    ·
                      refine ⟨2811889897389691826415715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3749186529852922435220953 2811889897389691826415715)
                      ·
                        rfl

theorem cell23_5476136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 1, 6, 2].length) (baseStart_5476136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476136 prefixEnd_5476136 := by exact prefixLift 5476136
  have htrace : WordTrace (prefixWord ++ tailWord_5476136) baseStart_5476136 baseEnd_5476136 := by
    simpa [prefixWord, tailWord_5476136, baseEnd_5476136] using wordTrace_append hprefix tailTrace_5476136
  have hstable : (prefixWord ++ tailWord_5476136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476136).length < 2 ^ (prefixWord ++ tailWord_5476136).sum := by decide
  have hdescent : baseEnd_5476136 < baseStart_5476136 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476146 : List Nat := [3, 2, 1, 1, 3, 3, 1, 2, 3, 4]
def baseStart_5476146 : Nat := 118140960795 + 5476146 * 2 ^ 59
def prefixEnd_5476146 : Nat := 4983230072969 + 3 ^ 40 * 5476146 * 2
def baseEnd_5476146 : Nat := 937298344065412262430223

theorem tailTrace_5476146 : CollatzResearch.WordTrace tailWord_5476146 prefixEnd_5476146 937298344065412262430223 := by
  unfold tailWord_5476146
  simp only [CollatzResearch.WordTrace]
  refine ⟨49932863304716442030688073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133154302145910512081834861 49932863304716442030688073)
  ·
    refine ⟨37449647478537331523016055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49932863304716442030688073 37449647478537331523016055)
    ·
      refine ⟨56174471217805997284524083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37449647478537331523016055 56174471217805997284524083)
      ·
        refine ⟨84261706826708995926786125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56174471217805997284524083 84261706826708995926786125)
        ·
          refine ⟨31598140060015873472544797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84261706826708995926786125 31598140060015873472544797)
          ·
            refine ⟨11849302522505952552204299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31598140060015873472544797 11849302522505952552204299)
            ·
              refine ⟨17773953783758928828306449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11849302522505952552204299 17773953783758928828306449)
              ·
                refine ⟨13330465337819196621229837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17773953783758928828306449 13330465337819196621229837)
                ·
                  refine ⟨4998924501682198732961189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13330465337819196621229837 4998924501682198732961189)
                  ·
                    refine ⟨937298344065412262430223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4998924501682198732961189 937298344065412262430223)
                    ·
                      rfl

theorem cell23_5476146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_5476146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476146 prefixEnd_5476146 := by exact prefixLift 5476146
  have htrace : WordTrace (prefixWord ++ tailWord_5476146) baseStart_5476146 baseEnd_5476146 := by
    simpa [prefixWord, tailWord_5476146, baseEnd_5476146] using wordTrace_append hprefix tailTrace_5476146
  have hstable : (prefixWord ++ tailWord_5476146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476146).length < 2 ^ (prefixWord ++ tailWord_5476146).sum := by decide
  have hdescent : baseEnd_5476146 < baseStart_5476146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476156 : List Nat := [2, 2, 2, 2, 1, 1, 5, 1, 2, 2, 3]
def baseStart_5476156 : Nat := 118140960795 + 5476156 * 2 ^ 59
def prefixEnd_5476156 : Nat := 4983230072969 + 3 ^ 40 * 5476156 * 2
def baseEnd_5476156 : Nat := 2811900167002781748165623

theorem tailTrace_5476156 : CollatzResearch.WordTrace tailWord_5476156 prefixEnd_5476156 2811900167002781748165623 := by
  unfold tailWord_5476156
  simp only [CollatzResearch.WordTrace]
  refine ⟨99865908974414769915308161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133154545299219693220410881 99865908974414769915308161)
  ·
    refine ⟨74899431730811077436481121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99865908974414769915308161 74899431730811077436481121)
    ·
      refine ⟨56174573798108308077360841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74899431730811077436481121 56174573798108308077360841)
      ·
        refine ⟨42130930348581231058020631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56174573798108308077360841 42130930348581231058020631)
        ·
          refine ⟨63196395522871846587030947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42130930348581231058020631 63196395522871846587030947)
          ·
            refine ⟨94794593284307769880546421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63196395522871846587030947 94794593284307769880546421)
            ·
              refine ⟨8886993120403853426301227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94794593284307769880546421 8886993120403853426301227)
              ·
                refine ⟨13330489680605780139451841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8886993120403853426301227 13330489680605780139451841)
                ·
                  refine ⟨9997867260454335104588881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13330489680605780139451841 9997867260454335104588881)
                  ·
                    refine ⟨7498400445340751328441661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9997867260454335104588881 7498400445340751328441661)
                    ·
                      refine ⟨2811900167002781748165623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7498400445340751328441661 2811900167002781748165623)
                      ·
                        rfl

theorem cell23_5476156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 2, 2, 3].length) (baseStart_5476156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476156 prefixEnd_5476156 := by exact prefixLift 5476156
  have htrace : WordTrace (prefixWord ++ tailWord_5476156) baseStart_5476156 baseEnd_5476156 := by
    simpa [prefixWord, tailWord_5476156, baseEnd_5476156] using wordTrace_append hprefix tailTrace_5476156
  have hstable : (prefixWord ++ tailWord_5476156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476156).length < 2 ^ (prefixWord ++ tailWord_5476156).sum := by decide
  have hdescent : baseEnd_5476156 < baseStart_5476156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476163 : List Nat := [1, 1, 1, 3, 1, 6, 2, 3, 1, 4]
def baseStart_5476163 : Nat := 118140960795 + 5476163 * 2 ^ 59
def prefixEnd_5476163 : Nat := 4983230072969 + 3 ^ 40 * 5476163 * 2
def baseEnd_5476163 : Nat := 937301253789121073592697

theorem tailTrace_5476163 : CollatzResearch.WordTrace tailWord_5476163 prefixEnd_5476163 937301253789121073592697 := by
  unfold tailWord_5476163
  simp only [CollatzResearch.WordTrace]
  refine ⟨199732073259804180026121143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133154715506536120017414095 199732073259804180026121143)
  ·
    refine ⟨299598109889706270039181715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199732073259804180026121143 299598109889706270039181715)
    ·
      refine ⟨449397164834559405058772573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299598109889706270039181715 449397164834559405058772573)
      ·
        refine ⟨168523936812959776897039715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 449397164834559405058772573 168523936812959776897039715)
        ·
          refine ⟨252785905219439665345559573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168523936812959776897039715 252785905219439665345559573)
          ·
            refine ⟨11849339307161234313073105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 252785905219439665345559573 11849339307161234313073105)
            ·
              refine ⟨8887004480370925734804829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11849339307161234313073105 8887004480370925734804829)
              ·
                refine ⟨3332626680139097150551811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8887004480370925734804829 3332626680139097150551811)
                ·
                  refine ⟨4998940020208645725827717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3332626680139097150551811 4998940020208645725827717)
                  ·
                    refine ⟨937301253789121073592697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4998940020208645725827717 937301253789121073592697)
                    ·
                      rfl

theorem cell23_5476163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 1, 4].length) (baseStart_5476163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476163 prefixEnd_5476163 := by exact prefixLift 5476163
  have htrace : WordTrace (prefixWord ++ tailWord_5476163) baseStart_5476163 baseEnd_5476163 := by
    simpa [prefixWord, tailWord_5476163, baseEnd_5476163] using wordTrace_append hprefix tailTrace_5476163
  have hstable : (prefixWord ++ tailWord_5476163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476163).length < 2 ^ (prefixWord ++ tailWord_5476163).sum := by decide
  have hdescent : baseEnd_5476163 < baseStart_5476163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476213 : List Nat := [1, 3, 4, 1, 1, 1, 2, 3, 2, 3, 2]
def baseStart_5476213 : Nat := 118140960795 + 5476213 * 2 ^ 59
def prefixEnd_5476213 : Nat := 4983230072969 + 3 ^ 40 * 5476213 * 2
def baseEnd_5476213 : Nat := 2811929435400088025152861

theorem tailTrace_5476213 : CollatzResearch.WordTrace tailWord_5476213 prefixEnd_5476213 2811929435400088025152861 := by
  unfold tailWord_5476213
  simp only [CollatzResearch.WordTrace]
  refine ⟨199733896909623038565441293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133155931273082025710294195 199733896909623038565441293)
  ·
    refine ⟨74900211341108639462040485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199733896909623038565441293 74900211341108639462040485)
    ·
      refine ⟨14043789626457869899132591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74900211341108639462040485 14043789626457869899132591)
      ·
        refine ⟨21065684439686804848698887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14043789626457869899132591 21065684439686804848698887)
        ·
          refine ⟨31598526659530207273048331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21065684439686804848698887 31598526659530207273048331)
          ·
            refine ⟨47397789989295310909572497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31598526659530207273048331 47397789989295310909572497)
            ·
              refine ⟨35548342491971483182179373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47397789989295310909572497 35548342491971483182179373)
              ·
                refine ⟨13330628434489306193317265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35548342491971483182179373 13330628434489306193317265)
                ·
                  refine ⟨9997971325866979644987949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13330628434489306193317265 9997971325866979644987949)
                  ·
                    refine ⟨3749239247200117366870481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9997971325866979644987949 3749239247200117366870481)
                    ·
                      refine ⟨2811929435400088025152861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3749239247200117366870481 2811929435400088025152861)
                      ·
                        rfl

theorem cell23_5476213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 2, 3, 2, 3, 2].length) (baseStart_5476213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476213 prefixEnd_5476213 := by exact prefixLift 5476213
  have htrace : WordTrace (prefixWord ++ tailWord_5476213) baseStart_5476213 baseEnd_5476213 := by
    simpa [prefixWord, tailWord_5476213, baseEnd_5476213] using wordTrace_append hprefix tailTrace_5476213
  have hstable : (prefixWord ++ tailWord_5476213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476213).length < 2 ^ (prefixWord ++ tailWord_5476213).sum := by decide
  have hdescent : baseEnd_5476213 < baseStart_5476213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476214 : List Nat := [5, 1, 1, 3, 3, 1, 1, 3, 1, 4]
def baseStart_5476214 : Nat := 118140960795 + 5476214 * 2 ^ 59
def prefixEnd_5476214 : Nat := 4983230072969 + 3 ^ 40 * 5476214 * 2
def baseEnd_5476214 : Nat := 937309982960247507080119

theorem tailTrace_5476214 : CollatzResearch.WordTrace tailWord_5476214 prefixEnd_5476214 937309982960247507080119 := by
  unfold tailWord_5476214
  simp only [CollatzResearch.WordTrace]
  refine ⟨12483370836413713483514231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133155955588412943824151797 12483370836413713483514231)
  ·
    refine ⟨18725056254620570225271347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12483370836413713483514231 18725056254620570225271347)
    ·
      refine ⟨28087584381930855337907021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18725056254620570225271347 28087584381930855337907021)
      ·
        refine ⟨10532844143224070751715133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28087584381930855337907021 10532844143224070751715133)
        ·
          refine ⟨3949816553709026531893175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10532844143224070751715133 3949816553709026531893175)
          ·
            refine ⟨5924724830563539797839763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3949816553709026531893175 5924724830563539797839763)
            ·
              refine ⟨8887087245845309696759645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5924724830563539797839763 8887087245845309696759645)
              ·
                refine ⟨3332657717191991136284867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8887087245845309696759645 3332657717191991136284867)
                ·
                  refine ⟨4998986575787986704427301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3332657717191991136284867 4998986575787986704427301)
                  ·
                    refine ⟨937309982960247507080119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4998986575787986704427301 937309982960247507080119)
                    ·
                      rfl

theorem cell23_5476214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_5476214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476214 prefixEnd_5476214 := by exact prefixLift 5476214
  have htrace : WordTrace (prefixWord ++ tailWord_5476214) baseStart_5476214 baseEnd_5476214 := by
    simpa [prefixWord, tailWord_5476214, baseEnd_5476214] using wordTrace_append hprefix tailTrace_5476214
  have hstable : (prefixWord ++ tailWord_5476214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476214).length < 2 ^ (prefixWord ++ tailWord_5476214).sum := by decide
  have hdescent : baseEnd_5476214 < baseStart_5476214 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476236 : List Nat := [2, 2, 1, 2, 1, 2, 1, 6, 2, 4]
def baseStart_5476236 : Nat := 118140960795 + 5476236 * 2 ^ 59
def prefixEnd_5476236 : Nat := 4983230072969 + 3 ^ 40 * 5476236 * 2
def baseEnd_5476236 : Nat := 937313748485047145055085

theorem tailTrace_5476236 : CollatzResearch.WordTrace tailWord_5476236 prefixEnd_5476236 937313748485047145055085 := by
  unfold tailWord_5476236
  simp only [CollatzResearch.WordTrace]
  refine ⟨99867367894269856746764281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133156490525693142329019041 99867367894269856746764281)
  ·
    refine ⟨74900525920702392560073211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99867367894269856746764281 74900525920702392560073211)
    ·
      refine ⟨112350788881053588840109817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74900525920702392560073211 112350788881053588840109817)
      ·
        refine ⟨84263091660790191630082363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112350788881053588840109817 84263091660790191630082363)
        ·
          refine ⟨126394637491185287445123545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84263091660790191630082363 126394637491185287445123545)
          ·
            refine ⟨94795978118388965583842659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126394637491185287445123545 94795978118388965583842659)
            ·
              refine ⟨142193967177583448375763989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94795978118388965583842659 142193967177583448375763989)
              ·
                refine ⟨6665342211449224142613937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 142193967177583448375763989 6665342211449224142613937)
                ·
                  refine ⟨4999006658586918106960453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6665342211449224142613937 4999006658586918106960453)
                  ·
                    refine ⟨937313748485047145055085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4999006658586918106960453 937313748485047145055085)
                    ·
                      rfl

theorem cell23_5476236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 6, 2, 4].length) (baseStart_5476236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476236 prefixEnd_5476236 := by exact prefixLift 5476236
  have htrace : WordTrace (prefixWord ++ tailWord_5476236) baseStart_5476236 baseEnd_5476236 := by
    simpa [prefixWord, tailWord_5476236, baseEnd_5476236] using wordTrace_append hprefix tailTrace_5476236
  have hstable : (prefixWord ++ tailWord_5476236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476236).length < 2 ^ (prefixWord ++ tailWord_5476236).sum := by decide
  have hdescent : baseEnd_5476236 < baseStart_5476236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476253 : List Nat := [1, 4, 2, 1, 2, 3, 1, 3, 2, 4]
def baseStart_5476253 : Nat := 118140960795 + 5476253 * 2 ^ 59
def prefixEnd_5476253 : Nat := 4983230072969 + 3 ^ 40 * 5476253 * 2
def baseEnd_5476253 : Nat := 937316658208755956217559

theorem tailTrace_5476253 : CollatzResearch.WordTrace tailWord_5476253 prefixEnd_5476253 937316658208755956217559 := by
  unfold tailWord_5476253
  simp only [CollatzResearch.WordTrace]
  refine ⟨199735355829478125396897413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133156903886318750264598275 199735355829478125396897413)
  ·
    refine ⟨37450379218027148511918265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199735355829478125396897413 37450379218027148511918265)
    ·
      refine ⟨28087784413520361383938699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37450379218027148511918265 28087784413520361383938699)
      ·
        refine ⟨42131676620280542075908049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28087784413520361383938699 42131676620280542075908049)
        ·
          refine ⟨31598757465210406556931037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42131676620280542075908049 31598757465210406556931037)
          ·
            refine ⟨11849534049453902458849139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31598757465210406556931037 11849534049453902458849139)
            ·
              refine ⟨17774301074180853688273709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11849534049453902458849139 17774301074180853688273709)
              ·
                refine ⟨6665362902817820133102641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17774301074180853688273709 6665362902817820133102641)
                ·
                  refine ⟨4999022177113365099826981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6665362902817820133102641 4999022177113365099826981)
                  ·
                    refine ⟨937316658208755956217559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4999022177113365099826981 937316658208755956217559)
                    ·
                      rfl

theorem cell23_5476253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_5476253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476253 prefixEnd_5476253 := by exact prefixLift 5476253
  have htrace : WordTrace (prefixWord ++ tailWord_5476253) baseStart_5476253 baseEnd_5476253 := by
    simpa [prefixWord, tailWord_5476253, baseEnd_5476253] using wordTrace_append hprefix tailTrace_5476253
  have hstable : (prefixWord ++ tailWord_5476253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476253).length < 2 ^ (prefixWord ++ tailWord_5476253).sum := by decide
  have hdescent : baseEnd_5476253 < baseStart_5476253 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476263 : List Nat := [1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 3]
def baseStart_5476263 : Nat := 118140960795 + 5476263 * 2 ^ 59
def prefixEnd_5476263 : Nat := 4983230072969 + 3 ^ 40 * 5476263 * 2
def baseEnd_5476263 : Nat := 2811955109432812829527631

theorem tailTrace_5476263 : CollatzResearch.WordTrace tailWord_5476263 prefixEnd_5476263 2811955109432812829527631 := by
  unfold tailWord_5476263
  simp only [CollatzResearch.WordTrace]
  refine ⟨199735720559441897104761443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133157147039627931403174295 199735720559441897104761443)
  ·
    refine ⟨299603580839162845657142165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199735720559441897104761443 299603580839162845657142165)
    ·
      refine ⟨14043917851835758390178539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 299603580839162845657142165 14043917851835758390178539)
      ·
        refine ⟨21065876777753637585267809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14043917851835758390178539 21065876777753637585267809)
        ·
          refine ⟨15799407583315228188950857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21065876777753637585267809 15799407583315228188950857)
          ·
            refine ⟨11849555687486421141713143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15799407583315228188950857 11849555687486421141713143)
            ·
              refine ⟨17774333531229631712569715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11849555687486421141713143 17774333531229631712569715)
              ·
                refine ⟨26661500296844447568854573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17774333531229631712569715 26661500296844447568854573)
                ·
                  refine ⟨9998062611316667838320465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26661500296844447568854573 9998062611316667838320465)
                  ·
                    refine ⟨7498546958487500878740349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9998062611316667838320465 7498546958487500878740349)
                    ·
                      refine ⟨2811955109432812829527631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7498546958487500878740349 2811955109432812829527631)
                      ·
                        rfl

theorem cell23_5476263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_5476263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476263 prefixEnd_5476263 := by exact prefixLift 5476263
  have htrace : WordTrace (prefixWord ++ tailWord_5476263) baseStart_5476263 baseEnd_5476263 := by
    simpa [prefixWord, tailWord_5476263, baseEnd_5476263] using wordTrace_append hprefix tailTrace_5476263
  have hstable : (prefixWord ++ tailWord_5476263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476263).length < 2 ^ (prefixWord ++ tailWord_5476263).sum := by decide
  have hdescent : baseEnd_5476263 < baseStart_5476263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476299 : List Nat := [1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 4]
def baseStart_5476299 : Nat := 118140960795 + 5476299 * 2 ^ 59
def prefixEnd_5476299 : Nat := 4983230072969 + 3 ^ 40 * 5476299 * 2
def baseEnd_5476299 : Nat := 2811973594736374688677465

theorem tailTrace_5476299 : CollatzResearch.WordTrace tailWord_5476299 prefixEnd_5476299 2811973594736374688677465 := by
  unfold tailWord_5476299
  simp only [CollatzResearch.WordTrace]
  refine ⟨199737033587311475253071951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133158022391540983502047967 199737033587311475253071951)
  ·
    refine ⟨299605550380967212879607927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199737033587311475253071951 299605550380967212879607927)
    ·
      refine ⟨449408325571450819319411891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299605550380967212879607927 449408325571450819319411891)
      ·
        refine ⟨674112488357176228979117837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449408325571450819319411891 674112488357176228979117837)
        ·
          refine ⟨252792183133941085867169189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 674112488357176228979117837 252792183133941085867169189)
          ·
            refine ⟨47398534337613953600094223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 252792183133941085867169189 47398534337613953600094223)
            ·
              refine ⟨71097801506420930400141335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47398534337613953600094223 71097801506420930400141335)
              ·
                refine ⟨106646702259631395600212003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71097801506420930400141335 106646702259631395600212003)
                ·
                  refine ⟨159970053389447093400318005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106646702259631395600212003 159970053389447093400318005)
                  ·
                    refine ⟨14997192505260665006279813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 159970053389447093400318005 14997192505260665006279813)
                    ·
                      refine ⟨2811973594736374688677465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14997192505260665006279813 2811973594736374688677465)
                      ·
                        rfl

theorem cell23_5476299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 1, 1, 5, 4].length) (baseStart_5476299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476299 prefixEnd_5476299 := by exact prefixLift 5476299
  have htrace : WordTrace (prefixWord ++ tailWord_5476299) baseStart_5476299 baseEnd_5476299 := by
    simpa [prefixWord, tailWord_5476299, baseEnd_5476299] using wordTrace_append hprefix tailTrace_5476299
  have hstable : (prefixWord ++ tailWord_5476299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476299).length < 2 ^ (prefixWord ++ tailWord_5476299).sum := by decide
  have hdescent : baseEnd_5476299 < baseStart_5476299 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476379 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 7]
def baseStart_5476379 : Nat := 118140960795 + 5476379 * 2 ^ 59
def prefixEnd_5476379 : Nat := 4983230072969 + 3 ^ 40 * 5476379 * 2
def baseEnd_5476379 : Nat := 2812014673188734375677097

theorem tailTrace_5476379 : CollatzResearch.WordTrace tailWord_5476379 prefixEnd_5476379 2812014673188734375677097 := by
  unfold tailWord_5476379
  simp only [CollatzResearch.WordTrace]
  refine ⟨199739951427021648915984191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133159967618014432610656127 199739951427021648915984191)
  ·
    refine ⟨299609927140532473373976287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199739951427021648915984191 299609927140532473373976287)
    ·
      refine ⟨449414890710798710060964431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299609927140532473373976287 449414890710798710060964431)
      ·
        refine ⟨674122336066198065091446647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449414890710798710060964431 674122336066198065091446647)
        ·
          refine ⟨1011183504099297097637169971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 674122336066198065091446647 1011183504099297097637169971)
          ·
            refine ⟨1516775256148945646455754957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1011183504099297097637169971 1516775256148945646455754957)
            ·
              refine ⟨568790721055854617420908109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1516775256148945646455754957 568790721055854617420908109)
              ·
                refine ⟨213296520395945481532840541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 568790721055854617420908109 213296520395945481532840541)
                ·
                  refine ⟨79986195148479555574815203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 213296520395945481532840541 79986195148479555574815203)
                  ·
                    refine ⟨119979292722719333362222805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79986195148479555574815203 119979292722719333362222805)
                    ·
                      refine ⟨2812014673188734375677097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119979292722719333362222805 2812014673188734375677097)
                      ·
                        rfl

theorem cell23_5476379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 1, 7].length) (baseStart_5476379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476379 prefixEnd_5476379 := by exact prefixLift 5476379
  have htrace : WordTrace (prefixWord ++ tailWord_5476379) baseStart_5476379 baseEnd_5476379 := by
    simpa [prefixWord, tailWord_5476379, baseEnd_5476379] using wordTrace_append hprefix tailTrace_5476379
  have hstable : (prefixWord ++ tailWord_5476379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476379).length < 2 ^ (prefixWord ++ tailWord_5476379).sum := by decide
  have hdescent : baseEnd_5476379 < baseStart_5476379 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476386 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 1, 7]
def baseStart_5476386 : Nat := 118140960795 + 5476386 * 2 ^ 59
def prefixEnd_5476386 : Nat := 4983230072969 + 3 ^ 40 * 5476386 * 2
def baseEnd_5476386 : Nat := 937339422517771949429855

theorem tailTrace_5476386 : CollatzResearch.WordTrace tailWord_5476386 prefixEnd_5476386 937339422517771949429855 := by
  unfold tailWord_5476386
  simp only [CollatzResearch.WordTrace]
  refine ⟨49935051684499072277872253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133160137825330859407659341 49935051684499072277872253)
  ·
    refine ⟨18725644381687152104202095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49935051684499072277872253 18725644381687152104202095)
    ·
      refine ⟨28088466572530728156303143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18725644381687152104202095 28088466572530728156303143)
      ·
        refine ⟨42132699858796092234454715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28088466572530728156303143 42132699858796092234454715)
        ·
          refine ⟨63199049788194138351682073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42132699858796092234454715 63199049788194138351682073)
          ·
            refine ⟨47399287341145603763761555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63199049788194138351682073 47399287341145603763761555)
            ·
              refine ⟨71098931011718405645642333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47399287341145603763761555 71098931011718405645642333)
              ·
                refine ⟨26662099129394402117115875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71098931011718405645642333 26662099129394402117115875)
                ·
                  refine ⟨39993148694091603175673813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26662099129394402117115875 39993148694091603175673813)
                  ·
                    refine ⟨937339422517771949429855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39993148694091603175673813 937339422517771949429855)
                    ·
                      rfl

theorem cell23_5476386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_5476386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476386 prefixEnd_5476386 := by exact prefixLift 5476386
  have htrace : WordTrace (prefixWord ++ tailWord_5476386) baseStart_5476386 baseEnd_5476386 := by
    simpa [prefixWord, tailWord_5476386, baseEnd_5476386] using wordTrace_append hprefix tailTrace_5476386
  have hstable : (prefixWord ++ tailWord_5476386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476386).length < 2 ^ (prefixWord ++ tailWord_5476386).sum := by decide
  have hdescent : baseEnd_5476386 < baseStart_5476386 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476423 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 1, 6, 2]
def baseStart_5476423 : Nat := 118140960795 + 5476423 * 2 ^ 59
def prefixEnd_5476423 : Nat := 4983230072969 + 3 ^ 40 * 5476423 * 2
def baseEnd_5476423 : Nat := 2812037266337532203526895

theorem tailTrace_5476423 : CollatzResearch.WordTrace tailWord_5476423 prefixEnd_5476423 2812037266337532203526895 := by
  unfold tailWord_5476423
  simp only [CollatzResearch.WordTrace]
  refine ⟨199741556238862244430585923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133161037492574829620390615 199741556238862244430585923)
  ·
    refine ⟨299612334358293366645878885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199741556238862244430585923 299612334358293366645878885)
    ·
      refine ⟨56177312692180006246102291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 299612334358293366645878885 56177312692180006246102291)
      ·
        refine ⟨84265969038270009369153437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56177312692180006246102291 84265969038270009369153437)
        ·
          refine ⟨31599738389351253513432539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84265969038270009369153437 31599738389351253513432539)
          ·
            refine ⟨47399607584026880270148809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31599738389351253513432539 47399607584026880270148809)
            ·
              refine ⟨35549705688020160202611607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47399607584026880270148809 35549705688020160202611607)
              ·
                refine ⟨53324558532030240303917411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35549705688020160202611607 53324558532030240303917411)
                ·
                  refine ⟨79986837798045360455876117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53324558532030240303917411 79986837798045360455876117)
                  ·
                    refine ⟨3749383021783376271369193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79986837798045360455876117 3749383021783376271369193)
                    ·
                      refine ⟨2812037266337532203526895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3749383021783376271369193 2812037266337532203526895)
                      ·
                        rfl

theorem cell23_5476423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 1, 6, 2].length) (baseStart_5476423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476423 prefixEnd_5476423 := by exact prefixLift 5476423
  have htrace : WordTrace (prefixWord ++ tailWord_5476423) baseStart_5476423 baseEnd_5476423 := by
    simpa [prefixWord, tailWord_5476423, baseEnd_5476423] using wordTrace_append hprefix tailTrace_5476423
  have hstable : (prefixWord ++ tailWord_5476423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476423).length < 2 ^ (prefixWord ++ tailWord_5476423).sum := by decide
  have hdescent : baseEnd_5476423 < baseStart_5476423 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476436 : List Nat := [2, 4, 1, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_5476436 : Nat := 118140960795 + 5476436 * 2 ^ 59
def prefixEnd_5476436 : Nat := 4983230072969 + 3 ^ 40 * 5476436 * 2
def baseEnd_5476436 : Nat := 2812043941586040652664335

theorem tailTrace_5476436 : CollatzResearch.WordTrace tailWord_5476436 prefixEnd_5476436 2812043941586040652664335 := by
  unfold tailWord_5476436
  simp only [CollatzResearch.WordTrace]
  refine ⟨99871015193907573825404581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133161353591876765100539441 99871015193907573825404581)
  ·
    refine ⟨18725815348857670092263359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99871015193907573825404581 18725815348857670092263359)
    ·
      refine ⟨28088723023286505138395039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18725815348857670092263359 28088723023286505138395039)
      ·
        refine ⟨42133084534929757707592559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28088723023286505138395039 42133084534929757707592559)
        ·
          refine ⟨63199626802394636561388839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42133084534929757707592559 63199626802394636561388839)
          ·
            refine ⟨94799440203591954842083259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63199626802394636561388839 94799440203591954842083259)
            ·
              refine ⟨142199160305387932263124889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94799440203591954842083259 142199160305387932263124889)
              ·
                refine ⟨106649370229040949197343667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142199160305387932263124889 106649370229040949197343667)
                ·
                  refine ⟨159974055343561423796015501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106649370229040949197343667 159974055343561423796015501)
                  ·
                    refine ⟨59990270753835533923505813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 159974055343561423796015501 59990270753835533923505813)
                    ·
                      refine ⟨2812043941586040652664335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59990270753835533923505813 2812043941586040652664335)
                      ·
                        rfl

theorem cell23_5476436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_5476436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476436 prefixEnd_5476436 := by exact prefixLift 5476436
  have htrace : WordTrace (prefixWord ++ tailWord_5476436) baseStart_5476436 baseEnd_5476436 := by
    simpa [prefixWord, tailWord_5476436, baseEnd_5476436] using wordTrace_append hprefix tailTrace_5476436
  have hstable : (prefixWord ++ tailWord_5476436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476436).length < 2 ^ (prefixWord ++ tailWord_5476436).sum := by decide
  have hdescent : baseEnd_5476436 < baseStart_5476436 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476463 : List Nat := [1, 1, 2, 1, 3, 5, 2, 2, 6]
def baseStart_5476463 : Nat := 118140960795 + 5476463 * 2 ^ 59
def prefixEnd_5476463 : Nat := 4983230072969 + 3 ^ 40 * 5476463 * 2
def baseEnd_5476463 : Nat := 312450867284856894114079

theorem tailTrace_5476463 : CollatzResearch.WordTrace tailWord_5476463 prefixEnd_5476463 312450867284856894114079 := by
  unfold tailWord_5476463
  simp only [CollatzResearch.WordTrace]
  refine ⟨199743015158717331262042043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133162010105811554174694695 199743015158717331262042043)
  ·
    refine ⟨299614522738075996893063065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199743015158717331262042043 299614522738075996893063065)
    ·
      refine ⟨224710892053556997669797299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299614522738075996893063065 224710892053556997669797299)
      ·
        refine ⟨337066338080335496504695949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224710892053556997669797299 337066338080335496504695949)
        ·
          refine ⟨126399876780125811189260981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 337066338080335496504695949 126399876780125811189260981)
          ·
            refine ⟨11849988448136794798993217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126399876780125811189260981 11849988448136794798993217)
            ·
              refine ⟨8887491336102596099244913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11849988448136794798993217 8887491336102596099244913)
              ·
                refine ⟨6665618502076947074433685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8887491336102596099244913 6665618502076947074433685)
                ·
                  refine ⟨312450867284856894114079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6665618502076947074433685 312450867284856894114079)
                  ·
                    rfl

theorem cell23_5476463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 6].length) (baseStart_5476463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476463 prefixEnd_5476463 := by exact prefixLift 5476463
  have htrace : WordTrace (prefixWord ++ tailWord_5476463) baseStart_5476463 baseEnd_5476463 := by
    simpa [prefixWord, tailWord_5476463, baseEnd_5476463] using wordTrace_append hprefix tailTrace_5476463
  have hstable : (prefixWord ++ tailWord_5476463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476463).length < 2 ^ (prefixWord ++ tailWord_5476463).sum := by decide
  have hdescent : baseEnd_5476463 < baseStart_5476463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476490 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 5, 1, 3]
def baseStart_5476490 : Nat := 118140960795 + 5476490 * 2 ^ 59
def prefixEnd_5476490 : Nat := 4983230072969 + 3 ^ 40 * 5476490 * 2
def baseEnd_5476490 : Nat := 2812071669541383441389087

theorem tailTrace_5476490 : CollatzResearch.WordTrace tailWord_5476490 prefixEnd_5476490 2812071669541383441389087 := by
  unfold tailWord_5476490
  simp only [CollatzResearch.WordTrace]
  refine ⟨49935999982404878718318731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133162666619746343248849949 49935999982404878718318731)
  ·
    refine ⟨74903999973607318077478097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49935999982404878718318731 74903999973607318077478097)
    ·
      refine ⟨56177999980205488558108573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74903999973607318077478097 56177999980205488558108573)
      ·
        refine ⟨21066749992577058209290715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56177999980205488558108573 21066749992577058209290715)
        ·
          refine ⟨31600124988865587313936073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21066749992577058209290715 31600124988865587313936073)
          ·
            refine ⟨23700093741649190485452055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31600124988865587313936073 23700093741649190485452055)
            ·
              refine ⟨35550140612473785728178083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23700093741649190485452055 35550140612473785728178083)
              ·
                refine ⟨53325210918710678592267125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35550140612473785728178083 53325210918710678592267125)
                ·
                  refine ⟨4999238523629126118025043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53325210918710678592267125 4999238523629126118025043)
                  ·
                    refine ⟨7498857785443689177037565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4999238523629126118025043 7498857785443689177037565)
                    ·
                      refine ⟨2812071669541383441389087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7498857785443689177037565 2812071669541383441389087)
                      ·
                        rfl

theorem cell23_5476490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 5, 1, 3].length) (baseStart_5476490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476490 prefixEnd_5476490 := by exact prefixLift 5476490
  have htrace : WordTrace (prefixWord ++ tailWord_5476490) baseStart_5476490 baseEnd_5476490 := by
    simpa [prefixWord, tailWord_5476490, baseEnd_5476490] using wordTrace_append hprefix tailTrace_5476490
  have hstable : (prefixWord ++ tailWord_5476490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476490).length < 2 ^ (prefixWord ++ tailWord_5476490).sum := by decide
  have hdescent : baseEnd_5476490 < baseStart_5476490 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476494 : List Nat := [4, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3]
def baseStart_5476494 : Nat := 118140960795 + 5476494 * 2 ^ 59
def prefixEnd_5476494 : Nat := 4983230072969 + 3 ^ 40 * 5476494 * 2
def baseEnd_5476494 : Nat := 2812073723464001425739069

theorem tailTrace_5476494 : CollatzResearch.WordTrace tailWord_5476494 prefixEnd_5476494 2812073723464001425739069 := by
  unfold tailWord_5476494
  simp only [CollatzResearch.WordTrace]
  refine ⟨24968018227700627944552567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133162763881070015704280357 24968018227700627944552567)
  ·
    refine ⟨37452027341550941916828851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24968018227700627944552567 37452027341550941916828851)
    ·
      refine ⟨56178041012326412875243277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37452027341550941916828851 56178041012326412875243277)
      ·
        refine ⟨21066765379622404828216229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56178041012326412875243277 21066765379622404828216229)
        ·
          refine ⟨3950018508679200905290543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21066765379622404828216229 3950018508679200905290543)
          ·
            refine ⟨5925027763018801357935815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3950018508679200905290543 5925027763018801357935815)
            ·
              refine ⟨8887541644528202036903723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5925027763018801357935815 8887541644528202036903723)
              ·
                refine ⟨13331312466792303055355585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8887541644528202036903723 13331312466792303055355585)
                ·
                  refine ⟨9998484350094227291516689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13331312466792303055355585 9998484350094227291516689)
                  ·
                    refine ⟨7498863262570670468637517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9998484350094227291516689 7498863262570670468637517)
                    ·
                      refine ⟨2812073723464001425739069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7498863262570670468637517 2812073723464001425739069)
                      ·
                        rfl

theorem cell23_5476494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 1, 2, 2, 3].length) (baseStart_5476494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476494 prefixEnd_5476494 := by exact prefixLift 5476494
  have htrace : WordTrace (prefixWord ++ tailWord_5476494) baseStart_5476494 baseEnd_5476494 := by
    simpa [prefixWord, tailWord_5476494, baseEnd_5476494] using wordTrace_append hprefix tailTrace_5476494
  have hstable : (prefixWord ++ tailWord_5476494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476494).length < 2 ^ (prefixWord ++ tailWord_5476494).sum := by decide
  have hdescent : baseEnd_5476494 < baseStart_5476494 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476536 : List Nat := [2, 1, 2, 1, 2, 1, 4, 10]
def baseStart_5476536 : Nat := 118140960795 + 5476536 * 2 ^ 59
def prefixEnd_5476536 : Nat := 4983230072969 + 3 ^ 40 * 5476536 * 2
def baseEnd_5476536 : Nat := 104151677394499639311625

theorem tailTrace_5476536 : CollatzResearch.WordTrace tailWord_5476536 prefixEnd_5476536 104151677394499639311625 := by
  unfold tailWord_5476536
  simp only [CollatzResearch.WordTrace]
  refine ⟨99872838843726432364724731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133163785124968576486299641 99872838843726432364724731)
  ·
    refine ⟨149809258265589648547087097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99872838843726432364724731 149809258265589648547087097)
    ·
      refine ⟨112356943699192236410315323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149809258265589648547087097 112356943699192236410315323)
      ·
        refine ⟨168535415548788354615472985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112356943699192236410315323 168535415548788354615472985)
        ·
          refine ⟨126401561661591265961604739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168535415548788354615472985 126401561661591265961604739)
          ·
            refine ⟨189602342492386898942407109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126401561661591265961604739 189602342492386898942407109)
            ·
              refine ⟨35550439217322543551701333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189602342492386898942407109 35550439217322543551701333)
              ·
                refine ⟨104151677394499639311625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35550439217322543551701333 104151677394499639311625)
                ·
                  rfl

theorem cell23_5476536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 10].length) (baseStart_5476536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476536 prefixEnd_5476536 := by exact prefixLift 5476536
  have htrace : WordTrace (prefixWord ++ tailWord_5476536) baseStart_5476536 baseEnd_5476536 := by
    simpa [prefixWord, tailWord_5476536, baseEnd_5476536] using wordTrace_append hprefix tailTrace_5476536
  have hstable : (prefixWord ++ tailWord_5476536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476536).length < 2 ^ (prefixWord ++ tailWord_5476536).sum := by decide
  have hdescent : baseEnd_5476536 < baseStart_5476536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476590 : List Nat := [4, 1, 2, 1, 1, 1, 1, 1, 2, 7, 2]
def baseStart_5476590 : Nat := 118140960795 + 5476590 * 2 ^ 59
def prefixEnd_5476590 : Nat := 4983230072969 + 3 ^ 40 * 5476590 * 2
def baseEnd_5476590 : Nat := 2812123017606833050138627

theorem tailTrace_5476590 : CollatzResearch.WordTrace tailWord_5476590 prefixEnd_5476590 2812123017606833050138627 := by
  unfold tailWord_5476590
  simp only [CollatzResearch.WordTrace]
  refine ⟨24968455903657153993989403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133165098152838154634610149 24968455903657153993989403)
  ·
    refine ⟨37452683855485730990984105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24968455903657153993989403 37452683855485730990984105)
    ·
      refine ⟨28089512891614298243238079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37452683855485730990984105 28089512891614298243238079)
      ·
        refine ⟨42134269337421447364857119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28089512891614298243238079 42134269337421447364857119)
        ·
          refine ⟨63201404006132171047285679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42134269337421447364857119 63201404006132171047285679)
          ·
            refine ⟨94802106009198256570928519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63201404006132171047285679 94802106009198256570928519)
            ·
              refine ⟨142203159013797384856392779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94802106009198256570928519 142203159013797384856392779)
              ·
                refine ⟨213304738520696077284589169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142203159013797384856392779 213304738520696077284589169)
                ·
                  refine ⟨159978553890522057963441877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213304738520696077284589169 159978553890522057963441877)
                  ·
                    refine ⟨3749497356809110733518169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 159978553890522057963441877 3749497356809110733518169)
                    ·
                      refine ⟨2812123017606833050138627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3749497356809110733518169 2812123017606833050138627)
                      ·
                        rfl

theorem cell23_5476590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_5476590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476590 prefixEnd_5476590 := by exact prefixLift 5476590
  have htrace : WordTrace (prefixWord ++ tailWord_5476590) baseStart_5476590 baseEnd_5476590 := by
    simpa [prefixWord, tailWord_5476590, baseEnd_5476590] using wordTrace_append hprefix tailTrace_5476590
  have hstable : (prefixWord ++ tailWord_5476590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476590).length < 2 ^ (prefixWord ++ tailWord_5476590).sum := by decide
  have hdescent : baseEnd_5476590 < baseStart_5476590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476623 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 3]
def baseStart_5476623 : Nat := 118140960795 + 5476623 * 2 ^ 59
def prefixEnd_5476623 : Nat := 4983230072969 + 3 ^ 40 * 5476623 * 2
def baseEnd_5476623 : Nat := 2812139962468431421025975

theorem tailTrace_5476623 : CollatzResearch.WordTrace tailWord_5476623 prefixEnd_5476623 2812139962468431421025975 := by
  unfold tailWord_5476623
  simp only [CollatzResearch.WordTrace]
  refine ⟨199748850838137678587866523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133165900558758452391911015 199748850838137678587866523)
  ·
    refine ⟨299623276257206517881799785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199748850838137678587866523 299623276257206517881799785)
    ·
      refine ⟨224717457192904888411349839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299623276257206517881799785 224717457192904888411349839)
      ·
        refine ⟨337076185789357332617024759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224717457192904888411349839 337076185789357332617024759)
        ·
          refine ⟨505614278684035998925537139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337076185789357332617024759 505614278684035998925537139)
          ·
            refine ⟨758421418026053998388305709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505614278684035998925537139 758421418026053998388305709)
            ·
              refine ⟨284408031759770249395614641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 758421418026053998388305709 284408031759770249395614641)
              ·
                refine ⟨213306023819827687046710981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284408031759770249395614641 213306023819827687046710981)
                ·
                  refine ⟨39994879466217691321258309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 213306023819827687046710981 39994879466217691321258309)
                  ·
                    refine ⟨7499039899915817122735933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39994879466217691321258309 7499039899915817122735933)
                    ·
                      refine ⟨2812139962468431421025975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7499039899915817122735933 2812139962468431421025975)
                      ·
                        rfl

theorem cell23_5476623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 4, 4, 3].length) (baseStart_5476623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476623 prefixEnd_5476623 := by exact prefixLift 5476623
  have htrace : WordTrace (prefixWord ++ tailWord_5476623) baseStart_5476623 baseEnd_5476623 := by
    simpa [prefixWord, tailWord_5476623, baseEnd_5476623] using wordTrace_append hprefix tailTrace_5476623
  have hstable : (prefixWord ++ tailWord_5476623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476623).length < 2 ^ (prefixWord ++ tailWord_5476623).sum := by decide
  have hdescent : baseEnd_5476623 < baseStart_5476623 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476640 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 3]
def baseStart_5476640 : Nat := 118140960795 + 5476640 * 2 ^ 59
def prefixEnd_5476640 : Nat := 4983230072969 + 3 ^ 40 * 5476640 * 2
def baseEnd_5476640 : Nat := 2812148691639557854513397

theorem tailTrace_5476640 : CollatzResearch.WordTrace tailWord_5476640 prefixEnd_5476640 2812148691639557854513397 := by
  unfold tailWord_5476640
  simp only [CollatzResearch.WordTrace]
  refine ⟨99874735439538045245617687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133166313919384060327490249 99874735439538045245617687)
  ·
    refine ⟨149812103159307067868426531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99874735439538045245617687 149812103159307067868426531)
    ·
      refine ⟨224718154738960601802639797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149812103159307067868426531 224718154738960601802639797)
      ·
        refine ⟨21067327006777556418997481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 224718154738960601802639797 21067327006777556418997481)
        ·
          refine ⟨15800495255083167314248111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21067327006777556418997481 15800495255083167314248111)
          ·
            refine ⟨23700742882624750971372167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15800495255083167314248111 23700742882624750971372167)
            ·
              refine ⟨35551114323937126457058251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23700742882624750971372167 35551114323937126457058251)
              ·
                refine ⟨53326671485905689685587377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35551114323937126457058251 53326671485905689685587377)
                ·
                  refine ⟨39995003614429267264190533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53326671485905689685587377 39995003614429267264190533)
                  ·
                    refine ⟨7499063177705487612035725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39995003614429267264190533 7499063177705487612035725)
                    ·
                      refine ⟨2812148691639557854513397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7499063177705487612035725 2812148691639557854513397)
                      ·
                        rfl

theorem cell23_5476640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_5476640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476640 prefixEnd_5476640 := by exact prefixLift 5476640
  have htrace : WordTrace (prefixWord ++ tailWord_5476640) baseStart_5476640 baseEnd_5476640 := by
    simpa [prefixWord, tailWord_5476640, baseEnd_5476640] using wordTrace_append hprefix tailTrace_5476640
  have hstable : (prefixWord ++ tailWord_5476640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476640).length < 2 ^ (prefixWord ++ tailWord_5476640).sum := by decide
  have hdescent : baseEnd_5476640 < baseStart_5476640 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476643 : List Nat := [1, 1, 1, 4, 2, 2, 2, 3, 7]
def baseStart_5476643 : Nat := 118140960795 + 5476643 * 2 ^ 59
def prefixEnd_5476643 : Nat := 4983230072969 + 3 ^ 40 * 5476643 * 2
def baseEnd_5476643 : Nat := 312461136897946815863987

theorem tailTrace_5476643 : CollatzResearch.WordTrace tailWord_5476643 prefixEnd_5476643 312461136897946815863987 := by
  unfold tailWord_5476643
  simp only [CollatzResearch.WordTrace]
  refine ⟨199749580298065222003594583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133166386865376814669063055 199749580298065222003594583)
  ·
    refine ⟨299624370447097833005391875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199749580298065222003594583 299624370447097833005391875)
    ·
      refine ⟨449436555670646749508087813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299624370447097833005391875 449436555670646749508087813)
      ·
        refine ⟨84269354188246265532766465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 449436555670646749508087813 84269354188246265532766465)
        ·
          refine ⟨63202015641184699149574849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84269354188246265532766465 63202015641184699149574849)
          ·
            refine ⟨47401511730888524362181137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63202015641184699149574849 47401511730888524362181137)
            ·
              refine ⟨35551133798166393271635853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47401511730888524362181137 35551133798166393271635853)
              ·
                refine ⟨13331675174312397476863445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35551133798166393271635853 13331675174312397476863445)
                ·
                  refine ⟨312461136897946815863987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13331675174312397476863445 312461136897946815863987)
                  ·
                    rfl

theorem cell23_5476643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 7].length) (baseStart_5476643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476643 prefixEnd_5476643 := by exact prefixLift 5476643
  have htrace : WordTrace (prefixWord ++ tailWord_5476643) baseStart_5476643 baseEnd_5476643 := by
    simpa [prefixWord, tailWord_5476643, baseEnd_5476643] using wordTrace_append hprefix tailTrace_5476643
  have hstable : (prefixWord ++ tailWord_5476643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476643).length < 2 ^ (prefixWord ++ tailWord_5476643).sum := by decide
  have hdescent : baseEnd_5476643 < baseStart_5476643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476660 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 9]
def baseStart_5476660 : Nat := 118140960795 + 5476660 * 2 ^ 59
def prefixEnd_5476660 : Nat := 4983230072969 + 3 ^ 40 * 5476660 * 2
def baseEnd_5476660 : Nat := 312462106805849752918145

theorem tailTrace_5476660 : CollatzResearch.WordTrace tailWord_5476660 prefixEnd_5476660 312462106805849752918145 := by
  unfold tailWord_5476660
  simp only [CollatzResearch.WordTrace]
  refine ⟨99875100169501816953481717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133166800226002422604642289 99875100169501816953481717)
  ·
    refine ⟨9363290640890795339388911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99875100169501816953481717 9363290640890795339388911)
    ·
      refine ⟨14044935961336193009083367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9363290640890795339388911 14044935961336193009083367)
      ·
        refine ⟨21067403942004289513625051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14044935961336193009083367 21067403942004289513625051)
        ·
          refine ⟨31601105913006434270437577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21067403942004289513625051 31601105913006434270437577)
          ·
            refine ⟨23700829434754825702828183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31601105913006434270437577 23700829434754825702828183)
            ·
              refine ⟨35551244152132238554242275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23700829434754825702828183 35551244152132238554242275)
              ·
                refine ⟨53326866228198357831363413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35551244152132238554242275 53326866228198357831363413)
                ·
                  refine ⟨312462106805849752918145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53326866228198357831363413 312462106805849752918145)
                  ·
                    rfl

theorem cell23_5476660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 9].length) (baseStart_5476660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476660 prefixEnd_5476660 := by exact prefixLift 5476660
  have htrace : WordTrace (prefixWord ++ tailWord_5476660) baseStart_5476660 baseEnd_5476660 := by
    simpa [prefixWord, tailWord_5476660, baseEnd_5476660] using wordTrace_append hprefix tailTrace_5476660
  have hstable : (prefixWord ++ tailWord_5476660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476660).length < 2 ^ (prefixWord ++ tailWord_5476660).sum := by decide
  have hdescent : baseEnd_5476660 < baseStart_5476660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476683 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 5]
def baseStart_5476683 : Nat := 118140960795 + 5476683 * 2 ^ 59
def prefixEnd_5476683 : Nat := 4983230072969 + 3 ^ 40 * 5476683 * 2
def baseEnd_5476683 : Nat := 2812170771307701186275699

theorem tailTrace_5476683 : CollatzResearch.WordTrace tailWord_5476683 prefixEnd_5476683 2812170771307701186275699 := by
  unfold tailWord_5476683
  simp only [CollatzResearch.WordTrace]
  refine ⟨199751039217920308835050703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133167359478613539223367135 199751039217920308835050703)
  ·
    refine ⟨299626558826880463252576055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199751039217920308835050703 299626558826880463252576055)
    ·
      refine ⟨449439838240320694878864083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299626558826880463252576055 449439838240320694878864083)
      ·
        refine ⟨674159757360481042318296125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449439838240320694878864083 674159757360481042318296125)
        ·
          refine ⟨252809909010180390869361047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 674159757360481042318296125 252809909010180390869361047)
          ·
            refine ⟨379214863515270586304041571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252809909010180390869361047 379214863515270586304041571)
            ·
              refine ⟨568822295272905879456062357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379214863515270586304041571 568822295272905879456062357)
              ·
                refine ⟨26663545090917463099502923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 568822295272905879456062357 26663545090917463099502923)
                ·
                  refine ⟨39995317636376194649254385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26663545090917463099502923 39995317636376194649254385)
                  ·
                    refine ⟨29996488227282145986940789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39995317636376194649254385 29996488227282145986940789)
                    ·
                      refine ⟨2812170771307701186275699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29996488227282145986940789 2812170771307701186275699)
                      ·
                        rfl

theorem cell23_5476683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 1, 2, 5].length) (baseStart_5476683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476683 prefixEnd_5476683 := by exact prefixLift 5476683
  have htrace : WordTrace (prefixWord ++ tailWord_5476683) baseStart_5476683 baseEnd_5476683 := by
    simpa [prefixWord, tailWord_5476683, baseEnd_5476683] using wordTrace_append hprefix tailTrace_5476683
  have hstable : (prefixWord ++ tailWord_5476683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476683).length < 2 ^ (prefixWord ++ tailWord_5476683).sum := by decide
  have hdescent : baseEnd_5476683 < baseStart_5476683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476690 : List Nat := [3, 2, 2, 1, 1, 1, 2, 4, 2, 5]
def baseStart_5476690 : Nat := 118140960795 + 5476690 * 2 ^ 59
def prefixEnd_5476690 : Nat := 4983230072969 + 3 ^ 40 * 5476690 * 2
def baseEnd_5476690 : Nat := 937391455224094219629389

theorem tailTrace_5476690 : CollatzResearch.WordTrace tailWord_5476690 prefixEnd_5476690 937391455224094219629389 := by
  unfold tailWord_5476690
  simp only [CollatzResearch.WordTrace]
  refine ⟨49937823632223737257638881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133167529685929966020370349 49937823632223737257638881)
  ·
    refine ⟨37453367724167802943229161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49937823632223737257638881 37453367724167802943229161)
    ·
      refine ⟨28090025793125852207421871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37453367724167802943229161 28090025793125852207421871)
      ·
        refine ⟨42135038689688778311132807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28090025793125852207421871 42135038689688778311132807)
        ·
          refine ⟨63202558034533167466699211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42135038689688778311132807 63202558034533167466699211)
          ·
            refine ⟨94803837051799751200048817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63202558034533167466699211 94803837051799751200048817)
            ·
              refine ⟨71102877788849813400036613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94803837051799751200048817 71102877788849813400036613)
              ·
                refine ⟨13331789585409340012506865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71102877788849813400036613 13331789585409340012506865)
                ·
                  refine ⟨9998842189057005009380149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13331789585409340012506865 9998842189057005009380149)
                  ·
                    refine ⟨937391455224094219629389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9998842189057005009380149 937391455224094219629389)
                    ·
                      rfl

theorem cell23_5476690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 4, 2, 5].length) (baseStart_5476690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476690 prefixEnd_5476690 := by exact prefixLift 5476690
  have htrace : WordTrace (prefixWord ++ tailWord_5476690) baseStart_5476690 baseEnd_5476690 := by
    simpa [prefixWord, tailWord_5476690, baseEnd_5476690] using wordTrace_append hprefix tailTrace_5476690
  have hstable : (prefixWord ++ tailWord_5476690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476690).length < 2 ^ (prefixWord ++ tailWord_5476690).sum := by decide
  have hdescent : baseEnd_5476690 < baseStart_5476690 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476723 : List Nat := [1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 6]
def baseStart_5476723 : Nat := 118140960795 + 5476723 * 2 ^ 59
def prefixEnd_5476723 : Nat := 4983230072969 + 3 ^ 40 * 5476723 * 2
def baseEnd_5476723 : Nat := 2812191310533881029775515

theorem tailTrace_5476723 : CollatzResearch.WordTrace tailWord_5476723 prefixEnd_5476723 2812191310533881029775515 := by
  unfold tailWord_5476723
  simp only [CollatzResearch.WordTrace]
  refine ⟨199752498137775395666506823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133168332091850263777671215 199752498137775395666506823)
  ·
    refine ⟨299628747206663093499760235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199752498137775395666506823 299628747206663093499760235)
    ·
      refine ⟨449443120809994640249640353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299628747206663093499760235 449443120809994640249640353)
      ·
        refine ⟨337082340607495980187230265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 449443120809994640249640353 337082340607495980187230265)
        ·
          refine ⟨252811755455621985140422699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337082340607495980187230265 252811755455621985140422699)
          ·
            refine ⟨379217633183432977710634049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252811755455621985140422699 379217633183432977710634049)
            ·
              refine ⟨284413224887574733282975537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379217633183432977710634049 284413224887574733282975537)
              ·
                refine ⟨213309918665681049962231653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284413224887574733282975537 213309918665681049962231653)
                ·
                  refine ⟨39995609749815196867918435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 213309918665681049962231653 39995609749815196867918435)
                  ·
                    refine ⟨59993414624722795301877653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39995609749815196867918435 59993414624722795301877653)
                    ·
                      refine ⟨2812191310533881029775515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59993414624722795301877653 2812191310533881029775515)
                      ·
                        rfl

theorem cell23_5476723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 2, 4, 1, 6].length) (baseStart_5476723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476723 prefixEnd_5476723 := by exact prefixLift 5476723
  have htrace : WordTrace (prefixWord ++ tailWord_5476723) baseStart_5476723 baseEnd_5476723 := by
    simpa [prefixWord, tailWord_5476723, baseEnd_5476723] using wordTrace_append hprefix tailTrace_5476723
  have hstable : (prefixWord ++ tailWord_5476723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476723).length < 2 ^ (prefixWord ++ tailWord_5476723).sum := by decide
  have hdescent : baseEnd_5476723 < baseStart_5476723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476747 : List Nat := [1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 3]
def baseStart_5476747 : Nat := 118140960795 + 5476747 * 2 ^ 59
def prefixEnd_5476747 : Nat := 4983230072969 + 3 ^ 40 * 5476747 * 2
def baseEnd_5476747 : Nat := 2812203634069588935875405

theorem tailTrace_5476747 : CollatzResearch.WordTrace tailWord_5476747 prefixEnd_5476747 2812203634069588935875405 := by
  unfold tailWord_5476747
  simp only [CollatzResearch.WordTrace]
  refine ⟨199753373489688447765380495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133168915659792298510253663 199753373489688447765380495)
  ·
    refine ⟨299630060234532671648070743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199753373489688447765380495 299630060234532671648070743)
    ·
      refine ⟨449445090351799007472106115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299630060234532671648070743 449445090351799007472106115)
      ·
        refine ⟨674167635527698511208159173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449445090351799007472106115 674167635527698511208159173)
        ·
          refine ⟨126406431661443470851529845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 674167635527698511208159173 126406431661443470851529845)
          ·
            refine ⟨11850602968260325392330923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126406431661443470851529845 11850602968260325392330923)
            ·
              refine ⟨17775904452390488088496385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11850602968260325392330923 17775904452390488088496385)
              ·
                refine ⟨13331928339292866066372289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17775904452390488088496385 13331928339292866066372289)
                ·
                  refine ⟨9998946254469649549779217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13331928339292866066372289 9998946254469649549779217)
                  ·
                    refine ⟨7499209690852237162334413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9998946254469649549779217 7499209690852237162334413)
                    ·
                      refine ⟨2812203634069588935875405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7499209690852237162334413 2812203634069588935875405)
                      ·
                        rfl

theorem cell23_5476747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 2, 2, 3].length) (baseStart_5476747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476747 prefixEnd_5476747 := by exact prefixLift 5476747
  have htrace : WordTrace (prefixWord ++ tailWord_5476747) baseStart_5476747 baseEnd_5476747 := by
    simpa [prefixWord, tailWord_5476747, baseEnd_5476747] using wordTrace_append hprefix tailTrace_5476747
  have hstable : (prefixWord ++ tailWord_5476747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476747).length < 2 ^ (prefixWord ++ tailWord_5476747).sum := by decide
  have hdescent : baseEnd_5476747 < baseStart_5476747 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476777 : List Nat := [1, 2, 1, 1, 1, 1, 3, 6, 3, 1, 3]
def baseStart_5476777 : Nat := 118140960795 + 5476777 * 2 ^ 59
def prefixEnd_5476777 : Nat := 4983230072969 + 3 ^ 40 * 5476777 * 2
def baseEnd_5476777 : Nat := 2812219038489223818500267

theorem tailTrace_5476777 : CollatzResearch.WordTrace tailWord_5476777 prefixEnd_5476777 2812219038489223818500267 := by
  unfold tailWord_5476777
  simp only [CollatzResearch.WordTrace]
  refine ⟨199754467679579762888972585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133169645119719841925981723 199754467679579762888972585)
  ·
    refine ⟨149815850759684822166729439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199754467679579762888972585 149815850759684822166729439)
    ·
      refine ⟨224723776139527233250094159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149815850759684822166729439 224723776139527233250094159)
      ·
        refine ⟨337085664209290849875141239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224723776139527233250094159 337085664209290849875141239)
        ·
          refine ⟨505628496313936274812711859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337085664209290849875141239 505628496313936274812711859)
          ·
            refine ⟨758442744470904412219067789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505628496313936274812711859 758442744470904412219067789)
            ·
              refine ⟨284416029176589154582150421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 758442744470904412219067789 284416029176589154582150421)
              ·
                refine ⟨13332001367652616621038301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 284416029176589154582150421 13332001367652616621038301)
                ·
                  refine ⟨4999500512869731232889363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13332001367652616621038301 4999500512869731232889363)
                  ·
                    refine ⟨7499250769304596849334045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4999500512869731232889363 7499250769304596849334045)
                    ·
                      refine ⟨2812219038489223818500267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7499250769304596849334045 2812219038489223818500267)
                      ·
                        rfl

theorem cell23_5476777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 3, 1, 3].length) (baseStart_5476777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476777 prefixEnd_5476777 := by exact prefixLift 5476777
  have htrace : WordTrace (prefixWord ++ tailWord_5476777) baseStart_5476777 baseEnd_5476777 := by
    simpa [prefixWord, tailWord_5476777, baseEnd_5476777] using wordTrace_append hprefix tailTrace_5476777
  have hstable : (prefixWord ++ tailWord_5476777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476777).length < 2 ^ (prefixWord ++ tailWord_5476777).sum := by decide
  have hdescent : baseEnd_5476777 < baseStart_5476777 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476778 : List Nat := [3, 1, 6, 1, 1, 1, 2, 1, 2, 1, 4]
def baseStart_5476778 : Nat := 118140960795 + 5476778 * 2 ^ 59
def prefixEnd_5476778 : Nat := 4983230072969 + 3 ^ 40 * 5476778 * 2
def baseEnd_5476778 : Nat := 2812219551969878314587763

theorem tailTrace_5476778 : CollatzResearch.WordTrace tailWord_5476778 prefixEnd_5476778 2812219551969878314587763 := by
  unfold tailWord_5476778
  simp only [CollatzResearch.WordTrace]
  refine ⟨49938626038144035014939747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133169669435050760039839325 49938626038144035014939747)
  ·
    refine ⟨74907939057216052522409621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49938626038144035014939747 74907939057216052522409621)
    ·
      refine ⟨3511309643307002461987951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74907939057216052522409621 3511309643307002461987951)
      ·
        refine ⟨5266964464960503692981927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3511309643307002461987951 5266964464960503692981927)
        ·
          refine ⟨7900446697440755539472891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5266964464960503692981927 7900446697440755539472891)
          ·
            refine ⟨11850670046161133309209337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7900446697440755539472891 11850670046161133309209337)
            ·
              refine ⟨8888002534620849981907003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11850670046161133309209337 8888002534620849981907003)
              ·
                refine ⟨13332003801931274972860505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8888002534620849981907003 13332003801931274972860505)
                ·
                  refine ⟨9999002851448456229645379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13332003801931274972860505 9999002851448456229645379)
                  ·
                    refine ⟨14998504277172684344468069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9999002851448456229645379 14998504277172684344468069)
                    ·
                      refine ⟨2812219551969878314587763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14998504277172684344468069 2812219551969878314587763)
                      ·
                        rfl

theorem cell23_5476778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_5476778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476778 prefixEnd_5476778 := by exact prefixLift 5476778
  have htrace : WordTrace (prefixWord ++ tailWord_5476778) baseStart_5476778 baseEnd_5476778 := by
    simpa [prefixWord, tailWord_5476778, baseEnd_5476778] using wordTrace_append hprefix tailTrace_5476778
  have hstable : (prefixWord ++ tailWord_5476778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476778).length < 2 ^ (prefixWord ++ tailWord_5476778).sum := by decide
  have hdescent : baseEnd_5476778 < baseStart_5476778 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476781 : List Nat := [1, 5, 2, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_5476781 : Nat := 118140960795 + 5476781 * 2 ^ 59
def prefixEnd_5476781 : Nat := 4983230072969 + 3 ^ 40 * 5476781 * 2
def baseEnd_5476781 : Nat := 2812221092411841802850249

theorem tailTrace_5476781 : CollatzResearch.WordTrace tailWord_5476781 prefixEnd_5476781 2812221092411841802850249 := by
  unfold tailWord_5476781
  simp only [CollatzResearch.WordTrace]
  refine ⟨199754613571565271572118197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133169742381043514381412131 199754613571565271572118197)
  ·
    refine ⟨18726995022334244209886081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 199754613571565271572118197 18726995022334244209886081)
    ·
      refine ⟨14045246266750683157414561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18726995022334244209886081 14045246266750683157414561)
      ·
        refine ⟨10533934700063012368060921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14045246266750683157414561 10533934700063012368060921)
        ·
          refine ⟨7900451025047259276045691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10533934700063012368060921 7900451025047259276045691)
          ·
            refine ⟨11850676537570888914068537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7900451025047259276045691 11850676537570888914068537)
            ·
              refine ⟨8888007403178166685551403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11850676537570888914068537 8888007403178166685551403)
              ·
                refine ⟨13332011104767250028327105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8888007403178166685551403 13332011104767250028327105)
                ·
                  refine ⟨9999008328575437521245329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13332011104767250028327105 9999008328575437521245329)
                  ·
                    refine ⟨7499256246431578140933997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9999008328575437521245329 7499256246431578140933997)
                    ·
                      refine ⟨2812221092411841802850249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7499256246431578140933997 2812221092411841802850249)
                      ·
                        rfl

theorem cell23_5476781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_5476781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476781 prefixEnd_5476781 := by exact prefixLift 5476781
  have htrace : WordTrace (prefixWord ++ tailWord_5476781) baseStart_5476781 baseEnd_5476781 := by
    simpa [prefixWord, tailWord_5476781, baseEnd_5476781] using wordTrace_append hprefix tailTrace_5476781
  have hstable : (prefixWord ++ tailWord_5476781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476781).length < 2 ^ (prefixWord ++ tailWord_5476781).sum := by decide
  have hdescent : baseEnd_5476781 < baseStart_5476781 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476810 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 3, 6]
def baseStart_5476810 : Nat := 118140960795 + 5476810 * 2 ^ 59
def prefixEnd_5476810 : Nat := 4983230072969 + 3 ^ 40 * 5476810 * 2
def baseEnd_5476810 : Nat := 937411994450274063129205

theorem tailTrace_5476810 : CollatzResearch.WordTrace tailWord_5476810 prefixEnd_5476810 937411994450274063129205 := by
  unfold tailWord_5476810
  simp only [CollatzResearch.WordTrace]
  refine ⟨49938917822115052381230971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133170447525640139683282589 49938917822115052381230971)
  ·
    refine ⟨74908376733172578571846457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49938917822115052381230971 74908376733172578571846457)
    ·
      refine ⟨56181282549879433928884843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74908376733172578571846457 56181282549879433928884843)
      ·
        refine ⟨84271923824819150893327265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56181282549879433928884843 84271923824819150893327265)
        ·
          refine ⟨63203942868614363169995449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84271923824819150893327265 63203942868614363169995449)
          ·
            refine ⟨47402957151460772377496587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63203942868614363169995449 47402957151460772377496587)
            ·
              refine ⟨71104435727191158566244881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47402957151460772377496587 71104435727191158566244881)
              ·
                refine ⟨53328326795393368924683661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71104435727191158566244881 53328326795393368924683661)
                ·
                  refine ⟨19998122548272513346756373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53328326795393368924683661 19998122548272513346756373)
                  ·
                    refine ⟨937411994450274063129205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19998122548272513346756373 937411994450274063129205)
                    ·
                      rfl

theorem cell23_5476810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_5476810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476810 prefixEnd_5476810 := by exact prefixLift 5476810
  have htrace : WordTrace (prefixWord ++ tailWord_5476810) baseStart_5476810 baseEnd_5476810 := by
    simpa [prefixWord, tailWord_5476810, baseEnd_5476810] using wordTrace_append hprefix tailTrace_5476810
  have hstable : (prefixWord ++ tailWord_5476810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476810).length < 2 ^ (prefixWord ++ tailWord_5476810).sum := by decide
  have hdescent : baseEnd_5476810 < baseStart_5476810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476860 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 2, 2, 6]
def baseStart_5476860 : Nat := 118140960795 + 5476860 * 2 ^ 59
def prefixEnd_5476860 : Nat := 4983230072969 + 3 ^ 40 * 5476860 * 2
def baseEnd_5476860 : Nat := 2812261657383546993762385

theorem tailTrace_5476860 : CollatzResearch.WordTrace tailWord_5476860 prefixEnd_5476860 2812261657383546993762385 := by
  unfold tailWord_5476860
  simp only [CollatzResearch.WordTrace]
  refine ⟨99878747469139534032122017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133171663292186045376162689 99878747469139534032122017)
  ·
    refine ⟨74909060601854650524091513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99878747469139534032122017 74909060601854650524091513)
    ·
      refine ⟨56181795451390987893068635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74909060601854650524091513 56181795451390987893068635)
      ·
        refine ⟨84272693177086481839602953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56181795451390987893068635 84272693177086481839602953)
        ·
          refine ⟨63204519882814861379702215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84272693177086481839602953 63204519882814861379702215)
          ·
            refine ⟨94806779824222292069553323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63204519882814861379702215 94806779824222292069553323)
            ·
              refine ⟨142210169736333438104329985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94806779824222292069553323 142210169736333438104329985)
              ·
                refine ⟨106657627302250078578247489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142210169736333438104329985 106657627302250078578247489)
                ·
                  refine ⟨79993220476687558933685617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106657627302250078578247489 79993220476687558933685617)
                  ·
                    refine ⟨59994915357515669200264213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79993220476687558933685617 59994915357515669200264213)
                    ·
                      refine ⟨2812261657383546993762385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59994915357515669200264213 2812261657383546993762385)
                      ·
                        rfl

theorem cell23_5476860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_5476860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476860 prefixEnd_5476860 := by exact prefixLift 5476860
  have htrace : WordTrace (prefixWord ++ tailWord_5476860) baseStart_5476860 baseEnd_5476860 := by
    simpa [prefixWord, tailWord_5476860, baseEnd_5476860] using wordTrace_append hprefix tailTrace_5476860
  have hstable : (prefixWord ++ tailWord_5476860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476860).length < 2 ^ (prefixWord ++ tailWord_5476860).sum := by decide
  have hdescent : baseEnd_5476860 < baseStart_5476860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476868 : List Nat := [2, 3, 2, 3, 1, 2, 2, 1, 3, 2, 2]
def baseStart_5476868 : Nat := 118140960795 + 5476868 * 2 ^ 59
def prefixEnd_5476868 : Nat := 4983230072969 + 3 ^ 40 * 5476868 * 2
def baseEnd_5476868 : Nat := 2812265765228782962462349

theorem tailTrace_5476868 : CollatzResearch.WordTrace tailWord_5476868 prefixEnd_5476868 2812265765228782962462349 := by
  unfold tailWord_5476868
  simp only [CollatzResearch.WordTrace]
  refine ⟨99878893361125042715267629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133171857814833390287023505 99878893361125042715267629)
  ·
    refine ⟨37454585010421891018225361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99878893361125042715267629 37454585010421891018225361)
    ·
      refine ⟨28090938757816418263669021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37454585010421891018225361 28090938757816418263669021)
      ·
        refine ⟨10534102034181156848875883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28090938757816418263669021 10534102034181156848875883)
        ·
          refine ⟨15801153051271735273313825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10534102034181156848875883 15801153051271735273313825)
          ·
            refine ⟨11850864788453801454985369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15801153051271735273313825 11850864788453801454985369)
            ·
              refine ⟨8888148591340351091239027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11850864788453801454985369 8888148591340351091239027)
              ·
                refine ⟨13332222887010526636858541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8888148591340351091239027 13332222887010526636858541)
                ·
                  refine ⟨4999583582628947488821953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13332222887010526636858541 4999583582628947488821953)
                  ·
                    refine ⟨3749687686971710616616465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4999583582628947488821953 3749687686971710616616465)
                    ·
                      refine ⟨2812265765228782962462349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3749687686971710616616465 2812265765228782962462349)
                      ·
                        rfl

theorem cell23_5476868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 3, 2, 2].length) (baseStart_5476868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476868 prefixEnd_5476868 := by exact prefixLift 5476868
  have htrace : WordTrace (prefixWord ++ tailWord_5476868) baseStart_5476868 baseEnd_5476868 := by
    simpa [prefixWord, tailWord_5476868, baseEnd_5476868] using wordTrace_append hprefix tailTrace_5476868
  have hstable : (prefixWord ++ tailWord_5476868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476868).length < 2 ^ (prefixWord ++ tailWord_5476868).sum := by decide
  have hdescent : baseEnd_5476868 < baseStart_5476868 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476927 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 3]
def baseStart_5476927 : Nat := 118140960795 + 5476927 * 2 ^ 59
def prefixEnd_5476927 : Nat := 4983230072969 + 3 ^ 40 * 5476927 * 2
def baseEnd_5476927 : Nat := 2812296060587398231624577

theorem tailTrace_5476927 : CollatzResearch.WordTrace tailWord_5476927 prefixEnd_5476927 2812296060587398231624577 := by
  unfold tailWord_5476927
  simp only [CollatzResearch.WordTrace]
  refine ⟨199759938629036338506933035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133173292419357559004622023 199759938629036338506933035)
  ·
    refine ⟨299639907943554507760399553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199759938629036338506933035 299639907943554507760399553)
    ·
      refine ⟨224729930957665880820299665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299639907943554507760399553 224729930957665880820299665)
      ·
        refine ⟨168547448218249410615224749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224729930957665880820299665 168547448218249410615224749)
        ·
          refine ⟨63205293081843528980709281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168547448218249410615224749 63205293081843528980709281)
          ·
            refine ⟨47403969811382646735531961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63205293081843528980709281 47403969811382646735531961)
            ·
              refine ⟨35552977358536985051648971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47403969811382646735531961 35552977358536985051648971)
              ·
                refine ⟨53329466037805477577473457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35552977358536985051648971 53329466037805477577473457)
                ·
                  refine ⟨39997099528354108183105093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53329466037805477577473457 39997099528354108183105093)
                  ·
                    refine ⟨7499456161566395284332205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39997099528354108183105093 7499456161566395284332205)
                    ·
                      refine ⟨2812296060587398231624577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7499456161566395284332205 2812296060587398231624577)
                      ·
                        rfl

theorem cell23_5476927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 4, 3].length) (baseStart_5476927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476927 prefixEnd_5476927 := by exact prefixLift 5476927
  have htrace : WordTrace (prefixWord ++ tailWord_5476927) baseStart_5476927 baseEnd_5476927 := by
    simpa [prefixWord, tailWord_5476927, baseEnd_5476927] using wordTrace_append hprefix tailTrace_5476927
  have hstable : (prefixWord ++ tailWord_5476927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476927).length < 2 ^ (prefixWord ++ tailWord_5476927).sum := by decide
  have hdescent : baseEnd_5476927 < baseStart_5476927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476962 : List Nat := [3, 3, 2, 3, 1, 1, 3, 1, 1, 3, 2]
def baseStart_5476962 : Nat := 118140960795 + 5476962 * 2 ^ 59
def prefixEnd_5476962 : Nat := 4983230072969 + 3 ^ 40 * 5476962 * 2
def baseEnd_5476962 : Nat := 2812314032410305594686917

theorem tailTrace_5476962 : CollatzResearch.WordTrace tailWord_5476962 prefixEnd_5476962 2812314032410305594686917 := by
  unfold tailWord_5476962
  simp only [CollatzResearch.WordTrace]
  refine ⟨49940303795977384871114285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133174143455939692989638093 49940303795977384871114285)
  ·
    refine ⟨18727613923491519326667857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49940303795977384871114285 18727613923491519326667857)
    ·
      refine ⟨14045710442618639495000893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18727613923491519326667857 14045710442618639495000893)
      ·
        refine ⟨5267141415981989810625335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14045710442618639495000893 5267141415981989810625335)
        ·
          refine ⟨7900712123972984715938003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5267141415981989810625335 7900712123972984715938003)
          ·
            refine ⟨11851068185959477073907005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7900712123972984715938003 11851068185959477073907005)
            ·
              refine ⟨4444150569734803902715127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11851068185959477073907005 4444150569734803902715127)
              ·
                refine ⟨6666225854602205854072691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4444150569734803902715127 6666225854602205854072691)
                ·
                  refine ⟨9999338781903308781109037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6666225854602205854072691 9999338781903308781109037)
                  ·
                    refine ⟨3749752043213740792915889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9999338781903308781109037 3749752043213740792915889)
                    ·
                      refine ⟨2812314032410305594686917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3749752043213740792915889 2812314032410305594686917)
                      ·
                        rfl

theorem cell23_5476962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_5476962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476962 prefixEnd_5476962 := by exact prefixLift 5476962
  have htrace : WordTrace (prefixWord ++ tailWord_5476962) baseStart_5476962 baseEnd_5476962 := by
    simpa [prefixWord, tailWord_5476962, baseEnd_5476962] using wordTrace_append hprefix tailTrace_5476962
  have hstable : (prefixWord ++ tailWord_5476962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476962).length < 2 ^ (prefixWord ++ tailWord_5476962).sum := by decide
  have hdescent : baseEnd_5476962 < baseStart_5476962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5476964 : List Nat := [2, 3, 1, 1, 2, 2, 2, 5, 5]
def baseStart_5476964 : Nat := 118140960795 + 5476964 * 2 ^ 59
def prefixEnd_5476964 : Nat := 4983230072969 + 3 ^ 40 * 5476964 * 2
def baseEnd_5476964 : Nat := 312479451041290509651323

theorem tailTrace_5476964 : CollatzResearch.WordTrace tailWord_5476964 prefixEnd_5476964 312479451041290509651323 := by
  unfold tailWord_5476964
  simp only [CollatzResearch.WordTrace]
  refine ⟨99880644064951146913014973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133174192086601529217353297 99880644064951146913014973)
  ·
    refine ⟨37455241524356680092380615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99880644064951146913014973 37455241524356680092380615)
    ·
      refine ⟨56182862286535020138570923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37455241524356680092380615 56182862286535020138570923)
      ·
        refine ⟨84274293429802530207856385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56182862286535020138570923 84274293429802530207856385)
        ·
          refine ⟨63205720072351897655892289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84274293429802530207856385 63205720072351897655892289)
          ·
            refine ⟨47404290054263923241919217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63205720072351897655892289 47404290054263923241919217)
            ·
              refine ⟨35553217540697942431439413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47404290054263923241919217 35553217540697942431439413)
              ·
                refine ⟨3333114144440432102947445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35553217540697942431439413 3333114144440432102947445)
                ·
                  refine ⟨312479451041290509651323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3333114144440432102947445 312479451041290509651323)
                  ·
                    rfl

theorem cell23_5476964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 5].length) (baseStart_5476964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5476964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5476964 prefixEnd_5476964 := by exact prefixLift 5476964
  have htrace : WordTrace (prefixWord ++ tailWord_5476964) baseStart_5476964 baseEnd_5476964 := by
    simpa [prefixWord, tailWord_5476964, baseEnd_5476964] using wordTrace_append hprefix tailTrace_5476964
  have hstable : (prefixWord ++ tailWord_5476964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5476964).length < 2 ^ (prefixWord ++ tailWord_5476964).sum := by decide
  have hdescent : baseEnd_5476964 < baseStart_5476964 := by decide
  rcases family_descends (prefixWord ++ tailWord_5476964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477104 : List Nat := [2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 4]
def baseStart_5477104 : Nat := 118140960795 + 5477104 * 2 ^ 59
def prefixEnd_5477104 : Nat := 4983230072969 + 3 ^ 40 * 5477104 * 2
def baseEnd_5477104 : Nat := 2812386946663244039111263

theorem tailTrace_5477104 : CollatzResearch.WordTrace tailWord_5477104 prefixEnd_5477104 2812386946663244039111263 := by
  unfold tailWord_5477104
  simp only [CollatzResearch.WordTrace]
  refine ⟨99883197174697548868063183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133177596232930065157417577 99883197174697548868063183)
  ·
    refine ⟨149824795762046323302094775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99883197174697548868063183 149824795762046323302094775)
    ·
      refine ⟨224737193643069484953142163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149824795762046323302094775 224737193643069484953142163)
      ·
        refine ⟨337105790464604227429713245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224737193643069484953142163 337105790464604227429713245)
        ·
          refine ⟨126414671424226585286142467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 337105790464604227429713245 126414671424226585286142467)
          ·
            refine ⟨189622007136339877929213701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126414671424226585286142467 189622007136339877929213701)
            ·
              refine ⟨35554126338063727111727569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189622007136339877929213701 35554126338063727111727569)
              ·
                refine ⟨26665594753547795333795677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35554126338063727111727569 26665594753547795333795677)
                ·
                  refine ⟨9999598032580423250173379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26665594753547795333795677 9999598032580423250173379)
                  ·
                    refine ⟨14999397048870634875260069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9999598032580423250173379 14999397048870634875260069)
                    ·
                      refine ⟨2812386946663244039111263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14999397048870634875260069 2812386946663244039111263)
                      ·
                        rfl

theorem cell23_5477104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 4].length) (baseStart_5477104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477104 prefixEnd_5477104 := by exact prefixLift 5477104
  have htrace : WordTrace (prefixWord ++ tailWord_5477104) baseStart_5477104 baseEnd_5477104 := by
    simpa [prefixWord, tailWord_5477104, baseEnd_5477104] using wordTrace_append hprefix tailTrace_5477104
  have hstable : (prefixWord ++ tailWord_5477104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477104).length < 2 ^ (prefixWord ++ tailWord_5477104).sum := by decide
  have hdescent : baseEnd_5477104 < baseStart_5477104 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477118 : List Nat := [4, 2, 2, 1, 2, 1, 3, 2, 1, 5]
def baseStart_5477118 : Nat := 118140960795 + 5477118 * 2 ^ 59
def prefixEnd_5477118 : Nat := 4983230072969 + 3 ^ 40 * 5477118 * 2
def baseEnd_5477118 : Nat := 937464711797468994778733

theorem tailTrace_5477118 : CollatzResearch.WordTrace tailWord_5477118 prefixEnd_5477118 937464711797468994778733 := by
  unfold tailWord_5477118
  simp only [CollatzResearch.WordTrace]
  refine ⟨24970863121418047265892001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133177936647562918751424005 24970863121418047265892001)
  ·
    refine ⟨18728147341063535449419001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24970863121418047265892001 18728147341063535449419001)
    ·
      refine ⟨14046110505797651587064251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18728147341063535449419001 14046110505797651587064251)
      ·
        refine ⟨21069165758696477380596377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14046110505797651587064251 21069165758696477380596377)
        ·
          refine ⟨15801874319022358035447283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21069165758696477380596377 15801874319022358035447283)
          ·
            refine ⟨23702811478533537053170925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15801874319022358035447283 23702811478533537053170925)
            ·
              refine ⟨8888554304450076394939097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23702811478533537053170925 8888554304450076394939097)
              ·
                refine ⟨6666415728337557296204323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8888554304450076394939097 6666415728337557296204323)
                ·
                  refine ⟨9999623592506335944306485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6666415728337557296204323 9999623592506335944306485)
                  ·
                    refine ⟨937464711797468994778733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9999623592506335944306485 937464711797468994778733)
                    ·
                      rfl

theorem cell23_5477118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_5477118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477118 prefixEnd_5477118 := by exact prefixLift 5477118
  have htrace : WordTrace (prefixWord ++ tailWord_5477118) baseStart_5477118 baseEnd_5477118 := by
    simpa [prefixWord, tailWord_5477118, baseEnd_5477118] using wordTrace_append hprefix tailTrace_5477118
  have hstable : (prefixWord ++ tailWord_5477118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477118).length < 2 ^ (prefixWord ++ tailWord_5477118).sum := by decide
  have hdescent : baseEnd_5477118 < baseStart_5477118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477148 : List Nat := [2, 2, 3, 1, 1, 4, 2, 2, 2, 4]
def baseStart_5477148 : Nat := 118140960795 + 5477148 * 2 ^ 59
def prefixEnd_5477148 : Nat := 4983230072969 + 3 ^ 40 * 5477148 * 2
def baseEnd_5477148 : Nat := 937469846604013955653687

theorem tailTrace_5477148 : CollatzResearch.WordTrace tailWord_5477148 prefixEnd_5477148 937469846604013955653687 := by
  unfold tailWord_5477148
  simp only [CollatzResearch.WordTrace]
  refine ⟨99883999580617846625364049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133178666107490462167152065 99883999580617846625364049)
  ·
    refine ⟨74912999685463384969023037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99883999580617846625364049 74912999685463384969023037)
    ·
      refine ⟨28092374882048769363383639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74912999685463384969023037 28092374882048769363383639)
      ·
        refine ⟨42138562323073154045075459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28092374882048769363383639 42138562323073154045075459)
        ·
          refine ⟨63207843484609731067613189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42138562323073154045075459 63207843484609731067613189)
          ·
            refine ⟨11851470653364324575177473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 63207843484609731067613189 11851470653364324575177473)
            ·
              refine ⟨8888602990023243431383105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11851470653364324575177473 8888602990023243431383105)
              ·
                refine ⟨6666452242517432573537329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8888602990023243431383105 6666452242517432573537329)
                ·
                  refine ⟨4999839181888074430152997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6666452242517432573537329 4999839181888074430152997)
                  ·
                    refine ⟨937469846604013955653687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4999839181888074430152997 937469846604013955653687)
                    ·
                      rfl

theorem cell23_5477148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 2, 2, 4].length) (baseStart_5477148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477148 prefixEnd_5477148 := by exact prefixLift 5477148
  have htrace : WordTrace (prefixWord ++ tailWord_5477148) baseStart_5477148 baseEnd_5477148 := by
    simpa [prefixWord, tailWord_5477148, baseEnd_5477148] using wordTrace_append hprefix tailTrace_5477148
  have hstable : (prefixWord ++ tailWord_5477148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477148).length < 2 ^ (prefixWord ++ tailWord_5477148).sum := by decide
  have hdescent : baseEnd_5477148 < baseStart_5477148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477165 : List Nat := [1, 5, 3, 2, 1, 1, 2, 1, 1, 6]
def baseStart_5477165 : Nat := 118140960795 + 5477165 * 2 ^ 59
def prefixEnd_5477165 : Nat := 4983230072969 + 3 ^ 40 * 5477165 * 2
def baseEnd_5477165 : Nat := 937472756327722766816161

theorem tailTrace_5477165 : CollatzResearch.WordTrace tailWord_5477165 prefixEnd_5477165 937472756327722766816161 := by
  unfold tailWord_5477165
  simp only [CollatzResearch.WordTrace]
  refine ⟨199768619202174105154096949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133179079468116070102731299 199768619202174105154096949)
  ·
    refine ⟨18728308050203822358196589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 199768619202174105154096949 18728308050203822358196589)
    ·
      refine ⟨7023115518826433384323721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18728308050203822358196589 7023115518826433384323721)
      ·
        refine ⟨5267336639119825038242791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7023115518826433384323721 5267336639119825038242791)
        ·
          refine ⟨7901004958679737557364187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5267336639119825038242791 7901004958679737557364187)
          ·
            refine ⟨11851507438019606336046281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7901004958679737557364187 11851507438019606336046281)
            ·
              refine ⟨8888630578514704752034711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11851507438019606336046281 8888630578514704752034711)
              ·
                refine ⟨13332945867772057128052067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8888630578514704752034711 13332945867772057128052067)
                ·
                  refine ⟨19999418801658085692078101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13332945867772057128052067 19999418801658085692078101)
                  ·
                    refine ⟨937472756327722766816161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19999418801658085692078101 937472756327722766816161)
                    ·
                      rfl

theorem cell23_5477165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_5477165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477165 prefixEnd_5477165 := by exact prefixLift 5477165
  have htrace : WordTrace (prefixWord ++ tailWord_5477165) baseStart_5477165 baseEnd_5477165 := by
    simpa [prefixWord, tailWord_5477165, baseEnd_5477165] using wordTrace_append hprefix tailTrace_5477165
  have hstable : (prefixWord ++ tailWord_5477165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477165).length < 2 ^ (prefixWord ++ tailWord_5477165).sum := by decide
  have hdescent : baseEnd_5477165 < baseStart_5477165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477171 : List Nat := [1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 3]
def baseStart_5477171 : Nat := 118140960795 + 5477171 * 2 ^ 59
def prefixEnd_5477171 : Nat := 4983230072969 + 3 ^ 40 * 5477171 * 2
def baseEnd_5477171 : Nat := 2812421349867095276973455

theorem tailTrace_5477171 : CollatzResearch.WordTrace tailWord_5477171 prefixEnd_5477171 2812421349867095276973455 := by
  unfold tailWord_5477171
  simp only [CollatzResearch.WordTrace]
  refine ⟨199768838040152368178815367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133179225360101578785876911 199768838040152368178815367)
  ·
    refine ⟨299653257060228552268223051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199768838040152368178815367 299653257060228552268223051)
    ·
      refine ⟨449479885590342828402334577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299653257060228552268223051 449479885590342828402334577)
      ·
        refine ⟨337109914192757121301750933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 449479885590342828402334577 337109914192757121301750933)
        ·
          refine ⟨15802027227785490061019575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 337109914192757121301750933 15802027227785490061019575)
          ·
            refine ⟨23703040841678235091529363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15802027227785490061019575 23703040841678235091529363)
            ·
              refine ⟨35554561262517352637294045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23703040841678235091529363 35554561262517352637294045)
              ·
                refine ⟨13332960473444007238985267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35554561262517352637294045 13332960473444007238985267)
                ·
                  refine ⟨19999440710166010858477901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13332960473444007238985267 19999440710166010858477901)
                  ·
                    refine ⟨7499790266312254071929213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19999440710166010858477901 7499790266312254071929213)
                    ·
                      refine ⟨2812421349867095276973455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7499790266312254071929213 2812421349867095276973455)
                      ·
                        rfl

theorem cell23_5477171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 3, 1, 3, 3].length) (baseStart_5477171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477171 prefixEnd_5477171 := by exact prefixLift 5477171
  have htrace : WordTrace (prefixWord ++ tailWord_5477171) baseStart_5477171 baseEnd_5477171 := by
    simpa [prefixWord, tailWord_5477171, baseEnd_5477171] using wordTrace_append hprefix tailTrace_5477171
  have hstable : (prefixWord ++ tailWord_5477171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477171).length < 2 ^ (prefixWord ++ tailWord_5477171).sum := by decide
  have hdescent : baseEnd_5477171 < baseStart_5477171 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477172 : List Nat := [2, 5, 1, 1, 3, 1, 1, 2, 3, 2, 2]
def baseStart_5477172 : Nat := 118140960795 + 5477172 * 2 ^ 59
def prefixEnd_5477172 : Nat := 4983230072969 + 3 ^ 40 * 5477172 * 2
def baseEnd_5477172 : Nat := 2812421863347749773060951

theorem tailTrace_5477172 : CollatzResearch.WordTrace tailWord_5477172 prefixEnd_5477172 2812421863347749773060951 := by
  unfold tailWord_5477172
  simp only [CollatzResearch.WordTrace]
  refine ⟨99884437256574372674800885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133179249675432496899734513 99884437256574372674800885)
  ·
    refine ⟨9364165992803847438262583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99884437256574372674800885 9364165992803847438262583)
    ·
      refine ⟨14046248989205771157393875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9364165992803847438262583 14046248989205771157393875)
      ·
        refine ⟨21069373483808656736090813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14046248989205771157393875 21069373483808656736090813)
        ·
          refine ⟨7901015056428246276034055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21069373483808656736090813 7901015056428246276034055)
          ·
            refine ⟨11851522584642369414051083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7901015056428246276034055 11851522584642369414051083)
            ·
              refine ⟨17777283876963554121076625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11851522584642369414051083 17777283876963554121076625)
              ·
                refine ⟨13332962907722665590807469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17777283876963554121076625 13332962907722665590807469)
                ·
                  refine ⟨4999861090395999596552801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13332962907722665590807469 4999861090395999596552801)
                  ·
                    refine ⟨3749895817796999697414601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4999861090395999596552801 3749895817796999697414601)
                    ·
                      refine ⟨2812421863347749773060951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3749895817796999697414601 2812421863347749773060951)
                      ·
                        rfl

theorem cell23_5477172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_5477172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477172 prefixEnd_5477172 := by exact prefixLift 5477172
  have htrace : WordTrace (prefixWord ++ tailWord_5477172) baseStart_5477172 baseEnd_5477172 := by
    simpa [prefixWord, tailWord_5477172, baseEnd_5477172] using wordTrace_append hprefix tailTrace_5477172
  have hstable : (prefixWord ++ tailWord_5477172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477172).length < 2 ^ (prefixWord ++ tailWord_5477172).sum := by decide
  have hdescent : baseEnd_5477172 < baseStart_5477172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477194 : List Nat := [3, 1, 2, 1, 1, 1, 2, 2, 1, 5, 4]
def baseStart_5477194 : Nat := 118140960795 + 5477194 * 2 ^ 59
def prefixEnd_5477194 : Nat := 4983230072969 + 3 ^ 40 * 5477194 * 2
def baseEnd_5477194 : Nat := 2812433159922148686985849

theorem tailTrace_5477194 : CollatzResearch.WordTrace tailWord_5477194 prefixEnd_5477194 2812433159922148686985849 := by
  unfold tailWord_5477194
  simp only [CollatzResearch.WordTrace]
  refine ⟨49942419229767260776725659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133179784612712695404601757 49942419229767260776725659)
  ·
    refine ⟨74913628844650891165088489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49942419229767260776725659 74913628844650891165088489)
    ·
      refine ⟨56185221633488168373816367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74913628844650891165088489 56185221633488168373816367)
      ·
        refine ⟨84277832450232252560724551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56185221633488168373816367 84277832450232252560724551)
        ·
          refine ⟨126416748675348378841086827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84277832450232252560724551 126416748675348378841086827)
          ·
            refine ⟨189625123013022568261630241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126416748675348378841086827 189625123013022568261630241)
            ·
              refine ⟨142218842259766926196222681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189625123013022568261630241 142218842259766926196222681)
              ·
                refine ⟨106664131694825194647167011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142218842259766926196222681 106664131694825194647167011)
                ·
                  refine ⟨159996197542237791970750517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106664131694825194647167011 159996197542237791970750517)
                  ·
                    refine ⟨14999643519584792997257861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 159996197542237791970750517 14999643519584792997257861)
                    ·
                      refine ⟨2812433159922148686985849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14999643519584792997257861 2812433159922148686985849)
                      ·
                        rfl

theorem cell23_5477194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 2, 1, 5, 4].length) (baseStart_5477194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477194 prefixEnd_5477194 := by exact prefixLift 5477194
  have htrace : WordTrace (prefixWord ++ tailWord_5477194) baseStart_5477194 baseEnd_5477194 := by
    simpa [prefixWord, tailWord_5477194, baseEnd_5477194] using wordTrace_append hprefix tailTrace_5477194
  have hstable : (prefixWord ++ tailWord_5477194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477194).length < 2 ^ (prefixWord ++ tailWord_5477194).sum := by decide
  have hdescent : baseEnd_5477194 < baseStart_5477194 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477279 : List Nat := [1, 1, 2, 5, 2, 3, 2, 1, 2, 2, 2]
def baseStart_5477279 : Nat := 118140960795 + 5477279 * 2 ^ 59
def prefixEnd_5477279 : Nat := 4983230072969 + 3 ^ 40 * 5477279 * 2
def baseEnd_5477279 : Nat := 2812476805777780854422959

theorem tailTrace_5477279 : CollatzResearch.WordTrace tailWord_5477279 prefixEnd_5477279 2812476805777780854422959 := by
  unfold tailWord_5477279
  simp only [CollatzResearch.WordTrace]
  refine ⟨199772777123761102623746891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133181851415840735082497927 199772777123761102623746891)
  ·
    refine ⟨299659165685641653935620337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199772777123761102623746891 299659165685641653935620337)
    ·
      refine ⟨224744374264231240451715253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299659165685641653935620337 224744374264231240451715253)
      ·
        refine ⟨21069785087271678792348305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 224744374264231240451715253 21069785087271678792348305)
        ·
          refine ⟨15802338815453759094261229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21069785087271678792348305 15802338815453759094261229)
          ·
            refine ⟨5925877055795159660347961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15802338815453759094261229 5925877055795159660347961)
            ·
              refine ⟨4444407791846369745260971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5925877055795159660347961 4444407791846369745260971)
              ·
                refine ⟨6666611687769554617891457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4444407791846369745260971 6666611687769554617891457)
                ·
                  refine ⟨4999958765827165963418593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6666611687769554617891457 4999958765827165963418593)
                  ·
                    refine ⟨3749969074370374472563945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4999958765827165963418593 3749969074370374472563945)
                    ·
                      refine ⟨2812476805777780854422959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3749969074370374472563945 2812476805777780854422959)
                      ·
                        rfl

theorem cell23_5477279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 2, 1, 2, 2, 2].length) (baseStart_5477279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477279 prefixEnd_5477279 := by exact prefixLift 5477279
  have htrace : WordTrace (prefixWord ++ tailWord_5477279) baseStart_5477279 baseEnd_5477279 := by
    simpa [prefixWord, tailWord_5477279, baseEnd_5477279] using wordTrace_append hprefix tailTrace_5477279
  have hstable : (prefixWord ++ tailWord_5477279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477279).length < 2 ^ (prefixWord ++ tailWord_5477279).sum := by decide
  have hdescent : baseEnd_5477279 < baseStart_5477279 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477311 : List Nat := [1, 1, 2, 2, 2, 1, 2, 1, 7, 4]
def baseStart_5477311 : Nat := 118140960795 + 5477311 * 2 ^ 59
def prefixEnd_5477311 : Nat := 4983230072969 + 3 ^ 40 * 5477311 * 2
def baseEnd_5477311 : Nat := 937497745719574909740937

theorem tailTrace_5477311 : CollatzResearch.WordTrace tailWord_5477311 prefixEnd_5477311 937497745719574909740937 := by
  unfold tailWord_5477311
  simp only [CollatzResearch.WordTrace]
  refine ⟨199773944259645172088911787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133182629506430114725941191 199773944259645172088911787)
  ·
    refine ⟨299660916389467758133367681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199773944259645172088911787 299660916389467758133367681)
    ·
      refine ⟨224745687292100818600025761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299660916389467758133367681 224745687292100818600025761)
      ·
        refine ⟨168559265469075613950019321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224745687292100818600025761 168559265469075613950019321)
        ·
          refine ⟨126419449101806710462514491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168559265469075613950019321 126419449101806710462514491)
          ·
            refine ⟨189629173652710065693771737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126419449101806710462514491 189629173652710065693771737)
            ·
              refine ⟨142221880239532549270328803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189629173652710065693771737 142221880239532549270328803)
              ·
                refine ⟨213332820359298823905493205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142221880239532549270328803 213332820359298823905493205)
                ·
                  refine ⟨4999987977171066185284997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 213332820359298823905493205 4999987977171066185284997)
                  ·
                    refine ⟨937497745719574909740937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4999987977171066185284997 937497745719574909740937)
                    ·
                      rfl

theorem cell23_5477311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 7, 4].length) (baseStart_5477311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477311 prefixEnd_5477311 := by exact prefixLift 5477311
  have htrace : WordTrace (prefixWord ++ tailWord_5477311) baseStart_5477311 baseEnd_5477311 := by
    simpa [prefixWord, tailWord_5477311, baseEnd_5477311] using wordTrace_append hprefix tailTrace_5477311
  have hstable : (prefixWord ++ tailWord_5477311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477311).length < 2 ^ (prefixWord ++ tailWord_5477311).sum := by decide
  have hdescent : baseEnd_5477311 < baseStart_5477311 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477368 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 7, 1, 3]
def baseStart_5477368 : Nat := 118140960795 + 5477368 * 2 ^ 59
def prefixEnd_5477368 : Nat := 4983230072969 + 3 ^ 40 * 5477368 * 2
def baseEnd_5477368 : Nat := 2812522505556031006210049

theorem tailTrace_5477368 : CollatzResearch.WordTrace tailWord_5477368 prefixEnd_5477368 2812522505556031006210049 := by
  unfold tailWord_5477368
  simp only [CollatzResearch.WordTrace]
  refine ⟨99888011610219335411868379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133184015480292447215824505 99888011610219335411868379)
  ·
    refine ⟨149832017415329003117802569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99888011610219335411868379 149832017415329003117802569)
    ·
      refine ⟨112374013061496752338351927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149832017415329003117802569 112374013061496752338351927)
      ·
        refine ⟨168561019592245128507527891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112374013061496752338351927 168561019592245128507527891)
        ·
          refine ⟨252841529388367692761291837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168561019592245128507527891 252841529388367692761291837)
          ·
            refine ⟨94815573520637884785484439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252841529388367692761291837 94815573520637884785484439)
            ·
              refine ⟨142223360280956827178226659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94815573520637884785484439 142223360280956827178226659)
              ·
                refine ⟨213335040421435240767339989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142223360280956827178226659 213335040421435240767339989)
                ·
                  refine ⟨5000040009877388455484531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 213335040421435240767339989 5000040009877388455484531)
                  ·
                    refine ⟨7500060014816082683226797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5000040009877388455484531 7500060014816082683226797)
                    ·
                      refine ⟨2812522505556031006210049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7500060014816082683226797 2812522505556031006210049)
                      ·
                        rfl

theorem cell23_5477368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 7, 1, 3].length) (baseStart_5477368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477368 prefixEnd_5477368 := by exact prefixLift 5477368
  have htrace : WordTrace (prefixWord ++ tailWord_5477368) baseStart_5477368 baseEnd_5477368 := by
    simpa [prefixWord, tailWord_5477368, baseEnd_5477368] using wordTrace_append hprefix tailTrace_5477368
  have hstable : (prefixWord ++ tailWord_5477368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477368).length < 2 ^ (prefixWord ++ tailWord_5477368).sum := by decide
  have hdescent : baseEnd_5477368 < baseStart_5477368 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477491 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 5, 8]
def baseStart_5477491 : Nat := 118140960795 + 5477491 * 2 ^ 59
def prefixEnd_5477491 : Nat := 4983230072969 + 3 ^ 40 * 5477491 * 2
def baseEnd_5477491 : Nat := 937528554558844674990661

theorem tailTrace_5477491 : CollatzResearch.WordTrace tailWord_5477491 prefixEnd_5477491 937528554558844674990661 := by
  unfold tailWord_5477491
  simp only [CollatzResearch.WordTrace]
  refine ⟨199780509398993062830464327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133187006265995375220309551 199780509398993062830464327)
  ·
    refine ⟨299670764098489594245696491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199780509398993062830464327 299670764098489594245696491)
    ·
      refine ⟨449506146147734391368544737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299670764098489594245696491 449506146147734391368544737)
      ·
        refine ⟨337129609610800793526408553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 449506146147734391368544737 337129609610800793526408553)
        ·
          refine ⟨252847207208100595144806415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337129609610800793526408553 252847207208100595144806415)
          ·
            refine ⟨379270810812150892717209623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252847207208100595144806415 379270810812150892717209623)
            ·
              refine ⟨568906216218226339075814435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379270810812150892717209623 568906216218226339075814435)
              ·
                refine ⟨853359324327339508613721653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 568906216218226339075814435 853359324327339508613721653)
                ·
                  refine ⟨80002436655688078932536405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 853359324327339508613721653 80002436655688078932536405)
                  ·
                    refine ⟨937528554558844674990661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80002436655688078932536405 937528554558844674990661)
                    ·
                      rfl

theorem cell23_5477491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 5, 8].length) (baseStart_5477491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477491 prefixEnd_5477491 := by exact prefixLift 5477491
  have htrace : WordTrace (prefixWord ++ tailWord_5477491) baseStart_5477491 baseEnd_5477491 := by
    simpa [prefixWord, tailWord_5477491, baseEnd_5477491] using wordTrace_append hprefix tailTrace_5477491
  have hstable : (prefixWord ++ tailWord_5477491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477491).length < 2 ^ (prefixWord ++ tailWord_5477491).sum := by decide
  have hdescent : baseEnd_5477491 < baseStart_5477491 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477493 : List Nat := [1, 3, 4, 3, 1, 1, 1, 4, 1, 2, 2]
def baseStart_5477493 : Nat := 118140960795 + 5477493 * 2 ^ 59
def prefixEnd_5477493 : Nat := 4983230072969 + 3 ^ 40 * 5477493 * 2
def baseEnd_5477493 : Nat := 2812586690637843017146975

theorem tailTrace_5477493 : CollatzResearch.WordTrace tailWord_5477493 prefixEnd_5477493 2812586690637843017146975 := by
  unfold tailWord_5477493
  simp only [CollatzResearch.WordTrace]
  refine ⟨199780582344985817172037133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133187054896657211448024755 199780582344985817172037133)
  ·
    refine ⟨74917718379369681439513925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199780582344985817172037133 74917718379369681439513925)
    ·
      refine ⟨14047072196131815269908861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74917718379369681439513925 14047072196131815269908861)
      ·
        refine ⟨5267652073549430726215823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14047072196131815269908861 5267652073549430726215823)
        ·
          refine ⟨7901478110324146089323735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5267652073549430726215823 7901478110324146089323735)
          ·
            refine ⟨11852217165486219133985603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7901478110324146089323735 11852217165486219133985603)
            ·
              refine ⟨17778325748229328700978405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11852217165486219133985603 17778325748229328700978405)
              ·
                refine ⟨3333436077792999131433451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17778325748229328700978405 3333436077792999131433451)
                ·
                  refine ⟨5000154116689498697150177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3333436077792999131433451 5000154116689498697150177)
                  ·
                    refine ⟨3750115587517124022862633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5000154116689498697150177 3750115587517124022862633)
                    ·
                      refine ⟨2812586690637843017146975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3750115587517124022862633 2812586690637843017146975)
                      ·
                        rfl

theorem cell23_5477493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_5477493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477493 prefixEnd_5477493 := by exact prefixLift 5477493
  have htrace : WordTrace (prefixWord ++ tailWord_5477493) baseStart_5477493 baseEnd_5477493 := by
    simpa [prefixWord, tailWord_5477493, baseEnd_5477493] using wordTrace_append hprefix tailTrace_5477493
  have hstable : (prefixWord ++ tailWord_5477493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477493).length < 2 ^ (prefixWord ++ tailWord_5477493).sum := by decide
  have hdescent : baseEnd_5477493 < baseStart_5477493 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477508 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 1, 8]
def baseStart_5477508 : Nat := 118140960795 + 5477508 * 2 ^ 59
def prefixEnd_5477508 : Nat := 4983230072969 + 3 ^ 40 * 5477508 * 2
def baseEnd_5477508 : Nat := 937531464282553486153135

theorem tailTrace_5477508 : CollatzResearch.WordTrace tailWord_5477508 prefixEnd_5477508 937531464282553486153135 := by
  unfold tailWord_5477508
  simp only [CollatzResearch.WordTrace]
  refine ⟨99890564719965737366916589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133187419626620983155888785 99890564719965737366916589)
  ·
    refine ⟨37458961769987151512593721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99890564719965737366916589 37458961769987151512593721)
    ·
      refine ⟨28094221327490363634445291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37458961769987151512593721 28094221327490363634445291)
      ·
        refine ⟨42141331991235545451667937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28094221327490363634445291 42141331991235545451667937)
        ·
          refine ⟨31605998993426659088750953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42141331991235545451667937 31605998993426659088750953)
          ·
            refine ⟨23704499245069994316563215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31605998993426659088750953 23704499245069994316563215)
            ·
              refine ⟨35556748867604991474844823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23704499245069994316563215 35556748867604991474844823)
              ·
                refine ⟨53335123301407487212267235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35556748867604991474844823 53335123301407487212267235)
                ·
                  refine ⟨80002684952111230818400853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53335123301407487212267235 80002684952111230818400853)
                  ·
                    refine ⟨937531464282553486153135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80002684952111230818400853 937531464282553486153135)
                    ·
                      rfl

theorem cell23_5477508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_5477508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477508 prefixEnd_5477508 := by exact prefixLift 5477508
  have htrace : WordTrace (prefixWord ++ tailWord_5477508) baseStart_5477508 baseEnd_5477508 := by
    simpa [prefixWord, tailWord_5477508, baseEnd_5477508] using wordTrace_append hprefix tailTrace_5477508
  have hstable : (prefixWord ++ tailWord_5477508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477508).length < 2 ^ (prefixWord ++ tailWord_5477508).sum := by decide
  have hdescent : baseEnd_5477508 < baseStart_5477508 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477532 : List Nat := [2, 2, 3, 2, 1, 2, 2, 2, 1, 4, 2]
def baseStart_5477532 : Nat := 118140960795 + 5477532 * 2 ^ 59
def prefixEnd_5477532 : Nat := 4983230072969 + 3 ^ 40 * 5477532 * 2
def baseEnd_5477532 : Nat := 2812606716383368364559295

theorem tailTrace_5477532 : CollatzResearch.WordTrace tailWord_5477532 prefixEnd_5477532 2812606716383368364559295 := by
  unfold tailWord_5477532
  simp only [CollatzResearch.WordTrace]
  refine ⟨99891002395922263416353425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133188003194563017888471233 99891002395922263416353425)
  ·
    refine ⟨74918251796941697562265069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99891002395922263416353425 74918251796941697562265069)
    ·
      refine ⟨28094344423853136585849401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74918251796941697562265069 28094344423853136585849401)
      ·
        refine ⟨21070758317889852439387051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28094344423853136585849401 21070758317889852439387051)
        ·
          refine ⟨31606137476834778659080577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21070758317889852439387051 31606137476834778659080577)
          ·
            refine ⟨23704603107626083994310433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31606137476834778659080577 23704603107626083994310433)
            ·
              refine ⟨17778452330719562995732825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23704603107626083994310433 17778452330719562995732825)
              ·
                refine ⟨13333839248039672246799619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17778452330719562995732825 13333839248039672246799619)
                ·
                  refine ⟨20000758872059508370199429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13333839248039672246799619 20000758872059508370199429)
                  ·
                    refine ⟨3750142288511157819412393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20000758872059508370199429 3750142288511157819412393)
                    ·
                      refine ⟨2812606716383368364559295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3750142288511157819412393 2812606716383368364559295)
                      ·
                        rfl

theorem cell23_5477532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 2, 1, 4, 2].length) (baseStart_5477532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477532 prefixEnd_5477532 := by exact prefixLift 5477532
  have htrace : WordTrace (prefixWord ++ tailWord_5477532) baseStart_5477532 baseEnd_5477532 := by
    simpa [prefixWord, tailWord_5477532, baseEnd_5477532] using wordTrace_append hprefix tailTrace_5477532
  have hstable : (prefixWord ++ tailWord_5477532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477532).length < 2 ^ (prefixWord ++ tailWord_5477532).sum := by decide
  have hdescent : baseEnd_5477532 < baseStart_5477532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477555 : List Nat := [1, 1, 1, 2, 3, 2, 4, 4, 5]
def baseStart_5477555 : Nat := 118140960795 + 5477555 * 2 ^ 59
def prefixEnd_5477555 : Nat := 4983230072969 + 3 ^ 40 * 5477555 * 2
def baseEnd_5477555 : Nat := 312513169604269086063521

theorem tailTrace_5477555 : CollatzResearch.WordTrace tailWord_5477555 prefixEnd_5477555 312513169604269086063521 := by
  unfold tailWord_5477555
  simp only [CollatzResearch.WordTrace]
  refine ⟨199782843670761201760794119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133188562447174134507196079 199782843670761201760794119)
  ·
    refine ⟨299674265506141802641191179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199782843670761201760794119 299674265506141802641191179)
    ·
      refine ⟨449511398259212703961786769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299674265506141802641191179 449511398259212703961786769)
      ·
        refine ⟨337133548694409527971340077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 449511398259212703961786769 337133548694409527971340077)
        ·
          refine ⟨126425080760403572989252529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 337133548694409527971340077 126425080760403572989252529)
          ·
            refine ⟨94818810570302679741939397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126425080760403572989252529 94818810570302679741939397)
            ·
              refine ⟨17778526981931752451613637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94818810570302679741939397 17778526981931752451613637)
              ·
                refine ⟨3333473809112203584677557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17778526981931752451613637 3333473809112203584677557)
                ·
                  refine ⟨312513169604269086063521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3333473809112203584677557 312513169604269086063521)
                  ·
                    rfl

theorem cell23_5477555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 5].length) (baseStart_5477555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477555 prefixEnd_5477555 := by exact prefixLift 5477555
  have htrace : WordTrace (prefixWord ++ tailWord_5477555) baseStart_5477555 baseEnd_5477555 := by
    simpa [prefixWord, tailWord_5477555, baseEnd_5477555] using wordTrace_append hprefix tailTrace_5477555
  have hstable : (prefixWord ++ tailWord_5477555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477555).length < 2 ^ (prefixWord ++ tailWord_5477555).sum := by decide
  have hdescent : baseEnd_5477555 < baseStart_5477555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477565 : List Nat := [1, 4, 1, 2, 1, 1, 4, 1, 2, 3, 3]
def baseStart_5477565 : Nat := 118140960795 + 5477565 * 2 ^ 59
def prefixEnd_5477565 : Nat := 4983230072969 + 3 ^ 40 * 5477565 * 2
def baseEnd_5477565 : Nat := 2812623661244966735446643

theorem tailTrace_5477565 : CollatzResearch.WordTrace tailWord_5477565 prefixEnd_5477565 2812623661244966735446643 := by
  unfold tailWord_5477565
  simp only [CollatzResearch.WordTrace]
  refine ⟨199783208400724973468658149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133188805600483315645772099 199783208400724973468658149)
  ·
    refine ⟨37459351575135932525373403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199783208400724973468658149 37459351575135932525373403)
    ·
      refine ⟨56189027362703898788060105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37459351575135932525373403 56189027362703898788060105)
      ·
        refine ⟨42141770522027924091045079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56189027362703898788060105 42141770522027924091045079)
        ·
          refine ⟨63212655783041886136567619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42141770522027924091045079 63212655783041886136567619)
          ·
            refine ⟨94818983674562829204851429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63212655783041886136567619 94818983674562829204851429)
            ·
              refine ⟨17778559438980530475909643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94818983674562829204851429 17778559438980530475909643)
              ·
                refine ⟨26667839158470795713864465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17778559438980530475909643 26667839158470795713864465)
                ·
                  refine ⟨20000879368853096785398349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26667839158470795713864465 20000879368853096785398349)
                  ·
                    refine ⟨7500329763319911294524381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20000879368853096785398349 7500329763319911294524381)
                    ·
                      refine ⟨2812623661244966735446643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7500329763319911294524381 2812623661244966735446643)
                      ·
                        rfl

theorem cell23_5477565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 1, 2, 3, 3].length) (baseStart_5477565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477565 prefixEnd_5477565 := by exact prefixLift 5477565
  have htrace : WordTrace (prefixWord ++ tailWord_5477565) baseStart_5477565 baseEnd_5477565 := by
    simpa [prefixWord, tailWord_5477565, baseEnd_5477565] using wordTrace_append hprefix tailTrace_5477565
  have hstable : (prefixWord ++ tailWord_5477565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477565).length < 2 ^ (prefixWord ++ tailWord_5477565).sum := by decide
  have hdescent : baseEnd_5477565 < baseStart_5477565 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477575 : List Nat := [1, 1, 4, 1, 1, 1, 1, 4, 2, 5, 2]
def baseStart_5477575 : Nat := 118140960795 + 5477575 * 2 ^ 59
def prefixEnd_5477575 : Nat := 4983230072969 + 3 ^ 40 * 5477575 * 2
def baseEnd_5477575 : Nat := 2812628796051511696321597

theorem tailTrace_5477575 : CollatzResearch.WordTrace tailWord_5477575 prefixEnd_5477575 2812628796051511696321597 := by
  unfold tailWord_5477575
  simp only [CollatzResearch.WordTrace]
  refine ⟨199783573130688745176522179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133189048753792496784348119 199783573130688745176522179)
  ·
    refine ⟨299675359696033117764783269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199783573130688745176522179 299675359696033117764783269)
    ·
      refine ⟨56189129943006209580896863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 299675359696033117764783269 56189129943006209580896863)
      ·
        refine ⟨84283694914509314371345295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56189129943006209580896863 84283694914509314371345295)
        ·
          refine ⟨126425542371763971557017943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84283694914509314371345295 126425542371763971557017943)
          ·
            refine ⟨189638313557645957335526915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126425542371763971557017943 189638313557645957335526915)
            ·
              refine ⟨284457470336468936003290373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189638313557645957335526915 284457470336468936003290373)
              ·
                refine ⟨53335775688087925500616945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 284457470336468936003290373 53335775688087925500616945)
                ·
                  refine ⟨40001831766065944125462709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53335775688087925500616945 40001831766065944125462709)
                  ·
                    refine ⟨3750171728068682261762129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40001831766065944125462709 3750171728068682261762129)
                    ·
                      refine ⟨2812628796051511696321597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3750171728068682261762129 2812628796051511696321597)
                      ·
                        rfl

theorem cell23_5477575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 4, 2, 5, 2].length) (baseStart_5477575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477575 prefixEnd_5477575 := by exact prefixLift 5477575
  have htrace : WordTrace (prefixWord ++ tailWord_5477575) baseStart_5477575 baseEnd_5477575 := by
    simpa [prefixWord, tailWord_5477575, baseEnd_5477575] using wordTrace_append hprefix tailTrace_5477575
  have hstable : (prefixWord ++ tailWord_5477575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477575).length < 2 ^ (prefixWord ++ tailWord_5477575).sum := by decide
  have hdescent : baseEnd_5477575 < baseStart_5477575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477589 : List Nat := [1, 3, 2, 4, 1, 3, 1, 3, 5]
def baseStart_5477589 : Nat := 118140960795 + 5477589 * 2 ^ 59
def prefixEnd_5477589 : Nat := 4983230072969 + 3 ^ 40 * 5477589 * 2
def baseEnd_5477589 : Nat := 312515109420074960171837

theorem tailTrace_5477589 : CollatzResearch.WordTrace tailWord_5477589 prefixEnd_5477589 312515109420074960171837 := by
  unfold tailWord_5477589
  simp only [CollatzResearch.WordTrace]
  refine ⟨199784083752638025567531821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133189389168425350378354547 199784083752638025567531821)
  ·
    refine ⟨74919031407239259587824433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199784083752638025567531821 74919031407239259587824433)
    ·
      refine ⟨56189273555429444690868325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74919031407239259587824433 56189273555429444690868325)
      ·
        refine ⟨10535488791643020879537811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56189273555429444690868325 10535488791643020879537811)
        ·
          refine ⟨15803233187464531319306717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10535488791643020879537811 15803233187464531319306717)
          ·
            refine ⟨5926212445299199244740019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15803233187464531319306717 5926212445299199244740019)
            ·
              refine ⟨8889318667948798867110029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5926212445299199244740019 8889318667948798867110029)
              ·
                refine ⟨3333494500480799575166261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8889318667948798867110029 3333494500480799575166261)
                ·
                  refine ⟨312515109420074960171837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3333494500480799575166261 312515109420074960171837)
                  ·
                    rfl

theorem cell23_5477589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 3, 5].length) (baseStart_5477589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477589 prefixEnd_5477589 := by exact prefixLift 5477589
  have htrace : WordTrace (prefixWord ++ tailWord_5477589) baseStart_5477589 baseEnd_5477589 := by
    simpa [prefixWord, tailWord_5477589, baseEnd_5477589] using wordTrace_append hprefix tailTrace_5477589
  have hstable : (prefixWord ++ tailWord_5477589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477589).length < 2 ^ (prefixWord ++ tailWord_5477589).sum := by decide
  have hdescent : baseEnd_5477589 < baseStart_5477589 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477622 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2]
def baseStart_5477622 : Nat := 118140960795 + 5477622 * 2 ^ 59
def prefixEnd_5477622 : Nat := 4983230072969 + 3 ^ 40 * 5477622 * 2
def baseEnd_5477622 : Nat := 2812652929642273012433881

theorem tailTrace_5477622 : CollatzResearch.WordTrace tailWord_5477622 prefixEnd_5477622 2812652929642273012433881 := by
  unfold tailWord_5477622
  simp only [CollatzResearch.WordTrace]
  refine ⟨12486580460094904512717695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 133190191574345648135655413 12486580460094904512717695)
  ·
    refine ⟨18729870690142356769076543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12486580460094904512717695 18729870690142356769076543)
    ·
      refine ⟨28094806035213535153614815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18729870690142356769076543 28094806035213535153614815)
      ·
        refine ⟨42142209052820302730422223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28094806035213535153614815 42142209052820302730422223)
        ·
          refine ⟨63213313579230454095633335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42142209052820302730422223 63213313579230454095633335)
          ·
            refine ⟨94819970368845681143450003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63213313579230454095633335 94819970368845681143450003)
            ·
              refine ⟨142229955553268521715175005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94819970368845681143450003 142229955553268521715175005)
              ·
                refine ⟨53336233332475695643190627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 142229955553268521715175005 53336233332475695643190627)
                ·
                  refine ⟨80004349998713543464785941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53336233332475695643190627 80004349998713543464785941)
                  ·
                    refine ⟨3750203906189697349911841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 80004349998713543464785941 3750203906189697349911841)
                    ·
                      refine ⟨2812652929642273012433881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3750203906189697349911841 2812652929642273012433881)
                      ·
                        rfl

theorem cell23_5477622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_5477622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477622 prefixEnd_5477622 := by exact prefixLift 5477622
  have htrace : WordTrace (prefixWord ++ tailWord_5477622) baseStart_5477622 baseEnd_5477622 := by
    simpa [prefixWord, tailWord_5477622, baseEnd_5477622] using wordTrace_append hprefix tailTrace_5477622
  have hstable : (prefixWord ++ tailWord_5477622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477622).length < 2 ^ (prefixWord ++ tailWord_5477622).sum := by decide
  have hdescent : baseEnd_5477622 < baseStart_5477622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477625 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 4, 2, 3]
def baseStart_5477625 : Nat := 118140960795 + 5477625 * 2 ^ 59
def prefixEnd_5477625 : Nat := 4983230072969 + 3 ^ 40 * 5477625 * 2
def baseEnd_5477625 : Nat := 2812654470084236500696367

theorem tailTrace_5477625 : CollatzResearch.WordTrace tailWord_5477625 prefixEnd_5477625 2812654470084236500696367 := by
  unfold tailWord_5477625
  simp only [CollatzResearch.WordTrace]
  refine ⟨199785396780507603715842329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133190264520338402477228219 199785396780507603715842329)
  ·
    refine ⟨149839047585380702786881747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199785396780507603715842329 149839047585380702786881747)
    ·
      refine ⟨224758571378071054180322621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149839047585380702786881747 224758571378071054180322621)
      ·
        refine ⟨84284464266776645317620983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224758571378071054180322621 84284464266776645317620983)
        ·
          refine ⟨126426696400164967976431475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84284464266776645317620983 126426696400164967976431475)
          ·
            refine ⟨189640044600247451964647213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126426696400164967976431475 189640044600247451964647213)
            ·
              refine ⟨71115016725092794486742705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189640044600247451964647213 71115016725092794486742705)
              ·
                refine ⟨53336262543819595865057029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71115016725092794486742705 53336262543819595865057029)
                ·
                  refine ⟨10000549226966174224698193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53336262543819595865057029 10000549226966174224698193)
                  ·
                    refine ⟨7500411920224630668523645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10000549226966174224698193 7500411920224630668523645)
                    ·
                      refine ⟨2812654470084236500696367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7500411920224630668523645 2812654470084236500696367)
                      ·
                        rfl

theorem cell23_5477625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 4, 2, 3].length) (baseStart_5477625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477625 prefixEnd_5477625 := by exact prefixLift 5477625
  have htrace : WordTrace (prefixWord ++ tailWord_5477625) baseStart_5477625 baseEnd_5477625 := by
    simpa [prefixWord, tailWord_5477625, baseEnd_5477625] using wordTrace_append hprefix tailTrace_5477625
  have hstable : (prefixWord ++ tailWord_5477625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477625).length < 2 ^ (prefixWord ++ tailWord_5477625).sum := by decide
  have hdescent : baseEnd_5477625 < baseStart_5477625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477666 : List Nat := [3, 3, 1, 1, 4, 1, 1, 4, 1, 4]
def baseStart_5477666 : Nat := 118140960795 + 5477666 * 2 ^ 59
def prefixEnd_5477666 : Nat := 4983230072969 + 3 ^ 40 * 5477666 * 2
def baseEnd_5477666 : Nat := 937558507597023613427893

theorem tailTrace_5477666 : CollatzResearch.WordTrace tailWord_5477666 prefixEnd_5477666 937558507597023613427893 := by
  unfold tailWord_5477666
  simp only [CollatzResearch.WordTrace]
  refine ⟨49946723043339766929521213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133191261448906045145389901 49946723043339766929521213)
  ·
    refine ⟨18730021141252412598570455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49946723043339766929521213 18730021141252412598570455)
    ·
      refine ⟨28095031711878618897855683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18730021141252412598570455 28095031711878618897855683)
      ·
        refine ⟨42142547567817928346783525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28095031711878618897855683 42142547567817928346783525)
        ·
          refine ⟨7901727668965861565021911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42142547567817928346783525 7901727668965861565021911)
          ·
            refine ⟨11852591503448792347532867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7901727668965861565021911 11852591503448792347532867)
            ·
              refine ⟨17778887255173188521299301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11852591503448792347532867 17778887255173188521299301)
              ·
                refine ⟨3333541360344972847743619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17778887255173188521299301 3333541360344972847743619)
                ·
                  refine ⟨5000312040517459271615429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3333541360344972847743619 5000312040517459271615429)
                  ·
                    refine ⟨937558507597023613427893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5000312040517459271615429 937558507597023613427893)
                    ·
                      rfl

theorem cell23_5477666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_5477666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477666 prefixEnd_5477666 := by exact prefixLift 5477666
  have htrace : WordTrace (prefixWord ++ tailWord_5477666) baseStart_5477666 baseEnd_5477666 := by
    simpa [prefixWord, tailWord_5477666, baseEnd_5477666] using wordTrace_append hprefix tailTrace_5477666
  have hstable : (prefixWord ++ tailWord_5477666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477666).length < 2 ^ (prefixWord ++ tailWord_5477666).sum := by decide
  have hdescent : baseEnd_5477666 < baseStart_5477666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477693 : List Nat := [1, 4, 1, 5, 2, 1, 1, 1, 2, 2, 3]
def baseStart_5477693 : Nat := 118140960795 + 5477693 * 2 ^ 59
def prefixEnd_5477693 : Nat := 4983230072969 + 3 ^ 40 * 5477693 * 2
def baseEnd_5477693 : Nat := 2812689386768742234646055

theorem tailTrace_5477693 : CollatzResearch.WordTrace tailWord_5477693 prefixEnd_5477693 2812689386768742234646055 := by
  unfold tailWord_5477693
  simp only [CollatzResearch.WordTrace]
  refine ⟨199787876944261251329317733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133191917962840834219545155 199787876944261251329317733)
  ·
    refine ⟨37460226927048984624247075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199787876944261251329317733 37460226927048984624247075)
    ·
      refine ⟨56190340390573476936370613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37460226927048984624247075 56190340390573476936370613)
      ·
        refine ⟨5267844411616263462784745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56190340390573476936370613 5267844411616263462784745)
        ·
          refine ⟨3950883308712197597088559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5267844411616263462784745 3950883308712197597088559)
          ·
            refine ⟨5926324963068296395632839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3950883308712197597088559 5926324963068296395632839)
            ·
              refine ⟨8889487444602444593449259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5926324963068296395632839 8889487444602444593449259)
              ·
                refine ⟨13334231166903666890173889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8889487444602444593449259 13334231166903666890173889)
                ·
                  refine ⟨10000673375177750167630417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13334231166903666890173889 10000673375177750167630417)
                  ·
                    refine ⟨7500505031383312625722813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10000673375177750167630417 7500505031383312625722813)
                    ·
                      refine ⟨2812689386768742234646055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7500505031383312625722813 2812689386768742234646055)
                      ·
                        rfl

theorem cell23_5477693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_5477693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477693 prefixEnd_5477693 := by exact prefixLift 5477693
  have htrace : WordTrace (prefixWord ++ tailWord_5477693) baseStart_5477693 baseEnd_5477693 := by
    simpa [prefixWord, tailWord_5477693, baseEnd_5477693] using wordTrace_append hprefix tailTrace_5477693
  have hstable : (prefixWord ++ tailWord_5477693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477693).length < 2 ^ (prefixWord ++ tailWord_5477693).sum := by decide
  have hdescent : baseEnd_5477693 < baseStart_5477693 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477705 : List Nat := [1, 2, 1, 1, 2, 3, 4, 2, 1, 6]
def baseStart_5477705 : Nat := 118140960795 + 5477705 * 2 ^ 59
def prefixEnd_5477705 : Nat := 4983230072969 + 3 ^ 40 * 5477705 * 2
def baseEnd_5477705 : Nat := 937565182845532062565333

theorem tailTrace_5477705 : CollatzResearch.WordTrace tailWord_5477705 prefixEnd_5477705 937565182845532062565333 := by
  unfold tailWord_5477705
  simp only [CollatzResearch.WordTrace]
  refine ⟨199788314620217777378754569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133192209746811851585836379 199788314620217777378754569)
  ·
    refine ⟨149841235965163333034065927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199788314620217777378754569 149841235965163333034065927)
    ·
      refine ⟨224761853947744999551098891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149841235965163333034065927 224761853947744999551098891)
      ·
        refine ⟨337142780921617499326648337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224761853947744999551098891 337142780921617499326648337)
        ·
          refine ⟨252857085691213124494986253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337142780921617499326648337 252857085691213124494986253)
          ·
            refine ⟨94821407134204921685619845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252857085691213124494986253 94821407134204921685619845)
            ·
              refine ⟨17779013837663422816053721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94821407134204921685619845 17779013837663422816053721)
              ·
                refine ⟨13334260378247567112040291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17779013837663422816053721 13334260378247567112040291)
                ·
                  refine ⟨20001390567371350668060437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13334260378247567112040291 20001390567371350668060437)
                  ·
                    refine ⟨937565182845532062565333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20001390567371350668060437 937565182845532062565333)
                    ·
                      rfl

theorem cell23_5477705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 1, 6].length) (baseStart_5477705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477705 prefixEnd_5477705 := by exact prefixLift 5477705
  have htrace : WordTrace (prefixWord ++ tailWord_5477705) baseStart_5477705 baseEnd_5477705 := by
    simpa [prefixWord, tailWord_5477705, baseEnd_5477705] using wordTrace_append hprefix tailTrace_5477705
  have hstable : (prefixWord ++ tailWord_5477705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477705).length < 2 ^ (prefixWord ++ tailWord_5477705).sum := by decide
  have hdescent : baseEnd_5477705 < baseStart_5477705 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477712 : List Nat := [2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 4]
def baseStart_5477712 : Nat := 118140960795 + 5477712 * 2 ^ 59
def prefixEnd_5477712 : Nat := 4983230072969 + 3 ^ 40 * 5477712 * 2
def baseEnd_5477712 : Nat := 2812699142901177660308467

theorem tailTrace_5477712 : CollatzResearch.WordTrace tailWord_5477712 prefixEnd_5477712 2812699142901177660308467 := by
  unfold tailWord_5477712
  simp only [CollatzResearch.WordTrace]
  refine ⟨99894284965596208787129695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133192379954128278382839593 99894284965596208787129695)
  ·
    refine ⟨149841427448394313180694543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99894284965596208787129695 149841427448394313180694543)
    ·
      refine ⟨224762141172591469771041815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149841427448394313180694543 224762141172591469771041815)
      ·
        refine ⟨337143211758887204656562723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224762141172591469771041815 337143211758887204656562723)
        ·
          refine ⟨505714817638330806984844085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337143211758887204656562723 505714817638330806984844085)
          ·
            refine ⟨47410764153593513154829133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 505714817638330806984844085 47410764153593513154829133)
            ·
              refine ⟨17779036557597567433060925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47410764153593513154829133 17779036557597567433060925)
              ·
                refine ⟨6667138709099087787397847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17779036557597567433060925 6667138709099087787397847)
                ·
                  refine ⟨10000708063648631681096771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6667138709099087787397847 10000708063648631681096771)
                  ·
                    refine ⟨15001062095472947521645157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10000708063648631681096771 15001062095472947521645157)
                    ·
                      refine ⟨2812699142901177660308467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15001062095472947521645157 2812699142901177660308467)
                      ·
                        rfl

theorem cell23_5477712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 3, 1, 1, 4].length) (baseStart_5477712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477712 prefixEnd_5477712 := by exact prefixLift 5477712
  have htrace : WordTrace (prefixWord ++ tailWord_5477712) baseStart_5477712 baseEnd_5477712 := by
    simpa [prefixWord, tailWord_5477712, baseEnd_5477712] using wordTrace_append hprefix tailTrace_5477712
  have hstable : (prefixWord ++ tailWord_5477712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477712).length < 2 ^ (prefixWord ++ tailWord_5477712).sum := by decide
  have hdescent : baseEnd_5477712 < baseStart_5477712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477715 : List Nat := [1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 5]
def baseStart_5477715 : Nat := 118140960795 + 5477715 * 2 ^ 59
def prefixEnd_5477715 : Nat := 4983230072969 + 3 ^ 40 * 5477715 * 2
def baseEnd_5477715 : Nat := 2812700683343141148570953

theorem tailTrace_5477715 : CollatzResearch.WordTrace tailWord_5477715 prefixEnd_5477715 2812700683343141148570953 := by
  unfold tailWord_5477715
  simp only [CollatzResearch.WordTrace]
  refine ⟨199788679350181549086618599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133192452900121032724412399 199788679350181549086618599)
  ·
    refine ⟨299683019025272323629927899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199788679350181549086618599 299683019025272323629927899)
    ·
      refine ⟨449524528537908485444891849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299683019025272323629927899 449524528537908485444891849)
      ·
        refine ⟨337143396403431364083668887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 449524528537908485444891849 337143396403431364083668887)
        ·
          refine ⟨505715094605147046125503331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337143396403431364083668887 505715094605147046125503331)
          ·
            refine ⟨758572641907720569188254997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505715094605147046125503331 758572641907720569188254997)
            ·
              refine ⟨35558092589424401680699453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 758572641907720569188254997 35558092589424401680699453)
              ·
                refine ⟨13334284721034150630262295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35558092589424401680699453 13334284721034150630262295)
                ·
                  refine ⟨20001427081551225945393443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13334284721034150630262295 20001427081551225945393443)
                  ·
                    refine ⟨30002140622326838918090165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20001427081551225945393443 30002140622326838918090165)
                    ·
                      refine ⟨2812700683343141148570953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30002140622326838918090165 2812700683343141148570953)
                      ·
                        rfl

theorem cell23_5477715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 1, 5].length) (baseStart_5477715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477715 prefixEnd_5477715 := by exact prefixLift 5477715
  have htrace : WordTrace (prefixWord ++ tailWord_5477715) baseStart_5477715 baseEnd_5477715 := by
    simpa [prefixWord, tailWord_5477715, baseEnd_5477715] using wordTrace_append hprefix tailTrace_5477715
  have hstable : (prefixWord ++ tailWord_5477715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477715).length < 2 ^ (prefixWord ++ tailWord_5477715).sum := by decide
  have hdescent : baseEnd_5477715 < baseStart_5477715 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477732 : List Nat := [2, 3, 1, 1, 3, 3, 1, 2, 1, 1, 5]
def baseStart_5477732 : Nat := 118140960795 + 5477732 * 2 ^ 59
def prefixEnd_5477732 : Nat := 4983230072969 + 3 ^ 40 * 5477732 * 2
def baseEnd_5477732 : Nat := 2812709412514267582058375

theorem tailTrace_5477732 : CollatzResearch.WordTrace tailWord_5477732 prefixEnd_5477732 2812709412514267582058375 := by
  unfold tailWord_5477732
  simp only [CollatzResearch.WordTrace]
  refine ⟨99894649695559980494993725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133192866260746640659991633 99894649695559980494993725)
  ·
    refine ⟨37460493635834992685622647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99894649695559980494993725 37460493635834992685622647)
    ·
      refine ⟨56190740453752489028433971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37460493635834992685622647 56190740453752489028433971)
      ·
        refine ⟨84286110680628733542650957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56190740453752489028433971 84286110680628733542650957)
        ·
          refine ⟨31607291505235775078494109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84286110680628733542650957 31607291505235775078494109)
          ·
            refine ⟨11852734314463415654435291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31607291505235775078494109 11852734314463415654435291)
            ·
              refine ⟨17779101471695123481652937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11852734314463415654435291 17779101471695123481652937)
              ·
                refine ⟨13334326103771342611239703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17779101471695123481652937 13334326103771342611239703)
                ·
                  refine ⟨20001489155657013916859555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13334326103771342611239703 20001489155657013916859555)
                  ·
                    refine ⟨30002233733485520875289333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20001489155657013916859555 30002233733485520875289333)
                    ·
                      refine ⟨2812709412514267582058375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30002233733485520875289333 2812709412514267582058375)
                      ·
                        rfl

theorem cell23_5477732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_5477732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477732 prefixEnd_5477732 := by exact prefixLift 5477732
  have htrace : WordTrace (prefixWord ++ tailWord_5477732) baseStart_5477732 baseEnd_5477732 := by
    simpa [prefixWord, tailWord_5477732, baseEnd_5477732] using wordTrace_append hprefix tailTrace_5477732
  have hstable : (prefixWord ++ tailWord_5477732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477732).length < 2 ^ (prefixWord ++ tailWord_5477732).sum := by decide
  have hdescent : baseEnd_5477732 < baseStart_5477732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477763 : List Nat := [1, 1, 1, 3, 5, 1, 3, 3, 1, 2, 2]
def baseStart_5477763 : Nat := 118140960795 + 5477763 * 2 ^ 59
def prefixEnd_5477763 : Nat := 4983230072969 + 3 ^ 40 * 5477763 * 2
def baseEnd_5477763 : Nat := 2812725330414556960770733

theorem tailTrace_5477763 : CollatzResearch.WordTrace tailWord_5477763 prefixEnd_5477763 2812725330414556960770733 := by
  unfold tailWord_5477763
  simp only [CollatzResearch.WordTrace]
  refine ⟨199790430054007653284365943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133193620036005102189577295 199790430054007653284365943)
  ·
    refine ⟨299685645081011479926548915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199790430054007653284365943 299685645081011479926548915)
    ·
      refine ⟨449528467621517219889823373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299685645081011479926548915 449528467621517219889823373)
      ·
        refine ⟨168573175358068957458683765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 449528467621517219889823373 168573175358068957458683765)
        ·
          refine ⟨15803735189818964761751603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 168573175358068957458683765 15803735189818964761751603)
          ·
            refine ⟨23705602784728447142627405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15803735189818964761751603 23705602784728447142627405)
            ·
              refine ⟨8889601044273167678485277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23705602784728447142627405 8889601044273167678485277)
              ·
                refine ⟨3333600391602437879431979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8889601044273167678485277 3333600391602437879431979)
                ·
                  refine ⟨5000400587403656819147969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3333600391602437879431979 5000400587403656819147969)
                  ·
                    refine ⟨3750300440552742614360977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5000400587403656819147969 3750300440552742614360977)
                    ·
                      refine ⟨2812725330414556960770733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3750300440552742614360977 2812725330414556960770733)
                      ·
                        rfl

theorem cell23_5477763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 3, 1, 2, 2].length) (baseStart_5477763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477763 prefixEnd_5477763 := by exact prefixLift 5477763
  have htrace : WordTrace (prefixWord ++ tailWord_5477763) baseStart_5477763 baseEnd_5477763 := by
    simpa [prefixWord, tailWord_5477763, baseEnd_5477763] using wordTrace_append hprefix tailTrace_5477763
  have hstable : (prefixWord ++ tailWord_5477763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477763).length < 2 ^ (prefixWord ++ tailWord_5477763).sum := by decide
  have hdescent : baseEnd_5477763 < baseStart_5477763 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477790 : List Nat := [4, 3, 1, 2, 2, 2, 2, 1, 2, 4]
def baseStart_5477790 : Nat := 118140960795 + 5477790 * 2 ^ 59
def prefixEnd_5477790 : Nat := 4983230072969 + 3 ^ 40 * 5477790 * 2
def baseEnd_5477790 : Nat := 937579731464076118377703

theorem tailTrace_5477790 : CollatzResearch.WordTrace tailWord_5477790 prefixEnd_5477790 937579731464076118377703 := by
  unfold tailWord_5477790
  simp only [CollatzResearch.WordTrace]
  refine ⟨24973926853113729611949853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133194276549939891263732549 24973926853113729611949853)
  ·
    refine ⟨9365222569917648604481195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24973926853113729611949853 9365222569917648604481195)
    ·
      refine ⟨14047833854876472906721793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9365222569917648604481195 14047833854876472906721793)
      ·
        refine ⟨10535875391157354680041345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14047833854876472906721793 10535875391157354680041345)
        ·
          refine ⟨7901906543368016010031009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10535875391157354680041345 7901906543368016010031009)
          ·
            refine ⟨5926429907526012007523257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7901906543368016010031009 5926429907526012007523257)
            ·
              refine ⟨4444822430644509005642443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5926429907526012007523257 4444822430644509005642443)
              ·
                refine ⟨6667233645966763508463665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4444822430644509005642443 6667233645966763508463665)
                ·
                  refine ⟨5000425234475072631347749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6667233645966763508463665 5000425234475072631347749)
                  ·
                    refine ⟨937579731464076118377703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5000425234475072631347749 937579731464076118377703)
                    ·
                      rfl

theorem cell23_5477790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_5477790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477790 prefixEnd_5477790 := by exact prefixLift 5477790
  have htrace : WordTrace (prefixWord ++ tailWord_5477790) baseStart_5477790 baseEnd_5477790 := by
    simpa [prefixWord, tailWord_5477790, baseEnd_5477790] using wordTrace_append hprefix tailTrace_5477790
  have hstable : (prefixWord ++ tailWord_5477790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477790).length < 2 ^ (prefixWord ++ tailWord_5477790).sum := by decide
  have hdescent : baseEnd_5477790 < baseStart_5477790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477795 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 1, 8]
def baseStart_5477795 : Nat := 118140960795 + 5477795 * 2 ^ 59
def prefixEnd_5477795 : Nat := 4983230072969 + 3 ^ 40 * 5477795 * 2
def baseEnd_5477795 : Nat := 937580587265166945190195

theorem tailTrace_5477795 : CollatzResearch.WordTrace tailWord_5477795 prefixEnd_5477795 937580587265166945190195 := by
  unfold tailWord_5477795
  simp only [CollatzResearch.WordTrace]
  refine ⟨199791597189891722749530839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133194398126594481833020559 199791597189891722749530839)
  ·
    refine ⟨299687395784837584124296259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199791597189891722749530839 299687395784837584124296259)
    ·
      refine ⟨449531093677256376186444389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299687395784837584124296259 449531093677256376186444389)
      ·
        refine ⟨84287080064485570534958323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 449531093677256376186444389 84287080064485570534958323)
        ·
          refine ⟨126430620096728355802437485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84287080064485570534958323 126430620096728355802437485)
          ·
            refine ⟨47411482536273133425914057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126430620096728355802437485 47411482536273133425914057)
            ·
              refine ⟨35558611902204850069435543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47411482536273133425914057 35558611902204850069435543)
              ·
                refine ⟨53337917853307275104153315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35558611902204850069435543 53337917853307275104153315)
                ·
                  refine ⟨80006876779960912656229973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53337917853307275104153315 80006876779960912656229973)
                  ·
                    refine ⟨937580587265166945190195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80006876779960912656229973 937580587265166945190195)
                    ·
                      rfl

theorem cell23_5477795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 1, 8].length) (baseStart_5477795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477795 prefixEnd_5477795 := by exact prefixLift 5477795
  have htrace : WordTrace (prefixWord ++ tailWord_5477795) baseStart_5477795 baseEnd_5477795 := by
    simpa [prefixWord, tailWord_5477795, baseEnd_5477795] using wordTrace_append hprefix tailTrace_5477795
  have hstable : (prefixWord ++ tailWord_5477795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477795).length < 2 ^ (prefixWord ++ tailWord_5477795).sum := by decide
  have hdescent : baseEnd_5477795 < baseStart_5477795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477800 : List Nat := [2, 1, 6, 1, 3, 1, 1, 2, 1, 2, 3]
def baseStart_5477800 : Nat := 118140960795 + 5477800 * 2 ^ 59
def prefixEnd_5477800 : Nat := 4983230072969 + 3 ^ 40 * 5477800 * 2
def baseEnd_5477800 : Nat := 2812744329198773316008063

theorem tailTrace_5477800 : CollatzResearch.WordTrace tailWord_5477800 prefixEnd_5477800 2812744329198773316008063 := by
  unfold tailWord_5477800
  simp only [CollatzResearch.WordTrace]
  refine ⟨99895889777436804301731427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133194519703249072402308569 99895889777436804301731427)
  ·
    refine ⟨149843834666155206452597141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99895889777436804301731427 149843834666155206452597141)
    ·
      refine ⟨7023929749976025302465491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 149843834666155206452597141 7023929749976025302465491)
      ·
        refine ⟨10535894624964037953698237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7023929749976025302465491 10535894624964037953698237)
        ·
          refine ⟨3950960484361514232636839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10535894624964037953698237 3950960484361514232636839)
          ·
            refine ⟨5926440726542271348955259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3950960484361514232636839 5926440726542271348955259)
            ·
              refine ⟨8889661089813407023432889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5926440726542271348955259 8889661089813407023432889)
              ·
                refine ⟨6667245817360055267574667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8889661089813407023432889 6667245817360055267574667)
                ·
                  refine ⟨10000868726040082901362001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6667245817360055267574667 10000868726040082901362001)
                  ·
                    refine ⟨7500651544530062176021501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10000868726040082901362001 7500651544530062176021501)
                    ·
                      refine ⟨2812744329198773316008063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7500651544530062176021501 2812744329198773316008063)
                      ·
                        rfl

theorem cell23_5477800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 1, 2, 3].length) (baseStart_5477800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477800 prefixEnd_5477800 := by exact prefixLift 5477800
  have htrace : WordTrace (prefixWord ++ tailWord_5477800) baseStart_5477800 baseEnd_5477800 := by
    simpa [prefixWord, tailWord_5477800, baseEnd_5477800] using wordTrace_append hprefix tailTrace_5477800
  have hstable : (prefixWord ++ tailWord_5477800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477800).length < 2 ^ (prefixWord ++ tailWord_5477800).sum := by decide
  have hdescent : baseEnd_5477800 < baseStart_5477800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477832 : List Nat := [2, 1, 3, 1, 3, 1, 2, 2, 2, 2, 4]
def baseStart_5477832 : Nat := 118140960795 + 5477832 * 2 ^ 59
def prefixEnd_5477832 : Nat := 4983230072969 + 3 ^ 40 * 5477832 * 2
def baseEnd_5477832 : Nat := 2812760760579717190807915

theorem tailTrace_5477832 : CollatzResearch.WordTrace tailWord_5477832 prefixEnd_5477832 2812760760579717190807915 := by
  unfold tailWord_5477832
  simp only [CollatzResearch.WordTrace]
  refine ⟨99896473345378839034313875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133195297793838452045751833 99896473345378839034313875)
  ·
    refine ⟨149844710018068258551470813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99896473345378839034313875 149844710018068258551470813)
    ·
      refine ⟨56191766256775596956801555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149844710018068258551470813 56191766256775596956801555)
      ·
        refine ⟨84287649385163395435202333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56191766256775596956801555 84287649385163395435202333)
        ·
          refine ⟨31607868519436273288200875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84287649385163395435202333 31607868519436273288200875)
          ·
            refine ⟨47411802779154409932301313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31607868519436273288200875 47411802779154409932301313)
            ·
              refine ⟨35558852084365807449225985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47411802779154409932301313 35558852084365807449225985)
              ·
                refine ⟨26669139063274355586919489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35558852084365807449225985 26669139063274355586919489)
                ·
                  refine ⟨20001854297455766690189617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26669139063274355586919489 20001854297455766690189617)
                  ·
                    refine ⟨15001390723091825017642213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20001854297455766690189617 15001390723091825017642213)
                    ·
                      refine ⟨2812760760579717190807915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15001390723091825017642213 2812760760579717190807915)
                      ·
                        rfl

theorem cell23_5477832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_5477832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477832 prefixEnd_5477832 := by exact prefixLift 5477832
  have htrace : WordTrace (prefixWord ++ tailWord_5477832) baseStart_5477832 baseEnd_5477832 := by
    simpa [prefixWord, tailWord_5477832, baseEnd_5477832] using wordTrace_append hprefix tailTrace_5477832
  have hstable : (prefixWord ++ tailWord_5477832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477832).length < 2 ^ (prefixWord ++ tailWord_5477832).sum := by decide
  have hdescent : baseEnd_5477832 < baseStart_5477832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477835 : List Nat := [1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 7]
def baseStart_5477835 : Nat := 118140960795 + 5477835 * 2 ^ 59
def prefixEnd_5477835 : Nat := 4983230072969 + 3 ^ 40 * 5477835 * 2
def baseEnd_5477835 : Nat := 2812762301021680679070401

theorem tailTrace_5477835 : CollatzResearch.WordTrace tailWord_5477835 prefixEnd_5477835 2812762301021680679070401 := by
  unfold tailWord_5477835
  simp only [CollatzResearch.WordTrace]
  refine ⟨199793056109746809580986959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133195370739831206387324639 199793056109746809580986959)
  ·
    refine ⟨299689584164620214371480439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199793056109746809580986959 299689584164620214371480439)
    ·
      refine ⟨449534376246930321557220659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299689584164620214371480439 449534376246930321557220659)
      ·
        refine ⟨674301564370395482335830989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449534376246930321557220659 674301564370395482335830989)
        ·
          refine ⟨252863086638898305875936621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 674301564370395482335830989 252863086638898305875936621)
          ·
            refine ⟨94823657489586864703476233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252863086638898305875936621 94823657489586864703476233)
            ·
              refine ⟨71117743117190148527607175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94823657489586864703476233 71117743117190148527607175)
              ·
                refine ⟨106676614675785222791410763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71117743117190148527607175 106676614675785222791410763)
                ·
                  refine ⟨160014922013677834187116145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 106676614675785222791410763 160014922013677834187116145)
                  ·
                    refine ⟨120011191510258375640337109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 160014922013677834187116145 120011191510258375640337109)
                    ·
                      refine ⟨2812762301021680679070401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120011191510258375640337109 2812762301021680679070401)
                      ·
                        rfl

theorem cell23_5477835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 2, 7].length) (baseStart_5477835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477835 prefixEnd_5477835 := by exact prefixLift 5477835
  have htrace : WordTrace (prefixWord ++ tailWord_5477835) baseStart_5477835 baseEnd_5477835 := by
    simpa [prefixWord, tailWord_5477835, baseEnd_5477835] using wordTrace_append hprefix tailTrace_5477835
  have hstable : (prefixWord ++ tailWord_5477835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477835).length < 2 ^ (prefixWord ++ tailWord_5477835).sum := by decide
  have hdescent : baseEnd_5477835 < baseStart_5477835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477853 : List Nat := [1, 4, 3, 1, 1, 2, 2, 3, 2, 2, 2]
def baseStart_5477853 : Nat := 118140960795 + 5477853 * 2 ^ 59
def prefixEnd_5477853 : Nat := 4983230072969 + 3 ^ 40 * 5477853 * 2
def baseEnd_5477853 : Nat := 2812771543673461608645319

theorem tailTrace_5477853 : CollatzResearch.WordTrace tailWord_5477853 prefixEnd_5477853 2812771543673461608645319 := by
  unfold tailWord_5477853
  simp only [CollatzResearch.WordTrace]
  refine ⟨199793712623681598655142213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133195808415787732436761475 199793712623681598655142213)
  ·
    refine ⟨37461321116940299747839165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199793712623681598655142213 37461321116940299747839165)
    ·
      refine ⟨14047995418852612405439687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37461321116940299747839165 14047995418852612405439687)
      ·
        refine ⟨21071993128278918608159531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14047995418852612405439687 21071993128278918608159531)
        ·
          refine ⟨31607989692418377912239297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21071993128278918608159531 31607989692418377912239297)
          ·
            refine ⟨23705992269313783434179473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31607989692418377912239297 23705992269313783434179473)
            ·
              refine ⟨17779494201985337575634605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23705992269313783434179473 17779494201985337575634605)
              ·
                refine ⟨6667310325744501590862977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17779494201985337575634605 6667310325744501590862977)
                ·
                  refine ⟨5000482744308376193147233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6667310325744501590862977 5000482744308376193147233)
                  ·
                    refine ⟨3750362058231282144860425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5000482744308376193147233 3750362058231282144860425)
                    ·
                      refine ⟨2812771543673461608645319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3750362058231282144860425 2812771543673461608645319)
                      ·
                        rfl

theorem cell23_5477853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_5477853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477853 prefixEnd_5477853 := by exact prefixLift 5477853
  have htrace : WordTrace (prefixWord ++ tailWord_5477853) baseStart_5477853 baseEnd_5477853 := by
    simpa [prefixWord, tailWord_5477853, baseEnd_5477853] using wordTrace_append hprefix tailTrace_5477853
  have hstable : (prefixWord ++ tailWord_5477853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477853).length < 2 ^ (prefixWord ++ tailWord_5477853).sum := by decide
  have hdescent : baseEnd_5477853 < baseStart_5477853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477872 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 1, 7]
def baseStart_5477872 : Nat := 118140960795 + 5477872 * 2 ^ 59
def prefixEnd_5477872 : Nat := 4983230072969 + 3 ^ 40 * 5477872 * 2
def baseEnd_5477872 : Nat := 937593766601965678102577

theorem tailTrace_5477872 : CollatzResearch.WordTrace tailWord_5477872 prefixEnd_5477872 937593766601965678102577 := by
  unfold tailWord_5477872
  simp only [CollatzResearch.WordTrace]
  refine ⟨99897202805306382450041935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133196270407075176600055913 99897202805306382450041935)
  ·
    refine ⟨149845804207959573675062903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99897202805306382450041935 149845804207959573675062903)
    ·
      refine ⟨224768706311939360512594355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149845804207959573675062903 224768706311939360512594355)
      ·
        refine ⟨337153059467909040768891533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224768706311939360512594355 337153059467909040768891533)
        ·
          refine ⟨126432397300465890288334325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 337153059467909040768891533 126432397300465890288334325)
          ·
            refine ⟨11853037246918677214531343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 126432397300465890288334325 11853037246918677214531343)
            ·
              refine ⟨17779555870378015821797015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11853037246918677214531343 17779555870378015821797015)
              ·
                refine ⟨26669333805567023732695523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17779555870378015821797015 26669333805567023732695523)
                ·
                  refine ⟨40004000708350535599043285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26669333805567023732695523 40004000708350535599043285)
                  ·
                    refine ⟨937593766601965678102577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40004000708350535599043285 937593766601965678102577)
                    ·
                      rfl

theorem cell23_5477872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 1, 7].length) (baseStart_5477872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477872 prefixEnd_5477872 := by exact prefixLift 5477872
  have htrace : WordTrace (prefixWord ++ tailWord_5477872) baseStart_5477872 baseEnd_5477872 := by
    simpa [prefixWord, tailWord_5477872, baseEnd_5477872] using wordTrace_append hprefix tailTrace_5477872
  have hstable : (prefixWord ++ tailWord_5477872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477872).length < 2 ^ (prefixWord ++ tailWord_5477872).sum := by decide
  have hdescent : baseEnd_5477872 < baseStart_5477872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5477919 : List Nat := [1, 1, 2, 4, 1, 1, 4, 2, 3, 4]
def baseStart_5477919 : Nat := 118140960795 + 5477919 * 2 ^ 59
def prefixEnd_5477919 : Nat := 4983230072969 + 3 ^ 40 * 5477919 * 2
def baseEnd_5477919 : Nat := 937601811132219450140005

theorem tailTrace_5477919 : CollatzResearch.WordTrace tailWord_5477919 prefixEnd_5477919 937601811132219450140005 := by
  unfold tailWord_5477919
  simp only [CollatzResearch.WordTrace]
  refine ⟨199796119841442491927044811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133197413227628327951363207 199796119841442491927044811)
  ·
    refine ⟨299694179762163737890567217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199796119841442491927044811 299694179762163737890567217)
    ·
      refine ⟨224770634821622803417925413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299694179762163737890567217 224770634821622803417925413)
      ·
        refine ⟨42144494029054275640861015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224770634821622803417925413 42144494029054275640861015)
        ·
          refine ⟨63216741043581413461291523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42144494029054275640861015 63216741043581413461291523)
          ·
            refine ⟨94825111565372120191937285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63216741043581413461291523 94825111565372120191937285)
            ·
              refine ⟨17779708418507272535988241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94825111565372120191937285 17779708418507272535988241)
              ·
                refine ⟨13334781313880454401991181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17779708418507272535988241 13334781313880454401991181)
                ·
                  refine ⟨5000542992705170400746693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13334781313880454401991181 5000542992705170400746693)
                  ·
                    refine ⟨937601811132219450140005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5000542992705170400746693 937601811132219450140005)
                    ·
                      rfl

theorem cell23_5477919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 2, 3, 4].length) (baseStart_5477919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5477919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5477919 prefixEnd_5477919 := by exact prefixLift 5477919
  have htrace : WordTrace (prefixWord ++ tailWord_5477919) baseStart_5477919 baseEnd_5477919 := by
    simpa [prefixWord, tailWord_5477919, baseEnd_5477919] using wordTrace_append hprefix tailTrace_5477919
  have hstable : (prefixWord ++ tailWord_5477919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5477919).length < 2 ^ (prefixWord ++ tailWord_5477919).sum := by decide
  have hdescent : baseEnd_5477919 < baseStart_5477919 := by decide
  rcases family_descends (prefixWord ++ tailWord_5477919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478026 : List Nat := [3, 1, 2, 3, 2, 2, 2, 1, 1, 6]
def baseStart_5478026 : Nat := 118140960795 + 5478026 * 2 ^ 59
def prefixEnd_5478026 : Nat := 4983230072969 + 3 ^ 40 * 5478026 * 2
def baseEnd_5478026 : Nat := 937620125275563143927341

theorem tailTrace_5478026 : CollatzResearch.WordTrace tailWord_5478026 prefixEnd_5478026 937620125275563143927341 := by
  unfold tailWord_5478026
  simp only [CollatzResearch.WordTrace]
  refine ⟨49950005613013712300297483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133200014968036566134126621 49950005613013712300297483)
  ·
    refine ⟨74925008419520568450446225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49950005613013712300297483 74925008419520568450446225)
    ·
      refine ⟨56193756314640426337834669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74925008419520568450446225 56193756314640426337834669)
      ·
        refine ⟨21072658617990159876688001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56193756314640426337834669 21072658617990159876688001)
        ·
          refine ⟨15804493963492619907516001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21072658617990159876688001 15804493963492619907516001)
          ·
            refine ⟨11853370472619464930637001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15804493963492619907516001 11853370472619464930637001)
            ·
              refine ⟨8890027854464598697977751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11853370472619464930637001 8890027854464598697977751)
              ·
                refine ⟨13335041781696898046966627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8890027854464598697977751 13335041781696898046966627)
                ·
                  refine ⟨20002562672545347070449941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13335041781696898046966627 20002562672545347070449941)
                  ·
                    refine ⟨937620125275563143927341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20002562672545347070449941 937620125275563143927341)
                    ·
                      rfl

theorem cell23_5478026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 1, 6].length) (baseStart_5478026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478026 prefixEnd_5478026 := by exact prefixLift 5478026
  have htrace : WordTrace (prefixWord ++ tailWord_5478026) baseStart_5478026 baseEnd_5478026 := by
    simpa [prefixWord, tailWord_5478026, baseEnd_5478026] using wordTrace_append hprefix tailTrace_5478026
  have hstable : (prefixWord ++ tailWord_5478026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478026).length < 2 ^ (prefixWord ++ tailWord_5478026).sum := by decide
  have hdescent : baseEnd_5478026 < baseStart_5478026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478032 : List Nat := [2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 7]
def baseStart_5478032 : Nat := 118140960795 + 5478032 * 2 ^ 59
def prefixEnd_5478032 : Nat := 4983230072969 + 3 ^ 40 * 5478032 * 2
def baseEnd_5478032 : Nat := 2812863456710616408306995

theorem tailTrace_5478032 : CollatzResearch.WordTrace tailWord_5478032 prefixEnd_5478032 2812863456710616408306995 := by
  unfold tailWord_5478032
  simp only [CollatzResearch.WordTrace]
  refine ⟨99900120645016556112954175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133200160860022074817272233 99900120645016556112954175)
  ·
    refine ⟨149850180967524834169431263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99900120645016556112954175 149850180967524834169431263)
    ·
      refine ⟨224775271451287251254146895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149850180967524834169431263 224775271451287251254146895)
      ·
        refine ⟨337162907176930876881220343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224775271451287251254146895 337162907176930876881220343)
        ·
          refine ⟨505744360765396315321830515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337162907176930876881220343 505744360765396315321830515)
          ·
            refine ⟨758616541148094472982745773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505744360765396315321830515 758616541148094472982745773)
            ·
              refine ⟨284481202930535427368529665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 758616541148094472982745773 284481202930535427368529665)
              ·
                refine ⟨213360902197901570526397249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284481202930535427368529665 213360902197901570526397249)
                ·
                  refine ⟨160020676648426177894797937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213360902197901570526397249 160020676648426177894797937)
                  ·
                    refine ⟨120015507486319633421098453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 160020676648426177894797937 120015507486319633421098453)
                    ·
                      refine ⟨2812863456710616408306995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120015507486319633421098453 2812863456710616408306995)
                      ·
                        rfl

theorem cell23_5478032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 2, 2, 2, 7].length) (baseStart_5478032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478032 prefixEnd_5478032 := by exact prefixLift 5478032
  have htrace : WordTrace (prefixWord ++ tailWord_5478032) baseStart_5478032 baseEnd_5478032 := by
    simpa [prefixWord, tailWord_5478032, baseEnd_5478032] using wordTrace_append hprefix tailTrace_5478032
  have hstable : (prefixWord ++ tailWord_5478032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478032).length < 2 ^ (prefixWord ++ tailWord_5478032).sum := by decide
  have hdescent : baseEnd_5478032 < baseStart_5478032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478047 : List Nat := [1, 1, 2, 7, 2, 1, 2, 1, 1, 5]
def baseStart_5478047 : Nat := 118140960795 + 5478047 * 2 ^ 59
def prefixEnd_5478047 : Nat := 4983230072969 + 3 ^ 40 * 5478047 * 2
def baseEnd_5478047 : Nat := 937623719640144616539809

theorem tailTrace_5478047 : CollatzResearch.WordTrace tailWord_5478047 prefixEnd_5478047 937623719640144616539809 := by
  unfold tailWord_5478047
  simp only [CollatzResearch.WordTrace]
  refine ⟨199800788384978769787704395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133200525589985846525136263 199800788384978769787704395)
  ·
    refine ⟨299701182577468154681556593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199800788384978769787704395 299701182577468154681556593)
    ·
      refine ⟨224775886933101116011167445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299701182577468154681556593 224775886933101116011167445)
      ·
        refine ⟨5268184849994557406511737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 224775886933101116011167445 5268184849994557406511737)
        ·
          refine ⟨3951138637495918054883803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5268184849994557406511737 3951138637495918054883803)
          ·
            refine ⟨5926707956243877082325705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3951138637495918054883803 5926707956243877082325705)
            ·
              refine ⟨4445030967182907811744279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5926707956243877082325705 4445030967182907811744279)
              ·
                refine ⟨6667546450774361717616419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4445030967182907811744279 6667546450774361717616419)
                ·
                  refine ⟨10001319676161542576424629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6667546450774361717616419 10001319676161542576424629)
                  ·
                    refine ⟨937623719640144616539809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10001319676161542576424629 937623719640144616539809)
                    ·
                      rfl

theorem cell23_5478047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 1, 1, 5].length) (baseStart_5478047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478047 prefixEnd_5478047 := by exact prefixLift 5478047
  have htrace : WordTrace (prefixWord ++ tailWord_5478047) baseStart_5478047 baseEnd_5478047 := by
    simpa [prefixWord, tailWord_5478047, baseEnd_5478047] using wordTrace_append hprefix tailTrace_5478047
  have hstable : (prefixWord ++ tailWord_5478047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478047).length < 2 ^ (prefixWord ++ tailWord_5478047).sum := by decide
  have hdescent : baseEnd_5478047 < baseStart_5478047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478050 : List Nat := [3, 3, 1, 4, 1, 1, 1, 3, 1, 1, 4]
def baseStart_5478050 : Nat := 118140960795 + 5478050 * 2 ^ 59
def prefixEnd_5478050 : Nat := 4983230072969 + 3 ^ 40 * 5478050 * 2
def baseEnd_5478050 : Nat := 2812872699362397337881913

theorem tailTrace_5478050 : CollatzResearch.WordTrace tailWord_5478050 prefixEnd_5478050 2812872699362397337881913 := by
  unfold tailWord_5478050
  simp only [CollatzResearch.WordTrace]
  refine ⟨49950224450991975325015901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133200598535978600866709069 49950224450991975325015901)
  ·
    refine ⟨18731334169121990746880963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49950224450991975325015901 18731334169121990746880963)
    ·
      refine ⟨28097001253682986120321445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18731334169121990746880963 28097001253682986120321445)
      ·
        refine ⟨5268187735065559897560271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28097001253682986120321445 5268187735065559897560271)
        ·
          refine ⟨7902281602598339846340407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5268187735065559897560271 7902281602598339846340407)
          ·
            refine ⟨11853422403897509769510611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7902281602598339846340407 11853422403897509769510611)
            ·
              refine ⟨17780133605846264654265917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11853422403897509769510611 17780133605846264654265917)
              ·
                refine ⟨6667550102192349245349719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17780133605846264654265917 6667550102192349245349719)
                ·
                  refine ⟨10001325153288523868024579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6667550102192349245349719 10001325153288523868024579)
                  ·
                    refine ⟨15001987729932785802036869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10001325153288523868024579 15001987729932785802036869)
                    ·
                      refine ⟨2812872699362397337881913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15001987729932785802036869 2812872699362397337881913)
                      ·
                        rfl

theorem cell23_5478050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_5478050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478050 prefixEnd_5478050 := by exact prefixLift 5478050
  have htrace : WordTrace (prefixWord ++ tailWord_5478050) baseStart_5478050 baseEnd_5478050 := by
    simpa [prefixWord, tailWord_5478050, baseEnd_5478050] using wordTrace_append hprefix tailTrace_5478050
  have hstable : (prefixWord ++ tailWord_5478050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478050).length < 2 ^ (prefixWord ++ tailWord_5478050).sum := by decide
  have hdescent : baseEnd_5478050 < baseStart_5478050 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478053 : List Nat := [1, 3, 1, 2, 1, 2, 6, 1, 1, 2, 3]
def baseStart_5478053 : Nat := 118140960795 + 5478053 * 2 ^ 59
def prefixEnd_5478053 : Nat := 4983230072969 + 3 ^ 40 * 5478053 * 2
def baseEnd_5478053 : Nat := 2812874239804360826144399

theorem tailTrace_5478053 : CollatzResearch.WordTrace tailWord_5478053 prefixEnd_5478053 2812874239804360826144399 := by
  unfold tailWord_5478053
  simp only [CollatzResearch.WordTrace]
  refine ⟨199801007222957032812422813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133200671481971355208281875 199801007222957032812422813)
  ·
    refine ⟨74925377708608887304658555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199801007222957032812422813 74925377708608887304658555)
    ·
      refine ⟨112388066562913330956987833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74925377708608887304658555 112388066562913330956987833)
      ·
        refine ⟨84291049922184998217740875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112388066562913330956987833 84291049922184998217740875)
        ·
          refine ⟨126436574883277497326611313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84291049922184998217740875 126436574883277497326611313)
          ·
            refine ⟨94827431162458122994958485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126436574883277497326611313 94827431162458122994958485)
            ·
              refine ⟨4445035835740224515388679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94827431162458122994958485 4445035835740224515388679)
              ·
                refine ⟨6667553753610336773083019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4445035835740224515388679 6667553753610336773083019)
                ·
                  refine ⟨10001330630415505159624529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6667553753610336773083019 10001330630415505159624529)
                  ·
                    refine ⟨7500997972811628869718397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10001330630415505159624529 7500997972811628869718397)
                    ·
                      refine ⟨2812874239804360826144399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7500997972811628869718397 2812874239804360826144399)
                      ·
                        rfl

theorem cell23_5478053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 6, 1, 1, 2, 3].length) (baseStart_5478053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478053 prefixEnd_5478053 := by exact prefixLift 5478053
  have htrace : WordTrace (prefixWord ++ tailWord_5478053) baseStart_5478053 baseEnd_5478053 := by
    simpa [prefixWord, tailWord_5478053, baseEnd_5478053] using wordTrace_append hprefix tailTrace_5478053
  have hstable : (prefixWord ++ tailWord_5478053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478053).length < 2 ^ (prefixWord ++ tailWord_5478053).sum := by decide
  have hdescent : baseEnd_5478053 < baseStart_5478053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478123 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 4, 2, 2]
def baseStart_5478123 : Nat := 118140960795 + 5478123 * 2 ^ 59
def prefixEnd_5478123 : Nat := 4983230072969 + 3 ^ 40 * 5478123 * 2
def baseEnd_5478123 : Nat := 2812910183450175552269077

theorem tailTrace_5478123 : CollatzResearch.WordTrace tailWord_5478123 prefixEnd_5478123 2812910183450175552269077 := by
  unfold tailWord_5478123
  simp only [CollatzResearch.WordTrace]
  refine ⟨199803560332703434767471023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133202373555135623178314015 199803560332703434767471023)
  ·
    refine ⟨299705340499055152151206535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199803560332703434767471023 299705340499055152151206535)
    ·
      refine ⟨449558010748582728226809803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299705340499055152151206535 449558010748582728226809803)
      ·
        refine ⟨674337016122874092340214705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449558010748582728226809803 674337016122874092340214705)
        ·
          refine ⟨505752762092155569255161029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 674337016122874092340214705 505752762092155569255161029)
          ·
            refine ⟨94828642892279169235342693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 505752762092155569255161029 94828642892279169235342693)
            ·
              refine ⟨17780370542302344231626755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94828642892279169235342693 17780370542302344231626755)
              ·
                refine ⟨26670555813453516347440133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17780370542302344231626755 26670555813453516347440133)
                ·
                  refine ⟨5000729215022534315145025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26670555813453516347440133 5000729215022534315145025)
                  ·
                    refine ⟨3750546911266900736358769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5000729215022534315145025 3750546911266900736358769)
                    ·
                      refine ⟨2812910183450175552269077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3750546911266900736358769 2812910183450175552269077)
                      ·
                        rfl

theorem cell23_5478123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 4, 2, 2].length) (baseStart_5478123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478123 prefixEnd_5478123 := by exact prefixLift 5478123
  have htrace : WordTrace (prefixWord ++ tailWord_5478123) baseStart_5478123 baseEnd_5478123 := by
    simpa [prefixWord, tailWord_5478123, baseEnd_5478123] using wordTrace_append hprefix tailTrace_5478123
  have hstable : (prefixWord ++ tailWord_5478123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478123).length < 2 ^ (prefixWord ++ tailWord_5478123).sum := by decide
  have hdescent : baseEnd_5478123 < baseStart_5478123 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478126 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 2, 4, 3]
def baseStart_5478126 : Nat := 118140960795 + 5478126 * 2 ^ 59
def prefixEnd_5478126 : Nat := 4983230072969 + 3 ^ 40 * 5478126 * 2
def baseEnd_5478126 : Nat := 2812911723892139040531563

theorem tailTrace_5478126 : CollatzResearch.WordTrace tailWord_5478126 prefixEnd_5478126 2812911723892139040531563 := by
  unfold tailWord_5478126
  simp only [CollatzResearch.WordTrace]
  refine ⟨24975458718961570784978779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133202446501128377519886821 24975458718961570784978779)
  ·
    refine ⟨37463188078442356177468169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24975458718961570784978779 37463188078442356177468169)
    ·
      refine ⟨28097391058831767133101127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37463188078442356177468169 28097391058831767133101127)
      ·
        refine ⟨42146086588247650699651691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28097391058831767133101127 42146086588247650699651691)
        ·
          refine ⟨63219129882371476049477537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42146086588247650699651691 63219129882371476049477537)
          ·
            refine ⟨47414347411778607037108153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63219129882371476049477537 47414347411778607037108153)
            ·
              refine ⟨35560760558833955277831115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47414347411778607037108153 35560760558833955277831115)
              ·
                refine ⟨53341140838250932916746673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35560760558833955277831115 53341140838250932916746673)
                ·
                  refine ⟨40005855628688199687560005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53341140838250932916746673 40005855628688199687560005)
                  ·
                    refine ⟨7501097930379037441417501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40005855628688199687560005 7501097930379037441417501)
                    ·
                      refine ⟨2812911723892139040531563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7501097930379037441417501 2812911723892139040531563)
                      ·
                        rfl

theorem cell23_5478126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 2, 4, 3].length) (baseStart_5478126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478126 prefixEnd_5478126 := by exact prefixLift 5478126
  have htrace : WordTrace (prefixWord ++ tailWord_5478126) baseStart_5478126 baseEnd_5478126 := by
    simpa [prefixWord, tailWord_5478126, baseEnd_5478126] using wordTrace_append hprefix tailTrace_5478126
  have hstable : (prefixWord ++ tailWord_5478126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478126).length < 2 ^ (prefixWord ++ tailWord_5478126).sum := by decide
  have hdescent : baseEnd_5478126 < baseStart_5478126 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478140 : List Nat := [2, 2, 2, 1, 3, 1, 3, 3, 2, 2, 2]
def baseStart_5478140 : Nat := 118140960795 + 5478140 * 2 ^ 59
def prefixEnd_5478140 : Nat := 4983230072969 + 3 ^ 40 * 5478140 * 2
def baseEnd_5478140 : Nat := 2812918912621301985756499

theorem tailTrace_5478140 : CollatzResearch.WordTrace tailWord_5478140 prefixEnd_5478140 2812918912621301985756499 := by
  unfold tailWord_5478140
  simp only [CollatzResearch.WordTrace]
  refine ⟨99902090186820923335419937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133202786915761231113893249 99902090186820923335419937)
  ·
    refine ⟨74926567640115692501564953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99902090186820923335419937 74926567640115692501564953)
    ·
      refine ⟨56194925730086769376173715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74926567640115692501564953 56194925730086769376173715)
      ·
        refine ⟨84292388595130154064260573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56194925730086769376173715 84292388595130154064260573)
        ·
          refine ⟨31609645723173807774097715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84292388595130154064260573 31609645723173807774097715)
          ·
            refine ⟨47414468584760711661146573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31609645723173807774097715 47414468584760711661146573)
            ·
              refine ⟨17780425719285266872929965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47414468584760711661146573 17780425719285266872929965)
              ·
                refine ⟨6667659644731975077348737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17780425719285266872929965 6667659644731975077348737)
                ·
                  refine ⟨5000744733548981308011553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6667659644731975077348737 5000744733548981308011553)
                  ·
                    refine ⟨3750558550161735981008665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5000744733548981308011553 3750558550161735981008665)
                    ·
                      refine ⟨2812918912621301985756499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3750558550161735981008665 2812918912621301985756499)
                      ·
                        rfl

theorem cell23_5478140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 3, 2, 2, 2].length) (baseStart_5478140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478140 prefixEnd_5478140 := by exact prefixLift 5478140
  have htrace : WordTrace (prefixWord ++ tailWord_5478140) baseStart_5478140 baseEnd_5478140 := by
    simpa [prefixWord, tailWord_5478140, baseEnd_5478140] using wordTrace_append hprefix tailTrace_5478140
  have hstable : (prefixWord ++ tailWord_5478140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478140).length < 2 ^ (prefixWord ++ tailWord_5478140).sum := by decide
  have hdescent : baseEnd_5478140 < baseStart_5478140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478146 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 9]
def baseStart_5478146 : Nat := 118140960795 + 5478146 * 2 ^ 59
def prefixEnd_5478146 : Nat := 4983230072969 + 3 ^ 40 * 5478146 * 2
def baseEnd_5478146 : Nat := 312546888167247662475719

theorem tailTrace_5478146 : CollatzResearch.WordTrace tailWord_5478146 prefixEnd_5478146 312546888167247662475719 := by
  unfold tailWord_5478146
  simp only [CollatzResearch.WordTrace]
  refine ⟨49951099802905027423889573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133202932807746739797038861 49951099802905027423889573)
  ·
    refine ⟨9365831213044692641979295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49951099802905027423889573 9365831213044692641979295)
    ·
      refine ⟨14048746819567038962968943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9365831213044692641979295 14048746819567038962968943)
      ·
        refine ⟨21073120229350558444453415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14048746819567038962968943 21073120229350558444453415)
        ·
          refine ⟨31609680344025837666680123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21073120229350558444453415 31609680344025837666680123)
          ·
            refine ⟨47414520516038756500020185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31609680344025837666680123 47414520516038756500020185)
            ·
              refine ⟨35560890387029067375015139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47414520516038756500020185 35560890387029067375015139)
              ·
                refine ⟨53341335580543601062522709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35560890387029067375015139 53341335580543601062522709)
                ·
                  refine ⟨312546888167247662475719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 53341335580543601062522709 312546888167247662475719)
                  ·
                    rfl

theorem cell23_5478146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_5478146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478146 prefixEnd_5478146 := by exact prefixLift 5478146
  have htrace : WordTrace (prefixWord ++ tailWord_5478146) baseStart_5478146 baseEnd_5478146 := by
    simpa [prefixWord, tailWord_5478146, baseEnd_5478146] using wordTrace_append hprefix tailTrace_5478146
  have hstable : (prefixWord ++ tailWord_5478146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478146).length < 2 ^ (prefixWord ++ tailWord_5478146).sum := by decide
  have hdescent : baseEnd_5478146 < baseStart_5478146 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478176 : List Nat := [2, 1, 1, 5, 1, 1, 1, 4, 2, 5]
def baseStart_5478176 : Nat := 118140960795 + 5478176 * 2 ^ 59
def prefixEnd_5478176 : Nat := 4983230072969 + 3 ^ 40 * 5478176 * 2
def baseEnd_5478176 : Nat := 937645799308287948302111

theorem tailTrace_5478176 : CollatzResearch.WordTrace tailWord_5478176 prefixEnd_5478176 937645799308287948302111 := by
  unfold tailWord_5478176
  simp only [CollatzResearch.WordTrace]
  refine ⟨99902746700755712409575191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133203662267674283212766921 99902746700755712409575191)
  ·
    refine ⟨149854120051133568614362787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99902746700755712409575191 149854120051133568614362787)
    ·
      refine ⟨224781180076700352921544181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149854120051133568614362787 224781180076700352921544181)
      ·
        refine ⟨21073235632190658086394767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 224781180076700352921544181 21073235632190658086394767)
        ·
          refine ⟨31609853448285987129592151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21073235632190658086394767 31609853448285987129592151)
          ·
            refine ⟨47414780172428980694388227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31609853448285987129592151 47414780172428980694388227)
            ·
              refine ⟨71122170258643471041582341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47414780172428980694388227 71122170258643471041582341)
              ·
                refine ⟨13335406923495650820296689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71122170258643471041582341 13335406923495650820296689)
                ·
                  refine ⟨10001555192621738115222517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13335406923495650820296689 10001555192621738115222517)
                  ·
                    refine ⟨937645799308287948302111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10001555192621738115222517 937645799308287948302111)
                    ·
                      rfl

theorem cell23_5478176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 2, 5].length) (baseStart_5478176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478176 prefixEnd_5478176 := by exact prefixLift 5478176
  have htrace : WordTrace (prefixWord ++ tailWord_5478176) baseStart_5478176 baseEnd_5478176 := by
    simpa [prefixWord, tailWord_5478176, baseEnd_5478176] using wordTrace_append hprefix tailTrace_5478176
  have hstable : (prefixWord ++ tailWord_5478176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478176).length < 2 ^ (prefixWord ++ tailWord_5478176).sum := by decide
  have hdescent : baseEnd_5478176 < baseStart_5478176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478180 : List Nat := [2, 3, 1, 3, 2, 1, 4, 2, 5]
def baseStart_5478180 : Nat := 118140960795 + 5478180 * 2 ^ 59
def prefixEnd_5478180 : Nat := 4983230072969 + 3 ^ 40 * 5478180 * 2
def baseEnd_5478180 : Nat := 312548827983053536584035

theorem tailTrace_5478180 : CollatzResearch.WordTrace tailWord_5478180 prefixEnd_5478180 312548827983053536584035 := by
  unfold tailWord_5478180
  simp only [CollatzResearch.WordTrace]
  refine ⟨99902819646748466751147997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133203759528997955668197329 99902819646748466751147997)
  ·
    refine ⟨37463557367530675031680499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99902819646748466751147997 37463557367530675031680499)
    ·
      refine ⟨56195336051296012547520749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37463557367530675031680499 56195336051296012547520749)
      ·
        refine ⟨21073251019236004705320281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56195336051296012547520749 21073251019236004705320281)
        ·
          refine ⟨15804938264427003528990211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21073251019236004705320281 15804938264427003528990211)
          ·
            refine ⟨23707407396640505293485317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15804938264427003528990211 23707407396640505293485317)
            ·
              refine ⟨4445138886870094742528497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23707407396640505293485317 4445138886870094742528497)
              ·
                refine ⟨3333854165152571056896373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4445138886870094742528497 3333854165152571056896373)
                ·
                  refine ⟨312548827983053536584035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3333854165152571056896373 312548827983053536584035)
                  ·
                    rfl

theorem cell23_5478180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 2, 5].length) (baseStart_5478180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478180 prefixEnd_5478180 := by exact prefixLift 5478180
  have htrace : WordTrace (prefixWord ++ tailWord_5478180) baseStart_5478180 baseEnd_5478180 := by
    simpa [prefixWord, tailWord_5478180, baseEnd_5478180] using wordTrace_append hprefix tailTrace_5478180
  have hstable : (prefixWord ++ tailWord_5478180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478180).length < 2 ^ (prefixWord ++ tailWord_5478180).sum := by decide
  have hdescent : baseEnd_5478180 < baseStart_5478180 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478190 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 2, 3, 3]
def baseStart_5478190 : Nat := 118140960795 + 5478190 * 2 ^ 59
def prefixEnd_5478190 : Nat := 4983230072969 + 3 ^ 40 * 5478190 * 2
def baseEnd_5478190 : Nat := 2812944586654026790131269

theorem tailTrace_5478190 : CollatzResearch.WordTrace tailWord_5478190 prefixEnd_5478190 2812944586654026790131269 := by
  unfold tailWord_5478190
  simp only [CollatzResearch.WordTrace]
  refine ⟨24975750502932588151270003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133204002682307136806773349 24975750502932588151270003)
  ·
    refine ⟨37463625754398882226905005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24975750502932588151270003 37463625754398882226905005)
    ·
      refine ⟨14048859657899580835089377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37463625754398882226905005 14048859657899580835089377)
      ·
        refine ⟨10536644743424685626317033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14048859657899580835089377 10536644743424685626317033)
        ·
          refine ⟨7902483557568514219737775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10536644743424685626317033 7902483557568514219737775)
          ·
            refine ⟨11853725336352771329606663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7902483557568514219737775 11853725336352771329606663)
            ·
              refine ⟨17780588004529156994409995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11853725336352771329606663 17780588004529156994409995)
              ·
                refine ⟨26670882006793735491614993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17780588004529156994409995 26670882006793735491614993)
                ·
                  refine ⟨20003161505095301618711245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26670882006793735491614993 20003161505095301618711245)
                  ·
                    refine ⟨7501185564410738107016717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20003161505095301618711245 7501185564410738107016717)
                    ·
                      refine ⟨2812944586654026790131269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7501185564410738107016717 2812944586654026790131269)
                      ·
                        rfl

theorem cell23_5478190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_5478190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478190 prefixEnd_5478190 := by exact prefixLift 5478190
  have htrace : WordTrace (prefixWord ++ tailWord_5478190) baseStart_5478190 baseEnd_5478190 := by
    simpa [prefixWord, tailWord_5478190, baseEnd_5478190] using wordTrace_append hprefix tailTrace_5478190
  have hstable : (prefixWord ++ tailWord_5478190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478190).length < 2 ^ (prefixWord ++ tailWord_5478190).sum := by decide
  have hdescent : baseEnd_5478190 < baseStart_5478190 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478226 : List Nat := [3, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6]
def baseStart_5478226 : Nat := 118140960795 + 5478226 * 2 ^ 59
def prefixEnd_5478226 : Nat := 4983230072969 + 3 ^ 40 * 5478226 * 2
def baseEnd_5478226 : Nat := 2812963071957588649281103

theorem tailTrace_5478226 : CollatzResearch.WordTrace tailWord_5478226 prefixEnd_5478226 2812963071957588649281103 := by
  unfold tailWord_5478226
  simp only [CollatzResearch.WordTrace]
  refine ⟨49951829262832570839617633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133204878034220188905647021 49951829262832570839617633)
  ·
    refine ⟨37463871947124428129713225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49951829262832570839617633 37463871947124428129713225)
    ·
      refine ⟨28097903960343321097284919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37463871947124428129713225 28097903960343321097284919)
      ·
        refine ⟨42146855940514981645927379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28097903960343321097284919 42146855940514981645927379)
        ·
          refine ⟨63220283910772472468891069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42146855940514981645927379 63220283910772472468891069)
          ·
            refine ⟨23707606466539677175834151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63220283910772472468891069 23707606466539677175834151)
            ·
              refine ⟨35561409699809515763751227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23707606466539677175834151 35561409699809515763751227)
              ·
                refine ⟨53342114549714273645626841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35561409699809515763751227 53342114549714273645626841)
                ·
                  refine ⟨40006585912285705234220131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53342114549714273645626841 40006585912285705234220131)
                  ·
                    refine ⟨60009878868428557851330197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40006585912285705234220131 60009878868428557851330197)
                    ·
                      refine ⟨2812963071957588649281103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60009878868428557851330197 2812963071957588649281103)
                      ·
                        rfl

theorem cell23_5478226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_5478226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478226 prefixEnd_5478226 := by exact prefixLift 5478226
  have htrace : WordTrace (prefixWord ++ tailWord_5478226) baseStart_5478226 baseEnd_5478226 := by
    simpa [prefixWord, tailWord_5478226, baseEnd_5478226] using wordTrace_append hprefix tailTrace_5478226
  have hstable : (prefixWord ++ tailWord_5478226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478226).length < 2 ^ (prefixWord ++ tailWord_5478226).sum := by decide
  have hdescent : baseEnd_5478226 < baseStart_5478226 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478240 : List Nat := [2, 1, 1, 3, 3, 2, 2, 4, 1, 4]
def baseStart_5478240 : Nat := 118140960795 + 5478240 * 2 ^ 59
def prefixEnd_5478240 : Nat := 4983230072969 + 3 ^ 40 * 5478240 * 2
def baseEnd_5478240 : Nat := 937656753562250531502013

theorem tailTrace_5478240 : CollatzResearch.WordTrace tailWord_5478240 prefixEnd_5478240 937656753562250531502013 := by
  unfold tailWord_5478240
  simp only [CollatzResearch.WordTrace]
  refine ⟨99903913836639781874740087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133205218448853042499653449 99903913836639781874740087)
  ·
    refine ⟨149855870754959672812110131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99903913836639781874740087 149855870754959672812110131)
    ·
      refine ⟨224783806132439509218165197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149855870754959672812110131 224783806132439509218165197)
      ·
        refine ⟨84293927299664815956811949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224783806132439509218165197 84293927299664815956811949)
        ·
          refine ⟨31610222737374305983804481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84293927299664815956811949 31610222737374305983804481)
          ·
            refine ⟨23707667053030729487853361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31610222737374305983804481 23707667053030729487853361)
            ·
              refine ⟨17780750289773047115890021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23707667053030729487853361 17780750289773047115890021)
              ·
                refine ⟨3333890679332446334229379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17780750289773047115890021 3333890679332446334229379)
                ·
                  refine ⟨5000836018998669501344069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3333890679332446334229379 5000836018998669501344069)
                  ·
                    refine ⟨937656753562250531502013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5000836018998669501344069 937656753562250531502013)
                    ·
                      rfl

theorem cell23_5478240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 4, 1, 4].length) (baseStart_5478240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478240 prefixEnd_5478240 := by exact prefixLift 5478240
  have htrace : WordTrace (prefixWord ++ tailWord_5478240) baseStart_5478240 baseEnd_5478240 := by
    simpa [prefixWord, tailWord_5478240, baseEnd_5478240] using wordTrace_append hprefix tailTrace_5478240
  have hstable : (prefixWord ++ tailWord_5478240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478240).length < 2 ^ (prefixWord ++ tailWord_5478240).sum := by decide
  have hdescent : baseEnd_5478240 < baseStart_5478240 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478266 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 3, 5]
def baseStart_5478266 : Nat := 118140960795 + 5478266 * 2 ^ 59
def prefixEnd_5478266 : Nat := 4983230072969 + 3 ^ 40 * 5478266 * 2
def baseEnd_5478266 : Nat := 937661203727922830926973

theorem tailTrace_5478266 : CollatzResearch.WordTrace tailWord_5478266 prefixEnd_5478266 937661203727922830926973 := by
  unfold tailWord_5478266
  simp only [CollatzResearch.WordTrace]
  refine ⟨49952193992796342547481663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133205850647456913459951101 49952193992796342547481663)
  ·
    refine ⟨74928290989194513821222495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49952193992796342547481663 74928290989194513821222495)
    ·
      refine ⟨112392436483791770731833743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74928290989194513821222495 112392436483791770731833743)
      ·
        refine ⟨168588654725687656097750615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112392436483791770731833743 168588654725687656097750615)
        ·
          refine ⟨252882982088531484146625923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168588654725687656097750615 252882982088531484146625923)
          ·
            refine ⟨379324473132797226219938885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252882982088531484146625923 379324473132797226219938885)
            ·
              refine ⟨71123338712399479916238541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 379324473132797226219938885 71123338712399479916238541)
              ·
                refine ⟨26671252017149804968589453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71123338712399479916238541 26671252017149804968589453)
                ·
                  refine ⟨10001719506431176863221045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26671252017149804968589453 10001719506431176863221045)
                  ·
                    refine ⟨937661203727922830926973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10001719506431176863221045 937661203727922830926973)
                    ·
                      rfl

theorem cell23_5478266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 3, 5].length) (baseStart_5478266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478266 prefixEnd_5478266 := by exact prefixLift 5478266
  have htrace : WordTrace (prefixWord ++ tailWord_5478266) baseStart_5478266 baseEnd_5478266 := by
    simpa [prefixWord, tailWord_5478266, baseEnd_5478266] using wordTrace_append hprefix tailTrace_5478266
  have hstable : (prefixWord ++ tailWord_5478266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478266).length < 2 ^ (prefixWord ++ tailWord_5478266).sum := by decide
  have hdescent : baseEnd_5478266 < baseStart_5478266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478323 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 3]
def baseStart_5478323 : Nat := 118140960795 + 5478323 * 2 ^ 59
def prefixEnd_5478323 : Nat := 4983230072969 + 3 ^ 40 * 5478323 * 2
def baseEnd_5478323 : Nat := 2813012879581074769768157

theorem tailTrace_5478323 : CollatzResearch.WordTrace tailWord_5478323 prefixEnd_5478323 2813012879581074769768157 := by
  unfold tailWord_5478323
  simp only [CollatzResearch.WordTrace]
  refine ⟨199810854931978868924751623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133207236621319245949834415 199810854931978868924751623)
  ·
    refine ⟨299716282397968303387127435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199810854931978868924751623 299716282397968303387127435)
    ·
      refine ⟨449574423596952455080691153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299716282397968303387127435 449574423596952455080691153)
      ·
        refine ⟨337180817697714341310518365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 449574423596952455080691153 337180817697714341310518365)
        ·
          refine ⟨126442806636642877991444387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 337180817697714341310518365 126442806636642877991444387)
          ·
            refine ⟨189664209954964316987166581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126442806636642877991444387 189664209954964316987166581)
            ·
              refine ⟨17781019683277904717546867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 189664209954964316987166581 17781019683277904717546867)
              ·
                refine ⟨26671529524916857076320301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17781019683277904717546867 26671529524916857076320301)
                ·
                  refine ⟨10001823571843821403620113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26671529524916857076320301 10001823571843821403620113)
                  ·
                    refine ⟨7501367678882866052715085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10001823571843821403620113 7501367678882866052715085)
                    ·
                      refine ⟨2813012879581074769768157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7501367678882866052715085 2813012879581074769768157)
                      ·
                        rfl

theorem cell23_5478323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 3, 2, 3].length) (baseStart_5478323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478323 prefixEnd_5478323 := by exact prefixLift 5478323
  have htrace : WordTrace (prefixWord ++ tailWord_5478323) baseStart_5478323 baseEnd_5478323 := by
    simpa [prefixWord, tailWord_5478323, baseEnd_5478323] using wordTrace_append hprefix tailTrace_5478323
  have hstable : (prefixWord ++ tailWord_5478323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478323).length < 2 ^ (prefixWord ++ tailWord_5478323).sum := by decide
  have hdescent : baseEnd_5478323 < baseStart_5478323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478333 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 3, 2, 4]
def baseStart_5478333 : Nat := 118140960795 + 5478333 * 2 ^ 59
def prefixEnd_5478333 : Nat := 4983230072969 + 3 ^ 40 * 5478333 * 2
def baseEnd_5478333 : Nat := 2813018014387619730643111

theorem tailTrace_5478333 : CollatzResearch.WordTrace tailWord_5478333 prefixEnd_5478333 2813018014387619730643111 := by
  unfold tailWord_5478333
  simp only [CollatzResearch.WordTrace]
  refine ⟨199811219661942640632615653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133207479774628427088410435 199811219661942640632615653)
  ·
    refine ⟨37464603686614245118615435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199811219661942640632615653 37464603686614245118615435)
    ·
      refine ⟨56196905529921367677923153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37464603686614245118615435 56196905529921367677923153)
      ·
        refine ⟨42147679147441025758442365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56196905529921367677923153 42147679147441025758442365)
        ·
          refine ⟨15805379680290384659415887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42147679147441025758442365 15805379680290384659415887)
          ·
            refine ⟨23708069520435576989123831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15805379680290384659415887 23708069520435576989123831)
            ·
              refine ⟨35562104280653365483685747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23708069520435576989123831 35562104280653365483685747)
              ·
                refine ⟨53343156420980048225528621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35562104280653365483685747 53343156420980048225528621)
                ·
                  refine ⟨20003683657867518084573233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 53343156420980048225528621 20003683657867518084573233)
                  ·
                    refine ⟨15002762743400638563429925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20003683657867518084573233 15002762743400638563429925)
                    ·
                      refine ⟨2813018014387619730643111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15002762743400638563429925 2813018014387619730643111)
                      ·
                        rfl

theorem cell23_5478333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 3, 2, 4].length) (baseStart_5478333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478333 prefixEnd_5478333 := by exact prefixLift 5478333
  have htrace : WordTrace (prefixWord ++ tailWord_5478333) baseStart_5478333 baseEnd_5478333 := by
    simpa [prefixWord, tailWord_5478333, baseEnd_5478333] using wordTrace_append hprefix tailTrace_5478333
  have hstable : (prefixWord ++ tailWord_5478333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478333).length < 2 ^ (prefixWord ++ tailWord_5478333).sum := by decide
  have hdescent : baseEnd_5478333 < baseStart_5478333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478364 : List Nat := [2, 2, 6, 1, 1, 1, 2, 1, 1, 6]
def baseStart_5478364 : Nat := 118140960795 + 5478364 * 2 ^ 59
def prefixEnd_5478364 : Nat := 4983230072969 + 3 ^ 40 * 5478364 * 2
def baseEnd_5478364 : Nat := 937677977429303036451823

theorem tailTrace_5478364 : CollatzResearch.WordTrace tailWord_5478364 prefixEnd_5478364 937677977429303036451823 := by
  unfold tailWord_5478364
  simp only [CollatzResearch.WordTrace]
  refine ⟨99906175162415166463497073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133208233549886888617996097 99906175162415166463497073)
  ·
    refine ⟨74929631371811374847622805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99906175162415166463497073 74929631371811374847622805)
    ·
      refine ⟨3512326470553658195982319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74929631371811374847622805 3512326470553658195982319)
      ·
        refine ⟨5268489705830487293973479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3512326470553658195982319 5268489705830487293973479)
        ·
          refine ⟨7902734558745730940960219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5268489705830487293973479 7902734558745730940960219)
          ·
            refine ⟨11854101838118596411440329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7902734558745730940960219 11854101838118596411440329)
            ·
              refine ⟨8890576378588947308580247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11854101838118596411440329 8890576378588947308580247)
              ·
                refine ⟨13335864567883420962870371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8890576378588947308580247 13335864567883420962870371)
                ·
                  refine ⟨20003796851825131444305557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13335864567883420962870371 20003796851825131444305557)
                  ·
                    refine ⟨937677977429303036451823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20003796851825131444305557 937677977429303036451823)
                    ·
                      rfl

theorem cell23_5478364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_5478364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478364 prefixEnd_5478364 := by exact prefixLift 5478364
  have htrace : WordTrace (prefixWord ++ tailWord_5478364) baseStart_5478364 baseEnd_5478364 := by
    simpa [prefixWord, tailWord_5478364, baseEnd_5478364] using wordTrace_append hprefix tailTrace_5478364
  have hstable : (prefixWord ++ tailWord_5478364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478364).length < 2 ^ (prefixWord ++ tailWord_5478364).sum := by decide
  have hdescent : baseEnd_5478364 < baseStart_5478364 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478404 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 4, 1, 3]
def baseStart_5478404 : Nat := 118140960795 + 5478404 * 2 ^ 59
def prefixEnd_5478404 : Nat := 4983230072969 + 3 ^ 40 * 5478404 * 2
def baseEnd_5478404 : Nat := 2813054471514088952855285

theorem tailTrace_5478404 : CollatzResearch.WordTrace tailWord_5478404 prefixEnd_5478404 2813054471514088952855285 := by
  unfold tailWord_5478404
  simp only [CollatzResearch.WordTrace]
  refine ⟨99906904622342709879225133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133209206163123613172300177 99906904622342709879225133)
  ·
    refine ⟨37465089233378516204709425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99906904622342709879225133 37465089233378516204709425)
    ·
      refine ⟨28098816925033887153532069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37465089233378516204709425 28098816925033887153532069)
      ·
        refine ⟨5268528173443853841287263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28098816925033887153532069 5268528173443853841287263)
        ·
          refine ⟨7902792260165780761930895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5268528173443853841287263 7902792260165780761930895)
          ·
            refine ⟨11854188390248671142896343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7902792260165780761930895 11854188390248671142896343)
            ·
              refine ⟨17781282585373006714344515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11854188390248671142896343 17781282585373006714344515)
              ·
                refine ⟨26671923878059510071516773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17781282585373006714344515 26671923878059510071516773)
                ·
                  refine ⟨5000985727136158138409395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26671923878059510071516773 5000985727136158138409395)
                  ·
                    refine ⟨7501478590704237207614093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5000985727136158138409395 7501478590704237207614093)
                    ·
                      refine ⟨2813054471514088952855285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7501478590704237207614093 2813054471514088952855285)
                      ·
                        rfl

theorem cell23_5478404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 4, 1, 3].length) (baseStart_5478404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478404 prefixEnd_5478404 := by exact prefixLift 5478404
  have htrace : WordTrace (prefixWord ++ tailWord_5478404) baseStart_5478404 baseEnd_5478404 := by
    simpa [prefixWord, tailWord_5478404, baseEnd_5478404] using wordTrace_append hprefix tailTrace_5478404
  have hstable : (prefixWord ++ tailWord_5478404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478404).length < 2 ^ (prefixWord ++ tailWord_5478404).sum := by decide
  have hdescent : baseEnd_5478404 < baseStart_5478404 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478416 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 11]
def baseStart_5478416 : Nat := 118140960795 + 5478416 * 2 ^ 59
def prefixEnd_5478416 : Nat := 4983230072969 + 3 ^ 40 * 5478416 * 2
def baseEnd_5478416 : Nat := 312562292586882545100581

theorem tailTrace_5478416 : CollatzResearch.WordTrace tailWord_5478416 prefixEnd_5478416 312562292586882545100581 := by
  unfold tailWord_5478416
  simp only [CollatzResearch.WordTrace]
  refine ⟨99907123460320972903943551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133209497947094630538591401 99907123460320972903943551)
  ·
    refine ⟨149860685190481459355915327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99907123460320972903943551 149860685190481459355915327)
    ·
      refine ⟨224791027785722189033872991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149860685190481459355915327 224791027785722189033872991)
      ·
        refine ⟨337186541678583283550809487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224791027785722189033872991 337186541678583283550809487)
        ·
          refine ⟨505779812517874925326214231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337186541678583283550809487 505779812517874925326214231)
          ·
            refine ⟨758669718776812387989321347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505779812517874925326214231 758669718776812387989321347)
            ·
              refine ⟨1138004578165218581983982021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 758669718776812387989321347 1138004578165218581983982021)
              ·
                refine ⟨213375858405978484121996629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1138004578165218581983982021 213375858405978484121996629)
                ·
                  refine ⟨312562292586882545100581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 213375858405978484121996629 312562292586882545100581)
                  ·
                    rfl

theorem cell23_5478416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 11].length) (baseStart_5478416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478416 prefixEnd_5478416 := by exact prefixLift 5478416
  have htrace : WordTrace (prefixWord ++ tailWord_5478416) baseStart_5478416 baseEnd_5478416 := by
    simpa [prefixWord, tailWord_5478416, baseEnd_5478416] using wordTrace_append hprefix tailTrace_5478416
  have hstable : (prefixWord ++ tailWord_5478416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478416).length < 2 ^ (prefixWord ++ tailWord_5478416).sum := by decide
  have hdescent : baseEnd_5478416 < baseStart_5478416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478443 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 3]
def baseStart_5478443 : Nat := 118140960795 + 5478443 * 2 ^ 59
def prefixEnd_5478443 : Nat := 4983230072969 + 3 ^ 40 * 5478443 * 2
def baseEnd_5478443 : Nat := 2813074497259614300267605

theorem tailTrace_5478443 : CollatzResearch.WordTrace tailWord_5478443 prefixEnd_5478443 2813074497259614300267605 := by
  unfold tailWord_5478443
  simp only [CollatzResearch.WordTrace]
  refine ⟨199815231691544129419119983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133210154461029419612746655 199815231691544129419119983)
  ·
    refine ⟨299722847537316194128679975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199815231691544129419119983 299722847537316194128679975)
    ·
      refine ⟨449584271305974291193019963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299722847537316194128679975 449584271305974291193019963)
      ·
        refine ⟨674376406958961436789529945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449584271305974291193019963 674376406958961436789529945)
        ·
          refine ⟨505782305219221077592147459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 674376406958961436789529945 505782305219221077592147459)
          ·
            refine ⟨758673457828831616388221189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505782305219221077592147459 758673457828831616388221189)
            ·
              refine ⟨142251273342905928072791473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 758673457828831616388221189 142251273342905928072791473)
              ·
                refine ⟨106688455007179446054593605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 142251273342905928072791473 106688455007179446054593605)
                ·
                  refine ⟨20004085313846146135236301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106688455007179446054593605 20004085313846146135236301)
                  ·
                    refine ⟨7501531992692304800713613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20004085313846146135236301 7501531992692304800713613)
                    ·
                      refine ⟨2813074497259614300267605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7501531992692304800713613 2813074497259614300267605)
                      ·
                        rfl

theorem cell23_5478443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 4, 3, 3].length) (baseStart_5478443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478443 prefixEnd_5478443 := by exact prefixLift 5478443
  have htrace : WordTrace (prefixWord ++ tailWord_5478443) baseStart_5478443 baseEnd_5478443 := by
    simpa [prefixWord, tailWord_5478443, baseEnd_5478443] using wordTrace_append hprefix tailTrace_5478443
  have hstable : (prefixWord ++ tailWord_5478443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478443).length < 2 ^ (prefixWord ++ tailWord_5478443).sum := by decide
  have hdescent : baseEnd_5478443 < baseStart_5478443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478463 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 4, 5]
def baseStart_5478463 : Nat := 118140960795 + 5478463 * 2 ^ 59
def prefixEnd_5478463 : Nat := 4983230072969 + 3 ^ 40 * 5478463 * 2
def baseEnd_5478463 : Nat := 937694922290901407339171

theorem tailTrace_5478463 : CollatzResearch.WordTrace tailWord_5478463 prefixEnd_5478463 937694922290901407339171 := by
  unfold tailWord_5478463
  simp only [CollatzResearch.WordTrace]
  refine ⟨199815961151471672834848043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133210640767647781889898695 199815961151471672834848043)
  ·
    refine ⟨299723941727207509252272065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199815961151471672834848043 299723941727207509252272065)
    ·
      refine ⟨224792956295405631939204049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299723941727207509252272065 224792956295405631939204049)
      ·
        refine ⟨168594717221554223954403037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224792956295405631939204049 168594717221554223954403037)
        ·
          refine ⟨63223018958082833982901139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168594717221554223954403037 63223018958082833982901139)
          ·
            refine ⟨94834528437124250974351709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63223018958082833982901139 94834528437124250974351709)
            ·
              refine ⟨35562948163921594115381891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94834528437124250974351709 35562948163921594115381891)
              ·
                refine ⟨53344422245882391173072837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35562948163921594115381891 53344422245882391173072837)
                ·
                  refine ⟨10002079171102948344951157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53344422245882391173072837 10002079171102948344951157)
                  ·
                    refine ⟨937694922290901407339171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10002079171102948344951157 937694922290901407339171)
                    ·
                      rfl

theorem cell23_5478463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 4, 5].length) (baseStart_5478463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478463 prefixEnd_5478463 := by exact prefixLift 5478463
  have htrace : WordTrace (prefixWord ++ tailWord_5478463) baseStart_5478463 baseEnd_5478463 := by
    simpa [prefixWord, tailWord_5478463, baseEnd_5478463] using wordTrace_append hprefix tailTrace_5478463
  have hstable : (prefixWord ++ tailWord_5478463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478463).length < 2 ^ (prefixWord ++ tailWord_5478463).sum := by decide
  have hdescent : baseEnd_5478463 < baseStart_5478463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478473 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 1, 2, 5]
def baseStart_5478473 : Nat := 118140960795 + 5478473 * 2 ^ 59
def prefixEnd_5478473 : Nat := 4983230072969 + 3 ^ 40 * 5478473 * 2
def baseEnd_5478473 : Nat := 2813089901679249182892467

theorem tailTrace_5478473 : CollatzResearch.WordTrace tailWord_5478473 prefixEnd_5478473 2813089901679249182892467 := by
  unfold tailWord_5478473
  simp only [CollatzResearch.WordTrace]
  refine ⟨199816325881435444542712073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133210883920956963028474715 199816325881435444542712073)
  ·
    refine ⟨149862244411076583407034055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199816325881435444542712073 149862244411076583407034055)
    ·
      refine ⟨224793366616614875110551083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149862244411076583407034055 224793366616614875110551083)
      ·
        refine ⟨337190049924922312665826625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224793366616614875110551083 337190049924922312665826625)
        ·
          refine ⟨252892537443691734499369969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337190049924922312665826625 252892537443691734499369969)
          ·
            refine ⟨189669403082768800874527477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252892537443691734499369969 189669403082768800874527477)
            ·
              refine ⟨17781506539009575081986951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 189669403082768800874527477 17781506539009575081986951)
              ·
                refine ⟨26672259808514362622980427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17781506539009575081986951 26672259808514362622980427)
                ·
                  refine ⟨40008389712771543934470641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26672259808514362622980427 40008389712771543934470641)
                  ·
                    refine ⟨30006292284578657950852981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40008389712771543934470641 30006292284578657950852981)
                    ·
                      refine ⟨2813089901679249182892467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30006292284578657950852981 2813089901679249182892467)
                      ·
                        rfl

theorem cell23_5478473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 1, 2, 5].length) (baseStart_5478473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478473 prefixEnd_5478473 := by exact prefixLift 5478473
  have htrace : WordTrace (prefixWord ++ tailWord_5478473) baseStart_5478473 baseEnd_5478473 := by
    simpa [prefixWord, tailWord_5478473, baseEnd_5478473] using wordTrace_append hprefix tailTrace_5478473
  have hstable : (prefixWord ++ tailWord_5478473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478473).length < 2 ^ (prefixWord ++ tailWord_5478473).sum := by decide
  have hdescent : baseEnd_5478473 < baseStart_5478473 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478500 : List Nat := [2, 3, 1, 1, 2, 1, 3, 3, 2, 1, 4]
def baseStart_5478500 : Nat := 118140960795 + 5478500 * 2 ^ 59
def prefixEnd_5478500 : Nat := 4983230072969 + 3 ^ 40 * 5478500 * 2
def baseEnd_5478500 : Nat := 2813103765656920577254843

theorem tailTrace_5478500 : CollatzResearch.WordTrace tailWord_5478500 prefixEnd_5478500 2813103765656920577254843 := by
  unfold tailWord_5478500
  simp only [CollatzResearch.WordTrace]
  refine ⟨99908655326168814076972477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133211540434891752102629969 99908655326168814076972477)
  ·
    refine ⟨37465745747313305278864679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99908655326168814076972477 37465745747313305278864679)
    ·
      refine ⟨56198618620969957918297019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37465745747313305278864679 56198618620969957918297019)
      ·
        refine ⟨84297927931454936877445529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56198618620969957918297019 84297927931454936877445529)
        ·
          refine ⟨63223445948591202658084147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84297927931454936877445529 63223445948591202658084147)
          ·
            refine ⟨94835168922886803987126221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63223445948591202658084147 94835168922886803987126221)
            ·
              refine ⟨35563188346082551495172333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94835168922886803987126221 35563188346082551495172333)
              ·
                refine ⟨13336195629780956810689625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35563188346082551495172333 13336195629780956810689625)
                ·
                  refine ⟨10002146722335717608017219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13336195629780956810689625 10002146722335717608017219)
                  ·
                    refine ⟨15003220083503576412025829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10002146722335717608017219 15003220083503576412025829)
                    ·
                      refine ⟨2813103765656920577254843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15003220083503576412025829 2813103765656920577254843)
                      ·
                        rfl

theorem cell23_5478500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_5478500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478500 prefixEnd_5478500 := by exact prefixLift 5478500
  have htrace : WordTrace (prefixWord ++ tailWord_5478500) baseStart_5478500 baseEnd_5478500 := by
    simpa [prefixWord, tailWord_5478500, baseEnd_5478500] using wordTrace_append hprefix tailTrace_5478500
  have hstable : (prefixWord ++ tailWord_5478500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478500).length < 2 ^ (prefixWord ++ tailWord_5478500).sum := by decide
  have hdescent : baseEnd_5478500 < baseStart_5478500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478513 : List Nat := [1, 2, 2, 2, 1, 1, 4, 1, 2, 1, 6]
def baseStart_5478513 : Nat := 118140960795 + 5478513 * 2 ^ 59
def prefixEnd_5478513 : Nat := 4983230072969 + 3 ^ 40 * 5478513 * 2
def baseEnd_5478513 : Nat := 2813110440905429026392283

theorem tailTrace_5478513 : CollatzResearch.WordTrace tailWord_5478513 prefixEnd_5478513 2813110440905429026392283 := by
  unfold tailWord_5478513
  simp only [CollatzResearch.WordTrace]
  refine ⟨199817784801290531374168193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133211856534193687582778795 199817784801290531374168193)
  ·
    refine ⟨149863338600967898530626145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199817784801290531374168193 149863338600967898530626145)
    ·
      refine ⟨112397503950725923897969609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149863338600967898530626145 112397503950725923897969609)
      ·
        refine ⟨84298127963044442923477207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112397503950725923897969609 84298127963044442923477207)
        ·
          refine ⟨126447191944566664385215811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84298127963044442923477207 126447191944566664385215811)
          ·
            refine ⟨189670787916849996577823717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126447191944566664385215811 189670787916849996577823717)
            ·
              refine ⟨35563272734409374358341947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189670787916849996577823717 35563272734409374358341947)
              ·
                refine ⟨53344909101614061537512921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35563272734409374358341947 53344909101614061537512921)
                ·
                  refine ⟨40008681826210546153134691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 53344909101614061537512921 40008681826210546153134691)
                  ·
                    refine ⟨60013022739315819229702037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40008681826210546153134691 60013022739315819229702037)
                    ·
                      refine ⟨2813110440905429026392283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60013022739315819229702037 2813110440905429026392283)
                      ·
                        rfl

theorem cell23_5478513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 2, 1, 6].length) (baseStart_5478513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478513 prefixEnd_5478513 := by exact prefixLift 5478513
  have htrace : WordTrace (prefixWord ++ tailWord_5478513) baseStart_5478513 baseEnd_5478513 := by
    simpa [prefixWord, tailWord_5478513, baseEnd_5478513] using wordTrace_append hprefix tailTrace_5478513
  have hstable : (prefixWord ++ tailWord_5478513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478513).length < 2 ^ (prefixWord ++ tailWord_5478513).sum := by decide
  have hdescent : baseEnd_5478513 < baseStart_5478513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478563 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 5]
def baseStart_5478563 : Nat := 118140960795 + 5478563 * 2 ^ 59
def prefixEnd_5478563 : Nat := 4983230072969 + 3 ^ 40 * 5478563 * 2
def baseEnd_5478563 : Nat := 2813136114938153830767053

theorem tailTrace_5478563 : CollatzResearch.WordTrace tailWord_5478563 prefixEnd_5478563 2813136114938153830767053 := by
  unfold tailWord_5478563
  simp only [CollatzResearch.WordTrace]
  refine ⟨199819608451109389913488343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133213072300739593275658895 199819608451109389913488343)
  ·
    refine ⟨299729412676664084870232515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199819608451109389913488343 299729412676664084870232515)
    ·
      refine ⟨449594119014996127305348773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299729412676664084870232515 449594119014996127305348773)
      ·
        refine ⟨84298897315311773869752895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 449594119014996127305348773 84298897315311773869752895)
        ·
          refine ⟨126448345972967660804629343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84298897315311773869752895 126448345972967660804629343)
          ·
            refine ⟨189672518959451491206944015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126448345972967660804629343 189672518959451491206944015)
            ·
              refine ⟨284508778439177236810416023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189672518959451491206944015 284508778439177236810416023)
              ·
                refine ⟨426763167658765855215624035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284508778439177236810416023 426763167658765855215624035)
                ·
                  refine ⟨640144751488148782823436053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 426763167658765855215624035 640144751488148782823436053)
                  ·
                    refine ⟨30006785226006974194848565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 640144751488148782823436053 30006785226006974194848565)
                    ·
                      refine ⟨2813136114938153830767053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30006785226006974194848565 2813136114938153830767053)
                      ·
                        rfl

theorem cell23_5478563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 6, 5].length) (baseStart_5478563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478563 prefixEnd_5478563 := by exact prefixLift 5478563
  have htrace : WordTrace (prefixWord ++ tailWord_5478563) baseStart_5478563 baseEnd_5478563 := by
    simpa [prefixWord, tailWord_5478563, baseEnd_5478563] using wordTrace_append hprefix tailTrace_5478563
  have hstable : (prefixWord ++ tailWord_5478563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478563).length < 2 ^ (prefixWord ++ tailWord_5478563).sum := by decide
  have hdescent : baseEnd_5478563 < baseStart_5478563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478574 : List Nat := [4, 1, 4, 2, 1, 1, 1, 1, 8]
def baseStart_5478574 : Nat := 118140960795 + 5478574 * 2 ^ 59
def prefixEnd_5478574 : Nat := 4983230072969 + 3 ^ 40 * 5478574 * 2
def baseEnd_5478574 : Nat := 312571307025039254192167

theorem tailTrace_5478574 : CollatzResearch.WordTrace tailWord_5478574 prefixEnd_5478574 312571307025039254192167 := by
  unfold tailWord_5478574
  simp only [CollatzResearch.WordTrace]
  refine ⟨24977501206758692349017347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133213339769379692528092517 24977501206758692349017347)
  ·
    refine ⟨37466251810138038523526021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24977501206758692349017347 37466251810138038523526021)
    ·
      refine ⟨7024922214400882223161129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37466251810138038523526021 7024922214400882223161129)
      ·
        refine ⟨5268691660800661667370847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7024922214400882223161129 5268691660800661667370847)
        ·
          refine ⟨7903037491200992501056271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5268691660800661667370847 7903037491200992501056271)
          ·
            refine ⟨11854556236801488751584407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7903037491200992501056271 11854556236801488751584407)
            ·
              refine ⟨17781834355202233127376611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11854556236801488751584407 17781834355202233127376611)
              ·
                refine ⟨26672751532803349691064917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17781834355202233127376611 26672751532803349691064917)
                ·
                  refine ⟨312571307025039254192167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26672751532803349691064917 312571307025039254192167)
                  ·
                    rfl

theorem cell23_5478574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 1, 8].length) (baseStart_5478574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478574 prefixEnd_5478574 := by exact prefixLift 5478574
  have htrace : WordTrace (prefixWord ++ tailWord_5478574) baseStart_5478574 baseEnd_5478574 := by
    simpa [prefixWord, tailWord_5478574, baseEnd_5478574] using wordTrace_append hprefix tailTrace_5478574
  have hstable : (prefixWord ++ tailWord_5478574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478574).length < 2 ^ (prefixWord ++ tailWord_5478574).sum := by decide
  have hdescent : baseEnd_5478574 < baseStart_5478574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478584 : List Nat := [2, 1, 2, 1, 2, 1, 3, 6, 1, 1, 3]
def baseStart_5478584 : Nat := 118140960795 + 5478584 * 2 ^ 59
def prefixEnd_5478584 : Nat := 4983230072969 + 3 ^ 40 * 5478584 * 2
def baseEnd_5478584 : Nat := 2813146898031898248604457

theorem tailTrace_5478584 : CollatzResearch.WordTrace tailWord_5478584 prefixEnd_5478584 2813146898031898248604457 := by
  unfold tailWord_5478584
  simp only [CollatzResearch.WordTrace]
  refine ⟨99910187192016655250001403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133213582922688873666668537 99910187192016655250001403)
  ·
    refine ⟨149865280788024982875002105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99910187192016655250001403 149865280788024982875002105)
    ·
      refine ⟨112398960591018737156251579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149865280788024982875002105 112398960591018737156251579)
      ·
        refine ⟨168598440886528105734377369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112398960591018737156251579 168598440886528105734377369)
        ·
          refine ⟨126448830664896079300783027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168598440886528105734377369 126448830664896079300783027)
          ·
            refine ⟨189673245997344118951174541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126448830664896079300783027 189673245997344118951174541)
            ·
              refine ⟨71127467249004044606690453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189673245997344118951174541 71127467249004044606690453)
              ·
                refine ⟨3334100027297064590938615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71127467249004044606690453 3334100027297064590938615)
                ·
                  refine ⟨5001150040945596886407923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3334100027297064590938615 5001150040945596886407923)
                  ·
                    refine ⟨7501725061418395329611885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5001150040945596886407923 7501725061418395329611885)
                    ·
                      refine ⟨2813146898031898248604457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7501725061418395329611885 2813146898031898248604457)
                      ·
                        rfl

theorem cell23_5478584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 1, 1, 3].length) (baseStart_5478584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478584 prefixEnd_5478584 := by exact prefixLift 5478584
  have htrace : WordTrace (prefixWord ++ tailWord_5478584) baseStart_5478584 baseEnd_5478584 := by
    simpa [prefixWord, tailWord_5478584, baseEnd_5478584] using wordTrace_append hprefix tailTrace_5478584
  have hstable : (prefixWord ++ tailWord_5478584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478584).length < 2 ^ (prefixWord ++ tailWord_5478584).sum := by decide
  have hdescent : baseEnd_5478584 < baseStart_5478584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478607 : List Nat := [1, 1, 2, 1, 1, 3, 6, 2, 1, 1, 4]
def baseStart_5478607 : Nat := 118140960795 + 5478607 * 2 ^ 59
def prefixEnd_5478607 : Nat := 4983230072969 + 3 ^ 40 * 5478607 * 2
def baseEnd_5478607 : Nat := 2813158708086951658616851

theorem tailTrace_5478607 : CollatzResearch.WordTrace tailWord_5478607 prefixEnd_5478607 2813158708086951658616851 := by
  unfold tailWord_5478607
  simp only [CollatzResearch.WordTrace]
  refine ⟨199821213262949985428090075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133214142175299990285393383 199821213262949985428090075)
  ·
    refine ⟨299731819894424978142135113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199821213262949985428090075 299731819894424978142135113)
    ·
      refine ⟨224798864920818733606601335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299731819894424978142135113 224798864920818733606601335)
      ·
        refine ⟨337198297381228100409902003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224798864920818733606601335 337198297381228100409902003)
        ·
          refine ⟨505797446071842150614853005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337198297381228100409902003 505797446071842150614853005)
          ·
            refine ⟨189674042276940806480569877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 505797446071842150614853005 189674042276940806480569877)
            ·
              refine ⟨8890970731731600303776713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 189674042276940806480569877 8890970731731600303776713)
              ·
                refine ⟨6668228048798700227832535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8890970731731600303776713 6668228048798700227832535)
                ·
                  refine ⟨10002342073198050341748803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6668228048798700227832535 10002342073198050341748803)
                  ·
                    refine ⟨15003513109797075512623205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10002342073198050341748803 15003513109797075512623205)
                    ·
                      refine ⟨2813158708086951658616851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15003513109797075512623205 2813158708086951658616851)
                      ·
                        rfl

theorem cell23_5478607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 2, 1, 1, 4].length) (baseStart_5478607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478607 prefixEnd_5478607 := by exact prefixLift 5478607
  have htrace : WordTrace (prefixWord ++ tailWord_5478607) baseStart_5478607 baseEnd_5478607 := by
    simpa [prefixWord, tailWord_5478607, baseEnd_5478607] using wordTrace_append hprefix tailTrace_5478607
  have hstable : (prefixWord ++ tailWord_5478607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478607).length < 2 ^ (prefixWord ++ tailWord_5478607).sum := by decide
  have hdescent : baseEnd_5478607 < baseStart_5478607 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478641 : List Nat := [1, 2, 2, 2, 2, 1, 2, 6, 1, 2, 2]
def baseStart_5478641 : Nat := 118140960795 + 5478641 * 2 ^ 59
def prefixEnd_5478641 : Nat := 4983230072969 + 3 ^ 40 * 5478641 * 2
def baseEnd_5478641 : Nat := 2813176166429204525591695

theorem tailTrace_5478641 : CollatzResearch.WordTrace tailWord_5478641 prefixEnd_5478641 2813176166429204525591695 := by
  unfold tailWord_5478641
  simp only [CollatzResearch.WordTrace]
  refine ⟨199822453344826809234827777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133214968896551206156551851 199822453344826809234827777)
  ·
    refine ⟨149866840008620106926120833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199822453344826809234827777 149866840008620106926120833)
    ·
      refine ⟨112400130006465080194590625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149866840008620106926120833 112400130006465080194590625)
      ·
        refine ⟨84300097504848810145942969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112400130006465080194590625 84300097504848810145942969)
        ·
          refine ⟨63225073128636607609457227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84300097504848810145942969 63225073128636607609457227)
          ·
            refine ⟨94837609692954911414185841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63225073128636607609457227 94837609692954911414185841)
            ·
              refine ⟨71128207269716183560639381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94837609692954911414185841 71128207269716183560639381)
              ·
                refine ⟨3334134715767946104404971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71128207269716183560639381 3334134715767946104404971)
                ·
                  refine ⟨5001202073651919156607457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3334134715767946104404971 5001202073651919156607457)
                  ·
                    refine ⟨3750901555238939367455593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5001202073651919156607457 3750901555238939367455593)
                    ·
                      refine ⟨2813176166429204525591695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3750901555238939367455593 2813176166429204525591695)
                      ·
                        rfl

theorem cell23_5478641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 6, 1, 2, 2].length) (baseStart_5478641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478641 prefixEnd_5478641 := by exact prefixLift 5478641
  have htrace : WordTrace (prefixWord ++ tailWord_5478641) baseStart_5478641 baseEnd_5478641 := by
    simpa [prefixWord, tailWord_5478641, baseEnd_5478641] using wordTrace_append hprefix tailTrace_5478641
  have hstable : (prefixWord ++ tailWord_5478641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478641).length < 2 ^ (prefixWord ++ tailWord_5478641).sum := by decide
  have hdescent : baseEnd_5478641 < baseStart_5478641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478657 : List Nat := [1, 2, 4, 1, 1, 2, 2, 3, 1, 3, 3]
def baseStart_5478657 : Nat := 118140960795 + 5478657 * 2 ^ 59
def prefixEnd_5478657 : Nat := 4983230072969 + 3 ^ 40 * 5478657 * 2
def baseEnd_5478657 : Nat := 2813184382119676462991621

theorem tailTrace_5478657 : CollatzResearch.WordTrace tailWord_5478657 prefixEnd_5478657 2813184382119676462991621 := by
  unfold tailWord_5478657
  simp only [CollatzResearch.WordTrace]
  refine ⟨199823036912768843967410225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133215357941845895978273483 199823036912768843967410225)
  ·
    refine ⟨149867277684576632975557669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199823036912768843967410225 149867277684576632975557669)
    ·
      refine ⟨28100114565858118682917063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149867277684576632975557669 28100114565858118682917063)
      ·
        refine ⟨42150171848787178024375595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28100114565858118682917063 42150171848787178024375595)
        ·
          refine ⟨63225257773180767036563393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42150171848787178024375595 63225257773180767036563393)
          ·
            refine ⟨47418943329885575277422545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 63225257773180767036563393 47418943329885575277422545)
            ·
              refine ⟨35564207497414181458066909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47418943329885575277422545 35564207497414181458066909)
              ·
                refine ⟨13336577811530318046775091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35564207497414181458066909 13336577811530318046775091)
                ·
                  refine ⟨20004866717295477070162637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13336577811530318046775091 20004866717295477070162637)
                  ·
                    refine ⟨7501825018985803901310989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20004866717295477070162637 7501825018985803901310989)
                    ·
                      refine ⟨2813184382119676462991621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7501825018985803901310989 2813184382119676462991621)
                      ·
                        rfl

theorem cell23_5478657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_5478657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478657 prefixEnd_5478657 := by exact prefixLift 5478657
  have htrace : WordTrace (prefixWord ++ tailWord_5478657) baseStart_5478657 baseEnd_5478657 := by
    simpa [prefixWord, tailWord_5478657, baseEnd_5478657] using wordTrace_append hprefix tailTrace_5478657
  have hstable : (prefixWord ++ tailWord_5478657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478657).length < 2 ^ (prefixWord ++ tailWord_5478657).sum := by decide
  have hdescent : baseEnd_5478657 < baseStart_5478657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478700 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 5]
def baseStart_5478700 : Nat := 118140960795 + 5478700 * 2 ^ 59
def prefixEnd_5478700 : Nat := 4983230072969 + 3 ^ 40 * 5478700 * 2
def baseEnd_5478700 : Nat := 2813206461787819794753923

theorem tailTrace_5478700 : CollatzResearch.WordTrace tailWord_5478700 prefixEnd_5478700 2813206461787819794753923 := by
  unfold tailWord_5478700
  simp only [CollatzResearch.WordTrace]
  refine ⟨99912302625806531155612777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133216403501075374874150369 99912302625806531155612777)
  ·
    refine ⟨74934226969354898366709583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99912302625806531155612777 74934226969354898366709583)
    ·
      refine ⟨112401340454032347550064375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74934226969354898366709583 112401340454032347550064375)
      ·
        refine ⟨168602010681048521325096563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112401340454032347550064375 168602010681048521325096563)
        ·
          refine ⟨252903016021572781987644845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168602010681048521325096563 252903016021572781987644845)
          ·
            refine ⟨94838631008089793245366817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252903016021572781987644845 94838631008089793245366817)
            ·
              refine ⟨71128973256067344934025113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94838631008089793245366817 71128973256067344934025113)
              ·
                refine ⟨53346729942050508700518835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71128973256067344934025113 53346729942050508700518835)
                ·
                  refine ⟨80020094913075763050778253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53346729942050508700518835 80020094913075763050778253)
                  ·
                    refine ⟨30007535592403411144041845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80020094913075763050778253 30007535592403411144041845)
                    ·
                      refine ⟨2813206461787819794753923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30007535592403411144041845 2813206461787819794753923)
                      ·
                        rfl

theorem cell23_5478700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_5478700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478700 prefixEnd_5478700 := by exact prefixLift 5478700
  have htrace : WordTrace (prefixWord ++ tailWord_5478700) baseStart_5478700 baseEnd_5478700 := by
    simpa [prefixWord, tailWord_5478700, baseEnd_5478700] using wordTrace_append hprefix tailTrace_5478700
  have hstable : (prefixWord ++ tailWord_5478700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478700).length < 2 ^ (prefixWord ++ tailWord_5478700).sum := by decide
  have hdescent : baseEnd_5478700 < baseStart_5478700 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478714 : List Nat := [3, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2]
def baseStart_5478714 : Nat := 118140960795 + 5478714 * 2 ^ 59
def prefixEnd_5478714 : Nat := 4983230072969 + 3 ^ 40 * 5478714 * 2
def baseEnd_5478714 : Nat := 2813213650516982739978859

theorem tailTrace_5478714 : CollatzResearch.WordTrace tailWord_5478714 prefixEnd_5478714 2813213650516982739978859 := by
  unfold tailWord_5478714
  simp only [CollatzResearch.WordTrace]
  refine ⟨49956278968390585675558799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133216743915708228468156797 49956278968390585675558799)
  ·
    refine ⟨74934418452585878513338199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49956278968390585675558799 74934418452585878513338199)
    ·
      refine ⟨112401627678878817770007299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74934418452585878513338199 112401627678878817770007299)
      ·
        refine ⟨168602441518318226655010949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112401627678878817770007299 168602441518318226655010949)
        ·
          refine ⟨31612957784684667497814553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168602441518318226655010949 31612957784684667497814553)
          ·
            refine ⟨23709718338513500623360915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31612957784684667497814553 23709718338513500623360915)
            ·
              refine ⟨35564577507770250935041373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23709718338513500623360915 35564577507770250935041373)
              ·
                refine ⟨13336716565413844100640515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35564577507770250935041373 13336716565413844100640515)
                ·
                  refine ⟨20005074848120766150960773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13336716565413844100640515 20005074848120766150960773)
                  ·
                    refine ⟨3750951534022643653305145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20005074848120766150960773 3750951534022643653305145)
                    ·
                      refine ⟨2813213650516982739978859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3750951534022643653305145 2813213650516982739978859)
                      ·
                        rfl

theorem cell23_5478714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 3, 1, 4, 2].length) (baseStart_5478714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478714 prefixEnd_5478714 := by exact prefixLift 5478714
  have htrace : WordTrace (prefixWord ++ tailWord_5478714) baseStart_5478714 baseEnd_5478714 := by
    simpa [prefixWord, tailWord_5478714, baseEnd_5478714] using wordTrace_append hprefix tailTrace_5478714
  have hstable : (prefixWord ++ tailWord_5478714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478714).length < 2 ^ (prefixWord ++ tailWord_5478714).sum := by decide
  have hdescent : baseEnd_5478714 < baseStart_5478714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478730 : List Nat := [3, 1, 2, 1, 1, 1, 1, 1, 3, 2, 7]
def baseStart_5478730 : Nat := 118140960795 + 5478730 * 2 ^ 59
def prefixEnd_5478730 : Nat := 4983230072969 + 3 ^ 40 * 5478730 * 2
def baseEnd_5478730 : Nat := 2813221866207454677378785

theorem tailTrace_5478730 : CollatzResearch.WordTrace tailWord_5478730 prefixEnd_5478730 2813221866207454677378785 := by
  unfold tailWord_5478730
  simp only [CollatzResearch.WordTrace]
  refine ⟨49956424860376094358704411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133217132961002918289878429 49956424860376094358704411)
  ·
    refine ⟨74934637290564141538056617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49956424860376094358704411 74934637290564141538056617)
    ·
      refine ⟨56200977967923106153542463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74934637290564141538056617 56200977967923106153542463)
      ·
        refine ⟨84301466951884659230313695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56200977967923106153542463 84301466951884659230313695)
        ·
          refine ⟨126452200427826988845470543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84301466951884659230313695 126452200427826988845470543)
          ·
            refine ⟨189678300641740483268205815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126452200427826988845470543 189678300641740483268205815)
            ·
              refine ⟨284517450962610724902308723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189678300641740483268205815 284517450962610724902308723)
              ·
                refine ⟨426776176443916087353463085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284517450962610724902308723 426776176443916087353463085)
                ·
                  refine ⟨160041066166468532757548657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 426776176443916087353463085 160041066166468532757548657)
                  ·
                    refine ⟨120030799624851399568161493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 160041066166468532757548657 120030799624851399568161493)
                    ·
                      refine ⟨2813221866207454677378785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120030799624851399568161493 2813221866207454677378785)
                      ·
                        rfl

theorem cell23_5478730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_5478730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478730 prefixEnd_5478730 := by exact prefixLift 5478730
  have htrace : WordTrace (prefixWord ++ tailWord_5478730) baseStart_5478730 baseEnd_5478730 := by
    simpa [prefixWord, tailWord_5478730, baseEnd_5478730] using wordTrace_append hprefix tailTrace_5478730
  have hstable : (prefixWord ++ tailWord_5478730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478730).length < 2 ^ (prefixWord ++ tailWord_5478730).sum := by decide
  have hdescent : baseEnd_5478730 < baseStart_5478730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478754 : List Nat := [3, 3, 2, 1, 1, 3, 2, 1, 7]
def baseStart_5478754 : Nat := 118140960795 + 5478754 * 2 ^ 59
def prefixEnd_5478754 : Nat := 4983230072969 + 3 ^ 40 * 5478754 * 2
def baseEnd_5478754 : Nat := 312581576638129175942075

theorem tailTrace_5478754 : CollatzResearch.WordTrace tailWord_5478754 prefixEnd_5478754 312581576638129175942075 := by
  unfold tailWord_5478754
  simp only [CollatzResearch.WordTrace]
  refine ⟨49956643698354357383422829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133217716528944953022460877 49956643698354357383422829)
  ·
    refine ⟨18733741386882884018783561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49956643698354357383422829 18733741386882884018783561)
    ·
      refine ⟨14050306040162163014087671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18733741386882884018783561 14050306040162163014087671)
      ·
        refine ⟨21075459060243244521131507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14050306040162163014087671 21075459060243244521131507)
        ·
          refine ⟨31613188590364866781697261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21075459060243244521131507 31613188590364866781697261)
          ·
            refine ⟨11854945721386825043136473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31613188590364866781697261 11854945721386825043136473)
            ·
              refine ⟨8891209291040118782352355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11854945721386825043136473 8891209291040118782352355)
              ·
                refine ⟨13336813936560178173528533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8891209291040118782352355 13336813936560178173528533)
                ·
                  refine ⟨312581576638129175942075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13336813936560178173528533 312581576638129175942075)
                  ·
                    rfl

theorem cell23_5478754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 1, 7].length) (baseStart_5478754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478754 prefixEnd_5478754 := by exact prefixLift 5478754
  have htrace : WordTrace (prefixWord ++ tailWord_5478754) baseStart_5478754 baseEnd_5478754 := by
    simpa [prefixWord, tailWord_5478754, baseEnd_5478754] using wordTrace_append hprefix tailTrace_5478754
  have hstable : (prefixWord ++ tailWord_5478754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478754).length < 2 ^ (prefixWord ++ tailWord_5478754).sum := by decide
  have hdescent : baseEnd_5478754 < baseStart_5478754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478841 : List Nat := [1, 2, 1, 4, 3, 2, 2, 1, 2, 2, 3]
def baseStart_5478841 : Nat := 118140960795 + 5478841 * 2 ^ 59
def prefixEnd_5478841 : Nat := 4983230072969 + 3 ^ 40 * 5478841 * 2
def baseEnd_5478841 : Nat := 2813278862560103743090775

theorem tailTrace_5478841 : CollatzResearch.WordTrace tailWord_5478841 prefixEnd_5478841 2813278862560103743090775 := by
  unfold tailWord_5478841
  simp only [CollatzResearch.WordTrace]
  refine ⟨199829747944102243392108377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133219831962734828928072251 199829747944102243392108377)
  ·
    refine ⟨149872310958076682544081283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199829747944102243392108377 149872310958076682544081283)
    ·
      refine ⟨224808466437115023816121925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149872310958076682544081283 224808466437115023816121925)
      ·
        refine ⟨42151587456959066965522861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224808466437115023816121925 42151587456959066965522861)
        ·
          refine ⟨15806845296359650112071073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42151587456959066965522861 15806845296359650112071073)
          ·
            refine ⟨11855133972269737584053305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15806845296359650112071073 11855133972269737584053305)
            ·
              refine ⟨8891350479202303188039979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11855133972269737584053305 8891350479202303188039979)
              ·
                refine ⟨13337025718803454782059969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8891350479202303188039979 13337025718803454782059969)
                ·
                  refine ⟨10002769289102591086544977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13337025718803454782059969 10002769289102591086544977)
                  ·
                    refine ⟨7502076966826943314908733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10002769289102591086544977 7502076966826943314908733)
                    ·
                      refine ⟨2813278862560103743090775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7502076966826943314908733 2813278862560103743090775)
                      ·
                        rfl

theorem cell23_5478841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 2, 2, 3].length) (baseStart_5478841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478841 prefixEnd_5478841 := by exact prefixLift 5478841
  have htrace : WordTrace (prefixWord ++ tailWord_5478841) baseStart_5478841 baseEnd_5478841 := by
    simpa [prefixWord, tailWord_5478841, baseEnd_5478841] using wordTrace_append hprefix tailTrace_5478841
  have hstable : (prefixWord ++ tailWord_5478841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478841).length < 2 ^ (prefixWord ++ tailWord_5478841).sum := by decide
  have hdescent : baseEnd_5478841 < baseStart_5478841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478898 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 1, 5, 2]
def baseStart_5478898 : Nat := 118140960795 + 5478898 * 2 ^ 59
def prefixEnd_5478898 : Nat := 4983230072969 + 3 ^ 40 * 5478898 * 2
def baseEnd_5478898 : Nat := 2813308130957410020078013

theorem tailTrace_5478898 : CollatzResearch.WordTrace tailWord_5478898 prefixEnd_5478898 2813308130957410020078013 := by
  unfold tailWord_5478898
  simp only [CollatzResearch.WordTrace]
  refine ⟨49957956726223935531733337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133221217936597161417955565 49957956726223935531733337)
  ·
    refine ⟨37468467544667951648800003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49957956726223935531733337 37468467544667951648800003)
    ·
      refine ⟨56202701317001927473200005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37468467544667951648800003 56202701317001927473200005)
      ·
        refine ⟨10538006496937861401225001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56202701317001927473200005 10538006496937861401225001)
        ·
          refine ⟨7903504872703396050918751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10538006496937861401225001 7903504872703396050918751)
          ·
            refine ⟨11855257309055094076378127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7903504872703396050918751 11855257309055094076378127)
            ·
              refine ⟨17782885963582641114567191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11855257309055094076378127 17782885963582641114567191)
              ·
                refine ⟨26674328945373961671850787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17782885963582641114567191 26674328945373961671850787)
                ·
                  refine ⟨40011493418060942507776181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26674328945373961671850787 40011493418060942507776181)
                  ·
                    refine ⟨3751077507943213360104017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40011493418060942507776181 3751077507943213360104017)
                    ·
                      refine ⟨2813308130957410020078013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3751077507943213360104017 2813308130957410020078013)
                      ·
                        rfl

theorem cell23_5478898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_5478898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478898 prefixEnd_5478898 := by exact prefixLift 5478898
  have htrace : WordTrace (prefixWord ++ tailWord_5478898) baseStart_5478898 baseEnd_5478898 := by
    simpa [prefixWord, tailWord_5478898, baseEnd_5478898] using wordTrace_append hprefix tailTrace_5478898
  have hstable : (prefixWord ++ tailWord_5478898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478898).length < 2 ^ (prefixWord ++ tailWord_5478898).sum := by decide
  have hdescent : baseEnd_5478898 < baseStart_5478898 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478904 : List Nat := [2, 1, 2, 1, 1, 4, 2, 2, 4, 4]
def baseStart_5478904 : Nat := 118140960795 + 5478904 * 2 ^ 59
def prefixEnd_5478904 : Nat := 4983230072969 + 3 ^ 40 * 5478904 * 2
def baseEnd_5478904 : Nat := 937770403947112332200995

theorem tailTrace_5478904 : CollatzResearch.WordTrace tailWord_5478904 prefixEnd_5478904 937770403947112332200995 := by
  unfold tailWord_5478904
  simp only [CollatzResearch.WordTrace]
  refine ⟨99916022871437002575825883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133221363828582670101101177 99916022871437002575825883)
  ·
    refine ⟨149874034307155503863738825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99916022871437002575825883 149874034307155503863738825)
    ·
      refine ⟨112405525730366627897804119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149874034307155503863738825 112405525730366627897804119)
      ·
        refine ⟨168608288595549941846706179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112405525730366627897804119 168608288595549941846706179)
        ·
          refine ⟨252912432893324912770059269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168608288595549941846706179 252912432893324912770059269)
          ·
            refine ⟨47421081167498421144386113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 252912432893324912770059269 47421081167498421144386113)
            ·
              refine ⟨35565810875623815858289585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47421081167498421144386113 35565810875623815858289585)
              ·
                refine ⟨26674358156717861893717189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35565810875623815858289585 26674358156717861893717189)
                ·
                  refine ⟨5001442154384599105071973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26674358156717861893717189 5001442154384599105071973)
                  ·
                    refine ⟨937770403947112332200995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5001442154384599105071973 937770403947112332200995)
                    ·
                      rfl

theorem cell23_5478904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 2, 4, 4].length) (baseStart_5478904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478904 prefixEnd_5478904 := by exact prefixLift 5478904
  have htrace : WordTrace (prefixWord ++ tailWord_5478904) baseStart_5478904 baseEnd_5478904 := by
    simpa [prefixWord, tailWord_5478904, baseEnd_5478904] using wordTrace_append hprefix tailTrace_5478904
  have hstable : (prefixWord ++ tailWord_5478904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478904).length < 2 ^ (prefixWord ++ tailWord_5478904).sum := by decide
  have hdescent : baseEnd_5478904 < baseStart_5478904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478911 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 5, 2, 2]
def baseStart_5478911 : Nat := 118140960795 + 5478911 * 2 ^ 59
def prefixEnd_5478911 : Nat := 4983230072969 + 3 ^ 40 * 5478911 * 2
def baseEnd_5478911 : Nat := 2813314806205918469215453

theorem tailTrace_5478911 : CollatzResearch.WordTrace tailWord_5478911 prefixEnd_5478911 2813314806205918469215453 := by
  unfold tailWord_5478911
  simp only [CollatzResearch.WordTrace]
  refine ⟨199832301053848645347156587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133221534035899096898104391 199832301053848645347156587)
  ·
    refine ⟨299748451580772968020734881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199832301053848645347156587 299748451580772968020734881)
    ·
      refine ⟨224811338685579726015551161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299748451580772968020734881 224811338685579726015551161)
      ·
        refine ⟨168608504014184794511663371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224811338685579726015551161 168608504014184794511663371)
        ·
          refine ⟨252912756021277191767495057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168608504014184794511663371 252912756021277191767495057)
          ·
            refine ⟨189684567015957893825621293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 252912756021277191767495057 189684567015957893825621293)
            ·
              refine ⟨71131712630984210184607985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189684567015957893825621293 71131712630984210184607985)
              ·
                refine ⟨53348784473238157638455989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71131712630984210184607985 53348784473238157638455989)
                ·
                  refine ⟨5001448544366077278605249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 53348784473238157638455989 5001448544366077278605249)
                  ·
                    refine ⟨3751086408274557958953937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5001448544366077278605249 3751086408274557958953937)
                    ·
                      refine ⟨2813314806205918469215453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3751086408274557958953937 2813314806205918469215453)
                      ·
                        rfl

theorem cell23_5478911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 5, 2, 2].length) (baseStart_5478911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478911 prefixEnd_5478911 := by exact prefixLift 5478911
  have htrace : WordTrace (prefixWord ++ tailWord_5478911) baseStart_5478911 baseEnd_5478911 := by
    simpa [prefixWord, tailWord_5478911, baseEnd_5478911] using wordTrace_append hprefix tailTrace_5478911
  have hstable : (prefixWord ++ tailWord_5478911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478911).length < 2 ^ (prefixWord ++ tailWord_5478911).sum := by decide
  have hdescent : baseEnd_5478911 < baseStart_5478911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478937 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 2, 2, 6]
def baseStart_5478937 : Nat := 118140960795 + 5478937 * 2 ^ 59
def prefixEnd_5478937 : Nat := 4983230072969 + 3 ^ 40 * 5478937 * 2
def baseEnd_5478937 : Nat := 2813328156702935367490333

theorem tailTrace_5478937 : CollatzResearch.WordTrace tailWord_5478937 prefixEnd_5478937 2813328156702935367490333 := by
  unfold tailWord_5478937
  simp only [CollatzResearch.WordTrace]
  refine ⟨199833249351754451787603065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133222166234502967858402043 199833249351754451787603065)
  ·
    refine ⟨149874937013815838840702299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199833249351754451787603065 149874937013815838840702299)
    ·
      refine ⟨224812405520723758261053449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149874937013815838840702299 224812405520723758261053449)
      ·
        refine ⟨168609304140542818695790087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224812405520723758261053449 168609304140542818695790087)
        ·
          refine ⟨252913956210814228043685131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168609304140542818695790087 252913956210814228043685131)
          ·
            refine ⟨379370934316221342065527697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252913956210814228043685131 379370934316221342065527697)
            ·
              refine ⟨284528200737166006549145773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379370934316221342065527697 284528200737166006549145773)
              ·
                refine ⟨106698075276437252455929665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 284528200737166006549145773 106698075276437252455929665)
                ·
                  refine ⟨80023556457327939341947249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 106698075276437252455929665 80023556457327939341947249)
                  ·
                    refine ⟨60017667342995954506460437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 80023556457327939341947249 60017667342995954506460437)
                    ·
                      refine ⟨2813328156702935367490333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60017667342995954506460437 2813328156702935367490333)
                      ·
                        rfl

theorem cell23_5478937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_5478937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478937 prefixEnd_5478937 := by exact prefixLift 5478937
  have htrace : WordTrace (prefixWord ++ tailWord_5478937) baseStart_5478937 baseEnd_5478937 := by
    simpa [prefixWord, tailWord_5478937, baseEnd_5478937] using wordTrace_append hprefix tailTrace_5478937
  have hstable : (prefixWord ++ tailWord_5478937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478937).length < 2 ^ (prefixWord ++ tailWord_5478937).sum := by decide
  have hdescent : baseEnd_5478937 < baseStart_5478937 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478941 : List Nat := [1, 4, 2, 2, 1, 2, 3, 1, 1, 2, 4]
def baseStart_5478941 : Nat := 118140960795 + 5478941 * 2 ^ 59
def prefixEnd_5478941 : Nat := 4983230072969 + 3 ^ 40 * 5478941 * 2
def baseEnd_5478941 : Nat := 2813330210625553351840315

theorem tailTrace_5478941 : CollatzResearch.WordTrace tailWord_5478941 prefixEnd_5478941 2813330210625553351840315 := by
  unfold tailWord_5478941
  simp only [CollatzResearch.WordTrace]
  refine ⟨199833395243739960470748677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133222263495826640313832451 199833395243739960470748677)
  ·
    refine ⟨37468761608201242588265377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199833395243739960470748677 37468761608201242588265377)
    ·
      refine ⟨28101571206150931941199033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37468761608201242588265377 28101571206150931941199033)
      ·
        refine ⟨21076178404613198955899275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28101571206150931941199033 21076178404613198955899275)
        ·
          refine ⟨31614267606919798433848913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21076178404613198955899275 31614267606919798433848913)
          ·
            refine ⟨23710700705189848825386685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31614267606919798433848913 23710700705189848825386685)
            ·
              refine ⟨8891512764446193309520007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23710700705189848825386685 8891512764446193309520007)
              ·
                refine ⟨13337269146669289964280011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8891512764446193309520007 13337269146669289964280011)
                ·
                  refine ⟨20005903720003934946420017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13337269146669289964280011 20005903720003934946420017)
                  ·
                    refine ⟨15004427790002951209815013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20005903720003934946420017 15004427790002951209815013)
                    ·
                      refine ⟨2813330210625553351840315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15004427790002951209815013 2813330210625553351840315)
                      ·
                        rfl

theorem cell23_5478941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 1, 1, 2, 4].length) (baseStart_5478941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478941 prefixEnd_5478941 := by exact prefixLift 5478941
  have htrace : WordTrace (prefixWord ++ tailWord_5478941) baseStart_5478941 baseEnd_5478941 := by
    simpa [prefixWord, tailWord_5478941, baseEnd_5478941] using wordTrace_append hprefix tailTrace_5478941
  have hstable : (prefixWord ++ tailWord_5478941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478941).length < 2 ^ (prefixWord ++ tailWord_5478941).sum := by decide
  have hdescent : baseEnd_5478941 < baseStart_5478941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478961 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 4, 1, 3]
def baseStart_5478961 : Nat := 118140960795 + 5478961 * 2 ^ 59
def prefixEnd_5478961 : Nat := 4983230072969 + 3 ^ 40 * 5478961 * 2
def baseEnd_5478961 : Nat := 2813340480238643273590223

theorem tailTrace_5478961 : CollatzResearch.WordTrace tailWord_5478961 prefixEnd_5478961 2813340480238643273590223 := by
  unfold tailWord_5478961
  simp only [CollatzResearch.WordTrace]
  refine ⟨199834124703667503886476737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133222749802445002590984491 199834124703667503886476737)
  ·
    refine ⟨149875593527750627914857553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199834124703667503886476737 149875593527750627914857553)
    ·
      refine ⟨112406695145812970936143165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149875593527750627914857553 112406695145812970936143165)
      ·
        refine ⟨42152510679679864101053687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 112406695145812970936143165 42152510679679864101053687)
        ·
          refine ⟨63228766019519796151580531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42152510679679864101053687 63228766019519796151580531)
          ·
            refine ⟨94843149029279694227370797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63228766019519796151580531 94843149029279694227370797)
            ·
              refine ⟨35566180885979885335264049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94843149029279694227370797 35566180885979885335264049)
              ·
                refine ⟨26674635664484914001448037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35566180885979885335264049 26674635664484914001448037)
                ·
                  refine ⟨5001494187090921375271507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26674635664484914001448037 5001494187090921375271507)
                  ·
                    refine ⟨7502241280636382062907261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5001494187090921375271507 7502241280636382062907261)
                    ·
                      refine ⟨2813340480238643273590223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7502241280636382062907261 2813340480238643273590223)
                      ·
                        rfl

theorem cell23_5478961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 4, 1, 3].length) (baseStart_5478961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478961 prefixEnd_5478961 := by exact prefixLift 5478961
  have htrace : WordTrace (prefixWord ++ tailWord_5478961) baseStart_5478961 baseEnd_5478961 := by
    simpa [prefixWord, tailWord_5478961, baseEnd_5478961] using wordTrace_append hprefix tailTrace_5478961
  have hstable : (prefixWord ++ tailWord_5478961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478961).length < 2 ^ (prefixWord ++ tailWord_5478961).sum := by decide
  have hdescent : baseEnd_5478961 < baseStart_5478961 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5478994 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 1, 8]
def baseStart_5478994 : Nat := 118140960795 + 5478994 * 2 ^ 59
def prefixEnd_5478994 : Nat := 4983230072969 + 3 ^ 40 * 5478994 * 2
def baseEnd_5478994 : Nat := 937785808366747214825857

theorem tailTrace_5478994 : CollatzResearch.WordTrace tailWord_5478994 prefixEnd_5478994 937785808366747214825857 := by
  unfold tailWord_5478994
  simp only [CollatzResearch.WordTrace]
  refine ⟨49958832078136987630607009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133223552208365300348285357 49958832078136987630607009)
  ·
    refine ⟨37469124058602740722955257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49958832078136987630607009 37469124058602740722955257)
    ·
      refine ⟨28101843043952055542216443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37469124058602740722955257 28101843043952055542216443)
      ·
        refine ⟨42152764565928083313324665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28101843043952055542216443 42152764565928083313324665)
        ·
          refine ⟨31614573424446062484993499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42152764565928083313324665 31614573424446062484993499)
          ·
            refine ⟨47421860136669093727490249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31614573424446062484993499 47421860136669093727490249)
            ·
              refine ⟨35566395102501820295617687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47421860136669093727490249 35566395102501820295617687)
              ·
                refine ⟨53349592653752730443426531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35566395102501820295617687 53349592653752730443426531)
                ·
                  refine ⟨80024388980629095665139797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53349592653752730443426531 80024388980629095665139797)
                  ·
                    refine ⟨937785808366747214825857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80024388980629095665139797 937785808366747214825857)
                    ·
                      rfl

theorem cell23_5478994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 1, 8].length) (baseStart_5478994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5478994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5478994 prefixEnd_5478994 := by exact prefixLift 5478994
  have htrace : WordTrace (prefixWord ++ tailWord_5478994) baseStart_5478994 baseEnd_5478994 := by
    simpa [prefixWord, tailWord_5478994, baseEnd_5478994] using wordTrace_append hprefix tailTrace_5478994
  have hstable : (prefixWord ++ tailWord_5478994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5478994).length < 2 ^ (prefixWord ++ tailWord_5478994).sum := by decide
  have hdescent : baseEnd_5478994 < baseStart_5478994 := by decide
  rcases family_descends (prefixWord ++ tailWord_5478994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479018 : List Nat := [3, 1, 3, 2, 1, 1, 3, 2, 1, 4, 2]
def baseStart_5479018 : Nat := 118140960795 + 5479018 * 2 ^ 59
def prefixEnd_5479018 : Nat := 4983230072969 + 3 ^ 40 * 5479018 * 2
def baseEnd_5479018 : Nat := 2813369748635949550577461

theorem tailTrace_5479018 : CollatzResearch.WordTrace tailWord_5479018 prefixEnd_5479018 2813369748635949550577461 := by
  unfold tailWord_5479018
  simp only [CollatzResearch.WordTrace]
  refine ⟨49959050916115250655325427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133224135776307335080867805 49959050916115250655325427)
  ·
    refine ⟨74938576374172875982988141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49959050916115250655325427 74938576374172875982988141)
    ·
      refine ⟨28101966140314828493620553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74938576374172875982988141 28101966140314828493620553)
      ·
        refine ⟨21076474605236121370215415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28101966140314828493620553 21076474605236121370215415)
        ·
          refine ⟨31614711907854182055323123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21076474605236121370215415 31614711907854182055323123)
          ·
            refine ⟨47422067861781273082984685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31614711907854182055323123 47422067861781273082984685)
            ·
              refine ⟨17783275448167977406119257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47422067861781273082984685 17783275448167977406119257)
              ·
                refine ⟨13337456586125983054589443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17783275448167977406119257 13337456586125983054589443)
                ·
                  refine ⟨20006184879188974581884165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13337456586125983054589443 20006184879188974581884165)
                  ·
                    refine ⟨3751159664847932734103281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20006184879188974581884165 3751159664847932734103281)
                    ·
                      refine ⟨2813369748635949550577461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3751159664847932734103281 2813369748635949550577461)
                      ·
                        rfl

theorem cell23_5479018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_5479018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479018 prefixEnd_5479018 := by exact prefixLift 5479018
  have htrace : WordTrace (prefixWord ++ tailWord_5479018) baseStart_5479018 baseEnd_5479018 := by
    simpa [prefixWord, tailWord_5479018, baseEnd_5479018] using wordTrace_append hprefix tailTrace_5479018
  have hstable : (prefixWord ++ tailWord_5479018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479018).length < 2 ^ (prefixWord ++ tailWord_5479018).sum := by decide
  have hdescent : baseEnd_5479018 < baseStart_5479018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479021 : List Nat := [1, 5, 1, 1, 3, 1, 2, 1, 2, 1, 5]
def baseStart_5479021 : Nat := 118140960795 + 5479021 * 2 ^ 59
def prefixEnd_5479021 : Nat := 4983230072969 + 3 ^ 40 * 5479021 * 2
def baseEnd_5479021 : Nat := 2813371289077913038839947

theorem tailTrace_5479021 : CollatzResearch.WordTrace tailWord_5479021 prefixEnd_5479021 2813371289077913038839947 := by
  unfold tailWord_5479021
  simp only [CollatzResearch.WordTrace]
  refine ⟨199836313083450134133660917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133224208722300089422440611 199836313083450134133660917)
  ·
    refine ⟨18734654351573450075030711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 199836313083450134133660917 18734654351573450075030711)
    ·
      refine ⟨28101981527360175112546067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18734654351573450075030711 28101981527360175112546067)
      ·
        refine ⟨42152972291040262668819101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28101981527360175112546067 42152972291040262668819101)
        ·
          refine ⟨15807364609140098500807163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42152972291040262668819101 15807364609140098500807163)
          ·
            refine ⟨23711046913710147751210745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15807364609140098500807163 23711046913710147751210745)
            ·
              refine ⟨17783285185282610813408059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23711046913710147751210745 17783285185282610813408059)
              ·
                refine ⟨26674927777923916220112089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17783285185282610813408059 26674927777923916220112089)
                ·
                  refine ⟨20006195833442937165084067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26674927777923916220112089 20006195833442937165084067)
                  ·
                    refine ⟨30009293750164405747626101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20006195833442937165084067 30009293750164405747626101)
                    ·
                      refine ⟨2813371289077913038839947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30009293750164405747626101 2813371289077913038839947)
                      ·
                        rfl

theorem cell23_5479021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_5479021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479021 prefixEnd_5479021 := by exact prefixLift 5479021
  have htrace : WordTrace (prefixWord ++ tailWord_5479021) baseStart_5479021 baseEnd_5479021 := by
    simpa [prefixWord, tailWord_5479021, baseEnd_5479021] using wordTrace_append hprefix tailTrace_5479021
  have hstable : (prefixWord ++ tailWord_5479021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479021).length < 2 ^ (prefixWord ++ tailWord_5479021).sum := by decide
  have hdescent : baseEnd_5479021 < baseStart_5479021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479022 : List Nat := [4, 1, 2, 2, 2, 2, 3, 1, 1, 3, 2]
def baseStart_5479022 : Nat := 118140960795 + 5479022 * 2 ^ 59
def prefixEnd_5479022 : Nat := 4983230072969 + 3 ^ 40 * 5479022 * 2
def baseEnd_5479022 : Nat := 2813371802558567534927443

theorem tailTrace_5479022 : CollatzResearch.WordTrace tailWord_5479022 prefixEnd_5479022 2813371802558567534927443 := by
  unfold tailWord_5479022
  simp only [CollatzResearch.WordTrace]
  refine ⟨24979543694555813913055915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133224233037631007536298213 24979543694555813913055915)
  ·
    refine ⟨37469315541833720869583873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24979543694555813913055915 37469315541833720869583873)
    ·
      refine ⟨28101986656375290652187905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37469315541833720869583873 28101986656375290652187905)
      ·
        refine ⟨21076489992281467989140929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28101986656375290652187905 21076489992281467989140929)
        ·
          refine ⟨15807367494211100991855697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21076489992281467989140929 15807367494211100991855697)
          ·
            refine ⟨11855525620658325743891773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15807367494211100991855697 11855525620658325743891773)
            ·
              refine ⟨4445822107746872153959415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11855525620658325743891773 4445822107746872153959415)
              ·
                refine ⟨6668733161620308230939123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4445822107746872153959415 6668733161620308230939123)
                ·
                  refine ⟨10003099742430462346408685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6668733161620308230939123 10003099742430462346408685)
                  ·
                    refine ⟨3751162403411423379903257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10003099742430462346408685 3751162403411423379903257)
                    ·
                      refine ⟨2813371802558567534927443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3751162403411423379903257 2813371802558567534927443)
                      ·
                        rfl

theorem cell23_5479022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_5479022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479022 prefixEnd_5479022 := by exact prefixLift 5479022
  have htrace : WordTrace (prefixWord ++ tailWord_5479022) baseStart_5479022 baseEnd_5479022 := by
    simpa [prefixWord, tailWord_5479022, baseEnd_5479022] using wordTrace_append hprefix tailTrace_5479022
  have hstable : (prefixWord ++ tailWord_5479022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479022).length < 2 ^ (prefixWord ++ tailWord_5479022).sum := by decide
  have hdescent : baseEnd_5479022 < baseStart_5479022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479111 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 3]
def baseStart_5479111 : Nat := 118140960795 + 5479111 * 2 ^ 59
def prefixEnd_5479111 : Nat := 4983230072969 + 3 ^ 40 * 5479111 * 2
def baseEnd_5479111 : Nat := 2813417502336817686714533

theorem tailTrace_5479111 : CollatzResearch.WordTrace tailWord_5479111 prefixEnd_5479111 2813417502336817686714533 := by
  unfold tailWord_5479111
  simp only [CollatzResearch.WordTrace]
  refine ⟨199839595653124079504437187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133226397102082719669624791 199839595653124079504437187)
  ·
    refine ⟨299759393479686119256655781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199839595653124079504437187 299759393479686119256655781)
    ·
      refine ⟨56204886277441147360622959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 299759393479686119256655781 56204886277441147360622959)
      ·
        refine ⟨84307329416161721040934439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56204886277441147360622959 84307329416161721040934439)
        ·
          refine ⟨126460994124242581561401659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84307329416161721040934439 126460994124242581561401659)
          ·
            refine ⟨189691491186363872342102489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126460994124242581561401659 189691491186363872342102489)
            ·
              refine ⟨142268618389772904256576867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189691491186363872342102489 142268618389772904256576867)
              ·
                refine ⟨213402927584659356384865301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142268618389772904256576867 213402927584659356384865301)
                ·
                  refine ⟨10003262230530907330540561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 213402927584659356384865301 10003262230530907330540561)
                  ·
                    refine ⟨7502446672898180497905421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10003262230530907330540561 7502446672898180497905421)
                    ·
                      refine ⟨2813417502336817686714533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7502446672898180497905421 2813417502336817686714533)
                      ·
                        rfl

theorem cell23_5479111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_5479111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479111 prefixEnd_5479111 := by exact prefixLift 5479111
  have htrace : WordTrace (prefixWord ++ tailWord_5479111) baseStart_5479111 baseEnd_5479111 := by
    simpa [prefixWord, tailWord_5479111, baseEnd_5479111] using wordTrace_append hprefix tailTrace_5479111
  have hstable : (prefixWord ++ tailWord_5479111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479111).length < 2 ^ (prefixWord ++ tailWord_5479111).sum := by decide
  have hdescent : baseEnd_5479111 < baseStart_5479111 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479118 : List Nat := [4, 1, 1, 1, 3, 2, 2, 2, 3, 4]
def baseStart_5479118 : Nat := 118140960795 + 5479118 * 2 ^ 59
def prefixEnd_5479118 : Nat := 4983230072969 + 3 ^ 40 * 5479118 * 2
def baseEnd_5479118 : Nat := 937807032233799719775667

theorem tailTrace_5479118 : CollatzResearch.WordTrace tailWord_5479118 prefixEnd_5479118 937807032233799719775667 := by
  unfold tailWord_5479118
  simp only [CollatzResearch.WordTrace]
  refine ⟨24979981370512339962492751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133226567309399146466628005 24979981370512339962492751)
  ·
    refine ⟨37469972055768509943739127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24979981370512339962492751 37469972055768509943739127)
    ·
      refine ⟨56204958083652764915608691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37469972055768509943739127 56204958083652764915608691)
      ·
        refine ⟨84307437125479147373413037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56204958083652764915608691 84307437125479147373413037)
        ·
          refine ⟨31615288922054680265029889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84307437125479147373413037 31615288922054680265029889)
          ·
            refine ⟨23711466691541010198772417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31615288922054680265029889 23711466691541010198772417)
            ·
              refine ⟨17783600018655757649079313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23711466691541010198772417 17783600018655757649079313)
              ·
                refine ⟨13337700013991818236809485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17783600018655757649079313 13337700013991818236809485)
                ·
                  refine ⟨5001637505246931838803557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13337700013991818236809485 5001637505246931838803557)
                  ·
                    refine ⟨937807032233799719775667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5001637505246931838803557 937807032233799719775667)
                    ·
                      rfl

theorem cell23_5479118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 3, 4].length) (baseStart_5479118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479118 prefixEnd_5479118 := by exact prefixLift 5479118
  have htrace : WordTrace (prefixWord ++ tailWord_5479118) baseStart_5479118 baseEnd_5479118 := by
    simpa [prefixWord, tailWord_5479118, baseEnd_5479118] using wordTrace_append hprefix tailTrace_5479118
  have hstable : (prefixWord ++ tailWord_5479118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479118).length < 2 ^ (prefixWord ++ tailWord_5479118).sum := by decide
  have hdescent : baseEnd_5479118 < baseStart_5479118 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479135 : List Nat := [1, 1, 2, 3, 2, 3, 3, 3, 1, 4]
def baseStart_5479135 : Nat := 118140960795 + 5479135 * 2 ^ 59
def prefixEnd_5479135 : Nat := 4983230072969 + 3 ^ 40 * 5479135 * 2
def baseEnd_5479135 : Nat := 937809941957508530938141

theorem tailTrace_5479135 : CollatzResearch.WordTrace tailWord_5479135 prefixEnd_5479135 937809941957508530938141 := by
  unfold tailWord_5479135
  simp only [CollatzResearch.WordTrace]
  refine ⟨199840471005037131603310859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133226980670024754402207239 199840471005037131603310859)
  ·
    refine ⟨299760706507555697404966289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199840471005037131603310859 299760706507555697404966289)
    ·
      refine ⟨224820529880666773053724717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299760706507555697404966289 224820529880666773053724717)
      ·
        refine ⟨84307698705250039895146769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224820529880666773053724717 84307698705250039895146769)
        ·
          refine ⟨63230774028937529921360077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84307698705250039895146769 63230774028937529921360077)
          ·
            refine ⟨23711540260851573720510029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 63230774028937529921360077 23711540260851573720510029)
            ·
              refine ⟨8891827597819340145191261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23711540260851573720510029 8891827597819340145191261)
              ·
                refine ⟨3334435349182252554446723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8891827597819340145191261 3334435349182252554446723)
                ·
                  refine ⟨5001653023773378831670085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3334435349182252554446723 5001653023773378831670085)
                  ·
                    refine ⟨937809941957508530938141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5001653023773378831670085 937809941957508530938141)
                    ·
                      rfl

theorem cell23_5479135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 3, 1, 4].length) (baseStart_5479135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479135 prefixEnd_5479135 := by exact prefixLift 5479135
  have htrace : WordTrace (prefixWord ++ tailWord_5479135) baseStart_5479135 baseEnd_5479135 := by
    simpa [prefixWord, tailWord_5479135, baseEnd_5479135] using wordTrace_append hprefix tailTrace_5479135
  have hstable : (prefixWord ++ tailWord_5479135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479135).length < 2 ^ (prefixWord ++ tailWord_5479135).sum := by decide
  have hdescent : baseEnd_5479135 < baseStart_5479135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479218 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3]
def baseStart_5479218 : Nat := 118140960795 + 5479218 * 2 ^ 59
def prefixEnd_5479218 : Nat := 4983230072969 + 3 ^ 40 * 5479218 * 2
def baseEnd_5479218 : Nat := 2813472444766848768076541

theorem tailTrace_5479218 : CollatzResearch.WordTrace tailWord_5479218 prefixEnd_5479218 2813472444766848768076541 := by
  unfold tailWord_5479218
  simp only [CollatzResearch.WordTrace]
  refine ⟨49960874565934109194645577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133228998842490957852388205 49960874565934109194645577)
  ·
    refine ⟨37470655924450581895984183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49960874565934109194645577 37470655924450581895984183)
    ·
      refine ⟨56205983886675872843976275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37470655924450581895984183 56205983886675872843976275)
      ·
        refine ⟨84308975830013809265964413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56205983886675872843976275 84308975830013809265964413)
        ·
          refine ⟨31615865936255178474736655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84308975830013809265964413 31615865936255178474736655)
          ·
            refine ⟨47423798904382767712104983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31615865936255178474736655 47423798904382767712104983)
            ·
              refine ⟨71135698356574151568157475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47423798904382767712104983 71135698356574151568157475)
              ·
                refine ⟨106703547534861227352236213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71135698356574151568157475 106703547534861227352236213)
                ·
                  refine ⟨10003457581393240064272145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106703547534861227352236213 10003457581393240064272145)
                  ·
                    refine ⟨7502593186044930048204109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10003457581393240064272145 7502593186044930048204109)
                    ·
                      refine ⟨2813472444766848768076541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7502593186044930048204109 2813472444766848768076541)
                      ·
                        rfl

theorem cell23_5479218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_5479218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479218 prefixEnd_5479218 := by exact prefixLift 5479218
  have htrace : WordTrace (prefixWord ++ tailWord_5479218) baseStart_5479218 baseEnd_5479218 := by
    simpa [prefixWord, tailWord_5479218, baseEnd_5479218] using wordTrace_append hprefix tailTrace_5479218
  have hstable : (prefixWord ++ tailWord_5479218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479218).length < 2 ^ (prefixWord ++ tailWord_5479218).sum := by decide
  have hdescent : baseEnd_5479218 < baseStart_5479218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479236 : List Nat := [2, 3, 4, 2, 1, 2, 1, 1, 2, 3, 2]
def baseStart_5479236 : Nat := 118140960795 + 5479236 * 2 ^ 59
def prefixEnd_5479236 : Nat := 4983230072969 + 3 ^ 40 * 5479236 * 2
def baseEnd_5479236 : Nat := 2813481687418629697651459

theorem tailTrace_5479236 : CollatzResearch.WordTrace tailWord_5479236 prefixEnd_5479236 2813481687418629697651459 := by
  unfold tailWord_5479236
  simp only [CollatzResearch.WordTrace]
  refine ⟨99922077388835612926368781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133229436518447483901825041 99922077388835612926368781)
  ·
    refine ⟨37470779020813354847388293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99922077388835612926368781 37470779020813354847388293)
    ·
      refine ⟨7025771066402504033885305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37470779020813354847388293 7025771066402504033885305)
      ·
        refine ⟨5269328299801878025413979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7025771066402504033885305 5269328299801878025413979)
        ·
          refine ⟨7903992449702817038120969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5269328299801878025413979 7903992449702817038120969)
          ·
            refine ⟨5927994337277112778590727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7903992449702817038120969 5927994337277112778590727)
            ·
              refine ⟨8891991505915669167886091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5927994337277112778590727 8891991505915669167886091)
              ·
                refine ⟨13337987258873503751829137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8891991505915669167886091 13337987258873503751829137)
                ·
                  refine ⟨10003490444155127813871853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13337987258873503751829137 10003490444155127813871853)
                  ·
                    refine ⟨3751308916558172930201945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10003490444155127813871853 3751308916558172930201945)
                    ·
                      refine ⟨2813481687418629697651459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3751308916558172930201945 2813481687418629697651459)
                      ·
                        rfl

theorem cell23_5479236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 2, 3, 2].length) (baseStart_5479236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479236 prefixEnd_5479236 := by exact prefixLift 5479236
  have htrace : WordTrace (prefixWord ++ tailWord_5479236) baseStart_5479236 baseEnd_5479236 := by
    simpa [prefixWord, tailWord_5479236, baseEnd_5479236] using wordTrace_append hprefix tailTrace_5479236
  have hstable : (prefixWord ++ tailWord_5479236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479236).length < 2 ^ (prefixWord ++ tailWord_5479236).sum := by decide
  have hdescent : baseEnd_5479236 < baseStart_5479236 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479248 : List Nat := [2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 3]
def baseStart_5479248 : Nat := 118140960795 + 5479248 * 2 ^ 59
def prefixEnd_5479248 : Nat := 4983230072969 + 3 ^ 40 * 5479248 * 2
def baseEnd_5479248 : Nat := 2813487849186483650701403

theorem tailTrace_5479248 : CollatzResearch.WordTrace tailWord_5479248 prefixEnd_5479248 2813487849186483650701403 := by
  unfold tailWord_5479248
  simp only [CollatzResearch.WordTrace]
  refine ⟨99922296226813875951087199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133229728302418501268116265 99922296226813875951087199)
  ·
    refine ⟨149883444340220813926630799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99922296226813875951087199 149883444340220813926630799)
    ·
      refine ⟨224825166510331220889946199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149883444340220813926630799 224825166510331220889946199)
      ·
        refine ⟨337237749765496831334919299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224825166510331220889946199 337237749765496831334919299)
        ·
          refine ⟨505856624648245247002378949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337237749765496831334919299 505856624648245247002378949)
          ·
            refine ⟨94848117121545983812946053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 505856624648245247002378949 94848117121545983812946053)
            ·
              refine ⟨17784021960289871964927385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94848117121545983812946053 17784021960289871964927385)
              ·
                refine ⟨13338016470217403973695539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17784021960289871964927385 13338016470217403973695539)
                ·
                  refine ⟨20007024705326105960543309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13338016470217403973695539 20007024705326105960543309)
                  ·
                    refine ⟨7502634264497289735203741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20007024705326105960543309 7502634264497289735203741)
                    ·
                      refine ⟨2813487849186483650701403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7502634264497289735203741 2813487849186483650701403)
                      ·
                        rfl

theorem cell23_5479248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 2, 1, 3, 3].length) (baseStart_5479248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479248 prefixEnd_5479248 := by exact prefixLift 5479248
  have htrace : WordTrace (prefixWord ++ tailWord_5479248) baseStart_5479248 baseEnd_5479248 := by
    simpa [prefixWord, tailWord_5479248, baseEnd_5479248] using wordTrace_append hprefix tailTrace_5479248
  have hstable : (prefixWord ++ tailWord_5479248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479248).length < 2 ^ (prefixWord ++ tailWord_5479248).sum := by decide
  have hdescent : baseEnd_5479248 < baseStart_5479248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479249 : List Nat := [1, 2, 2, 1, 7, 1, 2, 1, 1, 1, 4]
def baseStart_5479249 : Nat := 118140960795 + 5479249 * 2 ^ 59
def prefixEnd_5479249 : Nat := 4983230072969 + 3 ^ 40 * 5479249 * 2
def baseEnd_5479249 : Nat := 2813488362667138146788899

theorem tailTrace_5479249 : CollatzResearch.WordTrace tailWord_5479249 prefixEnd_5479249 2813488362667138146788899 := by
  unfold tailWord_5479249
  simp only [CollatzResearch.WordTrace]
  refine ⟨199844628926624129072960801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133229752617749419381973867 199844628926624129072960801)
  ·
    refine ⟨149883471694968096804720601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199844628926624129072960801 149883471694968096804720601)
    ·
      refine ⟨112412603771226072603540451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149883471694968096804720601 112412603771226072603540451)
      ·
        refine ⟨168618905656839108905310677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112412603771226072603540451 168618905656839108905310677)
        ·
          refine ⟨3952005601332166614968219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 168618905656839108905310677 3952005601332166614968219)
          ·
            refine ⟨5928008401998249922452329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3952005601332166614968219 5928008401998249922452329)
            ·
              refine ⟨4446006301498687441839247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5928008401998249922452329 4446006301498687441839247)
              ·
                refine ⟨6669009452248031162758871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4446006301498687441839247 6669009452248031162758871)
                ·
                  refine ⟨10003514178372046744138307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6669009452248031162758871 10003514178372046744138307)
                  ·
                    refine ⟨15005271267558070116207461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10003514178372046744138307 15005271267558070116207461)
                    ·
                      refine ⟨2813488362667138146788899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15005271267558070116207461 2813488362667138146788899)
                      ·
                        rfl

theorem cell23_5479249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 2, 1, 1, 1, 4].length) (baseStart_5479249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479249 prefixEnd_5479249 := by exact prefixLift 5479249
  have htrace : WordTrace (prefixWord ++ tailWord_5479249) baseStart_5479249 baseEnd_5479249 := by
    simpa [prefixWord, tailWord_5479249, baseEnd_5479249] using wordTrace_append hprefix tailTrace_5479249
  have hstable : (prefixWord ++ tailWord_5479249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479249).length < 2 ^ (prefixWord ++ tailWord_5479249).sum := by decide
  have hdescent : baseEnd_5479249 < baseStart_5479249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479252 : List Nat := [2, 4, 1, 1, 4, 1, 1, 3, 1, 2, 3]
def baseStart_5479252 : Nat := 118140960795 + 5479252 * 2 ^ 59
def prefixEnd_5479252 : Nat := 4983230072969 + 3 ^ 40 * 5479252 * 2
def baseEnd_5479252 : Nat := 2813489903109101635051385

theorem tailTrace_5479252 : CollatzResearch.WordTrace tailWord_5479252 prefixEnd_5479252 2813489903109101635051385 := by
  unfold tailWord_5479252
  simp only [CollatzResearch.WordTrace]
  refine ⟨99922369172806630292660005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133229825563742173723546673 99922369172806630292660005)
  ·
    refine ⟨18735444219901243179873751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99922369172806630292660005 18735444219901243179873751)
    ·
      refine ⟨28103166329851864769810627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18735444219901243179873751 28103166329851864769810627)
      ·
        refine ⟨42154749494777797154715941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28103166329851864769810627 42154749494777797154715941)
        ·
          refine ⟨7904015530270836966509239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42154749494777797154715941 7904015530270836966509239)
          ·
            refine ⟨11856023295406255449763859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7904015530270836966509239 11856023295406255449763859)
            ·
              refine ⟨17784034943109383174645789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11856023295406255449763859 17784034943109383174645789)
              ·
                refine ⟨6669013103666018690492171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17784034943109383174645789 6669013103666018690492171)
                ·
                  refine ⟨10003519655499028035738257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6669013103666018690492171 10003519655499028035738257)
                  ·
                    refine ⟨7502639741624271026803693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10003519655499028035738257 7502639741624271026803693)
                    ·
                      refine ⟨2813489903109101635051385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7502639741624271026803693 2813489903109101635051385)
                      ·
                        rfl

theorem cell23_5479252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_5479252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479252 prefixEnd_5479252 := by exact prefixLift 5479252
  have htrace : WordTrace (prefixWord ++ tailWord_5479252) baseStart_5479252 baseEnd_5479252 := by
    simpa [prefixWord, tailWord_5479252, baseEnd_5479252] using wordTrace_append hprefix tailTrace_5479252
  have hstable : (prefixWord ++ tailWord_5479252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479252).length < 2 ^ (prefixWord ++ tailWord_5479252).sum := by decide
  have hdescent : baseEnd_5479252 < baseStart_5479252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479265 : List Nat := [1, 2, 3, 1, 1, 1, 2, 6, 2, 1, 3]
def baseStart_5479265 : Nat := 118140960795 + 5479265 * 2 ^ 59
def prefixEnd_5479265 : Nat := 4983230072969 + 3 ^ 40 * 5479265 * 2
def baseEnd_5479265 : Nat := 2813496578357610084188825

theorem tailTrace_5479265 : CollatzResearch.WordTrace tailWord_5479265 prefixEnd_5479265 2813496578357610084188825 := by
  unfold tailWord_5479265
  simp only [CollatzResearch.WordTrace]
  refine ⟨199845212494566163805543249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133230141663044109203695499 199845212494566163805543249)
  ·
    refine ⟨149883909370924622854157437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199845212494566163805543249 149883909370924622854157437)
    ·
      refine ⟨56206466014096733570309039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149883909370924622854157437 56206466014096733570309039)
      ·
        refine ⟨84309699021145100355463559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56206466014096733570309039 84309699021145100355463559)
        ·
          refine ⟨126464548531717650533195339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84309699021145100355463559 126464548531717650533195339)
          ·
            refine ⟨189696822797576475799793009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126464548531717650533195339 189696822797576475799793009)
            ·
              refine ⟨142272617098182356849844757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189696822797576475799793009 142272617098182356849844757)
              ·
                refine ⟨6669028926477297977336473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 142272617098182356849844757 6669028926477297977336473)
                ·
                  refine ⟨5001771694857973483002355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6669028926477297977336473 5001771694857973483002355)
                  ·
                    refine ⟨7502657542286960224503533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5001771694857973483002355 7502657542286960224503533)
                    ·
                      refine ⟨2813496578357610084188825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7502657542286960224503533 2813496578357610084188825)
                      ·
                        rfl

theorem cell23_5479265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 2, 1, 3].length) (baseStart_5479265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479265 prefixEnd_5479265 := by exact prefixLift 5479265
  have htrace : WordTrace (prefixWord ++ tailWord_5479265) baseStart_5479265 baseEnd_5479265 := by
    simpa [prefixWord, tailWord_5479265, baseEnd_5479265] using wordTrace_append hprefix tailTrace_5479265
  have hstable : (prefixWord ++ tailWord_5479265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479265).length < 2 ^ (prefixWord ++ tailWord_5479265).sum := by decide
  have hdescent : baseEnd_5479265 < baseStart_5479265 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479321 : List Nat := [1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 9]
def baseStart_5479321 : Nat := 118140960795 + 5479321 * 2 ^ 59
def prefixEnd_5479321 : Nat := 4983230072969 + 3 ^ 40 * 5479321 * 2
def baseEnd_5479321 : Nat := 2813525333274261865088567

theorem tailTrace_5479321 : CollatzResearch.WordTrace tailWord_5479321 prefixEnd_5479321 2813525333274261865088567 := by
  unfold tailWord_5479321
  simp only [CollatzResearch.WordTrace]
  refine ⟨199847254982363285369581817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133231503321575523579721211 199847254982363285369581817)
  ·
    refine ⟨149885441236772464027186363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199847254982363285369581817 149885441236772464027186363)
    ·
      refine ⟨224828161855158696040779545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149885441236772464027186363 224828161855158696040779545)
      ·
        refine ⟨168621121391369022030584659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224828161855158696040779545 168621121391369022030584659)
        ·
          refine ⟨252931682087053533045876989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168621121391369022030584659 252931682087053533045876989)
          ·
            refine ⟨94849380782645074892203871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252931682087053533045876989 94849380782645074892203871)
            ·
              refine ⟨142274071173967612338305807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94849380782645074892203871 142274071173967612338305807)
              ·
                refine ⟨213411106760951418507458711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142274071173967612338305807 213411106760951418507458711)
                ·
                  refine ⟨320116660141427127761188067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213411106760951418507458711 320116660141427127761188067)
                  ·
                    refine ⟨480174990212140691641782101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 320116660141427127761188067 480174990212140691641782101)
                    ·
                      refine ⟨2813525333274261865088567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 480174990212140691641782101 2813525333274261865088567)
                      ·
                        rfl

theorem cell23_5479321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_5479321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479321 prefixEnd_5479321 := by exact prefixLift 5479321
  have htrace : WordTrace (prefixWord ++ tailWord_5479321) baseStart_5479321 baseEnd_5479321 := by
    simpa [prefixWord, tailWord_5479321, baseEnd_5479321] using wordTrace_append hprefix tailTrace_5479321
  have hstable : (prefixWord ++ tailWord_5479321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479321).length < 2 ^ (prefixWord ++ tailWord_5479321).sum := by decide
  have hdescent : baseEnd_5479321 < baseStart_5479321 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479328 : List Nat := [2, 1, 1, 4, 1, 1, 5, 1, 7]
def baseStart_5479328 : Nat := 118140960795 + 5479328 * 2 ^ 59
def prefixEnd_5479328 : Nat := 4983230072969 + 3 ^ 40 * 5479328 * 2
def baseEnd_5479328 : Nat := 312614325293204815300115

theorem tailTrace_5479328 : CollatzResearch.WordTrace tailWord_5479328 prefixEnd_5479328 312614325293204815300115 := by
  unfold tailWord_5479328
  simp only [CollatzResearch.WordTrace]
  refine ⟨99923755146668962782543319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133231673528891950376724425 99923755146668962782543319)
  ·
    refine ⟨149885632720003444173814979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99923755146668962782543319 149885632720003444173814979)
    ·
      refine ⟨224828449080005166260722469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149885632720003444173814979 224828449080005166260722469)
      ·
        refine ⟨42155334202500968673885463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 224828449080005166260722469 42155334202500968673885463)
        ·
          refine ⟨63233001303751453010828195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42155334202500968673885463 63233001303751453010828195)
          ·
            refine ⟨94849501955627179516242293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63233001303751453010828195 94849501955627179516242293)
            ·
              refine ⟨8892140808340048079647715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94849501955627179516242293 8892140808340048079647715)
              ·
                refine ⟨13338211212510072119471573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8892140808340048079647715 13338211212510072119471573)
                ·
                  refine ⟨312614325293204815300115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13338211212510072119471573 312614325293204815300115)
                  ·
                    rfl

theorem cell23_5479328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 7].length) (baseStart_5479328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479328 prefixEnd_5479328 := by exact prefixLift 5479328
  have htrace : WordTrace (prefixWord ++ tailWord_5479328) baseStart_5479328 baseEnd_5479328 := by
    simpa [prefixWord, tailWord_5479328, baseEnd_5479328] using wordTrace_append hprefix tailTrace_5479328
  have hstable : (prefixWord ++ tailWord_5479328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479328).length < 2 ^ (prefixWord ++ tailWord_5479328).sum := by decide
  have hdescent : baseEnd_5479328 < baseStart_5479328 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479435 : List Nat := [1, 1, 1, 1, 6, 2, 3, 2, 6]
def baseStart_5479435 : Nat := 118140960795 + 5479435 * 2 ^ 59
def prefixEnd_5479435 : Nat := 4983230072969 + 3 ^ 40 * 5479435 * 2
def baseEnd_5479435 : Nat := 312620430007652713229227

theorem tailTrace_5479435 : CollatzResearch.WordTrace tailWord_5479435 prefixEnd_5479435 312620430007652713229227 := by
  unfold tailWord_5479435
  simp only [CollatzResearch.WordTrace]
  refine ⟨199851412903950282839231759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133234275269300188559487839 199851412903950282839231759)
  ·
    refine ⟨299777119355925424258847639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199851412903950282839231759 299777119355925424258847639)
    ·
      refine ⟨449665679033888136388271459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299777119355925424258847639 449665679033888136388271459)
      ·
        refine ⟨674498518550832204582407189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449665679033888136388271459 674498518550832204582407189)
        ·
          refine ⟨31617118057070259589800337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 674498518550832204582407189 31617118057070259589800337)
          ·
            refine ⟨23712838542802694692350253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31617118057070259589800337 23712838542802694692350253)
            ·
              refine ⟨8892314453551010509631345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23712838542802694692350253 8892314453551010509631345)
              ·
                refine ⟨6669235840163257882223509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8892314453551010509631345 6669235840163257882223509)
                ·
                  refine ⟨312620430007652713229227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6669235840163257882223509 312620430007652713229227)
                  ·
                    rfl

theorem cell23_5479435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 3, 2, 6].length) (baseStart_5479435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479435 prefixEnd_5479435 := by exact prefixLift 5479435
  have htrace : WordTrace (prefixWord ++ tailWord_5479435) baseStart_5479435 baseEnd_5479435 := by
    simpa [prefixWord, tailWord_5479435, baseEnd_5479435] using wordTrace_append hprefix tailTrace_5479435
  have hstable : (prefixWord ++ tailWord_5479435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479435).length < 2 ^ (prefixWord ++ tailWord_5479435).sum := by decide
  have hdescent : baseEnd_5479435 < baseStart_5479435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479472 : List Nat := [2, 1, 1, 1, 2, 4, 2, 3, 2, 3, 2]
def baseStart_5479472 : Nat := 118140960795 + 5479472 * 2 ^ 59
def prefixEnd_5479472 : Nat := 4983230072969 + 3 ^ 40 * 5479472 * 2
def baseEnd_5479472 : Nat := 2813602868853090774300373

theorem tailTrace_5479472 : CollatzResearch.WordTrace tailWord_5479472 prefixEnd_5479472 2813602868853090774300373 := by
  unfold tailWord_5479472
  simp only [CollatzResearch.WordTrace]
  refine ⟨99926381202408119079164335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133235174936544158772219113 99926381202408119079164335)
  ·
    refine ⟨149889571803612178618746503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99926381202408119079164335 149889571803612178618746503)
    ·
      refine ⟨224834357705418267928119755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149889571803612178618746503 224834357705418267928119755)
      ·
        refine ⟨337251536558127401892179633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224834357705418267928119755 337251536558127401892179633)
        ·
          refine ⟨252938652418595551419134725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337251536558127401892179633 252938652418595551419134725)
          ·
            refine ⟨47425997328486665891087761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 252938652418595551419134725 47425997328486665891087761)
            ·
              refine ⟨35569497996364999418315821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47425997328486665891087761 35569497996364999418315821)
              ·
                refine ⟨13338561748636874781868433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35569497996364999418315821 13338561748636874781868433)
                ·
                  refine ⟨10003921311477656086401325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13338561748636874781868433 10003921311477656086401325)
                  ·
                    refine ⟨3751470491804121032400497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10003921311477656086401325 3751470491804121032400497)
                    ·
                      refine ⟨2813602868853090774300373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3751470491804121032400497 2813602868853090774300373)
                      ·
                        rfl

theorem cell23_5479472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 2, 3, 2].length) (baseStart_5479472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479472 prefixEnd_5479472 := by exact prefixLift 5479472
  have htrace : WordTrace (prefixWord ++ tailWord_5479472) baseStart_5479472 baseEnd_5479472 := by
    simpa [prefixWord, tailWord_5479472, baseEnd_5479472] using wordTrace_append hprefix tailTrace_5479472
  have hstable : (prefixWord ++ tailWord_5479472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479472).length < 2 ^ (prefixWord ++ tailWord_5479472).sum := by decide
  have hdescent : baseEnd_5479472 < baseStart_5479472 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479496 : List Nat := [2, 1, 3, 1, 1, 1, 7, 2, 1, 1, 3]
def baseStart_5479496 : Nat := 118140960795 + 5479496 * 2 ^ 59
def prefixEnd_5479496 : Nat := 4983230072969 + 3 ^ 40 * 5479496 * 2
def baseEnd_5479496 : Nat := 2813615192388798680400263

theorem tailTrace_5479496 : CollatzResearch.WordTrace tailWord_5479496 prefixEnd_5479496 2813615192388798680400263 := by
  unfold tailWord_5479496
  simp only [CollatzResearch.WordTrace]
  refine ⟨99926818878364645128601171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133235758504486193504801561 99926818878364645128601171)
  ·
    refine ⟨149890228317546967692901757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99926818878364645128601171 149890228317546967692901757)
    ·
      refine ⟨56208835619080112884838159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149890228317546967692901757 56208835619080112884838159)
      ·
        refine ⟨84313253428620169327257239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56208835619080112884838159 84313253428620169327257239)
        ·
          refine ⟨126469880142930253990885859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84313253428620169327257239 126469880142930253990885859)
          ·
            refine ⟨189704820214395380986328789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126469880142930253990885859 189704820214395380986328789)
            ·
              refine ⟨4446206723774891741867081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 189704820214395380986328789 4446206723774891741867081)
              ·
                refine ⟨3334655042831168806400311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4446206723774891741867081 3334655042831168806400311)
                ·
                  refine ⟨5001982564246753209600467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3334655042831168806400311 5001982564246753209600467)
                  ·
                    refine ⟨7502973846370129814400701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5001982564246753209600467 7502973846370129814400701)
                    ·
                      refine ⟨2813615192388798680400263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7502973846370129814400701 2813615192388798680400263)
                      ·
                        rfl

theorem cell23_5479496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 1, 1, 3].length) (baseStart_5479496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479496 prefixEnd_5479496 := by exact prefixLift 5479496
  have htrace : WordTrace (prefixWord ++ tailWord_5479496) baseStart_5479496 baseEnd_5479496 := by
    simpa [prefixWord, tailWord_5479496, baseEnd_5479496] using wordTrace_append hprefix tailTrace_5479496
  have hstable : (prefixWord ++ tailWord_5479496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479496).length < 2 ^ (prefixWord ++ tailWord_5479496).sum := by decide
  have hdescent : baseEnd_5479496 < baseStart_5479496 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479505 : List Nat := [1, 2, 2, 1, 3, 1, 4, 2, 1, 1, 5]
def baseStart_5479505 : Nat := 118140960795 + 5479505 * 2 ^ 59
def prefixEnd_5479505 : Nat := 4983230072969 + 3 ^ 40 * 5479505 * 2
def baseEnd_5479505 : Nat := 2813619813714689145187721

theorem tailTrace_5479505 : CollatzResearch.WordTrace tailWord_5479505 prefixEnd_5479505 2813619813714689145187721 := by
  unfold tailWord_5479505
  simp only [CollatzResearch.WordTrace]
  refine ⟨199853966013696684794279969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133235977342464456529519979 199853966013696684794279969)
  ·
    refine ⟨149890474510272513595709977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199853966013696684794279969 149890474510272513595709977)
    ·
      refine ⟨112417855882704385196782483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149890474510272513595709977 112417855882704385196782483)
      ·
        refine ⟨168626783824056577795173725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112417855882704385196782483 168626783824056577795173725)
        ·
          refine ⟨63235043934021216673190147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 168626783824056577795173725 63235043934021216673190147)
          ·
            refine ⟨94852565901031825009785221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63235043934021216673190147 94852565901031825009785221)
            ·
              refine ⟨17784856106443467189334729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94852565901031825009785221 17784856106443467189334729)
              ·
                refine ⟨13338642079832600392001047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17784856106443467189334729 13338642079832600392001047)
                ·
                  refine ⟨20007963119748900588001571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13338642079832600392001047 20007963119748900588001571)
                  ·
                    refine ⟨30011944679623350882002357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20007963119748900588001571 30011944679623350882002357)
                    ·
                      refine ⟨2813619813714689145187721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30011944679623350882002357 2813619813714689145187721)
                      ·
                        rfl

theorem cell23_5479505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_5479505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479505 prefixEnd_5479505 := by exact prefixLift 5479505
  have htrace : WordTrace (prefixWord ++ tailWord_5479505) baseStart_5479505 baseEnd_5479505 := by
    simpa [prefixWord, tailWord_5479505, baseEnd_5479505] using wordTrace_append hprefix tailTrace_5479505
  have hstable : (prefixWord ++ tailWord_5479505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479505).length < 2 ^ (prefixWord ++ tailWord_5479505).sum := by decide
  have hdescent : baseEnd_5479505 < baseStart_5479505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479512 : List Nat := [2, 1, 2, 2, 1, 3, 3, 3, 2, 4]
def baseStart_5479512 : Nat := 118140960795 + 5479512 * 2 ^ 59
def prefixEnd_5479512 : Nat := 4983230072969 + 3 ^ 40 * 5479512 * 2
def baseEnd_5479512 : Nat := 937874469359756872600063

theorem tailTrace_5479512 : CollatzResearch.WordTrace tailWord_5479512 prefixEnd_5479512 937874469359756872600063 := by
  unfold tailWord_5479512
  simp only [CollatzResearch.WordTrace]
  refine ⟨99927110662335662494892395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133236147549780883326523193 99927110662335662494892395)
  ·
    refine ⟨149890665993503493742338593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99927110662335662494892395 149890665993503493742338593)
    ·
      refine ⟨112417999495127620306753945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149890665993503493742338593 112417999495127620306753945)
      ·
        refine ⟨84313499621345715230065459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112417999495127620306753945 84313499621345715230065459)
        ·
          refine ⟨126470249432018572845098189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84313499621345715230065459 126470249432018572845098189)
          ·
            refine ⟨47426343537006964816911821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126470249432018572845098189 47426343537006964816911821)
            ·
              refine ⟨17784878826377611806341933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47426343537006964816911821 17784878826377611806341933)
              ·
                refine ⟨6669329559891604427378225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17784878826377611806341933 6669329559891604427378225)
                ·
                  refine ⟨5001997169918703320533669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6669329559891604427378225 5001997169918703320533669)
                  ·
                    refine ⟨937874469359756872600063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5001997169918703320533669 937874469359756872600063)
                    ·
                      rfl

theorem cell23_5479512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 3, 2, 4].length) (baseStart_5479512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479512 prefixEnd_5479512 := by exact prefixLift 5479512
  have htrace : WordTrace (prefixWord ++ tailWord_5479512) baseStart_5479512 baseEnd_5479512 := by
    simpa [prefixWord, tailWord_5479512, baseEnd_5479512] using wordTrace_append hprefix tailTrace_5479512
  have hstable : (prefixWord ++ tailWord_5479512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479512).length < 2 ^ (prefixWord ++ tailWord_5479512).sum := by decide
  have hdescent : baseEnd_5479512 < baseStart_5479512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479536 : List Nat := [2, 1, 1, 1, 5, 1, 2, 5, 1, 2, 2]
def baseStart_5479536 : Nat := 118140960795 + 5479536 * 2 ^ 59
def prefixEnd_5479536 : Nat := 4983230072969 + 3 ^ 40 * 5479536 * 2
def baseEnd_5479536 : Nat := 2813635731614978523900079

theorem tailTrace_5479536 : CollatzResearch.WordTrace tailWord_5479536 prefixEnd_5479536 2813635731614978523900079 := by
  unfold tailWord_5479536
  simp only [CollatzResearch.WordTrace]
  refine ⟨99927548338292188544329231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133236731117722918059105641 99927548338292188544329231)
  ·
    refine ⟨149891322507438282816493847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99927548338292188544329231 149891322507438282816493847)
    ·
      refine ⟨224836983761157424224740771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149891322507438282816493847 224836983761157424224740771)
      ·
        refine ⟨337255475641736136337111157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224836983761157424224740771 337255475641736136337111157)
        ·
          refine ⟨31617700841412762781604171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 337255475641736136337111157 31617700841412762781604171)
          ·
            refine ⟨47426551262119144172406257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31617700841412762781604171 47426551262119144172406257)
            ·
              refine ⟨35569913446589358129304693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47426551262119144172406257 35569913446589358129304693)
              ·
                refine ⟨3334679385617752324622315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35569913446589358129304693 3334679385617752324622315)
                ·
                  refine ⟨5002019078426628486933473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3334679385617752324622315 5002019078426628486933473)
                  ·
                    refine ⟨3751514308819971365200105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5002019078426628486933473 3751514308819971365200105)
                    ·
                      refine ⟨2813635731614978523900079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3751514308819971365200105 2813635731614978523900079)
                      ·
                        rfl

theorem cell23_5479536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 5, 1, 2, 2].length) (baseStart_5479536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479536 prefixEnd_5479536 := by exact prefixLift 5479536
  have htrace : WordTrace (prefixWord ++ tailWord_5479536) baseStart_5479536 baseEnd_5479536 := by
    simpa [prefixWord, tailWord_5479536, baseEnd_5479536] using wordTrace_append hprefix tailTrace_5479536
  have hstable : (prefixWord ++ tailWord_5479536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479536).length < 2 ^ (prefixWord ++ tailWord_5479536).sum := by decide
  have hdescent : baseEnd_5479536 < baseStart_5479536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479552 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 4, 1, 3]
def baseStart_5479552 : Nat := 118140960795 + 5479552 * 2 ^ 59
def prefixEnd_5479552 : Nat := 4983230072969 + 3 ^ 40 * 5479552 * 2
def baseEnd_5479552 : Nat := 2813643947305450461300005

theorem tailTrace_5479552 : CollatzResearch.WordTrace tailWord_5479552 prefixEnd_5479552 2813643947305450461300005 := by
  unfold tailWord_5479552
  simp only [CollatzResearch.WordTrace]
  refine ⟨99927840122263205910620455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133237120163017607880827273 99927840122263205910620455)
  ·
    refine ⟨149891760183394808865930683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99927840122263205910620455 149891760183394808865930683)
    ·
      refine ⟨224837640275092213298896025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149891760183394808865930683 224837640275092213298896025)
      ·
        refine ⟨168628230206319159974172019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224837640275092213298896025 168628230206319159974172019)
        ·
          refine ⟨252942345309478739961258029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168628230206319159974172019 252942345309478739961258029)
          ·
            refine ⟨94853379491054527485471761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252942345309478739961258029 94853379491054527485471761)
            ·
              refine ⟨71140034618290895614103821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94853379491054527485471761 71140034618290895614103821)
              ·
                refine ⟨26677512981859085855288933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 71140034618290895614103821 26677512981859085855288933)
                ·
                  refine ⟨5002033684098578597866675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26677512981859085855288933 5002033684098578597866675)
                  ·
                    refine ⟨7503050526147867896800013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5002033684098578597866675 7503050526147867896800013)
                    ·
                      refine ⟨2813643947305450461300005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7503050526147867896800013 2813643947305450461300005)
                      ·
                        rfl

theorem cell23_5479552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 4, 1, 3].length) (baseStart_5479552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479552 prefixEnd_5479552 := by exact prefixLift 5479552
  have htrace : WordTrace (prefixWord ++ tailWord_5479552) baseStart_5479552 baseEnd_5479552 := by
    simpa [prefixWord, tailWord_5479552, baseEnd_5479552] using wordTrace_append hprefix tailTrace_5479552
  have hstable : (prefixWord ++ tailWord_5479552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479552).length < 2 ^ (prefixWord ++ tailWord_5479552).sum := by decide
  have hdescent : baseEnd_5479552 < baseStart_5479552 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479553 : List Nat := [1, 2, 4, 2, 2, 2, 1, 4, 1, 2, 2]
def baseStart_5479553 : Nat := 118140960795 + 5479553 * 2 ^ 59
def prefixEnd_5479553 : Nat := 4983230072969 + 3 ^ 40 * 5479553 * 2
def baseEnd_5479553 : Nat := 2813644460786104957387501

theorem tailTrace_5479553 : CollatzResearch.WordTrace tailWord_5479553 prefixEnd_5479553 2813644460786104957387501 := by
  unfold tailWord_5479553
  simp only [CollatzResearch.WordTrace]
  refine ⟨199855716717522788992027313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133237144478348525994684875 199855716717522788992027313)
  ·
    refine ⟨149891787538142091744020485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199855716717522788992027313 149891787538142091744020485)
    ·
      refine ⟨28104710163401642202003841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149891787538142091744020485 28104710163401642202003841)
      ·
        refine ⟨21078532622551231651502881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28104710163401642202003841 21078532622551231651502881)
        ·
          refine ⟨15808899466913423738627161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21078532622551231651502881 15808899466913423738627161)
          ·
            refine ⟨11856674600185067803970371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15808899466913423738627161 11856674600185067803970371)
            ·
              refine ⟨17785011900277601705955557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11856674600185067803970371 17785011900277601705955557)
              ·
                refine ⟨3334689731302050319866667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17785011900277601705955557 3334689731302050319866667)
                ·
                  refine ⟨5002034596953075479800001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3334689731302050319866667 5002034596953075479800001)
                  ·
                    refine ⟨3751525947714806609850001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5002034596953075479800001 3751525947714806609850001)
                    ·
                      refine ⟨2813644460786104957387501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3751525947714806609850001 2813644460786104957387501)
                      ·
                        rfl

theorem cell23_5479553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_5479553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479553 prefixEnd_5479553 := by exact prefixLift 5479553
  have htrace : WordTrace (prefixWord ++ tailWord_5479553) baseStart_5479553 baseEnd_5479553 := by
    simpa [prefixWord, tailWord_5479553, baseEnd_5479553] using wordTrace_append hprefix tailTrace_5479553
  have hstable : (prefixWord ++ tailWord_5479553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479553).length < 2 ^ (prefixWord ++ tailWord_5479553).sum := by decide
  have hdescent : baseEnd_5479553 < baseStart_5479553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479585 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 1, 8]
def baseStart_5479585 : Nat := 118140960795 + 5479585 * 2 ^ 59
def prefixEnd_5479585 : Nat := 4983230072969 + 3 ^ 40 * 5479585 * 2
def baseEnd_5479585 : Nat := 937886964055682944062451

theorem tailTrace_5479585 : CollatzResearch.WordTrace tailWord_5479585 prefixEnd_5479585 937886964055682944062451 := by
  unfold tailWord_5479585
  simp only [CollatzResearch.WordTrace]
  refine ⟨199856883853406858457192209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133237922568937905638128139 199856883853406858457192209)
  ·
    refine ⟨149892662890055143842894157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199856883853406858457192209 149892662890055143842894157)
    ·
      refine ⟨56209748583770678941085309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149892662890055143842894157 56209748583770678941085309)
      ·
        refine ⟨21078655718914004602906991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56209748583770678941085309 21078655718914004602906991)
        ·
          refine ⟨31617983578371006904360487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21078655718914004602906991 31617983578371006904360487)
          ·
            refine ⟨47426975367556510356540731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31617983578371006904360487 47426975367556510356540731)
            ·
              refine ⟨71140463051334765534811097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47426975367556510356540731 71140463051334765534811097)
              ·
                refine ⟨53355347288501074151108323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 71140463051334765534811097 53355347288501074151108323)
                ·
                  refine ⟨80033020932751611226662485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 53355347288501074151108323 80033020932751611226662485)
                  ·
                    refine ⟨937886964055682944062451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 80033020932751611226662485 937886964055682944062451)
                    ·
                      rfl

theorem cell23_5479585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 8].length) (baseStart_5479585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479585 prefixEnd_5479585 := by exact prefixLift 5479585
  have htrace : WordTrace (prefixWord ++ tailWord_5479585) baseStart_5479585 baseEnd_5479585 := by
    simpa [prefixWord, tailWord_5479585, baseEnd_5479585] using wordTrace_append hprefix tailTrace_5479585
  have hstable : (prefixWord ++ tailWord_5479585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479585).length < 2 ^ (prefixWord ++ tailWord_5479585).sum := by decide
  have hdescent : baseEnd_5479585 < baseStart_5479585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479615 : List Nat := [1, 1, 2, 2, 2, 2, 3, 3, 7]
def baseStart_5479615 : Nat := 118140960795 + 5479615 * 2 ^ 59
def prefixEnd_5479615 : Nat := 4983230072969 + 3 ^ 40 * 5479615 * 2
def baseEnd_5479615 : Nat := 312630699620742634979135

theorem tailTrace_5479615 : CollatzResearch.WordTrace tailWord_5479615 prefixEnd_5479615 312630699620742634979135 := by
  unfold tailWord_5479615
  simp only [CollatzResearch.WordTrace]
  refine ⟨199857978043298173580784299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133238652028865449053856199 199857978043298173580784299)
  ·
    refine ⟨299786967064947260371176449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199857978043298173580784299 299786967064947260371176449)
    ·
      refine ⟨224840225298710445278382337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299786967064947260371176449 224840225298710445278382337)
      ·
        refine ⟨168630168974032833958786753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224840225298710445278382337 168630168974032833958786753)
        ·
          refine ⟨126472626730524625469090065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168630168974032833958786753 126472626730524625469090065)
          ·
            refine ⟨94854470047893469101817549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126472626730524625469090065 94854470047893469101817549)
            ·
              refine ⟨35570426267960050913181581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94854470047893469101817549 35570426267960050913181581)
              ·
                refine ⟨13338909850485019092443093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35570426267960050913181581 13338909850485019092443093)
                ·
                  refine ⟨312630699620742634979135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13338909850485019092443093 312630699620742634979135)
                  ·
                    rfl

theorem cell23_5479615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 7].length) (baseStart_5479615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479615 prefixEnd_5479615 := by exact prefixLift 5479615
  have htrace : WordTrace (prefixWord ++ tailWord_5479615) baseStart_5479615 baseEnd_5479615 := by
    simpa [prefixWord, tailWord_5479615, baseEnd_5479615] using wordTrace_append hprefix tailTrace_5479615
  have hstable : (prefixWord ++ tailWord_5479615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479615).length < 2 ^ (prefixWord ++ tailWord_5479615).sum := by decide
  have hdescent : baseEnd_5479615 < baseStart_5479615 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479626 : List Nat := [3, 1, 2, 1, 3, 4, 1, 1, 1, 4, 2]
def baseStart_5479626 : Nat := 118140960795 + 5479626 * 2 ^ 59
def prefixEnd_5479626 : Nat := 4983230072969 + 3 ^ 40 * 5479626 * 2
def baseEnd_5479626 : Nat := 2813681944873883171774665

theorem tailTrace_5479626 : CollatzResearch.WordTrace tailWord_5479626 prefixEnd_5479626 2813681944873883171774665 := by
  unfold tailWord_5479626
  simp only [CollatzResearch.WordTrace]
  refine ⟨49964594811564580614858683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133238919497505548306289821 49964594811564580614858683)
  ·
    refine ⟨74946892217346870922288025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49964594811564580614858683 74946892217346870922288025)
    ·
      refine ⟨56210169163010153191716019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74946892217346870922288025 56210169163010153191716019)
      ·
        refine ⟨84315253744515229787574029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56210169163010153191716019 84315253744515229787574029)
        ·
          refine ⟨31618220154193211170340261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84315253744515229787574029 31618220154193211170340261)
          ·
            refine ⟨5928416278911227094438799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31618220154193211170340261 5928416278911227094438799)
            ·
              refine ⟨8892624418366840641658199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5928416278911227094438799 8892624418366840641658199)
              ·
                refine ⟨13338936627550260962487299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8892624418366840641658199 13338936627550260962487299)
                ·
                  refine ⟨20008404941325391443730949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13338936627550260962487299 20008404941325391443730949)
                  ·
                    refine ⟨3751575926498510895699553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20008404941325391443730949 3751575926498510895699553)
                    ·
                      refine ⟨2813681944873883171774665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3751575926498510895699553 2813681944873883171774665)
                      ·
                        rfl

theorem cell23_5479626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 1, 1, 4, 2].length) (baseStart_5479626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479626 prefixEnd_5479626 := by exact prefixLift 5479626
  have htrace : WordTrace (prefixWord ++ tailWord_5479626) baseStart_5479626 baseEnd_5479626 := by
    simpa [prefixWord, tailWord_5479626, baseEnd_5479626] using wordTrace_append hprefix tailTrace_5479626
  have hstable : (prefixWord ++ tailWord_5479626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479626).length < 2 ^ (prefixWord ++ tailWord_5479626).sum := by decide
  have hdescent : baseEnd_5479626 < baseStart_5479626 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479649 : List Nat := [1, 2, 3, 1, 3, 2, 3, 3, 5]
def baseStart_5479649 : Nat := 118140960795 + 5479649 * 2 ^ 59
def prefixEnd_5479649 : Nat := 4983230072969 + 3 ^ 40 * 5479649 * 2
def baseEnd_5479649 : Nat := 312632639436548509087451

theorem tailTrace_5479649 : CollatzResearch.WordTrace tailWord_5479649 prefixEnd_5479649 312632639436548509087451 := by
  unfold tailWord_5479649
  simp only [CollatzResearch.WordTrace]
  refine ⟨199859218125174997387522001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133239478750116664925014667 199859218125174997387522001)
  ·
    refine ⟨149894413593881248040641501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199859218125174997387522001 149894413593881248040641501)
    ·
      refine ⟨56210405097705468015240563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149894413593881248040641501 56210405097705468015240563)
      ·
        refine ⟨84315607646558202022860845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56210405097705468015240563 84315607646558202022860845)
        ·
          refine ⟨31618352867459325758572817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84315607646558202022860845 31618352867459325758572817)
          ·
            refine ⟨23713764650594494318929613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31618352867459325758572817 23713764650594494318929613)
            ·
              refine ⟨8892661743972935369598605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23713764650594494318929613 8892661743972935369598605)
              ·
                refine ⟨3334748153989850763599477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8892661743972935369598605 3334748153989850763599477)
                ·
                  refine ⟨312632639436548509087451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3334748153989850763599477 312632639436548509087451)
                  ·
                    rfl

theorem cell23_5479649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 5].length) (baseStart_5479649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479649 prefixEnd_5479649 := by exact prefixLift 5479649
  have htrace : WordTrace (prefixWord ++ tailWord_5479649) baseStart_5479649 baseEnd_5479649 := by
    simpa [prefixWord, tailWord_5479649, baseEnd_5479649] using wordTrace_append hprefix tailTrace_5479649
  have hstable : (prefixWord ++ tailWord_5479649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479649).length < 2 ^ (prefixWord ++ tailWord_5479649).sum := by decide
  have hdescent : baseEnd_5479649 < baseStart_5479649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479662 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 4, 5]
def baseStart_5479662 : Nat := 118140960795 + 5479662 * 2 ^ 59
def prefixEnd_5479662 : Nat := 4983230072969 + 3 ^ 40 * 5479662 * 2
def baseEnd_5479662 : Nat := 937900143392481676974833

theorem tailTrace_5479662 : CollatzResearch.WordTrace tailWord_5479662 prefixEnd_5479662 937900143392481676974833 := by
  unfold tailWord_5479662
  simp only [CollatzResearch.WordTrace]
  refine ⟨24982461534265987575968155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133239794849418600405163493 24982461534265987575968155)
  ·
    refine ⟨37473692301398981363952233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24982461534265987575968155 37473692301398981363952233)
    ·
      refine ⟨28105269226049236022964175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37473692301398981363952233 28105269226049236022964175)
      ·
        refine ⟨42157903839073854034446263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28105269226049236022964175 42157903839073854034446263)
        ·
          refine ⟨63236855758610781051669395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42157903839073854034446263 63236855758610781051669395)
          ·
            refine ⟨94855283637916171577504093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63236855758610781051669395 94855283637916171577504093)
            ·
              refine ⟨35570731364218564341564035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94855283637916171577504093 35570731364218564341564035)
              ·
                refine ⟨53356097046327846512346053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35570731364218564341564035 53356097046327846512346053)
                ·
                  refine ⟨10004268196186471221064885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 53356097046327846512346053 10004268196186471221064885)
                  ·
                    refine ⟨937900143392481676974833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10004268196186471221064885 937900143392481676974833)
                    ·
                      rfl

theorem cell23_5479662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 4, 5].length) (baseStart_5479662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479662 prefixEnd_5479662 := by exact prefixLift 5479662
  have htrace : WordTrace (prefixWord ++ tailWord_5479662) baseStart_5479662 baseEnd_5479662 := by
    simpa [prefixWord, tailWord_5479662, baseEnd_5479662] using wordTrace_append hprefix tailTrace_5479662
  have hstable : (prefixWord ++ tailWord_5479662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479662).length < 2 ^ (prefixWord ++ tailWord_5479662).sum := by decide
  have hdescent : baseEnd_5479662 < baseStart_5479662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479666 : List Nat := [3, 2, 1, 3, 4, 1, 1, 1, 7]
def baseStart_5479666 : Nat := 118140960795 + 5479666 * 2 ^ 59
def prefixEnd_5479666 : Nat := 4983230072969 + 3 ^ 40 * 5479666 * 2
def baseEnd_5479666 : Nat := 312633609344451446141609

theorem tailTrace_5479666 : CollatzResearch.WordTrace tailWord_5479666 prefixEnd_5479666 312633609344451446141609 := by
  unfold tailWord_5479666
  simp only [CollatzResearch.WordTrace]
  refine ⟨49964959541528352322722713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133239892110742272860593901 49964959541528352322722713)
  ·
    refine ⟨37473719656146264242042035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49964959541528352322722713 37473719656146264242042035)
    ·
      refine ⟨56210579484219396363063053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37473719656146264242042035 56210579484219396363063053)
      ·
        refine ⟨21078967306582273636148645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56210579484219396363063053 21078967306582273636148645)
        ·
          refine ⟨3952306369984176306777871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21078967306582273636148645 3952306369984176306777871)
          ·
            refine ⟨5928459554976264460166807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3952306369984176306777871 5928459554976264460166807)
            ·
              refine ⟨8892689332464396690250211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5928459554976264460166807 8892689332464396690250211)
              ·
                refine ⟨13339033998696595035375317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8892689332464396690250211 13339033998696595035375317)
                ·
                  refine ⟨312633609344451446141609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13339033998696595035375317 312633609344451446141609)
                  ·
                    rfl

theorem cell23_5479666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 1, 7].length) (baseStart_5479666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479666 prefixEnd_5479666 := by exact prefixLift 5479666
  have htrace : WordTrace (prefixWord ++ tailWord_5479666) baseStart_5479666 baseEnd_5479666 := by
    simpa [prefixWord, tailWord_5479666, baseEnd_5479666] using wordTrace_append hprefix tailTrace_5479666
  have hstable : (prefixWord ++ tailWord_5479666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479666).length < 2 ^ (prefixWord ++ tailWord_5479666).sum := by decide
  have hdescent : baseEnd_5479666 < baseStart_5479666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479695 : List Nat := [1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 6]
def baseStart_5479695 : Nat := 118140960795 + 5479695 * 2 ^ 59
def prefixEnd_5479695 : Nat := 4983230072969 + 3 ^ 40 * 5479695 * 2
def baseEnd_5479695 : Nat := 2813717375039043401811847

theorem tailTrace_5479695 : CollatzResearch.WordTrace tailWord_5479695 prefixEnd_5479695 2813717375039043401811847 := by
  unfold tailWord_5479695
  simp only [CollatzResearch.WordTrace]
  refine ⟨199860895883008347243696539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133240597255338898162464359 199860895883008347243696539)
  ·
    refine ⟨299791343824512520865544809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199860895883008347243696539 299791343824512520865544809)
    ·
      refine ⟨224843507868384390649158607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299791343824512520865544809 224843507868384390649158607)
      ·
        refine ⟨337265261802576585973737911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224843507868384390649158607 337265261802576585973737911)
        ·
          refine ⟨505897892703864878960606867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337265261802576585973737911 505897892703864878960606867)
          ·
            refine ⟨758846839055797318440910301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505897892703864878960606867 758846839055797318440910301)
            ·
              refine ⟨284567564645923994415341363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 758846839055797318440910301 284567564645923994415341363)
              ·
                refine ⟨426851346968885991623012045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284567564645923994415341363 426851346968885991623012045)
                ·
                  refine ⟨160069255113332246858629517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 426851346968885991623012045 160069255113332246858629517)
                  ·
                    refine ⟨60025970667499592571986069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 160069255113332246858629517 60025970667499592571986069)
                    ·
                      refine ⟨2813717375039043401811847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60025970667499592571986069 2813717375039043401811847)
                      ·
                        rfl

theorem cell23_5479695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 1, 3, 3, 6].length) (baseStart_5479695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479695 prefixEnd_5479695 := by exact prefixLift 5479695
  have htrace : WordTrace (prefixWord ++ tailWord_5479695) baseStart_5479695 baseEnd_5479695 := by
    simpa [prefixWord, tailWord_5479695, baseEnd_5479695] using wordTrace_append hprefix tailTrace_5479695
  have hstable : (prefixWord ++ tailWord_5479695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479695).length < 2 ^ (prefixWord ++ tailWord_5479695).sum := by decide
  have hdescent : baseEnd_5479695 < baseStart_5479695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479762 : List Nat := [3, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5]
def baseStart_5479762 : Nat := 118140960795 + 5479762 * 2 ^ 59
def prefixEnd_5479762 : Nat := 4983230072969 + 3 ^ 40 * 5479762 * 2
def baseEnd_5479762 : Nat := 2813751778242894639674039

theorem tailTrace_5479762 : CollatzResearch.WordTrace tailWord_5479762 prefixEnd_5479762 2813751778242894639674039 := by
  unfold tailWord_5479762
  simp only [CollatzResearch.WordTrace]
  refine ⟨49965834893441404421596385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133242226382510411790923693 49965834893441404421596385)
  ·
    refine ⟨37474376170081053316197289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49965834893441404421596385 37474376170081053316197289)
    ·
      refine ⟨28105782127560789987147967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37474376170081053316197289 28105782127560789987147967)
      ·
        refine ⟨42158673191341184980721951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28105782127560789987147967 42158673191341184980721951)
        ·
          refine ⟨63238009787011777471082927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42158673191341184980721951 63238009787011777471082927)
          ·
            refine ⟨94857014680517666206624391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63238009787011777471082927 94857014680517666206624391)
            ·
              refine ⟨142285522020776499309936587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94857014680517666206624391 142285522020776499309936587)
              ·
                refine ⟨213428283031164748964904881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142285522020776499309936587 213428283031164748964904881)
                ·
                  refine ⟨160071212273373561723678661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 213428283031164748964904881 160071212273373561723678661)
                  ·
                    refine ⟨30013352301257542823189749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 160071212273373561723678661 30013352301257542823189749)
                    ·
                      refine ⟨2813751778242894639674039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30013352301257542823189749 2813751778242894639674039)
                      ·
                        rfl

theorem cell23_5479762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_5479762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479762 prefixEnd_5479762 := by exact prefixLift 5479762
  have htrace : WordTrace (prefixWord ++ tailWord_5479762) baseStart_5479762 baseEnd_5479762 := by
    simpa [prefixWord, tailWord_5479762, baseEnd_5479762] using wordTrace_append hprefix tailTrace_5479762
  have hstable : (prefixWord ++ tailWord_5479762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479762).length < 2 ^ (prefixWord ++ tailWord_5479762).sum := by decide
  have hdescent : baseEnd_5479762 < baseStart_5479762 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479773 : List Nat := [1, 4, 5, 1, 1, 1, 1, 1, 8]
def baseStart_5479773 : Nat := 118140960795 + 5479773 * 2 ^ 59
def prefixEnd_5479773 : Nat := 4983230072969 + 3 ^ 40 * 5479773 * 2
def baseEnd_5479773 : Nat := 312639714058899344070721

theorem tailTrace_5479773 : CollatzResearch.WordTrace tailWord_5479773 prefixEnd_5479773 312639714058899344070721 := by
  unfold tailWord_5479773
  simp only [CollatzResearch.WordTrace]
  refine ⟨199863740776725766565035973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133242493851150511043357315 199863740776725766565035973)
  ·
    refine ⟨37474451395636081230944245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199863740776725766565035973 37474451395636081230944245)
    ·
      refine ⟨3513229818340882615401023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37474451395636081230944245 3513229818340882615401023)
      ·
        refine ⟨5269844727511323923101535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3513229818340882615401023 5269844727511323923101535)
        ·
          refine ⟨7904767091266985884652303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5269844727511323923101535 7904767091266985884652303)
          ·
            refine ⟨11857150636900478826978455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7904767091266985884652303 11857150636900478826978455)
            ·
              refine ⟨17785725955350718240467683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11857150636900478826978455 17785725955350718240467683)
              ·
                refine ⟨26678588933026077360701525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17785725955350718240467683 26678588933026077360701525)
                ·
                  refine ⟨312639714058899344070721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26678588933026077360701525 312639714058899344070721)
                  ·
                    rfl

theorem cell23_5479773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_5479773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479773 prefixEnd_5479773 := by exact prefixLift 5479773
  have htrace : WordTrace (prefixWord ++ tailWord_5479773) baseStart_5479773 baseEnd_5479773 := by
    simpa [prefixWord, tailWord_5479773, baseEnd_5479773] using wordTrace_append hprefix tailTrace_5479773
  have hstable : (prefixWord ++ tailWord_5479773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479773).length < 2 ^ (prefixWord ++ tailWord_5479773).sum := by decide
  have hdescent : baseEnd_5479773 < baseStart_5479773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479783 : List Nat := [1, 1, 5, 1, 4, 1, 2, 1, 3, 1, 3]
def baseStart_5479783 : Nat := 118140960795 + 5479783 * 2 ^ 59
def prefixEnd_5479783 : Nat := 4983230072969 + 3 ^ 40 * 5479783 * 2
def baseEnd_5479783 : Nat := 2813762561336639057511443

theorem tailTrace_5479783 : CollatzResearch.WordTrace tailWord_5479783 prefixEnd_5479783 2813762561336639057511443 := by
  unfold tailWord_5479783
  simp only [CollatzResearch.WordTrace]
  refine ⟨199864105506689538272900003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133242737004459692181933335 199864105506689538272900003)
  ·
    refine ⟨299796158260034307409350005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199864105506689538272900003 299796158260034307409350005)
    ·
      refine ⟨28105889836878216319626563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 299796158260034307409350005 28105889836878216319626563)
      ·
        refine ⟨42158834755317324479439845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28105889836878216319626563 42158834755317324479439845)
        ·
          refine ⟨7904781516621998339894971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42158834755317324479439845 7904781516621998339894971)
          ·
            refine ⟨11857172274932997509842457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7904781516621998339894971 11857172274932997509842457)
            ·
              refine ⟨8892879206199748132381843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11857172274932997509842457 8892879206199748132381843)
              ·
                refine ⟨13339318809299622198572765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8892879206199748132381843 13339318809299622198572765)
                ·
                  refine ⟨5002244553487358324464787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13339318809299622198572765 5002244553487358324464787)
                  ·
                    refine ⟨7503366830231037486697181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5002244553487358324464787 7503366830231037486697181)
                    ·
                      refine ⟨2813762561336639057511443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7503366830231037486697181 2813762561336639057511443)
                      ·
                        rfl

theorem cell23_5479783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 1, 3, 1, 3].length) (baseStart_5479783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479783 prefixEnd_5479783 := by exact prefixLift 5479783
  have htrace : WordTrace (prefixWord ++ tailWord_5479783) baseStart_5479783 baseEnd_5479783 := by
    simpa [prefixWord, tailWord_5479783, baseEnd_5479783] using wordTrace_append hprefix tailTrace_5479783
  have hstable : (prefixWord ++ tailWord_5479783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479783).length < 2 ^ (prefixWord ++ tailWord_5479783).sum := by decide
  have hdescent : baseEnd_5479783 < baseStart_5479783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479802 : List Nat := [3, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6]
def baseStart_5479802 : Nat := 118140960795 + 5479802 * 2 ^ 59
def prefixEnd_5479802 : Nat := 4983230072969 + 3 ^ 40 * 5479802 * 2
def baseEnd_5479802 : Nat := 2813772317469074483173855

theorem tailTrace_5479802 : CollatzResearch.WordTrace tailWord_5479802 prefixEnd_5479802 2813772317469074483173855 := by
  unfold tailWord_5479802
  simp only [CollatzResearch.WordTrace]
  refine ⟨49966199623405176129460415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133243198995747136345227773 49966199623405176129460415)
  ·
    refine ⟨74949299435107764194190623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49966199623405176129460415 74949299435107764194190623)
    ·
      refine ⟨112423949152661646291285935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74949299435107764194190623 112423949152661646291285935)
      ·
        refine ⟨168635923728992469436928903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112423949152661646291285935 168635923728992469436928903)
        ·
          refine ⟨252953885593488704155393355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168635923728992469436928903 252953885593488704155393355)
          ·
            refine ⟨379430828390233056233090033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252953885593488704155393355 379430828390233056233090033)
            ·
              refine ⟨284573121292674792174817525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 379430828390233056233090033 284573121292674792174817525)
              ·
                refine ⟨26678730121188261766389143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 284573121292674792174817525 26678730121188261766389143)
                ·
                  refine ⟨40018095181782392649583715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26678730121188261766389143 40018095181782392649583715)
                  ·
                    refine ⟨60027142772673588974375573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40018095181782392649583715 60027142772673588974375573)
                    ·
                      refine ⟨2813772317469074483173855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 60027142772673588974375573 2813772317469074483173855)
                      ·
                        rfl

theorem cell23_5479802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6].length) (baseStart_5479802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479802 prefixEnd_5479802 := by exact prefixLift 5479802
  have htrace : WordTrace (prefixWord ++ tailWord_5479802) baseStart_5479802 baseEnd_5479802 := by
    simpa [prefixWord, tailWord_5479802, baseEnd_5479802] using wordTrace_append hprefix tailTrace_5479802
  have hstable : (prefixWord ++ tailWord_5479802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479802).length < 2 ^ (prefixWord ++ tailWord_5479802).sum := by decide
  have hdescent : baseEnd_5479802 < baseStart_5479802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479817 : List Nat := [1, 2, 1, 1, 8, 1, 1, 3, 1, 1, 3]
def baseStart_5479817 : Nat := 118140960795 + 5479817 * 2 ^ 59
def prefixEnd_5479817 : Nat := 4983230072969 + 3 ^ 40 * 5479817 * 2
def baseEnd_5479817 : Nat := 2813780019678891924486287

theorem tailTrace_5479817 : CollatzResearch.WordTrace tailWord_5479817 prefixEnd_5479817 2813780019678891924486287 := by
  unfold tailWord_5479817
  simp only [CollatzResearch.WordTrace]
  refine ⟨199865345588566362079637705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133243563725710908053091803 199865345588566362079637705)
  ·
    refine ⟨149899009191424771559728279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199865345588566362079637705 149899009191424771559728279)
    ·
      refine ⟨224848513787137157339592419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149899009191424771559728279 224848513787137157339592419)
      ·
        refine ⟨337272770680705736009388629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224848513787137157339592419 337272770680705736009388629)
        ·
          refine ⟨3952415281414520343860023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 337272770680705736009388629 3952415281414520343860023)
          ·
            refine ⟨5928622922121780515790035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3952415281414520343860023 5928622922121780515790035)
            ·
              refine ⟨8892934383182670773685053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5928622922121780515790035 8892934383182670773685053)
              ·
                refine ⟨3334850393693501540131895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8892934383182670773685053 3334850393693501540131895)
                ·
                  refine ⟨5002275590540252310197843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3334850393693501540131895 5002275590540252310197843)
                  ·
                    refine ⟨7503413385810378465296765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5002275590540252310197843 7503413385810378465296765)
                    ·
                      refine ⟨2813780019678891924486287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7503413385810378465296765 2813780019678891924486287)
                      ·
                        rfl

theorem cell23_5479817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 1, 1, 3].length) (baseStart_5479817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479817 prefixEnd_5479817 := by exact prefixLift 5479817
  have htrace : WordTrace (prefixWord ++ tailWord_5479817) baseStart_5479817 baseEnd_5479817 := by
    simpa [prefixWord, tailWord_5479817, baseEnd_5479817] using wordTrace_append hprefix tailTrace_5479817
  have hstable : (prefixWord ++ tailWord_5479817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479817).length < 2 ^ (prefixWord ++ tailWord_5479817).sum := by decide
  have hdescent : baseEnd_5479817 < baseStart_5479817 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479849 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 1, 9, 2]
def baseStart_5479849 : Nat := 118140960795 + 5479849 * 2 ^ 59
def prefixEnd_5479849 : Nat := 4983230072969 + 3 ^ 40 * 5479849 * 2
def baseEnd_5479849 : Nat := 2813796451059835799286139

theorem tailTrace_5479849 : CollatzResearch.WordTrace tailWord_5479849 prefixEnd_5479849 2813796451059835799286139 := by
  unfold tailWord_5479849
  simp only [CollatzResearch.WordTrace]
  refine ⟨199866512724450431544802601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133244341816300287696535067 199866512724450431544802601)
  ·
    refine ⟨149899884543337823658601951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199866512724450431544802601 149899884543337823658601951)
    ·
      refine ⟨224849826815006735487902927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149899884543337823658601951 224849826815006735487902927)
      ·
        refine ⟨337274740222510103231854391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224849826815006735487902927 337274740222510103231854391)
        ·
          refine ⟨505912110333765154847781587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337274740222510103231854391 505912110333765154847781587)
          ·
            refine ⟨758868165500647732271672381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 505912110333765154847781587 758868165500647732271672381)
            ·
              refine ⟨284575562062742899601877143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 758868165500647732271672381 284575562062742899601877143)
              ·
                refine ⟨426863343094114349402815715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284575562062742899601877143 426863343094114349402815715)
                ·
                  refine ⟨640295014641171524104223573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 426863343094114349402815715 640295014641171524104223573)
                  ·
                    refine ⟨3751728601413114399048185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 640295014641171524104223573 3751728601413114399048185)
                    ·
                      refine ⟨2813796451059835799286139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3751728601413114399048185 2813796451059835799286139)
                      ·
                        rfl

theorem cell23_5479849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 1, 9, 2].length) (baseStart_5479849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479849 prefixEnd_5479849 := by exact prefixLift 5479849
  have htrace : WordTrace (prefixWord ++ tailWord_5479849) baseStart_5479849 baseEnd_5479849 := by
    simpa [prefixWord, tailWord_5479849, baseEnd_5479849] using wordTrace_append hprefix tailTrace_5479849
  have hstable : (prefixWord ++ tailWord_5479849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479849).length < 2 ^ (prefixWord ++ tailWord_5479849).sum := by decide
  have hdescent : baseEnd_5479849 < baseStart_5479849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479929 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 3, 5, 3]
def baseStart_5479929 : Nat := 118140960795 + 5479929 * 2 ^ 59
def prefixEnd_5479929 : Nat := 4983230072969 + 3 ^ 40 * 5479929 * 2
def baseEnd_5479929 : Nat := 2813837529512195486285771

theorem tailTrace_5479929 : CollatzResearch.WordTrace tailWord_5479929 prefixEnd_5479929 2813837529512195486285771 := by
  unfold tailWord_5479929
  simp only [CollatzResearch.WordTrace]
  refine ⟨199869430564160605207714841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133246287042773736805143227 199869430564160605207714841)
  ·
    refine ⟨149902072923120453905786131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199869430564160605207714841 149902072923120453905786131)
    ·
      refine ⟨224853109384680680858679197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149902072923120453905786131 224853109384680680858679197)
      ·
        refine ⟨84319916019255255322004699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224853109384680680858679197 84319916019255255322004699)
        ·
          refine ⟨126479874028882882983007049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84319916019255255322004699 126479874028882882983007049)
          ·
            refine ⟨94859905521662162237255287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 126479874028882882983007049 94859905521662162237255287)
            ·
              refine ⟨142289858282493243355882931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94859905521662162237255287 142289858282493243355882931)
              ·
                refine ⟨213434787423739865033824397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142289858282493243355882931 213434787423739865033824397)
                ·
                  refine ⟨80038045283902449387684149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 213434787423739865033824397 80038045283902449387684149)
                  ·
                    refine ⟨7503566745365854630095389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 80038045283902449387684149 7503566745365854630095389)
                    ·
                      refine ⟨2813837529512195486285771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7503566745365854630095389 2813837529512195486285771)
                      ·
                        rfl

theorem cell23_5479929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 5, 3].length) (baseStart_5479929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479929 prefixEnd_5479929 := by exact prefixLift 5479929
  have htrace : WordTrace (prefixWord ++ tailWord_5479929) baseStart_5479929 baseEnd_5479929 := by
    simpa [prefixWord, tailWord_5479929, baseEnd_5479929] using wordTrace_append hprefix tailTrace_5479929
  have hstable : (prefixWord ++ tailWord_5479929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479929).length < 2 ^ (prefixWord ++ tailWord_5479929).sum := by decide
  have hdescent : baseEnd_5479929 < baseStart_5479929 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479946 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 2, 3, 3]
def baseStart_5479946 : Nat := 118140960795 + 5479946 * 2 ^ 59
def prefixEnd_5479946 : Nat := 4983230072969 + 3 ^ 40 * 5479946 * 2
def baseEnd_5479946 : Nat := 2813846258683321919773193

theorem tailTrace_5479946 : CollatzResearch.WordTrace tailWord_5479946 prefixEnd_5479946 2813846258683321919773193 := by
  unfold tailWord_5479946
  simp only [CollatzResearch.WordTrace]
  refine ⟨49967512651274754277770923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133246700403399344740722461 49967512651274754277770923)
  ·
    refine ⟨74951268976912131416656385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49967512651274754277770923 74951268976912131416656385)
    ·
      refine ⟨56213451732684098562492289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74951268976912131416656385 56213451732684098562492289)
      ·
        refine ⟨42160088799513073921869217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56213451732684098562492289 42160088799513073921869217)
        ·
          refine ⟨31620066599634805441401913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42160088799513073921869217 31620066599634805441401913)
          ·
            refine ⟨23715049949726104081051435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31620066599634805441401913 23715049949726104081051435)
            ·
              refine ⟨35572574924589156121577153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23715049949726104081051435 35572574924589156121577153)
              ·
                refine ⟨26679431193441867091182865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35572574924589156121577153 26679431193441867091182865)
                ·
                  refine ⟨20009573395081400318387149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26679431193441867091182865 20009573395081400318387149)
                  ·
                    refine ⟨7503590023155525119395181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20009573395081400318387149 7503590023155525119395181)
                    ·
                      refine ⟨2813846258683321919773193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7503590023155525119395181 2813846258683321919773193)
                      ·
                        rfl

theorem cell23_5479946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 2, 3, 3].length) (baseStart_5479946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479946 prefixEnd_5479946 := by exact prefixLift 5479946
  have htrace : WordTrace (prefixWord ++ tailWord_5479946) baseStart_5479946 baseEnd_5479946 := by
    simpa [prefixWord, tailWord_5479946, baseEnd_5479946] using wordTrace_append hprefix tailTrace_5479946
  have hstable : (prefixWord ++ tailWord_5479946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479946).length < 2 ^ (prefixWord ++ tailWord_5479946).sum := by decide
  have hdescent : baseEnd_5479946 < baseStart_5479946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479947 : List Nat := [1, 1, 1, 1, 8, 2, 1, 2, 2, 2, 2]
def baseStart_5479947 : Nat := 118140960795 + 5479947 * 2 ^ 59
def prefixEnd_5479947 : Nat := 4983230072969 + 3 ^ 40 * 5479947 * 2
def baseEnd_5479947 : Nat := 2813846772163976415860689

theorem tailTrace_5479947 : CollatzResearch.WordTrace tailWord_5479947 prefixEnd_5479947 2813846772163976415860689 := by
  unfold tailWord_5479947
  simp only [CollatzResearch.WordTrace]
  refine ⟨199870087078095394281870095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133246724718730262854580063 199870087078095394281870095)
  ·
    refine ⟨299805130617143091422805143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199870087078095394281870095 299805130617143091422805143)
    ·
      refine ⟨449707695925714637134207715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299805130617143091422805143 449707695925714637134207715)
      ·
        refine ⟨674561543888571955701311573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449707695925714637134207715 674561543888571955701311573)
        ·
          refine ⟨7905018092444202605874745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 674561543888571955701311573 7905018092444202605874745)
          ·
            refine ⟨5928763569333151954406059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7905018092444202605874745 5928763569333151954406059)
            ·
              refine ⟨8893145353999727931609089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5928763569333151954406059 8893145353999727931609089)
              ·
                refine ⟨6669859015499795948706817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8893145353999727931609089 6669859015499795948706817)
                ·
                  refine ⟨5002394261624846961530113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6669859015499795948706817 5002394261624846961530113)
                  ·
                    refine ⟨3751795696218635221147585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5002394261624846961530113 3751795696218635221147585)
                    ·
                      refine ⟨2813846772163976415860689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3751795696218635221147585 2813846772163976415860689)
                      ·
                        rfl

theorem cell23_5479947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 2, 2, 2, 2].length) (baseStart_5479947 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479947 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479947 prefixEnd_5479947 := by exact prefixLift 5479947
  have htrace : WordTrace (prefixWord ++ tailWord_5479947) baseStart_5479947 baseEnd_5479947 := by
    simpa [prefixWord, tailWord_5479947, baseEnd_5479947] using wordTrace_append hprefix tailTrace_5479947
  have hstable : (prefixWord ++ tailWord_5479947).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479947).length < 2 ^ (prefixWord ++ tailWord_5479947).sum := by decide
  have hdescent : baseEnd_5479947 < baseStart_5479947 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5479986 : List Nat := [3, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4]
def baseStart_5479986 : Nat := 118140960795 + 5479986 * 2 ^ 59
def prefixEnd_5479986 : Nat := 4983230072969 + 3 ^ 40 * 5479986 * 2
def baseEnd_5479986 : Nat := 2813866797909501763273009

theorem tailTrace_5479986 : CollatzResearch.WordTrace tailWord_5479986 prefixEnd_5479986 2813866797909501763273009 := by
  unfold tailWord_5479986
  simp only [CollatzResearch.WordTrace]
  refine ⟨49967877381238525985634953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133247673016636069295026541 49967877381238525985634953)
  ·
    refine ⟨37475908035928894489226215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49967877381238525985634953 37475908035928894489226215)
    ·
      refine ⟨56213862053893341733839323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37475908035928894489226215 56213862053893341733839323)
      ·
        refine ⟨84320793080840012600758985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56213862053893341733839323 84320793080840012600758985)
        ·
          refine ⟨63240594810630009450569239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 84320793080840012600758985 63240594810630009450569239)
          ·
            refine ⟨94860892215945014175853859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63240594810630009450569239 94860892215945014175853859)
            ·
              refine ⟨142291338323917521263780789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94860892215945014175853859 142291338323917521263780789)
              ·
                refine ⟨13339812967867267618479449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 142291338323917521263780789 13339812967867267618479449)
                ·
                  refine ⟨10004859725900450713859587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13339812967867267618479449 10004859725900450713859587)
                  ·
                    refine ⟨15007289588850676070789381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10004859725900450713859587 15007289588850676070789381)
                    ·
                      refine ⟨2813866797909501763273009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15007289588850676070789381 2813866797909501763273009)
                      ·
                        rfl

theorem cell23_5479986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_5479986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5479986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5479986 prefixEnd_5479986 := by exact prefixLift 5479986
  have htrace : WordTrace (prefixWord ++ tailWord_5479986) baseStart_5479986 baseEnd_5479986 := by
    simpa [prefixWord, tailWord_5479986, baseEnd_5479986] using wordTrace_append hprefix tailTrace_5479986
  have hstable : (prefixWord ++ tailWord_5479986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5479986).length < 2 ^ (prefixWord ++ tailWord_5479986).sum := by decide
  have hdescent : baseEnd_5479986 < baseStart_5479986 := by decide
  rcases family_descends (prefixWord ++ tailWord_5479986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480040 : List Nat := [2, 1, 4, 3, 1, 2, 2, 1, 2, 2, 3]
def baseStart_5480040 : Nat := 118140960795 + 5480040 * 2 ^ 59
def prefixEnd_5480040 : Nat := 4983230072969 + 3 ^ 40 * 5480040 * 2
def baseEnd_5480040 : Nat := 2813894525864844551997761

theorem tailTrace_5480040 : CollatzResearch.WordTrace tailWord_5480040 prefixEnd_5480040 2813894525864844551997761 := by
  unfold tailWord_5480040
  simp only [CollatzResearch.WordTrace]
  refine ⟨99936739533379235582502787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133248986044505647443337049 99936739533379235582502787)
  ·
    refine ⟨149905109300068853373754181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99936739533379235582502787 149905109300068853373754181)
    ·
      refine ⟨28107207993762910007578909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 149905109300068853373754181 28107207993762910007578909)
      ·
        refine ⟨10540202997661091252842091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28107207993762910007578909 10540202997661091252842091)
        ·
          refine ⟨15810304496491636879263137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10540202997661091252842091 15810304496491636879263137)
          ·
            refine ⟨11857728372368727659447353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15810304496491636879263137 11857728372368727659447353)
            ·
              refine ⟨8893296279276545744585515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11857728372368727659447353 8893296279276545744585515)
              ·
                refine ⟨13339944418914818616878273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8893296279276545744585515 13339944418914818616878273)
                ·
                  refine ⟨10004958314186113962658705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13339944418914818616878273 10004958314186113962658705)
                  ·
                    refine ⟨7503718735639585471994029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10004958314186113962658705 7503718735639585471994029)
                    ·
                      refine ⟨2813894525864844551997761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7503718735639585471994029 2813894525864844551997761)
                      ·
                        rfl

theorem cell23_5480040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_5480040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480040 prefixEnd_5480040 := by exact prefixLift 5480040
  have htrace : WordTrace (prefixWord ++ tailWord_5480040) baseStart_5480040 baseEnd_5480040 := by
    simpa [prefixWord, tailWord_5480040, baseEnd_5480040] using wordTrace_append hprefix tailTrace_5480040
  have hstable : (prefixWord ++ tailWord_5480040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480040).length < 2 ^ (prefixWord ++ tailWord_5480040).sum := by decide
  have hdescent : baseEnd_5480040 < baseStart_5480040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480049 : List Nat := [1, 2, 2, 2, 1, 1, 1, 2, 1, 3, 7]
def baseStart_5480049 : Nat := 118140960795 + 5480049 * 2 ^ 59
def prefixEnd_5480049 : Nat := 4983230072969 + 3 ^ 40 * 5480049 * 2
def baseEnd_5480049 : Nat := 2813899147190735016785219

theorem tailTrace_5480049 : CollatzResearch.WordTrace tailWord_5480049 prefixEnd_5480049 2813899147190735016785219 := by
  unfold tailWord_5480049
  simp only [CollatzResearch.WordTrace]
  refine ⟨199873807323725865702083201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133249204882483910468055467 199873807323725865702083201)
  ·
    refine ⟨149905355492794399276562401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199873807323725865702083201 149905355492794399276562401)
    ·
      refine ⟨112429016619595799457421801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149905355492794399276562401 112429016619595799457421801)
      ·
        refine ⟨84321762464696849593066351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112429016619595799457421801 84321762464696849593066351)
        ·
          refine ⟨126482643697045274389599527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84321762464696849593066351 126482643697045274389599527)
          ·
            refine ⟨189723965545567911584399291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126482643697045274389599527 189723965545567911584399291)
            ·
              refine ⟨284585948318351867376598937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 189723965545567911584399291 284585948318351867376598937)
              ·
                refine ⟨213439461238763900532449203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 284585948318351867376598937 213439461238763900532449203)
                ·
                  refine ⟨320159191858145850798673805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 213439461238763900532449203 320159191858145850798673805)
                  ·
                    refine ⟨120059696946804694049502677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 320159191858145850798673805 120059696946804694049502677)
                    ·
                      refine ⟨2813899147190735016785219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 120059696946804694049502677 2813899147190735016785219)
                      ·
                        rfl

theorem cell23_5480049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_5480049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480049 prefixEnd_5480049 := by exact prefixLift 5480049
  have htrace : WordTrace (prefixWord ++ tailWord_5480049) baseStart_5480049 baseEnd_5480049 := by
    simpa [prefixWord, tailWord_5480049, baseEnd_5480049] using wordTrace_append hprefix tailTrace_5480049
  have hstable : (prefixWord ++ tailWord_5480049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480049).length < 2 ^ (prefixWord ++ tailWord_5480049).sum := by decide
  have hdescent : baseEnd_5480049 < baseStart_5480049 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480076 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 5, 1, 4]
def baseStart_5480076 : Nat := 118140960795 + 5480076 * 2 ^ 59
def prefixEnd_5480076 : Nat := 4983230072969 + 3 ^ 40 * 5480076 * 2
def baseEnd_5480076 : Nat := 2813913011168406411147595

theorem tailTrace_5480076 : CollatzResearch.WordTrace tailWord_5480076 prefixEnd_5480076 2813913011168406411147595 := by
  unfold tailWord_5480076
  simp only [CollatzResearch.WordTrace]
  refine ⟨99937396047314024656658041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133249861396418699542210721 99937396047314024656658041)
  ·
    refine ⟨74953047035485518492493531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99937396047314024656658041 74953047035485518492493531)
    ·
      refine ⟨112429570553228277738740297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74953047035485518492493531 112429570553228277738740297)
      ·
        refine ⟨84322177914921208304055223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112429570553228277738740297 84322177914921208304055223)
        ·
          refine ⟨126483266872381812456082835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84322177914921208304055223 126483266872381812456082835)
          ·
            refine ⟨189724900308572718684124253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126483266872381812456082835 189724900308572718684124253)
            ·
              refine ⟨71146837615714769506546595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 189724900308572718684124253 71146837615714769506546595)
              ·
                refine ⟨106720256423572154259819893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71146837615714769506546595 106720256423572154259819893)
                ·
                  refine ⟨10005024039709889461858115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 106720256423572154259819893 10005024039709889461858115)
                  ·
                    refine ⟨15007536059564834192787173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10005024039709889461858115 15007536059564834192787173)
                    ·
                      refine ⟨2813913011168406411147595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15007536059564834192787173 2813913011168406411147595)
                      ·
                        rfl

theorem cell23_5480076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_5480076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480076 prefixEnd_5480076 := by exact prefixLift 5480076
  have htrace : WordTrace (prefixWord ++ tailWord_5480076) baseStart_5480076 baseEnd_5480076 := by
    simpa [prefixWord, tailWord_5480076, baseEnd_5480076] using wordTrace_append hprefix tailTrace_5480076
  have hstable : (prefixWord ++ tailWord_5480076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480076).length < 2 ^ (prefixWord ++ tailWord_5480076).sum := by decide
  have hdescent : baseEnd_5480076 < baseStart_5480076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480093 : List Nat := [1, 4, 2, 1, 1, 1, 1, 6, 1, 1, 4]
def baseStart_5480093 : Nat := 118140960795 + 5480093 * 2 ^ 59
def prefixEnd_5480093 : Nat := 4983230072969 + 3 ^ 40 * 5480093 * 2
def baseEnd_5480093 : Nat := 2813921740339532844635017

theorem tailTrace_5480093 : CollatzResearch.WordTrace tailWord_5480093 prefixEnd_5480093 2813921740339532844635017 := by
  unfold tailWord_5480093
  simp only [CollatzResearch.WordTrace]
  refine ⟨199875412135566461216684933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133250274757044307477789955 199875412135566461216684933)
  ·
    refine ⟨37476639775418711478128425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 199875412135566461216684933 37476639775418711478128425)
    ·
      refine ⟨28107479831564033608596319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37476639775418711478128425 28107479831564033608596319)
      ·
        refine ⟨42161219747346050412894479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28107479831564033608596319 42161219747346050412894479)
        ·
          refine ⟨63241829621019075619341719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42161219747346050412894479 63241829621019075619341719)
          ·
            refine ⟨94862744431528613429012579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 63241829621019075619341719 94862744431528613429012579)
            ·
              refine ⟨142294116647292920143518869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94862744431528613429012579 142294116647292920143518869)
              ·
                refine ⟨6670036717841855631727447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 142294116647292920143518869 6670036717841855631727447)
                ·
                  refine ⟨10005055076762783447591171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6670036717841855631727447 10005055076762783447591171)
                  ·
                    refine ⟨15007582615144175171386757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10005055076762783447591171 15007582615144175171386757)
                    ·
                      refine ⟨2813921740339532844635017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15007582615144175171386757 2813921740339532844635017)
                      ·
                        rfl

theorem cell23_5480093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 6, 1, 1, 4].length) (baseStart_5480093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480093 prefixEnd_5480093 := by exact prefixLift 5480093
  have htrace : WordTrace (prefixWord ++ tailWord_5480093) baseStart_5480093 baseEnd_5480093 := by
    simpa [prefixWord, tailWord_5480093, baseEnd_5480093] using wordTrace_append hprefix tailTrace_5480093
  have hstable : (prefixWord ++ tailWord_5480093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480093).length < 2 ^ (prefixWord ++ tailWord_5480093).sum := by decide
  have hdescent : baseEnd_5480093 < baseStart_5480093 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480097 : List Nat := [1, 2, 3, 3, 2, 3, 1, 1, 2, 3, 2]
def baseStart_5480097 : Nat := 118140960795 + 5480097 * 2 ^ 59
def prefixEnd_5480097 : Nat := 4983230072969 + 3 ^ 40 * 5480097 * 2
def baseEnd_5480097 : Nat := 2813923794262150828984999

theorem tailTrace_5480097 : CollatzResearch.WordTrace tailWord_5480097 prefixEnd_5480097 2813923794262150828984999 := by
  unfold tailWord_5480097
  simp only [CollatzResearch.WordTrace]
  refine ⟨199875558027551969899830545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133250372018367979933220363 199875558027551969899830545)
  ·
    refine ⟨149906668520663977424872909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199875558027551969899830545 149906668520663977424872909)
    ·
      refine ⟨56215000695248991534327341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149906668520663977424872909 56215000695248991534327341)
      ·
        refine ⟨21080625260718371825372753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56215000695248991534327341 21080625260718371825372753)
        ·
          refine ⟨15810468945538778869029565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21080625260718371825372753 15810468945538778869029565)
          ·
            refine ⟨5928925854577042075886087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15810468945538778869029565 5928925854577042075886087)
            ·
              refine ⟨8893388781865563113829131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5928925854577042075886087 8893388781865563113829131)
              ·
                refine ⟨13340083172798344670743697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8893388781865563113829131 13340083172798344670743697)
                ·
                  refine ⟨10005062379598758503057773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13340083172798344670743697 10005062379598758503057773)
                  ·
                    refine ⟨3751898392349534438646665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10005062379598758503057773 3751898392349534438646665)
                    ·
                      refine ⟨2813923794262150828984999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3751898392349534438646665 2813923794262150828984999)
                      ·
                        rfl

theorem cell23_5480097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 2, 3, 2].length) (baseStart_5480097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480097 prefixEnd_5480097 := by exact prefixLift 5480097
  have htrace : WordTrace (prefixWord ++ tailWord_5480097) baseStart_5480097 baseEnd_5480097 := by
    simpa [prefixWord, tailWord_5480097, baseEnd_5480097] using wordTrace_append hprefix tailTrace_5480097
  have hstable : (prefixWord ++ tailWord_5480097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480097).length < 2 ^ (prefixWord ++ tailWord_5480097).sum := by decide
  have hdescent : baseEnd_5480097 < baseStart_5480097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480127 : List Nat := [1, 1, 2, 2, 2, 3, 1, 6, 1, 2, 2]
def baseStart_5480127 : Nat := 118140960795 + 5480127 * 2 ^ 59
def prefixEnd_5480127 : Nat := 4983230072969 + 3 ^ 40 * 5480127 * 2
def baseEnd_5480127 : Nat := 2813939198681785711609861

theorem tailTrace_5480127 : CollatzResearch.WordTrace tailWord_5480127 prefixEnd_5480127 2813939198681785711609861 := by
  unfold tailWord_5480127
  simp only [CollatzResearch.WordTrace]
  refine ⟨199876652217443285023422635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133251101478295523348948423 199876652217443285023422635)
  ·
    refine ⟨299814978326164927535133953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199876652217443285023422635 299814978326164927535133953)
    ·
      refine ⟨224861233744623695651350465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299814978326164927535133953 224861233744623695651350465)
      ·
        refine ⟨168645925308467771738512849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 224861233744623695651350465 168645925308467771738512849)
        ·
          refine ⟨126484443981350828803884637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168645925308467771738512849 126484443981350828803884637)
          ·
            refine ⟨47431666493006560801456739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126484443981350828803884637 47431666493006560801456739)
            ·
              refine ⟨71147499739509841202185109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47431666493006560801456739 71147499739509841202185109)
              ·
                refine ⟨3335039050289523806352427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 71147499739509841202185109 3335039050289523806352427)
                ·
                  refine ⟨5002558575434285709528641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3335039050289523806352427 5002558575434285709528641)
                  ·
                    refine ⟨3751918931575714282146481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5002558575434285709528641 3751918931575714282146481)
                    ·
                      refine ⟨2813939198681785711609861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3751918931575714282146481 2813939198681785711609861)
                      ·
                        rfl

theorem cell23_5480127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 6, 1, 2, 2].length) (baseStart_5480127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480127 prefixEnd_5480127 := by exact prefixLift 5480127
  have htrace : WordTrace (prefixWord ++ tailWord_5480127) baseStart_5480127 baseEnd_5480127 := by
    simpa [prefixWord, tailWord_5480127, baseEnd_5480127] using wordTrace_append hprefix tailTrace_5480127
  have hstable : (prefixWord ++ tailWord_5480127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480127).length < 2 ^ (prefixWord ++ tailWord_5480127).sum := by decide
  have hdescent : baseEnd_5480127 < baseStart_5480127 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480161 : List Nat := [1, 2, 3, 1, 5, 2, 1, 3, 1, 2, 2]
def baseStart_5480161 : Nat := 118140960795 + 5480161 * 2 ^ 59
def prefixEnd_5480161 : Nat := 4983230072969 + 3 ^ 40 * 5480161 * 2
def baseEnd_5480161 : Nat := 2813956657024038578584705

theorem tailTrace_5480161 : CollatzResearch.WordTrace tailWord_5480161 prefixEnd_5480161 2813956657024038578584705 := by
  unfold tailWord_5480161
  simp only [CollatzResearch.WordTrace]
  refine ⟨199877892299320108830160337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133251928199546739220106891 199877892299320108830160337)
  ·
    refine ⟨149908419224490081622620253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199877892299320108830160337 149908419224490081622620253)
    ·
      refine ⟨56215657209183780608482595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149908419224490081622620253 56215657209183780608482595)
      ·
        refine ⟨84323485813775670912723893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56215657209183780608482595 84323485813775670912723893)
        ·
          refine ⟨7905326795041469148067865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 84323485813775670912723893 7905326795041469148067865)
          ·
            refine ⟨5928995096281101861050899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7905326795041469148067865 5928995096281101861050899)
            ·
              refine ⟨8893492644421652791576349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5928995096281101861050899 8893492644421652791576349)
              ·
                refine ⟨3335059741658119796841131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8893492644421652791576349 3335059741658119796841131)
                ·
                  refine ⟨5002589612487179695261697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3335059741658119796841131 5002589612487179695261697)
                  ·
                    refine ⟨3751942209365384771446273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5002589612487179695261697 3751942209365384771446273)
                    ·
                      refine ⟨2813956657024038578584705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3751942209365384771446273 2813956657024038578584705)
                      ·
                        rfl

theorem cell23_5480161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 3, 1, 2, 2].length) (baseStart_5480161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480161 prefixEnd_5480161 := by exact prefixLift 5480161
  have htrace : WordTrace (prefixWord ++ tailWord_5480161) baseStart_5480161 baseEnd_5480161 := by
    simpa [prefixWord, tailWord_5480161, baseEnd_5480161] using wordTrace_append hprefix tailTrace_5480161
  have hstable : (prefixWord ++ tailWord_5480161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480161).length < 2 ^ (prefixWord ++ tailWord_5480161).sum := by decide
  have hdescent : baseEnd_5480161 < baseStart_5480161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480176 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 2, 6]
def baseStart_5480176 : Nat := 118140960795 + 5480176 * 2 ^ 59
def prefixEnd_5480176 : Nat := 4983230072969 + 3 ^ 40 * 5480176 * 2
def baseEnd_5480176 : Nat := 937988119744618673299045

theorem tailTrace_5480176 : CollatzResearch.WordTrace tailWord_5480176 prefixEnd_5480176 937988119744618673299045 := by
  unfold tailWord_5480176
  simp only [CollatzResearch.WordTrace]
  refine ⟨99939219697132883195978191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133252292929510510927970921 99939219697132883195978191)
  ·
    refine ⟨149908829545699324793967287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99939219697132883195978191 149908829545699324793967287)
    ·
      refine ⟨224863244318548987190950931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149908829545699324793967287 224863244318548987190950931)
      ·
        refine ⟨337294866477823480786426397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224863244318548987190950931 337294866477823480786426397)
        ·
          refine ⟨126485574929183805294909899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 337294866477823480786426397 126485574929183805294909899)
          ·
            refine ⟨189728362393775707942364849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126485574929183805294909899 189728362393775707942364849)
            ·
              refine ⟨142296271795331780956773637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189728362393775707942364849 142296271795331780956773637)
              ·
                refine ⟨26680550961624708929395057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 142296271795331780956773637 26680550961624708929395057)
                ·
                  refine ⟨20010413221218531697046293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26680550961624708929395057 20010413221218531697046293)
                  ·
                    refine ⟨937988119744618673299045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 20010413221218531697046293 937988119744618673299045)
                    ·
                      rfl

theorem cell23_5480176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 2, 6].length) (baseStart_5480176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480176 prefixEnd_5480176 := by exact prefixLift 5480176
  have htrace : WordTrace (prefixWord ++ tailWord_5480176) baseStart_5480176 baseEnd_5480176 := by
    simpa [prefixWord, tailWord_5480176, baseEnd_5480176] using wordTrace_append hprefix tailTrace_5480176
  have hstable : (prefixWord ++ tailWord_5480176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480176).length < 2 ^ (prefixWord ++ tailWord_5480176).sum := by decide
  have hdescent : baseEnd_5480176 < baseStart_5480176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480186 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5]
def baseStart_5480186 : Nat := 118140960795 + 5480186 * 2 ^ 59
def prefixEnd_5480186 : Nat := 4983230072969 + 3 ^ 40 * 5480186 * 2
def baseEnd_5480186 : Nat := 2813969494040400980772089

theorem tailTrace_5480186 : CollatzResearch.WordTrace tailWord_5480186 prefixEnd_5480186 2813969494040400980772089 := by
  unfold tailWord_5480186
  simp only [CollatzResearch.WordTrace]
  refine ⟨49969701031057384524955103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133252536082819692066546941 49969701031057384524955103)
  ·
    refine ⟨74954551546586076787432655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49969701031057384524955103 74954551546586076787432655)
    ·
      refine ⟨112431827319879115181148983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74954551546586076787432655 112431827319879115181148983)
      ·
        refine ⟨168647740979818672771723475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112431827319879115181148983 168647740979818672771723475)
        ·
          refine ⟨252971611469728009157585213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168647740979818672771723475 252971611469728009157585213)
          ·
            refine ⟨94864354301148003434094455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 252971611469728009157585213 94864354301148003434094455)
            ·
              refine ⟨142296531451722005151141683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94864354301148003434094455 142296531451722005151141683)
              ·
                refine ⟨213444797177583007726712525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142296531451722005151141683 213444797177583007726712525)
                ·
                  refine ⟨80041798941593627897517197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 213444797177583007726712525 80041798941593627897517197)
                  ·
                    refine ⟨30015674603097610461568949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 80041798941593627897517197 30015674603097610461568949)
                    ·
                      refine ⟨2813969494040400980772089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30015674603097610461568949 2813969494040400980772089)
                      ·
                        rfl

theorem cell23_5480186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_5480186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480186 prefixEnd_5480186 := by exact prefixLift 5480186
  have htrace : WordTrace (prefixWord ++ tailWord_5480186) baseStart_5480186 baseEnd_5480186 := by
    simpa [prefixWord, tailWord_5480186, baseEnd_5480186] using wordTrace_append hprefix tailTrace_5480186
  have hstable : (prefixWord ++ tailWord_5480186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480186).length < 2 ^ (prefixWord ++ tailWord_5480186).sum := by decide
  have hdescent : baseEnd_5480186 < baseStart_5480186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480198 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3]
def baseStart_5480198 : Nat := 118140960795 + 5480198 * 2 ^ 59
def prefixEnd_5480198 : Nat := 4983230072969 + 3 ^ 40 * 5480198 * 2
def baseEnd_5480198 : Nat := 2813975655808254933822035

theorem tailTrace_5480198 : CollatzResearch.WordTrace tailWord_5480198 prefixEnd_5480198 2813975655808254933822035 := by
  unfold tailWord_5480198
  simp only [CollatzResearch.WordTrace]
  refine ⟨6246226306255814504664289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 133252827866790709432838165 6246226306255814504664289)
  ·
    refine ⟨4684669729691860878498217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6246226306255814504664289 4684669729691860878498217)
    ·
      refine ⟨3513502297268895658873663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4684669729691860878498217 3513502297268895658873663)
      ·
        refine ⟨5270253445903343488310495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3513502297268895658873663 5270253445903343488310495)
        ·
          refine ⟨7905380168855015232465743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5270253445903343488310495 7905380168855015232465743)
          ·
            refine ⟨11858070253282522848698615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7905380168855015232465743 11858070253282522848698615)
            ·
              refine ⟨17787105379923784273047923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11858070253282522848698615 17787105379923784273047923)
              ·
                refine ⟨26680658069885676409571885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17787105379923784273047923 26680658069885676409571885)
                ·
                  refine ⟨10005246776207128653589457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26680658069885676409571885 10005246776207128653589457)
                  ·
                    refine ⟨7503935082155346490192093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10005246776207128653589457 7503935082155346490192093)
                    ·
                      refine ⟨2813975655808254933822035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7503935082155346490192093 2813975655808254933822035)
                      ·
                        rfl

theorem cell23_5480198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_5480198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480198 prefixEnd_5480198 := by exact prefixLift 5480198
  have htrace : WordTrace (prefixWord ++ tailWord_5480198) baseStart_5480198 baseEnd_5480198 := by
    simpa [prefixWord, tailWord_5480198, baseEnd_5480198] using wordTrace_append hprefix tailTrace_5480198
  have hstable : (prefixWord ++ tailWord_5480198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480198).length < 2 ^ (prefixWord ++ tailWord_5480198).sum := by decide
  have hdescent : baseEnd_5480198 < baseStart_5480198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480200 : List Nat := [2, 1, 3, 2, 2, 1, 2, 3, 1, 4, 2]
def baseStart_5480200 : Nat := 118140960795 + 5480200 * 2 ^ 59
def prefixEnd_5480200 : Nat := 4983230072969 + 3 ^ 40 * 5480200 * 2
def baseEnd_5480200 : Nat := 2813976682769563925997025

theorem tailTrace_5480200 : CollatzResearch.WordTrace tailWord_5480200 prefixEnd_5480200 2813976682769563925997025 := by
  unfold tailWord_5480200
  simp only [CollatzResearch.WordTrace]
  refine ⟨99939657373089409245415027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133252876497452545660553369 99939657373089409245415027)
  ·
    refine ⟨149909486059634113868122541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99939657373089409245415027 149909486059634113868122541)
    ·
      refine ⟨56216057272362792700545953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149909486059634113868122541 56216057272362792700545953)
      ·
        refine ⟨42162042954272094525409465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56216057272362792700545953 42162042954272094525409465)
        ·
          refine ⟨31621532215704070894057099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42162042954272094525409465 31621532215704070894057099)
          ·
            refine ⟨47432298323556106341085649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31621532215704070894057099 47432298323556106341085649)
            ·
              refine ⟨35574223742667079755814237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47432298323556106341085649 35574223742667079755814237)
              ·
                refine ⟨13340333903500154908430339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35574223742667079755814237 13340333903500154908430339)
                ·
                  refine ⟨20010500855250232362645509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13340333903500154908430339 20010500855250232362645509)
                  ·
                    refine ⟨3751968910359418567996033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20010500855250232362645509 3751968910359418567996033)
                    ·
                      refine ⟨2813976682769563925997025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3751968910359418567996033 2813976682769563925997025)
                      ·
                        rfl

theorem cell23_5480200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_5480200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480200 prefixEnd_5480200 := by exact prefixLift 5480200
  have htrace : WordTrace (prefixWord ++ tailWord_5480200) baseStart_5480200 baseEnd_5480200 := by
    simpa [prefixWord, tailWord_5480200, baseEnd_5480200] using wordTrace_append hprefix tailTrace_5480200
  have hstable : (prefixWord ++ tailWord_5480200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480200).length < 2 ^ (prefixWord ++ tailWord_5480200).sum := by decide
  have hdescent : baseEnd_5480200 < baseStart_5480200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480250 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3]
def baseStart_5480250 : Nat := 118140960795 + 5480250 * 2 ^ 59
def prefixEnd_5480250 : Nat := 4983230072969 + 3 ^ 40 * 5480250 * 2
def baseEnd_5480250 : Nat := 2814002356802288730371795

theorem tailTrace_5480250 : CollatzResearch.WordTrace tailWord_5480250 prefixEnd_5480250 2814002356802288730371795 := by
  unfold tailWord_5480250
  simp only [CollatzResearch.WordTrace]
  refine ⟨49970284598999419257537551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 133254092263998451353433469 49970284598999419257537551)
  ·
    refine ⟨74955426898499128886306327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49970284598999419257537551 74955426898499128886306327)
    ·
      refine ⟨112433140347748693329459491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74955426898499128886306327 112433140347748693329459491)
      ·
        refine ⟨168649710521623039994189237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112433140347748693329459491 168649710521623039994189237)
        ·
          refine ⟨15810910361402159999455241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 168649710521623039994189237 15810910361402159999455241)
          ·
            refine ⟨11858182771051619999591431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15810910361402159999455241 11858182771051619999591431)
            ·
              refine ⟨17787274156577429999387147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11858182771051619999591431 17787274156577429999387147)
              ·
                refine ⟨26680911234866144999080721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17787274156577429999387147 26680911234866144999080721)
                ·
                  refine ⟨20010683426149608749310541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26680911234866144999080721 20010683426149608749310541)
                  ·
                    refine ⟨7504006284806103280991453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20010683426149608749310541 7504006284806103280991453)
                    ·
                      refine ⟨2814002356802288730371795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7504006284806103280991453 2814002356802288730371795)
                      ·
                        rfl

theorem cell23_5480250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 2, 3, 3].length) (baseStart_5480250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480250 prefixEnd_5480250 := by exact prefixLift 5480250
  have htrace : WordTrace (prefixWord ++ tailWord_5480250) baseStart_5480250 baseEnd_5480250 := by
    simpa [prefixWord, tailWord_5480250, baseEnd_5480250] using wordTrace_append hprefix tailTrace_5480250
  have hstable : (prefixWord ++ tailWord_5480250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480250).length < 2 ^ (prefixWord ++ tailWord_5480250).sum := by decide
  have hdescent : baseEnd_5480250 < baseStart_5480250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480300 : List Nat := [2, 2, 1, 1, 4, 2, 1, 3, 3, 4]
def baseStart_5480300 : Nat := 118140960795 + 5480300 * 2 ^ 59
def prefixEnd_5480300 : Nat := 4983230072969 + 3 ^ 40 * 5480300 * 2
def baseEnd_5480300 : Nat := 938009343611671178248855

theorem tailTrace_5480300 : CollatzResearch.WordTrace tailWord_5480300 prefixEnd_5480300 938009343611671178248855 := by
  unfold tailWord_5480300
  simp only [CollatzResearch.WordTrace]
  refine ⟨99941481022908267784735177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133255308030544357046313569 99941481022908267784735177)
  ·
    refine ⟨74956110767181200838551383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99941481022908267784735177 74956110767181200838551383)
    ·
      refine ⟨112434166150771801257827075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74956110767181200838551383 112434166150771801257827075)
      ·
        refine ⟨168651249226157701886740613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112434166150771801257827075 168651249226157701886740613)
        ·
          refine ⟨31622109229904569103763865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 168651249226157701886740613 31622109229904569103763865)
          ·
            refine ⟨23716581922428426827822899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31622109229904569103763865 23716581922428426827822899)
            ·
              refine ⟨35574872883642640241734349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23716581922428426827822899 35574872883642640241734349)
              ·
                refine ⟨13340577331365990090650381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35574872883642640241734349 13340577331365990090650381)
                ·
                  refine ⟨5002716499262246283993893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13340577331365990090650381 5002716499262246283993893)
                  ·
                    refine ⟨938009343611671178248855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5002716499262246283993893 938009343611671178248855)
                    ·
                      rfl

theorem cell23_5480300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 4].length) (baseStart_5480300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480300 prefixEnd_5480300 := by exact prefixLift 5480300
  have htrace : WordTrace (prefixWord ++ tailWord_5480300) baseStart_5480300 baseEnd_5480300 := by
    simpa [prefixWord, tailWord_5480300, baseEnd_5480300] using wordTrace_append hprefix tailTrace_5480300
  have hstable : (prefixWord ++ tailWord_5480300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480300).length < 2 ^ (prefixWord ++ tailWord_5480300).sum := by decide
  have hdescent : baseEnd_5480300 < baseStart_5480300 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480344 : List Nat := [2, 1, 2, 6, 1, 1, 1, 2, 2, 2, 3]
def baseStart_5480344 : Nat := 118140960795 + 5480344 * 2 ^ 59
def prefixEnd_5480344 : Nat := 4983230072969 + 3 ^ 40 * 5480344 * 2
def baseEnd_5480344 : Nat := 2814050623983811362596363

theorem tailTrace_5480344 : CollatzResearch.WordTrace tailWord_5480344 prefixEnd_5480344 2814050623983811362596363 := by
  unfold tailWord_5480344
  simp only [CollatzResearch.WordTrace]
  refine ⟨99942283428828565542036043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133256377905104754056048057 99942283428828565542036043)
  ·
    refine ⟨149913425143242848313054065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99942283428828565542036043 149913425143242848313054065)
    ·
      refine ⟨112435068857432136234790549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149913425143242848313054065 112435068857432136234790549)
      ·
        refine ⟨5270393852692131386005807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 112435068857432136234790549 5270393852692131386005807)
        ·
          refine ⟨7905590779038197079008711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5270393852692131386005807 7905590779038197079008711)
          ·
            refine ⟨11858386168557295618513067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7905590779038197079008711 11858386168557295618513067)
            ·
              refine ⟨17787579252835943427769601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11858386168557295618513067 17787579252835943427769601)
              ·
                refine ⟨13340684439626957570827201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17787579252835943427769601 13340684439626957570827201)
                ·
                  refine ⟨10005513329720218178120401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13340684439626957570827201 10005513329720218178120401)
                  ·
                    refine ⟨7504134997290163633590301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10005513329720218178120401 7504134997290163633590301)
                    ·
                      refine ⟨2814050623983811362596363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7504134997290163633590301 2814050623983811362596363)
                      ·
                        rfl

theorem cell23_5480344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_5480344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480344 prefixEnd_5480344 := by exact prefixLift 5480344
  have htrace : WordTrace (prefixWord ++ tailWord_5480344) baseStart_5480344 baseEnd_5480344 := by
    simpa [prefixWord, tailWord_5480344, baseEnd_5480344] using wordTrace_append hprefix tailTrace_5480344
  have hstable : (prefixWord ++ tailWord_5480344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480344).length < 2 ^ (prefixWord ++ tailWord_5480344).sum := by decide
  have hdescent : baseEnd_5480344 < baseStart_5480344 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480351 : List Nat := [1, 1, 2, 5, 3, 1, 3, 2, 1, 4]
def baseStart_5480351 : Nat := 118140960795 + 5480351 * 2 ^ 59
def prefixEnd_5480351 : Nat := 4983230072969 + 3 ^ 40 * 5480351 * 2
def baseEnd_5480351 : Nat := 938018072782797611736277

theorem tailTrace_5480351 : CollatzResearch.WordTrace tailWord_5480351 prefixEnd_5480351 938018072782797611736277 := by
  unfold tailWord_5480351
  simp only [CollatzResearch.WordTrace]
  refine ⟨199884822168631771279576907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133256548112421180853051271 199884822168631771279576907)
  ·
    refine ⟨299827233252947656919365361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199884822168631771279576907 299827233252947656919365361)
    ·
      refine ⟨224870424939710742689524021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299827233252947656919365361 224870424939710742689524021)
      ·
        refine ⟨21081602338097882127142877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 224870424939710742689524021 21081602338097882127142877)
        ·
          refine ⟨7905600876786705797678579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21081602338097882127142877 7905600876786705797678579)
          ·
            refine ⟨11858401315180058696517869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7905600876786705797678579 11858401315180058696517869)
            ·
              refine ⟨4446900493192522011194201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11858401315180058696517869 4446900493192522011194201)
              ·
                refine ⟨3335175369894391508395651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4446900493192522011194201 3335175369894391508395651)
                ·
                  refine ⟨5002763054841587262593477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3335175369894391508395651 5002763054841587262593477)
                  ·
                    refine ⟨938018072782797611736277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5002763054841587262593477 938018072782797611736277)
                    ·
                      rfl

theorem cell23_5480351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 1, 4].length) (baseStart_5480351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480351 prefixEnd_5480351 := by exact prefixLift 5480351
  have htrace : WordTrace (prefixWord ++ tailWord_5480351) baseStart_5480351 baseEnd_5480351 := by
    simpa [prefixWord, tailWord_5480351, baseEnd_5480351] using wordTrace_append hprefix tailTrace_5480351
  have hstable : (prefixWord ++ tailWord_5480351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480351).length < 2 ^ (prefixWord ++ tailWord_5480351).sum := by decide
  have hdescent : baseEnd_5480351 < baseStart_5480351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480400 : List Nat := [2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 5]
def baseStart_5480400 : Nat := 118140960795 + 5480400 * 2 ^ 59
def prefixEnd_5480400 : Nat := 4983230072969 + 3 ^ 40 * 5480400 * 2
def baseEnd_5480400 : Nat := 2814079378900463143496105

theorem tailTrace_5480400 : CollatzResearch.WordTrace tailWord_5480400 prefixEnd_5480400 2814079378900463143496105 := by
  unfold tailWord_5480400
  simp only [CollatzResearch.WordTrace]
  refine ⟨99943304672727126324055327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133257739563636168432073769 99943304672727126324055327)
  ·
    refine ⟨149914957009090689486082991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99943304672727126324055327 149914957009090689486082991)
    ·
      refine ⟨224872435513636034229124487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149914957009090689486082991 224872435513636034229124487)
      ·
        refine ⟨337308653270454051343686731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224872435513636034229124487 337308653270454051343686731)
        ·
          refine ⟨505962979905681077015530097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337308653270454051343686731 505962979905681077015530097)
          ·
            refine ⟨379472234929260807761647573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 505962979905681077015530097 379472234929260807761647573)
            ·
              refine ⟨8893880506154550181913615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 379472234929260807761647573 8893880506154550181913615)
              ·
                refine ⟨13340820759231825272870423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8893880506154550181913615 13340820759231825272870423)
                ·
                  refine ⟨20011231138847737909305635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13340820759231825272870423 20011231138847737909305635)
                  ·
                    refine ⟨30016846708271606863958453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20011231138847737909305635 30016846708271606863958453)
                    ·
                      refine ⟨2814079378900463143496105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 30016846708271606863958453 2814079378900463143496105)
                      ·
                        rfl

theorem cell23_5480400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 1, 1, 1, 5].length) (baseStart_5480400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480400 prefixEnd_5480400 := by exact prefixLift 5480400
  have htrace : WordTrace (prefixWord ++ tailWord_5480400) baseStart_5480400 baseEnd_5480400 := by
    simpa [prefixWord, tailWord_5480400, baseEnd_5480400] using wordTrace_append hprefix tailTrace_5480400
  have hstable : (prefixWord ++ tailWord_5480400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480400).length < 2 ^ (prefixWord ++ tailWord_5480400).sum := by decide
  have hdescent : baseEnd_5480400 < baseStart_5480400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480407 : List Nat := [1, 1, 3, 2, 1, 1, 6, 2, 2, 4]
def baseStart_5480407 : Nat := 118140960795 + 5480407 * 2 ^ 59
def prefixEnd_5480407 : Nat := 4983230072969 + 3 ^ 40 * 5480407 * 2
def baseEnd_5480407 : Nat := 938027657755014872036191

theorem tailTrace_5480407 : CollatzResearch.WordTrace tailWord_5480407 prefixEnd_5480407 938027657755014872036191 := by
  unfold tailWord_5480407
  simp only [CollatzResearch.WordTrace]
  refine ⟨199886864656428892843615475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133257909770952595229076983 199886864656428892843615475)
  ·
    refine ⟨299830296984643339265423213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199886864656428892843615475 299830296984643339265423213)
    ·
      refine ⟨112436361369241252224533705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299830296984643339265423213 112436361369241252224533705)
      ·
        refine ⟨84327271026930939168400279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112436361369241252224533705 84327271026930939168400279)
        ·
          refine ⟨126490906540396408752600419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84327271026930939168400279 126490906540396408752600419)
          ·
            refine ⟨189736359810594613128900629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126490906540396408752600419 189736359810594613128900629)
            ·
              refine ⟨8893891866121622490417217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 189736359810594613128900629 8893891866121622490417217)
              ·
                refine ⟨6670418899591216867812913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8893891866121622490417217 6670418899591216867812913)
                ·
                  refine ⟨5002814174693412650859685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6670418899591216867812913 5002814174693412650859685)
                  ·
                    refine ⟨938027657755014872036191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5002814174693412650859685 938027657755014872036191)
                    ·
                      rfl

theorem cell23_5480407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 4].length) (baseStart_5480407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480407 prefixEnd_5480407 := by exact prefixLift 5480407
  have htrace : WordTrace (prefixWord ++ tailWord_5480407) baseStart_5480407 baseEnd_5480407 := by
    simpa [prefixWord, tailWord_5480407, baseEnd_5480407] using wordTrace_append hprefix tailTrace_5480407
  have hstable : (prefixWord ++ tailWord_5480407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480407).length < 2 ^ (prefixWord ++ tailWord_5480407).sum := by decide
  have hdescent : baseEnd_5480407 < baseStart_5480407 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480481 : List Nat := [1, 2, 3, 2, 5, 1, 1, 1, 1, 3, 3]
def baseStart_5480481 : Nat := 118140960795 + 5480481 * 2 ^ 59
def prefixEnd_5480481 : Nat := 4983230072969 + 3 ^ 40 * 5480481 * 2
def baseEnd_5480481 : Nat := 2814120970833477326583233

theorem tailTrace_5480481 : CollatzResearch.WordTrace tailWord_5480481 prefixEnd_5480481 2814120970833477326583233 := by
  unfold tailWord_5480481
  simp only [CollatzResearch.WordTrace]
  refine ⟨199889563658160803481809297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133259709105440535654539531 199889563658160803481809297)
  ·
    refine ⟨149917172743620602611356973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199889563658160803481809297 149917172743620602611356973)
    ·
      refine ⟨56218939778857725979258865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149917172743620602611356973 56218939778857725979258865)
      ·
        refine ⟨42164204834143294484444149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56218939778857725979258865 42164204834143294484444149)
        ·
          refine ⟨3952894203200933857916639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 42164204834143294484444149 3952894203200933857916639)
          ·
            refine ⟨5929341304801400786874959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3952894203200933857916639 5929341304801400786874959)
            ·
              refine ⟨8894011957202101180312439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5929341304801400786874959 8894011957202101180312439)
              ·
                refine ⟨13341017935803151770468659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8894011957202101180312439 13341017935803151770468659)
                ·
                  refine ⟨20011526903704727655702989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13341017935803151770468659 20011526903704727655702989)
                  ·
                    refine ⟨7504322588889272870888621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20011526903704727655702989 7504322588889272870888621)
                    ·
                      refine ⟨2814120970833477326583233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7504322588889272870888621 2814120970833477326583233)
                      ·
                        rfl

theorem cell23_5480481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 1, 1, 3, 3].length) (baseStart_5480481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480481 prefixEnd_5480481 := by exact prefixLift 5480481
  have htrace : WordTrace (prefixWord ++ tailWord_5480481) baseStart_5480481 baseEnd_5480481 := by
    simpa [prefixWord, tailWord_5480481, baseEnd_5480481] using wordTrace_append hprefix tailTrace_5480481
  have hstable : (prefixWord ++ tailWord_5480481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480481).length < 2 ^ (prefixWord ++ tailWord_5480481).sum := by decide
  have hdescent : baseEnd_5480481 < baseStart_5480481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480542 : List Nat := [4, 4, 1, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_5480542 : Nat := 118140960795 + 5480542 * 2 ^ 59
def prefixEnd_5480542 : Nat := 4983230072969 + 3 ^ 40 * 5480542 * 2
def baseEnd_5480542 : Nat := 2814152293153401587920453

theorem tailTrace_5480542 : CollatzResearch.WordTrace tailWord_5480542 prefixEnd_5480542 2814152293153401587920453 := by
  unfold tailWord_5480542
  simp only [CollatzResearch.WordTrace]
  refine ⟨24986473563867476362472485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 133261192340626540599853253 24986473563867476362472485)
  ·
    refine ⟨4684963793225151817963591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24986473563867476362472485 4684963793225151817963591)
    ·
      refine ⟨7027445689837727726945387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4684963793225151817963591 7027445689837727726945387)
      ·
        refine ⟨10541168534756591590418081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7027445689837727726945387 10541168534756591590418081)
        ·
          refine ⟨7905876401067443692813561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10541168534756591590418081 7905876401067443692813561)
          ·
            refine ⟨5929407300800582769610171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7905876401067443692813561 5929407300800582769610171)
            ·
              refine ⟨8894110951200874154415257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5929407300800582769610171 8894110951200874154415257)
              ·
                refine ⟨6670583213400655615811443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8894110951200874154415257 6670583213400655615811443)
                ·
                  refine ⟨10005874820100983423717165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6670583213400655615811443 10005874820100983423717165)
                  ·
                    refine ⟨3752203057537868783893937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10005874820100983423717165 3752203057537868783893937)
                    ·
                      refine ⟨2814152293153401587920453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3752203057537868783893937 2814152293153401587920453)
                      ·
                        rfl

theorem cell23_5480542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_5480542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480542 prefixEnd_5480542 := by exact prefixLift 5480542
  have htrace : WordTrace (prefixWord ++ tailWord_5480542) baseStart_5480542 baseEnd_5480542 := by
    simpa [prefixWord, tailWord_5480542, baseEnd_5480542] using wordTrace_append hprefix tailTrace_5480542
  have hstable : (prefixWord ++ tailWord_5480542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480542).length < 2 ^ (prefixWord ++ tailWord_5480542).sum := by decide
  have hdescent : baseEnd_5480542 < baseStart_5480542 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480597 : List Nat := [1, 3, 2, 1, 1, 1, 4, 2, 1, 4, 3]
def baseStart_5480597 : Nat := 118140960795 + 5480597 * 2 ^ 59
def prefixEnd_5480597 : Nat := 4983230072969 + 3 ^ 40 * 5480597 * 2
def baseEnd_5480597 : Nat := 2814180534589398872732699

theorem tailTrace_5480597 : CollatzResearch.WordTrace tailWord_5480597 prefixEnd_5480597 2814180534589398872732699 := by
  unfold tailWord_5480597
  simp only [CollatzResearch.WordTrace]
  refine ⟨199893794525740555293032045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133262529683827036862021363 199893794525740555293032045)
  ·
    refine ⟨74960172947152708234887017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199893794525740555293032045 74960172947152708234887017)
    ·
      refine ⟨56220129710364531176165263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74960172947152708234887017 56220129710364531176165263)
      ·
        refine ⟨84330194565546796764247895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56220129710364531176165263 84330194565546796764247895)
        ·
          refine ⟨126495291848320195146371843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84330194565546796764247895 126495291848320195146371843)
          ·
            refine ⟨189742937772480292719557765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126495291848320195146371843 189742937772480292719557765)
            ·
              refine ⟨35576800832340054884917081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 189742937772480292719557765 35576800832340054884917081)
              ·
                refine ⟨26682600624255041163687811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35576800832340054884917081 26682600624255041163687811)
                ·
                  refine ⟨40023900936382561745531717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26682600624255041163687811 40023900936382561745531717)
                  ·
                    refine ⟨7504481425571730327287197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 40023900936382561745531717 7504481425571730327287197)
                    ·
                      refine ⟨2814180534589398872732699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7504481425571730327287197 2814180534589398872732699)
                      ·
                        rfl

theorem cell23_5480597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 4, 3].length) (baseStart_5480597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480597 prefixEnd_5480597 := by exact prefixLift 5480597
  have htrace : WordTrace (prefixWord ++ tailWord_5480597) baseStart_5480597 baseEnd_5480597 := by
    simpa [prefixWord, tailWord_5480597, baseEnd_5480597] using wordTrace_append hprefix tailTrace_5480597
  have hstable : (prefixWord ++ tailWord_5480597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480597).length < 2 ^ (prefixWord ++ tailWord_5480597).sum := by decide
  have hdescent : baseEnd_5480597 < baseStart_5480597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480604 : List Nat := [2, 2, 3, 2, 1, 1, 3, 2, 3, 4]
def baseStart_5480604 : Nat := 118140960795 + 5480604 * 2 ^ 59
def prefixEnd_5480604 : Nat := 4983230072969 + 3 ^ 40 * 5480604 * 2
def baseEnd_5480604 : Nat := 938061376317993448448389

theorem tailTrace_5480604 : CollatzResearch.WordTrace tailWord_5480604 prefixEnd_5480604 938061376317993448448389 := by
  unfold tailWord_5480604
  simp only [CollatzResearch.WordTrace]
  refine ⟨99947024918357597744268433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133262699891143463659024577 99947024918357597744268433)
  ·
    refine ⟨74960268688768198308201325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99947024918357597744268433 74960268688768198308201325)
    ·
      refine ⟨28110100758288074365575497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74960268688768198308201325 28110100758288074365575497)
      ·
        refine ⟨21082575568716055774181623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28110100758288074365575497 21082575568716055774181623)
        ·
          refine ⟨31623863353074083661272435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21082575568716055774181623 31623863353074083661272435)
          ·
            refine ⟨47435795029611125491908653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31623863353074083661272435 47435795029611125491908653)
            ·
              refine ⟨17788423136104172059465745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 47435795029611125491908653 17788423136104172059465745)
              ·
                refine ⟨13341317352078129044599309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17788423136104172059465745 13341317352078129044599309)
                ·
                  refine ⟨5002994007029298391724741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13341317352078129044599309 5002994007029298391724741)
                  ·
                    refine ⟨938061376317993448448389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5002994007029298391724741 938061376317993448448389)
                    ·
                      rfl

theorem cell23_5480604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 2, 3, 4].length) (baseStart_5480604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480604 prefixEnd_5480604 := by exact prefixLift 5480604
  have htrace : WordTrace (prefixWord ++ tailWord_5480604) baseStart_5480604 baseEnd_5480604 := by
    simpa [prefixWord, tailWord_5480604, baseEnd_5480604] using wordTrace_append hprefix tailTrace_5480604
  have hstable : (prefixWord ++ tailWord_5480604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480604).length < 2 ^ (prefixWord ++ tailWord_5480604).sum := by decide
  have hdescent : baseEnd_5480604 < baseStart_5480604 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480664 : List Nat := [2, 1, 2, 2, 4, 1, 1, 4, 1, 5]
def baseStart_5480664 : Nat := 118140960795 + 5480664 * 2 ^ 59
def prefixEnd_5480664 : Nat := 4983230072969 + 3 ^ 40 * 5480664 * 2
def baseEnd_5480664 : Nat := 938071645931083370198297

theorem tailTrace_5480664 : CollatzResearch.WordTrace tailWord_5480664 prefixEnd_5480664 938071645931083370198297 := by
  unfold tailWord_5480664
  simp only [CollatzResearch.WordTrace]
  refine ⟨99948119108248912867860523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133264158810998550490480697 99948119108248912867860523)
  ·
    refine ⟨149922178662373369301790785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99948119108248912867860523 149922178662373369301790785)
    ·
      refine ⟨112441633996780026976343089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149922178662373369301790785 112441633996780026976343089)
      ·
        refine ⟨84331225497585020232257317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112441633996780026976343089 84331225497585020232257317)
        ·
          refine ⟨15812104780797191293548247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 84331225497585020232257317 15812104780797191293548247)
          ·
            refine ⟨23718157171195786940322371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15812104780797191293548247 23718157171195786940322371)
            ·
              refine ⟨35577235756793680410483557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23718157171195786940322371 35577235756793680410483557)
              ·
                refine ⟨6670731704398815076965667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35577235756793680410483557 6670731704398815076965667)
                ·
                  refine ⟨10006097556598222615448501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6670731704398815076965667 10006097556598222615448501)
                  ·
                    refine ⟨938071645931083370198297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10006097556598222615448501 938071645931083370198297)
                    ·
                      rfl

theorem cell23_5480664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 4, 1, 5].length) (baseStart_5480664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480664 prefixEnd_5480664 := by exact prefixLift 5480664
  have htrace : WordTrace (prefixWord ++ tailWord_5480664) baseStart_5480664 baseEnd_5480664 := by
    simpa [prefixWord, tailWord_5480664, baseEnd_5480664] using wordTrace_append hprefix tailTrace_5480664
  have hstable : (prefixWord ++ tailWord_5480664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480664).length < 2 ^ (prefixWord ++ tailWord_5480664).sum := by decide
  have hdescent : baseEnd_5480664 < baseStart_5480664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480684 : List Nat := [2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 4]
def baseStart_5480684 : Nat := 118140960795 + 5480684 * 2 ^ 59
def prefixEnd_5480684 : Nat := 4983230072969 + 3 ^ 40 * 5480684 * 2
def baseEnd_5480684 : Nat := 2814225207406340032344799

theorem tailTrace_5480684 : CollatzResearch.WordTrace tailWord_5480684 prefixEnd_5480684 2814225207406340032344799 := by
  unfold tailWord_5480684
  simp only [CollatzResearch.WordTrace]
  refine ⟨99948483838212684575724553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133264645117616912767632737 99948483838212684575724553)
  ·
    refine ⟨74961362878659513431793415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99948483838212684575724553 74961362878659513431793415)
    ·
      refine ⟨112442044317989270147690123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74961362878659513431793415 112442044317989270147690123)
      ·
        refine ⟨168663066476983905221535185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112442044317989270147690123 168663066476983905221535185)
        ·
          refine ⟨126497299857737928916151389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168663066476983905221535185 126497299857737928916151389)
          ·
            refine ⟨47436487446651723343556771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126497299857737928916151389 47436487446651723343556771)
            ·
              refine ⟨71154731169977585015335157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47436487446651723343556771 71154731169977585015335157)
              ·
                refine ⟨6670756047185398595187671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 71154731169977585015335157 6670756047185398595187671)
                ·
                  refine ⟨10006134070778097892781507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6670756047185398595187671 10006134070778097892781507)
                  ·
                    refine ⟨15009201106167146839172261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10006134070778097892781507 15009201106167146839172261)
                    ·
                      refine ⟨2814225207406340032344799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15009201106167146839172261 2814225207406340032344799)
                      ·
                        rfl

theorem cell23_5480684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 4].length) (baseStart_5480684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480684 prefixEnd_5480684 := by exact prefixLift 5480684
  have htrace : WordTrace (prefixWord ++ tailWord_5480684) baseStart_5480684 baseEnd_5480684 := by
    simpa [prefixWord, tailWord_5480684, baseEnd_5480684] using wordTrace_append hprefix tailTrace_5480684
  have hstable : (prefixWord ++ tailWord_5480684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480684).length < 2 ^ (prefixWord ++ tailWord_5480684).sum := by decide
  have hdescent : baseEnd_5480684 < baseStart_5480684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480697 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 5, 2, 4]
def baseStart_5480697 : Nat := 118140960795 + 5480697 * 2 ^ 59
def prefixEnd_5480697 : Nat := 4983230072969 + 3 ^ 40 * 5480697 * 2
def baseEnd_5480697 : Nat := 2814231882654848481482239

theorem tailTrace_5480697 : CollatzResearch.WordTrace tailWord_5480697 prefixEnd_5480697 2814231882654848481482239 := by
  unfold tailWord_5480697
  simp only [CollatzResearch.WordTrace]
  refine ⟨199897441825378272371672345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133264961216918848247781563 199897441825378272371672345)
  ·
    refine ⟨149923081369033704278754259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199897441825378272371672345 149923081369033704278754259)
    ·
      refine ⟨224884622053550556418131389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 149923081369033704278754259 224884622053550556418131389)
      ·
        refine ⟨84331733270081458656799271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 224884622053550556418131389 84331733270081458656799271)
        ·
          refine ⟨126497599905122187985198907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84331733270081458656799271 126497599905122187985198907)
          ·
            refine ⟨189746399857683281977798361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 126497599905122187985198907 189746399857683281977798361)
            ·
              refine ⟨142309799893262461483348771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 189746399857683281977798361 142309799893262461483348771)
              ·
                refine ⟨213464699839893692225023157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 142309799893262461483348771 213464699839893692225023157)
                ·
                  refine ⟨20012315609990033646095921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 213464699839893692225023157 20012315609990033646095921)
                  ·
                    refine ⟨15009236707492525234571941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20012315609990033646095921 15009236707492525234571941)
                    ·
                      refine ⟨2814231882654848481482239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15009236707492525234571941 2814231882654848481482239)
                      ·
                        rfl

theorem cell23_5480697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 5, 2, 4].length) (baseStart_5480697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480697 prefixEnd_5480697 := by exact prefixLift 5480697
  have htrace : WordTrace (prefixWord ++ tailWord_5480697) baseStart_5480697 baseEnd_5480697 := by
    simpa [prefixWord, tailWord_5480697, baseEnd_5480697] using wordTrace_append hprefix tailTrace_5480697
  have hstable : (prefixWord ++ tailWord_5480697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480697).length < 2 ^ (prefixWord ++ tailWord_5480697).sum := by decide
  have hdescent : baseEnd_5480697 < baseStart_5480697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480707 : List Nat := [1, 1, 1, 3, 2, 3, 4, 8]
def baseStart_5480707 : Nat := 118140960795 + 5480707 * 2 ^ 59
def prefixEnd_5480707 : Nat := 4983230072969 + 3 ^ 40 * 5480707 * 2
def baseEnd_5480707 : Nat := 104231000646718275642859

theorem tailTrace_5480707 : CollatzResearch.WordTrace tailWord_5480707 prefixEnd_5480707 104231000646718275642859 := by
  unfold tailWord_5480707
  simp only [CollatzResearch.WordTrace]
  refine ⟨199897806555342044079536375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133265204370228029386357583 199897806555342044079536375)
  ·
    refine ⟨299846709833013066119304563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199897806555342044079536375 299846709833013066119304563)
    ·
      refine ⟨449770064749519599178956845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299846709833013066119304563 449770064749519599178956845)
      ·
        refine ⟨168663774281069849692108817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 449770064749519599178956845 168663774281069849692108817)
        ·
          refine ⟨126497830710802387269081613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 168663774281069849692108817 126497830710802387269081613)
          ·
            refine ⟨47436686516550895225905605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 126497830710802387269081613 47436686516550895225905605)
            ·
              refine ⟨8894378721853292854857301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47436686516550895225905605 8894378721853292854857301)
              ·
                refine ⟨104231000646718275642859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8894378721853292854857301 104231000646718275642859)
                ·
                  rfl

theorem cell23_5480707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 8].length) (baseStart_5480707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480707 prefixEnd_5480707 := by exact prefixLift 5480707
  have htrace : WordTrace (prefixWord ++ tailWord_5480707) baseStart_5480707 baseEnd_5480707 := by
    simpa [prefixWord, tailWord_5480707, baseEnd_5480707] using wordTrace_append hprefix tailTrace_5480707
  have hstable : (prefixWord ++ tailWord_5480707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480707).length < 2 ^ (prefixWord ++ tailWord_5480707).sum := by decide
  have hdescent : baseEnd_5480707 < baseStart_5480707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480721 : List Nat := [1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 3]
def baseStart_5480721 : Nat := 118140960795 + 5480721 * 2 ^ 59
def prefixEnd_5480721 : Nat := 4983230072969 + 3 ^ 40 * 5480721 * 2
def baseEnd_5480721 : Nat := 2814244206190556387582129

theorem tailTrace_5480721 : CollatzResearch.WordTrace tailWord_5480721 prefixEnd_5480721 2814244206190556387582129 := by
  unfold tailWord_5480721
  simp only [CollatzResearch.WordTrace]
  refine ⟨199898317177291324470546017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133265544784860882980364011 199898317177291324470546017)
  ·
    refine ⟨149923737882968493352909513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199898317177291324470546017 149923737882968493352909513)
    ·
      refine ⟨112442803412226370014682135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 149923737882968493352909513 112442803412226370014682135)
      ·
        refine ⟨168664205118339555022023203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 112442803412226370014682135 168664205118339555022023203)
        ·
          refine ⟨252996307677509332533034805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 168664205118339555022023203 252996307677509332533034805)
          ·
            refine ⟨23718403844766499924972013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 252996307677509332533034805 23718403844766499924972013)
            ·
              refine ⟨8894401441787437471864505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23718403844766499924972013 8894401441787437471864505)
              ·
                refine ⟨6670801081340578103898379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8894401441787437471864505 6670801081340578103898379)
                ·
                  refine ⟨10006201622010867155847569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6670801081340578103898379 10006201622010867155847569)
                  ·
                    refine ⟨7504651216508150366885677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10006201622010867155847569 7504651216508150366885677)
                    ·
                      refine ⟨2814244206190556387582129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7504651216508150366885677 2814244206190556387582129)
                      ·
                        rfl

theorem cell23_5480721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 3].length) (baseStart_5480721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480721 prefixEnd_5480721 := by exact prefixLift 5480721
  have htrace : WordTrace (prefixWord ++ tailWord_5480721) baseStart_5480721 baseEnd_5480721 := by
    simpa [prefixWord, tailWord_5480721, baseEnd_5480721] using wordTrace_append hprefix tailTrace_5480721
  have hstable : (prefixWord ++ tailWord_5480721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480721).length < 2 ^ (prefixWord ++ tailWord_5480721).sum := by decide
  have hdescent : baseEnd_5480721 < baseStart_5480721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480751 : List Nat := [1, 1, 2, 1, 2, 1, 5, 4, 2, 1, 3]
def baseStart_5480751 : Nat := 118140960795 + 5480751 * 2 ^ 59
def prefixEnd_5480751 : Nat := 4983230072969 + 3 ^ 40 * 5480751 * 2
def baseEnd_5480751 : Nat := 2814259610610191270206991

theorem tailTrace_5480751 : CollatzResearch.WordTrace tailWord_5480751 prefixEnd_5480751 2814259610610191270206991 := by
  unfold tailWord_5480751
  simp only [CollatzResearch.WordTrace]
  refine ⟨199899411367182639594138107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133266274244788426396092071 199899411367182639594138107)
  ·
    refine ⟨299849117050773959391207161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199899411367182639594138107 299849117050773959391207161)
    ·
      refine ⟨224886837788080469543405371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 299849117050773959391207161 224886837788080469543405371)
      ·
        refine ⟨337330256682120704315108057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 224886837788080469543405371 337330256682120704315108057)
        ·
          refine ⟨252997692511590528236331043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 337330256682120704315108057 252997692511590528236331043)
          ·
            refine ⟨379496538767385792354496565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 252997692511590528236331043 379496538767385792354496565)
            ·
              refine ⟨35577800509442418033234053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 379496538767385792354496565 35577800509442418033234053)
              ·
                refine ⟨6670837595520453381231385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35577800509442418033234053 6670837595520453381231385)
                ·
                  refine ⟨5003128196640340035923539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6670837595520453381231385 5003128196640340035923539)
                  ·
                    refine ⟨7504692294960510053885309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5003128196640340035923539 7504692294960510053885309)
                    ·
                      refine ⟨2814259610610191270206991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7504692294960510053885309 2814259610610191270206991)
                      ·
                        rfl

theorem cell23_5480751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 4, 2, 1, 3].length) (baseStart_5480751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480751 prefixEnd_5480751 := by exact prefixLift 5480751
  have htrace : WordTrace (prefixWord ++ tailWord_5480751) baseStart_5480751 baseEnd_5480751 := by
    simpa [prefixWord, tailWord_5480751, baseEnd_5480751] using wordTrace_append hprefix tailTrace_5480751
  have hstable : (prefixWord ++ tailWord_5480751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480751).length < 2 ^ (prefixWord ++ tailWord_5480751).sum := by decide
  have hdescent : baseEnd_5480751 < baseStart_5480751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480791 : List Nat := [1, 1, 3, 2, 3, 1, 1, 4, 1, 4, 2]
def baseStart_5480791 : Nat := 118140960795 + 5480791 * 2 ^ 59
def prefixEnd_5480791 : Nat := 4983230072969 + 3 ^ 40 * 5480791 * 2
def baseEnd_5480791 : Nat := 2814280149836371113706807

theorem tailTrace_5480791 : CollatzResearch.WordTrace tailWord_5480791 prefixEnd_5480791 2814280149836371113706807 := by
  unfold tailWord_5480791
  simp only [CollatzResearch.WordTrace]
  refine ⟨199900870287037726425594227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133267246858025150950396151 199900870287037726425594227)
  ·
    refine ⟨299851305430556589638391341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 199900870287037726425594227 299851305430556589638391341)
    ·
      refine ⟨112444239536458721114396753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 299851305430556589638391341 112444239536458721114396753)
      ·
        refine ⟨84333179652344040835797565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112444239536458721114396753 84333179652344040835797565)
        ·
          refine ⟨31624942369629015313424087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84333179652344040835797565 31624942369629015313424087)
          ·
            refine ⟨47437413554443522970136131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31624942369629015313424087 47437413554443522970136131)
            ·
              refine ⟨71156120331665284455204197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47437413554443522970136131 71156120331665284455204197)
              ·
                refine ⟨13341772562187240835350787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 71156120331665284455204197 13341772562187240835350787)
                ·
                  refine ⟨20012658843280861253026181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13341772562187240835350787 20012658843280861253026181)
                  ·
                    refine ⟨3752373533115161484942409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20012658843280861253026181 3752373533115161484942409)
                    ·
                      refine ⟨2814280149836371113706807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3752373533115161484942409 2814280149836371113706807)
                      ·
                        rfl

theorem cell23_5480791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 4, 1, 4, 2].length) (baseStart_5480791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480791 prefixEnd_5480791 := by exact prefixLift 5480791
  have htrace : WordTrace (prefixWord ++ tailWord_5480791) baseStart_5480791 baseEnd_5480791 := by
    simpa [prefixWord, tailWord_5480791, baseEnd_5480791] using wordTrace_append hprefix tailTrace_5480791
  have hstable : (prefixWord ++ tailWord_5480791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480791).length < 2 ^ (prefixWord ++ tailWord_5480791).sum := by decide
  have hdescent : baseEnd_5480791 < baseStart_5480791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480804 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 4, 2, 4]
def baseStart_5480804 : Nat := 118140960795 + 5480804 * 2 ^ 59
def prefixEnd_5480804 : Nat := 4983230072969 + 3 ^ 40 * 5480804 * 2
def baseEnd_5480804 : Nat := 2814286825084879562844247

theorem tailTrace_5480804 : CollatzResearch.WordTrace tailWord_5480804 prefixEnd_5480804 2814286825084879562844247 := by
  unfold tailWord_5480804
  simp only [CollatzResearch.WordTrace]
  refine ⟨99950672217995314822908733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133267562957327086430544977 99950672217995314822908733)
  ·
    refine ⟨37481502081748243058590775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99950672217995314822908733 37481502081748243058590775)
    ·
      refine ⟨56222253122622364587886163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37481502081748243058590775 56222253122622364587886163)
      ·
        refine ⟨84333379683933546881829245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56222253122622364587886163 84333379683933546881829245)
        ·
          refine ⟨31625017381475080080685967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 84333379683933546881829245 31625017381475080080685967)
          ·
            refine ⟨47437526072212620121028951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31625017381475080080685967 47437526072212620121028951)
            ·
              refine ⟨71156289108318930181543427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47437526072212620121028951 71156289108318930181543427)
              ·
                refine ⟨106734433662478395272315141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 71156289108318930181543427 106734433662478395272315141)
                ·
                  refine ⟨20012706311714699113559089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 106734433662478395272315141 20012706311714699113559089)
                  ·
                    refine ⟨15009529733786024335169317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20012706311714699113559089 15009529733786024335169317)
                    ·
                      refine ⟨2814286825084879562844247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15009529733786024335169317 2814286825084879562844247)
                      ·
                        rfl

theorem cell23_5480804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_5480804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480804 prefixEnd_5480804 := by exact prefixLift 5480804
  have htrace : WordTrace (prefixWord ++ tailWord_5480804) baseStart_5480804 baseEnd_5480804 := by
    simpa [prefixWord, tailWord_5480804, baseEnd_5480804] using wordTrace_append hprefix tailTrace_5480804
  have hstable : (prefixWord ++ tailWord_5480804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480804).length < 2 ^ (prefixWord ++ tailWord_5480804).sum := by decide
  have hdescent : baseEnd_5480804 < baseStart_5480804 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480821 : List Nat := [1, 3, 4, 1, 2, 1, 2, 1, 2, 2, 4]
def baseStart_5480821 : Nat := 118140960795 + 5480821 * 2 ^ 59
def prefixEnd_5480821 : Nat := 4983230072969 + 3 ^ 40 * 5480821 * 2
def baseEnd_5480821 : Nat := 2814295554256005996331669

theorem tailTrace_5480821 : CollatzResearch.WordTrace tailWord_5480821 prefixEnd_5480821 2814295554256005996331669 := by
  unfold tailWord_5480821
  simp only [CollatzResearch.WordTrace]
  refine ⟨199901964476929041549186317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133267976317952694366124211 199901964476929041549186317)
  ·
    refine ⟨74963236678848390580944869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 199901964476929041549186317 74963236678848390580944869)
    ·
      refine ⟨14055606877284073233927163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74963236678848390580944869 14055606877284073233927163)
      ·
        refine ⟨21083410315926109850890745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14055606877284073233927163 21083410315926109850890745)
        ·
          refine ⟨15812557736944582388168059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21083410315926109850890745 15812557736944582388168059)
          ·
            refine ⟨23718836605416873582252089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15812557736944582388168059 23718836605416873582252089)
            ·
              refine ⟨17789127454062655186689067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23718836605416873582252089 17789127454062655186689067)
              ·
                refine ⟨26683691181093982780033601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17789127454062655186689067 26683691181093982780033601)
                ·
                  refine ⟨20012768385820487085025201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26683691181093982780033601 20012768385820487085025201)
                  ·
                    refine ⟨15009576289365365313768901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20012768385820487085025201 15009576289365365313768901)
                    ·
                      refine ⟨2814295554256005996331669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 15009576289365365313768901 2814295554256005996331669)
                      ·
                        rfl

theorem cell23_5480821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_5480821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480821 prefixEnd_5480821 := by exact prefixLift 5480821
  have htrace : WordTrace (prefixWord ++ tailWord_5480821) baseStart_5480821 baseEnd_5480821 := by
    simpa [prefixWord, tailWord_5480821, baseEnd_5480821] using wordTrace_append hprefix tailTrace_5480821
  have hstable : (prefixWord ++ tailWord_5480821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480821).length < 2 ^ (prefixWord ++ tailWord_5480821).sum := by decide
  have hdescent : baseEnd_5480821 < baseStart_5480821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480844 : List Nat := [2, 2, 1, 2, 1, 4, 2, 1, 1, 7]
def baseStart_5480844 : Nat := 118140960795 + 5480844 * 2 ^ 59
def prefixEnd_5480844 : Nat := 4983230072969 + 3 ^ 40 * 5480844 * 2
def baseEnd_5480844 : Nat := 938102454770353135448021

theorem tailTrace_5480844 : CollatzResearch.WordTrace tailWord_5480844 prefixEnd_5480844 938102454770353135448021 := by
  unfold tailWord_5480844
  simp only [CollatzResearch.WordTrace]
  refine ⟨99951401677922858238636793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 133268535570563810984849057 99951401677922858238636793)
  ·
    refine ⟨74963551258442143678977595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99951401677922858238636793 74963551258442143678977595)
    ·
      refine ⟨112445326887663215518466393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74963551258442143678977595 112445326887663215518466393)
      ·
        refine ⟨84333995165747411638849795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 112445326887663215518466393 84333995165747411638849795)
        ·
          refine ⟨126500992748621117458274693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 84333995165747411638849795 126500992748621117458274693)
          ·
            refine ⟨23718936140366459523426505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 126500992748621117458274693 23718936140366459523426505)
            ·
              refine ⟨17789202105274844642569879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23718936140366459523426505 17789202105274844642569879)
              ·
                refine ⟨26683803157912266963854819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17789202105274844642569879 26683803157912266963854819)
                ·
                  refine ⟨40025704736868400445782229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26683803157912266963854819 40025704736868400445782229)
                  ·
                    refine ⟨938102454770353135448021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 40025704736868400445782229 938102454770353135448021)
                    ·
                      rfl

theorem cell23_5480844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 1, 1, 7].length) (baseStart_5480844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480844 prefixEnd_5480844 := by exact prefixLift 5480844
  have htrace : WordTrace (prefixWord ++ tailWord_5480844) baseStart_5480844 baseEnd_5480844 := by
    simpa [prefixWord, tailWord_5480844, baseEnd_5480844] using wordTrace_append hprefix tailTrace_5480844
  have hstable : (prefixWord ++ tailWord_5480844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480844).length < 2 ^ (prefixWord ++ tailWord_5480844).sum := by decide
  have hdescent : baseEnd_5480844 < baseStart_5480844 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5480865 : List Nat := [1, 2, 3, 5, 2, 1, 1, 1, 7]
def baseStart_5480865 : Nat := 118140960795 + 5480865 * 2 ^ 59
def prefixEnd_5480865 : Nat := 4983230072969 + 3 ^ 40 * 5480865 * 2
def baseEnd_5480865 : Nat := 312702016378311536020163

theorem tailTrace_5480865 : CollatzResearch.WordTrace tailWord_5480865 prefixEnd_5480865 312702016378311536020163 := by
  unfold tailWord_5480865
  simp only [CollatzResearch.WordTrace]
  refine ⟨199903569288769637063788049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 133269046192513091375858699 199903569288769637063788049)
  ·
    refine ⟨149927676966577227797841037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 199903569288769637063788049 149927676966577227797841037)
    ·
      refine ⟨56222878862466460424190389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 149927676966577227797841037 56222878862466460424190389)
      ·
        refine ⟨5270894893356230664767849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 56222878862466460424190389 5270894893356230664767849)
        ·
          refine ⟨3953171170017172998575887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5270894893356230664767849 3953171170017172998575887)
          ·
            refine ⟨5929756755025759497863831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3953171170017172998575887 5929756755025759497863831)
            ·
              refine ⟨8894635132538639246795747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5929756755025759497863831 8894635132538639246795747)
              ·
                refine ⟨13341952698807958870193621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8894635132538639246795747 13341952698807958870193621)
                ·
                  refine ⟨312702016378311536020163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13341952698807958870193621 312702016378311536020163)
                  ·
                    rfl

theorem cell23_5480865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 1, 7].length) (baseStart_5480865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5480865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5480865 prefixEnd_5480865 := by exact prefixLift 5480865
  have htrace : WordTrace (prefixWord ++ tailWord_5480865) baseStart_5480865 baseEnd_5480865 := by
    simpa [prefixWord, tailWord_5480865, baseEnd_5480865] using wordTrace_append hprefix tailTrace_5480865
  have hstable : (prefixWord ++ tailWord_5480865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5480865).length < 2 ^ (prefixWord ++ tailWord_5480865).sum := by decide
  have hdescent : baseEnd_5480865 < baseStart_5480865 := by decide
  rcases family_descends (prefixWord ++ tailWord_5480865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
