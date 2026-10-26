import V185TrunkScan22Chunk365

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3264504 : List Nat := [2, 1, 2, 1, 1, 3, 4, 4, 1, 3]
def baseStart_3264504 : Nat := 118140960795 + 3264504 * 2 ^ 59
def prefixEnd_3264504 : Nat := 4983230072969 + 3 ^ 40 * 3264504 * 2
def baseEnd_3264504 : Nat := 1117506433683467231191217

theorem tailTrace_3264504 : CollatzResearch.WordTrace tailWord_3264504 prefixEnd_3264504 1117506433683467231191217 := by
  unfold tailWord_3264504
  simp only [CollatzResearch.WordTrace]
  refine ⟨59533121282633507870424283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79377495043511343827232377 59533121282633507870424283)
  ·
    refine ⟨89299681923950261805636425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59533121282633507870424283 89299681923950261805636425)
    ·
      refine ⟨66974761442962696354227319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89299681923950261805636425 66974761442962696354227319)
      ·
        refine ⟨100462142164444044531340979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66974761442962696354227319 100462142164444044531340979)
        ·
          refine ⟨150693213246666066797011469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100462142164444044531340979 150693213246666066797011469)
          ·
            refine ⟨56509954967499775048879301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150693213246666066797011469 56509954967499775048879301)
            ·
              refine ⟨10595616556406207821664869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56509954967499775048879301 10595616556406207821664869)
              ·
                refine ⟨1986678104326163966562163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10595616556406207821664869 1986678104326163966562163)
                ·
                  refine ⟨2980017156489245949843245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1986678104326163966562163 2980017156489245949843245)
                  ·
                    refine ⟨1117506433683467231191217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2980017156489245949843245 1117506433683467231191217)
                    ·
                      rfl

theorem cell22_3264504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 1, 3].length) (baseStart_3264504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264504 prefixEnd_3264504 := by exact prefixLift 3264504
  have htrace : WordTrace (prefixWord ++ tailWord_3264504) baseStart_3264504 baseEnd_3264504 := by
    simpa [prefixWord, tailWord_3264504, baseEnd_3264504] using wordTrace_append hprefix tailTrace_3264504
  have hstable : (prefixWord ++ tailWord_3264504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264504).length < 2 ^ (prefixWord ++ tailWord_3264504).sum := by decide
  have hdescent : baseEnd_3264504 < baseStart_3264504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264547 : List Nat := [1, 1, 1, 4, 3, 1, 1, 5, 1, 4]
def baseStart_3264547 : Nat := 118140960795 + 3264547 * 2 ^ 59
def prefixEnd_3264547 : Nat := 4983230072969 + 3 ^ 40 * 3264547 * 2
def baseEnd_3264547 : Nat := 1117521153462229452366085

theorem tailTrace_3264547 : CollatzResearch.WordTrace tailWord_3264547 prefixEnd_3264547 1117521153462229452366085 := by
  unfold tailWord_3264547
  simp only [CollatzResearch.WordTrace]
  refine ⟨119067810904111234084663895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79378540602740822723109263 119067810904111234084663895)
  ·
    refine ⟨178601716356166851126995843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119067810904111234084663895 178601716356166851126995843)
    ·
      refine ⟨267902574534250276690493765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178601716356166851126995843 267902574534250276690493765)
      ·
        refine ⟨50231732725171926879467581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 267902574534250276690493765 50231732725171926879467581)
        ·
          refine ⟨18836899771939472579800343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50231732725171926879467581 18836899771939472579800343)
          ·
            refine ⟨28255349657909208869700515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18836899771939472579800343 28255349657909208869700515)
            ·
              refine ⟨42383024486863813304550773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28255349657909208869700515 42383024486863813304550773)
              ·
                refine ⟨3973408545643482497301635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42383024486863813304550773 3973408545643482497301635)
                ·
                  refine ⟨5960112818465223745952453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3973408545643482497301635 5960112818465223745952453)
                  ·
                    refine ⟨1117521153462229452366085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5960112818465223745952453 1117521153462229452366085)
                    ·
                      rfl

theorem cell22_3264547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 5, 1, 4].length) (baseStart_3264547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264547 prefixEnd_3264547 := by exact prefixLift 3264547
  have htrace : WordTrace (prefixWord ++ tailWord_3264547) baseStart_3264547 baseEnd_3264547 := by
    simpa [prefixWord, tailWord_3264547, baseEnd_3264547] using wordTrace_append hprefix tailTrace_3264547
  have hstable : (prefixWord ++ tailWord_3264547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264547).length < 2 ^ (prefixWord ++ tailWord_3264547).sum := by decide
  have hdescent : baseEnd_3264547 < baseStart_3264547 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264562 : List Nat := [3, 2, 1, 1, 2, 3, 3, 1, 6]
def baseStart_3264562 : Nat := 118140960795 + 3264562 * 2 ^ 59
def prefixEnd_3264562 : Nat := 4983230072969 + 3 ^ 40 * 3264562 * 2
def baseEnd_3264562 : Nat := 372508762756258137747013

theorem tailTrace_3264562 : CollatzResearch.WordTrace tailWord_3264562 prefixEnd_3264562 372508762756258137747013 := by
  unfold tailWord_3264562
  simp only [CollatzResearch.WordTrace]
  refine ⟨29767089499764222911614985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79378905332704594430973293 29767089499764222911614985)
  ·
    refine ⟨22325317124823167183711239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29767089499764222911614985 22325317124823167183711239)
    ·
      refine ⟨33487975687234750775566859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22325317124823167183711239 33487975687234750775566859)
      ·
        refine ⟨50231963530852126163350289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33487975687234750775566859 50231963530852126163350289)
        ·
          refine ⟨37673972648139094622512717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50231963530852126163350289 37673972648139094622512717)
          ·
            refine ⟨14127739743052160483442269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37673972648139094622512717 14127739743052160483442269)
            ·
              refine ⟨5297902403644560181290851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14127739743052160483442269 5297902403644560181290851)
              ·
                refine ⟨7946853605466840271936277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5297902403644560181290851 7946853605466840271936277)
                ·
                  refine ⟨372508762756258137747013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7946853605466840271936277 372508762756258137747013)
                  ·
                    rfl

theorem cell22_3264562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 3, 1, 6].length) (baseStart_3264562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264562 prefixEnd_3264562 := by exact prefixLift 3264562
  have htrace : WordTrace (prefixWord ++ tailWord_3264562) baseStart_3264562 baseEnd_3264562 := by
    simpa [prefixWord, tailWord_3264562, baseEnd_3264562] using wordTrace_append hprefix tailTrace_3264562
  have hstable : (prefixWord ++ tailWord_3264562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264562).length < 2 ^ (prefixWord ++ tailWord_3264562).sum := by decide
  have hdescent : baseEnd_3264562 < baseStart_3264562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264575 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 3, 6]
def baseStart_3264575 : Nat := 118140960795 + 3264575 * 2 ^ 59
def prefixEnd_3264575 : Nat := 4983230072969 + 3 ^ 40 * 3264575 * 2
def baseEnd_3264575 : Nat := 1117530738434446712665999

theorem tailTrace_3264575 : CollatzResearch.WordTrace tailWord_3264575 prefixEnd_3264575 1117530738434446712665999 := by
  unfold tailWord_3264575
  simp only [CollatzResearch.WordTrace]
  refine ⟨119068832148009794866683179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79379221432006529911122119 119068832148009794866683179)
  ·
    refine ⟨178603248222014692300024769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119068832148009794866683179 178603248222014692300024769)
    ·
      refine ⟨133952436166511019225018577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178603248222014692300024769 133952436166511019225018577)
      ·
        refine ⟨100464327124883264418763933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133952436166511019225018577 100464327124883264418763933)
        ·
          refine ⟨37674122671831224157036475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100464327124883264418763933 37674122671831224157036475)
          ·
            refine ⟨56511184007746836235554713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37674122671831224157036475 56511184007746836235554713)
            ·
              refine ⟨42383388005810127176666035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56511184007746836235554713 42383388005810127176666035)
              ·
                refine ⟨63575082008715190764999053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42383388005810127176666035 63575082008715190764999053)
                ·
                  refine ⟨23840655753268196536874645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63575082008715190764999053 23840655753268196536874645)
                  ·
                    refine ⟨1117530738434446712665999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23840655753268196536874645 1117530738434446712665999)
                    ·
                      rfl

theorem cell22_3264575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 3, 6].length) (baseStart_3264575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264575 prefixEnd_3264575 := by exact prefixLift 3264575
  have htrace : WordTrace (prefixWord ++ tailWord_3264575) baseStart_3264575 baseEnd_3264575 := by
    simpa [prefixWord, tailWord_3264575, baseEnd_3264575] using wordTrace_append hprefix tailTrace_3264575
  have hstable : (prefixWord ++ tailWord_3264575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264575).length < 2 ^ (prefixWord ++ tailWord_3264575).sum := by decide
  have hdescent : baseEnd_3264575 < baseStart_3264575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264594 : List Nat := [3, 2, 2, 1, 4, 1, 1, 2, 1, 5]
def baseStart_3264594 : Nat := 118140960795 + 3264594 * 2 ^ 59
def prefixEnd_3264594 : Nat := 4983230072969 + 3 ^ 40 * 3264594 * 2
def baseEnd_3264594 : Nat := 1117537242522736996440941

theorem tailTrace_3264594 : CollatzResearch.WordTrace tailWord_3264594 prefixEnd_3264594 1117537242522736996440941 := by
  unfold tailWord_3264594
  simp only [CollatzResearch.WordTrace]
  refine ⟨29767381283735240277906209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79379683423293974074416557 29767381283735240277906209)
  ·
    refine ⟨22325535962801430208429657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29767381283735240277906209 22325535962801430208429657)
    ·
      refine ⟨16744151972101072656322243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22325535962801430208429657 16744151972101072656322243)
      ·
        refine ⟨25116227958151608984483365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16744151972101072656322243 25116227958151608984483365)
        ·
          refine ⟨4709292742153426684590631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25116227958151608984483365 4709292742153426684590631)
          ·
            refine ⟨7063939113230140026885947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4709292742153426684590631 7063939113230140026885947)
            ·
              refine ⟨10595908669845210040328921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7063939113230140026885947 10595908669845210040328921)
              ·
                refine ⟨7946931502383907530246691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10595908669845210040328921 7946931502383907530246691)
                ·
                  refine ⟨11920397253575861295370037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7946931502383907530246691 11920397253575861295370037)
                  ·
                    refine ⟨1117537242522736996440941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11920397253575861295370037 1117537242522736996440941)
                    ·
                      rfl

theorem cell22_3264594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_3264594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264594 prefixEnd_3264594 := by exact prefixLift 3264594
  have htrace : WordTrace (prefixWord ++ tailWord_3264594) baseStart_3264594 baseEnd_3264594 := by
    simpa [prefixWord, tailWord_3264594, baseEnd_3264594] using wordTrace_append hprefix tailTrace_3264594
  have hstable : (prefixWord ++ tailWord_3264594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264594).length < 2 ^ (prefixWord ++ tailWord_3264594).sum := by decide
  have hdescent : baseEnd_3264594 < baseStart_3264594 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264635 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 11]
def baseStart_3264635 : Nat := 118140960795 + 3264635 * 2 ^ 59
def prefixEnd_3264635 : Nat := 4983230072969 + 3 ^ 40 * 3264635 * 2
def baseEnd_3264635 : Nat := 372517092553542185388605

theorem tailTrace_3264635 : CollatzResearch.WordTrace tailWord_3264635 prefixEnd_3264635 372517092553542185388605 := by
  unfold tailWord_3264635
  simp only [CollatzResearch.WordTrace]
  refine ⟨119071020527792425113867359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79380680351861616742578239 119071020527792425113867359)
  ·
    refine ⟨178606530791688637670801039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119071020527792425113867359 178606530791688637670801039)
    ·
      refine ⟨267909796187532956506201559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178606530791688637670801039 267909796187532956506201559)
      ·
        refine ⟨401864694281299434759302339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267909796187532956506201559 401864694281299434759302339)
        ·
          refine ⟨602797041421949152138953509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401864694281299434759302339 602797041421949152138953509)
          ·
            refine ⟨113024445266615466026053783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 602797041421949152138953509 113024445266615466026053783)
            ·
              refine ⟨169536667899923199039080675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113024445266615466026053783 169536667899923199039080675)
              ·
                refine ⟨254305001849884798558621013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169536667899923199039080675 254305001849884798558621013)
                ·
                  refine ⟨372517092553542185388605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 254305001849884798558621013 372517092553542185388605)
                  ·
                    rfl

theorem cell22_3264635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 11].length) (baseStart_3264635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264635 prefixEnd_3264635 := by exact prefixLift 3264635
  have htrace : WordTrace (prefixWord ++ tailWord_3264635) baseStart_3264635 baseEnd_3264635 := by
    simpa [prefixWord, tailWord_3264635, baseEnd_3264635] using wordTrace_append hprefix tailTrace_3264635
  have hstable : (prefixWord ++ tailWord_3264635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264635).length < 2 ^ (prefixWord ++ tailWord_3264635).sum := by decide
  have hdescent : baseEnd_3264635 < baseStart_3264635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264656 : List Nat := [2, 1, 1, 1, 1, 1, 8, 3, 1, 3]
def baseStart_3264656 : Nat := 118140960795 + 3264656 * 2 ^ 59
def prefixEnd_3264656 : Nat := 4983230072969 + 3 ^ 40 * 3264656 * 2
def baseEnd_3264656 : Nat := 1117558466389789501390751

theorem tailTrace_3264656 : CollatzResearch.WordTrace tailWord_3264656 prefixEnd_3264656 1117558466389789501390751 := by
  unfold tailWord_3264656
  simp only [CollatzResearch.WordTrace]
  refine ⟨59535893230358172850190911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79381190973810897133587881 59535893230358172850190911)
  ·
    refine ⟨89303839845537259275286367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59535893230358172850190911 89303839845537259275286367)
    ·
      refine ⟨133955759768305888912929551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89303839845537259275286367 133955759768305888912929551)
      ·
        refine ⟨200933639652458833369394327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133955759768305888912929551 200933639652458833369394327)
        ·
          refine ⟨301400459478688250054091491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200933639652458833369394327 301400459478688250054091491)
          ·
            refine ⟨452100689218032375081137237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301400459478688250054091491 452100689218032375081137237)
            ·
              refine ⟨5298054951773816895482077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 452100689218032375081137237 5298054951773816895482077)
              ·
                refine ⟨1986770606915181335805779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5298054951773816895482077 1986770606915181335805779)
                ·
                  refine ⟨2980155910372772003708669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1986770606915181335805779 2980155910372772003708669)
                  ·
                    refine ⟨1117558466389789501390751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2980155910372772003708669 1117558466389789501390751)
                    ·
                      rfl

theorem cell22_3264656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 3, 1, 3].length) (baseStart_3264656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264656 prefixEnd_3264656 := by exact prefixLift 3264656
  have htrace : WordTrace (prefixWord ++ tailWord_3264656) baseStart_3264656 baseEnd_3264656 := by
    simpa [prefixWord, tailWord_3264656, baseEnd_3264656] using wordTrace_append hprefix tailTrace_3264656
  have hstable : (prefixWord ++ tailWord_3264656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264656).length < 2 ^ (prefixWord ++ tailWord_3264656).sum := by decide
  have hdescent : baseEnd_3264656 < baseStart_3264656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264662 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 4, 3]
def baseStart_3264662 : Nat := 118140960795 + 3264662 * 2 ^ 59
def prefixEnd_3264662 : Nat := 4983230072969 + 3 ^ 40 * 3264662 * 2
def baseEnd_3264662 : Nat := 1117560520312407485740733

theorem tailTrace_3264662 : CollatzResearch.WordTrace tailWord_3264662 prefixEnd_3264662 1117560520312407485740733 := by
  unfold tailWord_3264662
  simp only [CollatzResearch.WordTrace]
  refine ⟨7442000331168413045318765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79381336865796405816733493 7442000331168413045318765)
  ·
    refine ⟨2790750124188154891994537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7442000331168413045318765 2790750124188154891994537)
    ·
      refine ⟨2093062593141116168995903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2790750124188154891994537 2093062593141116168995903)
      ·
        refine ⟨3139593889711674253493855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2093062593141116168995903 3139593889711674253493855)
        ·
          refine ⟨4709390834567511380240783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3139593889711674253493855 4709390834567511380240783)
          ·
            refine ⟨7064086251851267070361175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4709390834567511380240783 7064086251851267070361175)
            ·
              refine ⟨10596129377776900605541763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7064086251851267070361175 10596129377776900605541763)
              ·
                refine ⟨15894194066665350908312645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10596129377776900605541763 15894194066665350908312645)
                ·
                  refine ⟨2980161387499753295308621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15894194066665350908312645 2980161387499753295308621)
                  ·
                    refine ⟨1117560520312407485740733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2980161387499753295308621 1117560520312407485740733)
                    ·
                      rfl

theorem cell22_3264662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_3264662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264662 prefixEnd_3264662 := by exact prefixLift 3264662
  have htrace : WordTrace (prefixWord ++ tailWord_3264662) baseStart_3264662 baseEnd_3264662 := by
    simpa [prefixWord, tailWord_3264662, baseEnd_3264662] using wordTrace_append hprefix tailTrace_3264662
  have hstable : (prefixWord ++ tailWord_3264662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264662).length < 2 ^ (prefixWord ++ tailWord_3264662).sum := by decide
  have hdescent : baseEnd_3264662 < baseStart_3264662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264669 : List Nat := [1, 4, 2, 1, 1, 3, 3, 2, 5]
def baseStart_3264669 : Nat := 118140960795 + 3264669 * 2 ^ 59
def prefixEnd_3264669 : Nat := 4983230072969 + 3 ^ 40 * 3264669 * 2
def baseEnd_3264669 : Nat := 372520972185153933605237

theorem tailTrace_3264669 : CollatzResearch.WordTrace tailWord_3264669 prefixEnd_3264669 372520972185153933605237 := by
  unfold tailWord_3264669
  simp only [CollatzResearch.WordTrace]
  refine ⟨119072260609669248920605061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79381507073112832613736707 119072260609669248920605061)
  ·
    refine ⟨22326048864312984172613449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119072260609669248920605061 22326048864312984172613449)
    ·
      refine ⟨16744536648234738129460087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22326048864312984172613449 16744536648234738129460087)
      ·
        refine ⟨25116804972352107194190131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16744536648234738129460087 25116804972352107194190131)
        ·
          refine ⟨37675207458528160791285197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25116804972352107194190131 37675207458528160791285197)
          ·
            refine ⟨14128202796948060296731949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37675207458528160791285197 14128202796948060296731949)
            ·
              refine ⟨5298076048855522611274481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14128202796948060296731949 5298076048855522611274481)
              ·
                refine ⟨3973557036641641958455861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5298076048855522611274481 3973557036641641958455861)
                ·
                  refine ⟨372520972185153933605237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3973557036641641958455861 372520972185153933605237)
                  ·
                    rfl

theorem cell22_3264669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_3264669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264669 prefixEnd_3264669 := by exact prefixLift 3264669
  have htrace : WordTrace (prefixWord ++ tailWord_3264669) baseStart_3264669 baseEnd_3264669 := by
    simpa [prefixWord, tailWord_3264669, baseEnd_3264669] using wordTrace_append hprefix tailTrace_3264669
  have hstable : (prefixWord ++ tailWord_3264669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264669).length < 2 ^ (prefixWord ++ tailWord_3264669).sum := by decide
  have hdescent : baseEnd_3264669 < baseStart_3264669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264692 : List Nat := [2, 5, 3, 1, 2, 1, 2, 6]
def baseStart_3264692 : Nat := 118140960795 + 3264692 * 2 ^ 59
def prefixEnd_3264692 : Nat := 4983230072969 + 3 ^ 40 * 3264692 * 2
def baseEnd_3264692 : Nat := 124174532213944156387849

theorem tailTrace_3264692 : CollatzResearch.WordTrace tailWord_3264692 prefixEnd_3264692 124174532213944156387849 := by
  unfold tailWord_3264692
  simp only [CollatzResearch.WordTrace]
  refine ⟨59536549744292961924346165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79382066325723949232461553 59536549744292961924346165)
  ·
    refine ⟨5581551538527465180407453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59536549744292961924346165 5581551538527465180407453)
    ·
      refine ⟨2093081826947799442652795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5581551538527465180407453 2093081826947799442652795)
      ·
        refine ⟨3139622740421699163979193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2093081826947799442652795 3139622740421699163979193)
        ·
          refine ⟨2354717055316274372984395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3139622740421699163979193 2354717055316274372984395)
          ·
            refine ⟨3532075582974411559476593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2354717055316274372984395 3532075582974411559476593)
            ·
              refine ⟨2649056687230808669607445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3532075582974411559476593 2649056687230808669607445)
              ·
                refine ⟨124174532213944156387849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2649056687230808669607445 124174532213944156387849)
                ·
                  rfl

theorem cell22_3264692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 2, 6].length) (baseStart_3264692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264692 prefixEnd_3264692 := by exact prefixLift 3264692
  have htrace : WordTrace (prefixWord ++ tailWord_3264692) baseStart_3264692 baseEnd_3264692 := by
    simpa [prefixWord, tailWord_3264692, baseEnd_3264692] using wordTrace_append hprefix tailTrace_3264692
  have hstable : (prefixWord ++ tailWord_3264692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264692).length < 2 ^ (prefixWord ++ tailWord_3264692).sum := by decide
  have hdescent : baseEnd_3264692 < baseStart_3264692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264697 : List Nat := [1, 2, 1, 4, 1, 2, 1, 4, 6]
def baseStart_3264697 : Nat := 118140960795 + 3264697 * 2 ^ 59
def prefixEnd_3264697 : Nat := 4983230072969 + 3 ^ 40 * 3264697 * 2
def baseEnd_3264697 : Nat := 372524167175893020371875

theorem tailTrace_3264697 : CollatzResearch.WordTrace tailWord_3264697 prefixEnd_3264697 372524167175893020371875 := by
  unfold tailWord_3264697
  simp only [CollatzResearch.WordTrace]
  refine ⟨119073281853567809702624345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79382187902378539801749563 119073281853567809702624345)
  ·
    refine ⟨89304961390175857276968259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119073281853567809702624345 89304961390175857276968259)
    ·
      refine ⟨133957442085263785915452389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89304961390175857276968259 133957442085263785915452389)
      ·
        refine ⟨25117020390986959859147323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133957442085263785915452389 25117020390986959859147323)
        ·
          refine ⟨37675530586480439788720985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25117020390986959859147323 37675530586480439788720985)
          ·
            refine ⟨28256647939860329841540739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37675530586480439788720985 28256647939860329841540739)
            ·
              refine ⟨42384971909790494762311109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28256647939860329841540739 42384971909790494762311109)
              ·
                refine ⟨7947182233085717767933333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42384971909790494762311109 7947182233085717767933333)
                ·
                  refine ⟨372524167175893020371875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7947182233085717767933333 372524167175893020371875)
                  ·
                    rfl

theorem cell22_3264697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 4, 6].length) (baseStart_3264697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264697 prefixEnd_3264697 := by exact prefixLift 3264697
  have htrace : WordTrace (prefixWord ++ tailWord_3264697) baseStart_3264697 baseEnd_3264697 := by
    simpa [prefixWord, tailWord_3264697, baseEnd_3264697] using wordTrace_append hprefix tailTrace_3264697
  have hstable : (prefixWord ++ tailWord_3264697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264697).length < 2 ^ (prefixWord ++ tailWord_3264697).sum := by decide
  have hdescent : baseEnd_3264697 < baseStart_3264697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264699 : List Nat := [1, 1, 1, 1, 1, 2, 8, 2, 1, 4]
def baseStart_3264699 : Nat := 118140960795 + 3264699 * 2 ^ 59
def prefixEnd_3264699 : Nat := 4983230072969 + 3 ^ 40 * 3264699 * 2
def baseEnd_3264699 : Nat := 1117573186168551722565619

theorem tailTrace_3264699 : CollatzResearch.WordTrace tailWord_3264699 prefixEnd_3264699 1117573186168551722565619 := by
  unfold tailWord_3264699
  simp only [CollatzResearch.WordTrace]
  refine ⟨119073354799560564044197151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79382236533040376029464767 119073354799560564044197151)
  ·
    refine ⟨178610032199340846066295727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119073354799560564044197151 178610032199340846066295727)
    ·
      refine ⟨267915048299011269099443591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178610032199340846066295727 267915048299011269099443591)
      ·
        refine ⟨401872572448516903649165387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 267915048299011269099443591 401872572448516903649165387)
        ·
          refine ⟨602808858672775355473748081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401872572448516903649165387 602808858672775355473748081)
          ·
            refine ⟨452106644004581516605311061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 602808858672775355473748081 452106644004581516605311061)
            ·
              refine ⟨5298124734428689647718489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 452106644004581516605311061 5298124734428689647718489)
              ·
                refine ⟨3973593550821517235788867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5298124734428689647718489 3973593550821517235788867)
                ·
                  refine ⟨5960390326232275853683301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3973593550821517235788867 5960390326232275853683301)
                  ·
                    refine ⟨1117573186168551722565619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5960390326232275853683301 1117573186168551722565619)
                    ·
                      rfl

theorem cell22_3264699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 4].length) (baseStart_3264699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264699 prefixEnd_3264699 := by exact prefixLift 3264699
  have htrace : WordTrace (prefixWord ++ tailWord_3264699) baseStart_3264699 baseEnd_3264699 := by
    simpa [prefixWord, tailWord_3264699, baseEnd_3264699] using wordTrace_append hprefix tailTrace_3264699
  have hstable : (prefixWord ++ tailWord_3264699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264699).length < 2 ^ (prefixWord ++ tailWord_3264699).sum := by decide
  have hdescent : baseEnd_3264699 < baseStart_3264699 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264712 : List Nat := [2, 1, 3, 1, 2, 1, 1, 3, 3, 5]
def baseStart_3264712 : Nat := 118140960795 + 3264712 * 2 ^ 59
def prefixEnd_3264712 : Nat := 4983230072969 + 3 ^ 40 * 3264712 * 2
def baseEnd_3264712 : Nat := 1117577636334224021990579

theorem tailTrace_3264712 : CollatzResearch.WordTrace tailWord_3264712 prefixEnd_3264712 1117577636334224021990579 := by
  unfold tailWord_3264712
  simp only [CollatzResearch.WordTrace]
  refine ⟨59536914474256733632210195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79382552632342311509613593 59536914474256733632210195)
  ·
    refine ⟨89305371711385100448315293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59536914474256733632210195 89305371711385100448315293)
    ·
      refine ⟨33489514391769412668118235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89305371711385100448315293 33489514391769412668118235)
      ·
        refine ⟨50234271587654119002177353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33489514391769412668118235 50234271587654119002177353)
        ·
          refine ⟨37675703690740589251633015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50234271587654119002177353 37675703690740589251633015)
          ·
            refine ⟨56513555536110883877449523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37675703690740589251633015 56513555536110883877449523)
            ·
              refine ⟨84770333304166325816174285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56513555536110883877449523 84770333304166325816174285)
              ·
                refine ⟨31788874989062372181065357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84770333304166325816174285 31788874989062372181065357)
                ·
                  refine ⟨11920828120898389567899509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31788874989062372181065357 11920828120898389567899509)
                  ·
                    refine ⟨1117577636334224021990579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11920828120898389567899509 1117577636334224021990579)
                    ·
                      rfl

theorem cell22_3264712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_3264712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264712 prefixEnd_3264712 := by exact prefixLift 3264712
  have htrace : WordTrace (prefixWord ++ tailWord_3264712) baseStart_3264712 baseEnd_3264712 := by
    simpa [prefixWord, tailWord_3264712, baseEnd_3264712] using wordTrace_append hprefix tailTrace_3264712
  have hstable : (prefixWord ++ tailWord_3264712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264712).length < 2 ^ (prefixWord ++ tailWord_3264712).sum := by decide
  have hdescent : baseEnd_3264712 < baseStart_3264712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264729 : List Nat := [1, 2, 1, 2, 3, 1, 4, 1, 4, 3]
def baseStart_3264729 : Nat := 118140960795 + 3264729 * 2 ^ 59
def prefixEnd_3264729 : Nat := 4983230072969 + 3 ^ 40 * 3264729 * 2
def baseEnd_3264729 : Nat := 1117583455781641644315527

theorem tailTrace_3264729 : CollatzResearch.WordTrace tailWord_3264729 prefixEnd_3264729 1117583455781641644315527 := by
  unfold tailWord_3264729
  simp only [CollatzResearch.WordTrace]
  refine ⟨119074448989451879167789241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79382965992967919445192827 119074448989451879167789241)
  ·
    refine ⟨89305836742088909375841931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119074448989451879167789241 89305836742088909375841931)
    ·
      refine ⟨133958755113133364063762897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89305836742088909375841931 133958755113133364063762897)
      ·
        refine ⟨100469066334850023047822173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133958755113133364063762897 100469066334850023047822173)
        ·
          refine ⟨37675899875568758642933315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100469066334850023047822173 37675899875568758642933315)
          ·
            refine ⟨56513849813353137964399973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37675899875568758642933315 56513849813353137964399973)
            ·
              refine ⟨10596346840003713368324995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56513849813353137964399973 10596346840003713368324995)
              ·
                refine ⟨15894520260005570052487493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10596346840003713368324995 15894520260005570052487493)
                ·
                  refine ⟨2980222548751044384841405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15894520260005570052487493 2980222548751044384841405)
                  ·
                    refine ⟨1117583455781641644315527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2980222548751044384841405 1117583455781641644315527)
                    ·
                      rfl

theorem cell22_3264729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 4, 3].length) (baseStart_3264729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264729 prefixEnd_3264729 := by exact prefixLift 3264729
  have htrace : WordTrace (prefixWord ++ tailWord_3264729) baseStart_3264729 baseEnd_3264729 := by
    simpa [prefixWord, tailWord_3264729, baseEnd_3264729] using wordTrace_append hprefix tailTrace_3264729
  have hstable : (prefixWord ++ tailWord_3264729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264729).length < 2 ^ (prefixWord ++ tailWord_3264729).sum := by decide
  have hdescent : baseEnd_3264729 < baseStart_3264729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264746 : List Nat := [3, 1, 3, 1, 1, 2, 3, 3, 2, 3]
def baseStart_3264746 : Nat := 118140960795 + 3264746 * 2 ^ 59
def prefixEnd_3264746 : Nat := 4983230072969 + 3 ^ 40 * 3264746 * 2
def baseEnd_3264746 : Nat := 1117589275229059266640475

theorem tailTrace_3264746 : CollatzResearch.WordTrace tailWord_3264746 prefixEnd_3264746 1117589275229059266640475 := by
  unfold tailWord_3264746
  simp only [CollatzResearch.WordTrace]
  refine ⟨29768767257597572767789523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79383379353593527380772061 29768767257597572767789523)
  ·
    refine ⟨44653150886396359151684285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29768767257597572767789523 44653150886396359151684285)
    ·
      refine ⟨16744931582398634681881607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44653150886396359151684285 16744931582398634681881607)
      ·
        refine ⟨25117397373597952022822411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16744931582398634681881607 25117397373597952022822411)
        ·
          refine ⟨37676096060396928034233617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25117397373597952022822411 37676096060396928034233617)
          ·
            refine ⟨28257072045297696025675213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37676096060396928034233617 28257072045297696025675213)
            ·
              refine ⟨10596402016986636009628205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28257072045297696025675213 10596402016986636009628205)
              ·
                refine ⟨3973650756369988503610577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10596402016986636009628205 3973650756369988503610577)
                ·
                  refine ⟨2980238067277491377707933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3973650756369988503610577 2980238067277491377707933)
                  ·
                    refine ⟨1117589275229059266640475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2980238067277491377707933 1117589275229059266640475)
                    ·
                      rfl

theorem cell22_3264746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 3, 2, 3].length) (baseStart_3264746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264746 prefixEnd_3264746 := by exact prefixLift 3264746
  have htrace : WordTrace (prefixWord ++ tailWord_3264746) baseStart_3264746 baseEnd_3264746 := by
    simpa [prefixWord, tailWord_3264746, baseEnd_3264746] using wordTrace_append hprefix tailTrace_3264746
  have hstable : (prefixWord ++ tailWord_3264746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264746).length < 2 ^ (prefixWord ++ tailWord_3264746).sum := by decide
  have hdescent : baseEnd_3264746 < baseStart_3264746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264787 : List Nat := [1, 1, 1, 2, 1, 3, 1, 5, 7]
def baseStart_3264787 : Nat := 118140960795 + 3264787 * 2 ^ 59
def prefixEnd_3264787 : Nat := 4983230072969 + 3 ^ 40 * 3264787 * 2
def baseEnd_3264787 : Nat := 372534436788982942121783

theorem tailTrace_3264787 : CollatzResearch.WordTrace tailWord_3264787 prefixEnd_3264787 372534436788982942121783 := by
  unfold tailWord_3264787
  simp only [CollatzResearch.WordTrace]
  refine ⟨119076564423241755073400615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79384376282161170048933743 119076564423241755073400615)
  ·
    refine ⟨178614846634862632610100923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119076564423241755073400615 178614846634862632610100923)
    ·
      refine ⟨267922269952293948915151385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178614846634862632610100923 267922269952293948915151385)
      ·
        refine ⟨200941702464220461686363539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267922269952293948915151385 200941702464220461686363539)
        ·
          refine ⟨301412553696330692529545309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200941702464220461686363539 301412553696330692529545309)
          ·
            refine ⟨113029707636124009698579491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 301412553696330692529545309 113029707636124009698579491)
            ·
              refine ⟨169544561454186014547869237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113029707636124009698579491 169544561454186014547869237)
              ·
                refine ⟨15894802636329938863862741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 169544561454186014547869237 15894802636329938863862741)
                ·
                  refine ⟨372534436788982942121783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15894802636329938863862741 372534436788982942121783)
                  ·
                    rfl

theorem cell22_3264787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 5, 7].length) (baseStart_3264787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264787 prefixEnd_3264787 := by exact prefixLift 3264787
  have htrace : WordTrace (prefixWord ++ tailWord_3264787) baseStart_3264787 baseEnd_3264787 := by
    simpa [prefixWord, tailWord_3264787, baseEnd_3264787] using wordTrace_append hprefix tailTrace_3264787
  have hstable : (prefixWord ++ tailWord_3264787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264787).length < 2 ^ (prefixWord ++ tailWord_3264787).sum := by decide
  have hdescent : baseEnd_3264787 < baseStart_3264787 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264808 : List Nat := [2, 1, 5, 1, 3, 1, 1, 2, 3, 3]
def baseStart_3264808 : Nat := 118140960795 + 3264808 * 2 ^ 59
def prefixEnd_3264808 : Nat := 4983230072969 + 3 ^ 40 * 3264808 * 2
def baseEnd_3264808 : Nat := 1117610499096111771590285

theorem tailTrace_3264808 : CollatzResearch.WordTrace tailWord_3264808 prefixEnd_3264808 1117610499096111771590285 := by
  unfold tailWord_3264808
  simp only [CollatzResearch.WordTrace]
  refine ⟨59538665178082837829957539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79384886904110450439943385 59538665178082837829957539)
  ·
    refine ⟨89307997767124256744936309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59538665178082837829957539 89307997767124256744936309)
    ·
      refine ⟨8372624790667899069837779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89307997767124256744936309 8372624790667899069837779)
      ·
        refine ⟨12558937186001848604756669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8372624790667899069837779 12558937186001848604756669)
        ·
          refine ⟨4709601444750693226783751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12558937186001848604756669 4709601444750693226783751)
          ·
            refine ⟨7064402167126039840175627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4709601444750693226783751 7064402167126039840175627)
            ·
              refine ⟨10596603250689059760263441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7064402167126039840175627 10596603250689059760263441)
              ·
                refine ⟨7947452438016794820197581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10596603250689059760263441 7947452438016794820197581)
                ·
                  refine ⟨2980294664256298057574093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7947452438016794820197581 2980294664256298057574093)
                  ·
                    refine ⟨1117610499096111771590285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2980294664256298057574093 1117610499096111771590285)
                    ·
                      rfl

theorem cell22_3264808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_3264808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264808 prefixEnd_3264808 := by exact prefixLift 3264808
  have htrace : WordTrace (prefixWord ++ tailWord_3264808) baseStart_3264808 baseEnd_3264808 := by
    simpa [prefixWord, tailWord_3264808, baseEnd_3264808] using wordTrace_append hprefix tailTrace_3264808
  have hstable : (prefixWord ++ tailWord_3264808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264808).length < 2 ^ (prefixWord ++ tailWord_3264808).sum := by decide
  have hdescent : baseEnd_3264808 < baseStart_3264808 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264825 : List Nat := [1, 2, 1, 6, 1, 2, 2, 3, 1, 3]
def baseStart_3264825 : Nat := 118140960795 + 3264825 * 2 ^ 59
def prefixEnd_3264825 : Nat := 4983230072969 + 3 ^ 40 * 3264825 * 2
def baseEnd_3264825 : Nat := 1117616318543529393915233

theorem tailTrace_3264825 : CollatzResearch.WordTrace tailWord_3264825 prefixEnd_3264825 1117616318543529393915233 := by
  unfold tailWord_3264825
  simp only [CollatzResearch.WordTrace]
  refine ⟨119077950397104087563283929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79385300264736058375522619 119077950397104087563283929)
  ·
    refine ⟨89308462797828065672462947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119077950397104087563283929 89308462797828065672462947)
    ·
      refine ⟨133962694196742098508694421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89308462797828065672462947 133962694196742098508694421)
      ·
        refine ⟨6279501290472285867595051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 133962694196742098508694421 6279501290472285867595051)
        ·
          refine ⟨9419251935708428801392577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6279501290472285867595051 9419251935708428801392577)
          ·
            refine ⟨7064438951781321601044433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9419251935708428801392577 7064438951781321601044433)
            ·
              refine ⟨5298329213835991200783325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7064438951781321601044433 5298329213835991200783325)
              ·
                refine ⟨1986873455188496700293747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5298329213835991200783325 1986873455188496700293747)
                ·
                  refine ⟨2980310182782745050440621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1986873455188496700293747 2980310182782745050440621)
                  ·
                    refine ⟨1117616318543529393915233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2980310182782745050440621 1117616318543529393915233)
                    ·
                      rfl

theorem cell22_3264825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 3, 1, 3].length) (baseStart_3264825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264825 prefixEnd_3264825 := by exact prefixLift 3264825
  have htrace : WordTrace (prefixWord ++ tailWord_3264825) baseStart_3264825 baseEnd_3264825 := by
    simpa [prefixWord, tailWord_3264825, baseEnd_3264825] using wordTrace_append hprefix tailTrace_3264825
  have hstable : (prefixWord ++ tailWord_3264825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264825).length < 2 ^ (prefixWord ++ tailWord_3264825).sum := by decide
  have hdescent : baseEnd_3264825 < baseStart_3264825 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264849 : List Nat := [1, 2, 2, 1, 4, 2, 1, 3, 6]
def baseStart_3264849 : Nat := 118140960795 + 3264849 * 2 ^ 59
def prefixEnd_3264849 : Nat := 4983230072969 + 3 ^ 40 * 3264849 * 2
def baseEnd_3264849 : Nat := 372541511411333777105053

theorem tailTrace_3264849 : CollatzResearch.WordTrace tailWord_3264849 prefixEnd_3264849 372541511411333777105053 := by
  unfold tailWord_3264849
  simp only [CollatzResearch.WordTrace]
  refine ⟨119078825749017139662157601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79385883832678093108105067 119078825749017139662157601)
  ·
    refine ⟨89309119311762854746618201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119078825749017139662157601 89309119311762854746618201)
    ·
      refine ⟨66981839483822141059963651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89309119311762854746618201 66981839483822141059963651)
      ·
        refine ⟨100472759225733211589945477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66981839483822141059963651 100472759225733211589945477)
        ·
          refine ⟨18838642354824977173114777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100472759225733211589945477 18838642354824977173114777)
          ·
            refine ⟨14128981766118732879836083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18838642354824977173114777 14128981766118732879836083)
            ·
              refine ⟨21193472649178099319754125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14128981766118732879836083 21193472649178099319754125)
              ·
                refine ⟨7947552243441787244907797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21193472649178099319754125 7947552243441787244907797)
                ·
                  refine ⟨372541511411333777105053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7947552243441787244907797 372541511411333777105053)
                  ·
                    rfl

theorem cell22_3264849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 3, 6].length) (baseStart_3264849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264849 prefixEnd_3264849 := by exact prefixLift 3264849
  have htrace : WordTrace (prefixWord ++ tailWord_3264849) baseStart_3264849 baseEnd_3264849 := by
    simpa [prefixWord, tailWord_3264849, baseEnd_3264849] using wordTrace_append hprefix tailTrace_3264849
  have hstable : (prefixWord ++ tailWord_3264849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264849).length < 2 ^ (prefixWord ++ tailWord_3264849).sum := by decide
  have hdescent : baseEnd_3264849 < baseStart_3264849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264866 : List Nat := [3, 3, 2, 1, 1, 2, 2, 2, 6]
def baseStart_3264866 : Nat := 118140960795 + 3264866 * 2 ^ 59
def prefixEnd_3264866 : Nat := 4983230072969 + 3 ^ 40 * 3264866 * 2
def baseEnd_3264866 : Nat := 372543451227139651213369

theorem tailTrace_3264866 : CollatzResearch.WordTrace tailWord_3264866 prefixEnd_3264866 372543451227139651213369 := by
  unfold tailWord_3264866
  simp only [CollatzResearch.WordTrace]
  refine ⟨29769861447488887891381613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79386297193303701043684301 29769861447488887891381613)
  ·
    refine ⟨11163698042808332959268105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29769861447488887891381613 11163698042808332959268105)
    ·
      refine ⟨8372773532106249719451079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11163698042808332959268105 8372773532106249719451079)
      ·
        refine ⟨12559160298159374579176619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8372773532106249719451079 12559160298159374579176619)
        ·
          refine ⟨18838740447239061868764929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12559160298159374579176619 18838740447239061868764929)
          ·
            refine ⟨14129055335429296401573697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18838740447239061868764929 14129055335429296401573697)
            ·
              refine ⟨10596791501571972301180273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14129055335429296401573697 10596791501571972301180273)
              ·
                refine ⟨7947593626178979225885205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10596791501571972301180273 7947593626178979225885205)
                ·
                  refine ⟨372543451227139651213369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7947593626178979225885205 372543451227139651213369)
                  ·
                    rfl

theorem cell22_3264866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 2, 6].length) (baseStart_3264866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264866 prefixEnd_3264866 := by exact prefixLift 3264866
  have htrace : WordTrace (prefixWord ++ tailWord_3264866) baseStart_3264866 baseEnd_3264866 := by
    simpa [prefixWord, tailWord_3264866, baseEnd_3264866] using wordTrace_append hprefix tailTrace_3264866
  have hstable : (prefixWord ++ tailWord_3264866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264866).length < 2 ^ (prefixWord ++ tailWord_3264866).sum := by decide
  have hdescent : baseEnd_3264866 < baseStart_3264866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264954 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 3, 7]
def baseStart_3264954 : Nat := 118140960795 + 3264954 * 2 ^ 59
def prefixEnd_3264954 : Nat := 4983230072969 + 3 ^ 40 * 3264954 * 2
def baseEnd_3264954 : Nat := 1117660477879816057439837

theorem tailTrace_3264954 : CollatzResearch.WordTrace tailWord_3264954 prefixEnd_3264954 1117660477879816057439837 := by
  unfold tailWord_3264954
  simp only [CollatzResearch.WordTrace]
  refine ⟨29770663853409185648682479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79388436942424495063153277 29770663853409185648682479)
  ·
    refine ⟨44655995780113778473023719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29770663853409185648682479 44655995780113778473023719)
    ·
      refine ⟨66983993670170667709535579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44655995780113778473023719 66983993670170667709535579)
      ·
        refine ⟨100475990505256001564303369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66983993670170667709535579 100475990505256001564303369)
        ·
          refine ⟨75356992878942001173227527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100475990505256001564303369 75356992878942001173227527)
          ·
            refine ⟨113035489318413001759841291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75356992878942001173227527 113035489318413001759841291)
            ·
              refine ⟨169553233977619502639761937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113035489318413001759841291 169553233977619502639761937)
              ·
                refine ⟨127164925483214626979821453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 169553233977619502639761937 127164925483214626979821453)
                ·
                  refine ⟨47686847056205485117433045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127164925483214626979821453 47686847056205485117433045)
                  ·
                    refine ⟨1117660477879816057439837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47686847056205485117433045 1117660477879816057439837)
                    ·
                      rfl

theorem cell22_3264954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 3, 7].length) (baseStart_3264954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264954 prefixEnd_3264954 := by exact prefixLift 3264954
  have htrace : WordTrace (prefixWord ++ tailWord_3264954) baseStart_3264954 baseEnd_3264954 := by
    simpa [prefixWord, tailWord_3264954, baseEnd_3264954] using wordTrace_append hprefix tailTrace_3264954
  have hstable : (prefixWord ++ tailWord_3264954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264954).length < 2 ^ (prefixWord ++ tailWord_3264954).sum := by decide
  have hdescent : baseEnd_3264954 < baseStart_3264954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3264986 : List Nat := [3, 1, 1, 2, 3, 1, 1, 3, 3, 4]
def baseStart_3264986 : Nat := 118140960795 + 3264986 * 2 ^ 59
def prefixEnd_3264986 : Nat := 4983230072969 + 3 ^ 40 * 3264986 * 2
def baseEnd_3264986 : Nat := 1117671432133778640639739

theorem tailTrace_3264986 : CollatzResearch.WordTrace tailWord_3264986 prefixEnd_3264986 1117671432133778640639739 := by
  unfold tailWord_3264986
  simp only [CollatzResearch.WordTrace]
  refine ⟨29770955637380203014973703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79389215033013874706596541 29770955637380203014973703)
  ·
    refine ⟨44656433456070304522460555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29770955637380203014973703 44656433456070304522460555)
    ·
      refine ⟨66984650184105456783690833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44656433456070304522460555 66984650184105456783690833)
      ·
        refine ⟨50238487638079092587768125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 66984650184105456783690833 50238487638079092587768125)
        ·
          refine ⟨18839432864279659720413047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50238487638079092587768125 18839432864279659720413047)
          ·
            refine ⟨28259149296419489580619571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18839432864279659720413047 28259149296419489580619571)
            ·
              refine ⟨42388723944629234370929357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28259149296419489580619571 42388723944629234370929357)
              ·
                refine ⟨15895771479235962889098509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42388723944629234370929357 15895771479235962889098509)
                ·
                  refine ⟨5960914304713486083411941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15895771479235962889098509 5960914304713486083411941)
                  ·
                    refine ⟨1117671432133778640639739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5960914304713486083411941 1117671432133778640639739)
                    ·
                      rfl

theorem cell22_3264986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 3, 3, 4].length) (baseStart_3264986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3264986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3264986 prefixEnd_3264986 := by exact prefixLift 3264986
  have htrace : WordTrace (prefixWord ++ tailWord_3264986) baseStart_3264986 baseEnd_3264986 := by
    simpa [prefixWord, tailWord_3264986, baseEnd_3264986] using wordTrace_append hprefix tailTrace_3264986
  have hstable : (prefixWord ++ tailWord_3264986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3264986).length < 2 ^ (prefixWord ++ tailWord_3264986).sum := by decide
  have hdescent : baseEnd_3264986 < baseStart_3264986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3264986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265037 : List Nat := [1, 7, 1, 1, 1, 1, 1, 4, 1, 4]
def baseStart_3265037 : Nat := 118140960795 + 3265037 * 2 ^ 59
def prefixEnd_3265037 : Nat := 4983230072969 + 3 ^ 40 * 3265037 * 2
def baseEnd_3265037 : Nat := 1117688890476031507614583

theorem tailTrace_3265037 : CollatzResearch.WordTrace tailWord_3265037 prefixEnd_3265037 1117688890476031507614583 := by
  unfold tailWord_3265037
  simp only [CollatzResearch.WordTrace]
  refine ⟨119085682672336047770001365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79390455114890698513334243 119085682672336047770001365)
  ·
    refine ⟨2791070687632876119609407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 119085682672336047770001365 2791070687632876119609407)
    ·
      refine ⟨4186606031449314179414111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2791070687632876119609407 4186606031449314179414111)
      ·
        refine ⟨6279909047173971269121167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4186606031449314179414111 6279909047173971269121167)
        ·
          refine ⟨9419863570760956903681751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6279909047173971269121167 9419863570760956903681751)
          ·
            refine ⟨14129795356141435355522627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9419863570760956903681751 14129795356141435355522627)
            ·
              refine ⟨21194693034212153033283941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14129795356141435355522627 21194693034212153033283941)
              ·
                refine ⟨3974004943914778693740739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21194693034212153033283941 3974004943914778693740739)
                ·
                  refine ⟨5961007415872168040611109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3974004943914778693740739 5961007415872168040611109)
                  ·
                    refine ⟨1117688890476031507614583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5961007415872168040611109 1117688890476031507614583)
                    ·
                      rfl

theorem cell22_3265037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_3265037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265037 prefixEnd_3265037 := by exact prefixLift 3265037
  have htrace : WordTrace (prefixWord ++ tailWord_3265037) baseStart_3265037 baseEnd_3265037 := by
    simpa [prefixWord, tailWord_3265037, baseEnd_3265037] using wordTrace_append hprefix tailTrace_3265037
  have hstable : (prefixWord ++ tailWord_3265037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265037).length < 2 ^ (prefixWord ++ tailWord_3265037).sum := by decide
  have hdescent : baseEnd_3265037 < baseStart_3265037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265069 : List Nat := [1, 5, 4, 1, 1, 2, 1, 1, 6]
def baseStart_3265069 : Nat := 118140960795 + 3265069 * 2 ^ 59
def prefixEnd_3265069 : Nat := 4983230072969 + 3 ^ 40 * 3265069 * 2
def baseEnd_3265069 : Nat := 372566614909998030271495

theorem tailTrace_3265069 : CollatzResearch.WordTrace tailWord_3265069 prefixEnd_3265069 372566614909998030271495 := by
  unfold tailWord_3265069
  simp only [CollatzResearch.WordTrace]
  refine ⟨119086849808220117235166261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79391233205480078156777507 119086849808220117235166261)
  ·
    refine ⟨11164392169520635990796837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119086849808220117235166261 11164392169520635990796837)
    ·
      refine ⟨2093323531785119248274407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11164392169520635990796837 2093323531785119248274407)
      ·
        refine ⟨3139985297677678872411611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2093323531785119248274407 3139985297677678872411611)
        ·
          refine ⟨4709977946516518308617417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3139985297677678872411611 4709977946516518308617417)
          ·
            refine ⟨3532483459887388731463063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4709977946516518308617417 3532483459887388731463063)
            ·
              refine ⟨5298725189831083097194595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3532483459887388731463063 5298725189831083097194595)
              ·
                refine ⟨7948087784746624645791893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5298725189831083097194595 7948087784746624645791893)
                ·
                  refine ⟨372566614909998030271495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7948087784746624645791893 372566614909998030271495)
                  ·
                    rfl

theorem cell22_3265069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 2, 1, 1, 6].length) (baseStart_3265069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265069 prefixEnd_3265069 := by exact prefixLift 3265069
  have htrace : WordTrace (prefixWord ++ tailWord_3265069) baseStart_3265069 baseEnd_3265069 := by
    simpa [prefixWord, tailWord_3265069, baseEnd_3265069] using wordTrace_append hprefix tailTrace_3265069
  have hstable : (prefixWord ++ tailWord_3265069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265069).length < 2 ^ (prefixWord ++ tailWord_3265069).sum := by decide
  have hdescent : baseEnd_3265069 < baseStart_3265069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265125 : List Nat := [1, 3, 1, 3, 4, 1, 2, 2, 5]
def baseStart_3265125 : Nat := 118140960795 + 3265125 * 2 ^ 59
def prefixEnd_3265125 : Nat := 4983230072969 + 3 ^ 40 * 3265125 * 2
def baseEnd_3265125 : Nat := 372573004891476203804771

theorem tailTrace_3265125 : CollatzResearch.WordTrace tailWord_3265125 prefixEnd_3265125 372573004891476203804771 := by
  unfold tailWord_3265125
  simp only [CollatzResearch.WordTrace]
  refine ⟨119088892296017238799204829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79392594864011492532803219 119088892296017238799204829)
  ·
    refine ⟨44658334611006464549701811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119088892296017238799204829 44658334611006464549701811)
    ·
      refine ⟨66987501916509696824552717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44658334611006464549701811 66987501916509696824552717)
      ·
        refine ⟨25120313218691136309207269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 66987501916509696824552717 25120313218691136309207269)
        ·
          refine ⟨4710058728504588057976363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25120313218691136309207269 4710058728504588057976363)
          ·
            refine ⟨7065088092756882086964545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4710058728504588057976363 7065088092756882086964545)
            ·
              refine ⟨5298816069567661565223409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7065088092756882086964545 5298816069567661565223409)
              ·
                refine ⟨3974112052175746173917557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5298816069567661565223409 3974112052175746173917557)
                ·
                  refine ⟨372573004891476203804771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3974112052175746173917557 372573004891476203804771)
                  ·
                    rfl

theorem cell22_3265125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 2, 2, 5].length) (baseStart_3265125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265125 prefixEnd_3265125 := by exact prefixLift 3265125
  have htrace : WordTrace (prefixWord ++ tailWord_3265125) baseStart_3265125 baseEnd_3265125 := by
    simpa [prefixWord, tailWord_3265125, baseEnd_3265125] using wordTrace_append hprefix tailTrace_3265125
  have hstable : (prefixWord ++ tailWord_3265125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265125).length < 2 ^ (prefixWord ++ tailWord_3265125).sum := by decide
  have hdescent : baseEnd_3265125 < baseStart_3265125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265153 : List Nat := [1, 2, 4, 2, 1, 1, 3, 2, 6]
def baseStart_3265153 : Nat := 118140960795 + 3265153 * 2 ^ 59
def prefixEnd_3265153 : Nat := 4983230072969 + 3 ^ 40 * 3265153 * 2
def baseEnd_3265153 : Nat := 372576199882215290571409

theorem tailTrace_3265153 : CollatzResearch.WordTrace tailWord_3265153 prefixEnd_3265153 372576199882215290571409 := by
  unfold tailWord_3265153
  simp only [CollatzResearch.WordTrace]
  refine ⟨119089913539915799581224113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79393275693277199720816075 119089913539915799581224113)
  ·
    refine ⟨89317435154936849685918085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119089913539915799581224113 89317435154936849685918085)
    ·
      refine ⟨16747019091550659316109641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89317435154936849685918085 16747019091550659316109641)
      ·
        refine ⟨12560264318662994487082231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16747019091550659316109641 12560264318662994487082231)
        ·
          refine ⟨18840396477994491730623347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12560264318662994487082231 18840396477994491730623347)
          ·
            refine ⟨28260594716991737595935021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18840396477994491730623347 28260594716991737595935021)
            ·
              refine ⟨10597723018871901598475633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28260594716991737595935021 10597723018871901598475633)
              ·
                refine ⟨7948292264153926198856725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10597723018871901598475633 7948292264153926198856725)
                ·
                  refine ⟨372576199882215290571409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7948292264153926198856725 372576199882215290571409)
                  ·
                    rfl

theorem cell22_3265153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 2, 6].length) (baseStart_3265153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265153 prefixEnd_3265153 := by exact prefixLift 3265153
  have htrace : WordTrace (prefixWord ++ tailWord_3265153) baseStart_3265153 baseEnd_3265153 := by
    simpa [prefixWord, tailWord_3265153, baseEnd_3265153] using wordTrace_append hprefix tailTrace_3265153
  have hstable : (prefixWord ++ tailWord_3265153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265153).length < 2 ^ (prefixWord ++ tailWord_3265153).sum := by decide
  have hdescent : baseEnd_3265153 < baseStart_3265153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265172 : List Nat := [2, 4, 2, 2, 1, 2, 1, 3, 1, 4]
def baseStart_3265172 : Nat := 118140960795 + 3265172 * 2 ^ 59
def prefixEnd_3265172 : Nat := 4983230072969 + 3 ^ 40 * 3265172 * 2
def baseEnd_3265172 : Nat := 1117735103734936155489169

theorem tailTrace_3265172 : CollatzResearch.WordTrace tailWord_3265172 prefixEnd_3265172 1117735103734936155489169 := by
  unfold tailWord_3265172
  simp only [CollatzResearch.WordTrace]
  refine ⟨59545303263423482913082885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79393737684564643884110513 59545303263423482913082885)
  ·
    refine ⟨11164744361891903046203041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59545303263423482913082885 11164744361891903046203041)
    ·
      refine ⟨8373558271418927284652281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11164744361891903046203041 8373558271418927284652281)
      ·
        refine ⟨6280168703564195463489211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8373558271418927284652281 6280168703564195463489211)
        ·
          refine ⟨9420253055346293195233817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6280168703564195463489211 9420253055346293195233817)
          ·
            refine ⟨7065189791509719896425363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9420253055346293195233817 7065189791509719896425363)
            ·
              refine ⟨10597784687264579844638045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7065189791509719896425363 10597784687264579844638045)
              ·
                refine ⟨3974169257724217441739267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10597784687264579844638045 3974169257724217441739267)
                ·
                  refine ⟨5961253886586326162608901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3974169257724217441739267 5961253886586326162608901)
                  ·
                    refine ⟨1117735103734936155489169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5961253886586326162608901 1117735103734936155489169)
                    ·
                      rfl

theorem cell22_3265172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_3265172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265172 prefixEnd_3265172 := by exact prefixLift 3265172
  have htrace : WordTrace (prefixWord ++ tailWord_3265172) baseStart_3265172 baseEnd_3265172 := by
    simpa [prefixWord, tailWord_3265172, baseEnd_3265172] using wordTrace_append hprefix tailTrace_3265172
  have hstable : (prefixWord ++ tailWord_3265172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265172).length < 2 ^ (prefixWord ++ tailWord_3265172).sum := by decide
  have hdescent : baseEnd_3265172 < baseStart_3265172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265215 : List Nat := [1, 1, 2, 2, 2, 6, 2, 6]
def baseStart_3265215 : Nat := 118140960795 + 3265215 * 2 ^ 59
def prefixEnd_3265215 : Nat := 4983230072969 + 3 ^ 40 * 3265215 * 2
def baseEnd_3265215 : Nat := 124194424834855375184893

theorem tailTrace_3265215 : CollatzResearch.WordTrace tailWord_3265215 prefixEnd_3265215 124194424834855375184893 := by
  unfold tailWord_3265215
  simp only [CollatzResearch.WordTrace]
  refine ⟨119092174865691184169981099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79394783243794122779987399 119092174865691184169981099)
  ·
    refine ⟨178638262298536776254971649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119092174865691184169981099 178638262298536776254971649)
    ·
      refine ⟨133978696723902582191228737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178638262298536776254971649 133978696723902582191228737)
      ·
        refine ⟨100484022542926936643421553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 133978696723902582191228737 100484022542926936643421553)
        ·
          refine ⟨75363016907195202482566165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100484022542926936643421553 75363016907195202482566165)
          ·
            refine ⟨3532641417524775116370289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 75363016907195202482566165 3532641417524775116370289)
            ·
              refine ⟨2649481063143581337277717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3532641417524775116370289 2649481063143581337277717)
              ·
                refine ⟨124194424834855375184893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2649481063143581337277717 124194424834855375184893)
                ·
                  rfl

theorem cell22_3265215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 6].length) (baseStart_3265215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265215 prefixEnd_3265215 := by exact prefixLift 3265215
  have htrace : WordTrace (prefixWord ++ tailWord_3265215) baseStart_3265215 baseEnd_3265215 := by
    simpa [prefixWord, tailWord_3265215, baseEnd_3265215] using wordTrace_append hprefix tailTrace_3265215
  have hstable : (prefixWord ++ tailWord_3265215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265215).length < 2 ^ (prefixWord ++ tailWord_3265215).sum := by decide
  have hdescent : baseEnd_3265215 < baseStart_3265215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265247 : List Nat := [1, 1, 2, 3, 2, 5, 1, 1, 3, 3]
def baseStart_3265247 : Nat := 118140960795 + 3265247 * 2 ^ 59
def prefixEnd_3265247 : Nat := 4983230072969 + 3 ^ 40 * 3265247 * 2
def baseEnd_3265247 : Nat := 1117760777767660959863939

theorem tailTrace_3265247 : CollatzResearch.WordTrace tailWord_3265247 prefixEnd_3265247 1117760777767660959863939 := by
  unfold tailWord_3265247
  simp only [CollatzResearch.WordTrace]
  refine ⟨119093342001575253635145995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79395561334383502423430663 119093342001575253635145995)
  ·
    refine ⟨178640013002362880452718993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119093342001575253635145995 178640013002362880452718993)
    ·
      refine ⟨133980009751772160339539245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178640013002362880452718993 133980009751772160339539245)
      ·
        refine ⟨50242503656914560127327217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 133980009751772160339539245 50242503656914560127327217)
        ·
          refine ⟨37681877742685920095495413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50242503656914560127327217 37681877742685920095495413)
          ·
            refine ⟨3532676038376805008952695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37681877742685920095495413 3532676038376805008952695)
            ·
              refine ⟨5299014057565207513429043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3532676038376805008952695 5299014057565207513429043)
              ·
                refine ⟨7948521086347811270143565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5299014057565207513429043 7948521086347811270143565)
                ·
                  refine ⟨2980695407380429226303837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7948521086347811270143565 2980695407380429226303837)
                  ·
                    refine ⟨1117760777767660959863939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2980695407380429226303837 1117760777767660959863939)
                    ·
                      rfl

theorem cell22_3265247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 3].length) (baseStart_3265247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265247 prefixEnd_3265247 := by exact prefixLift 3265247
  have htrace : WordTrace (prefixWord ++ tailWord_3265247) baseStart_3265247 baseEnd_3265247 := by
    simpa [prefixWord, tailWord_3265247, baseEnd_3265247] using wordTrace_append hprefix tailTrace_3265247
  have hstable : (prefixWord ++ tailWord_3265247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265247).length < 2 ^ (prefixWord ++ tailWord_3265247).sum := by decide
  have hdescent : baseEnd_3265247 < baseStart_3265247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265258 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 1, 7]
def baseStart_3265258 : Nat := 118140960795 + 3265258 * 2 ^ 59
def prefixEnd_3265258 : Nat := 4983230072969 + 3 ^ 40 * 3265258 * 2
def baseEnd_3265258 : Nat := 1117764543292460597838905

theorem tailTrace_3265258 : CollatzResearch.WordTrace tailWord_3265258 prefixEnd_3265258 1117764543292460597838905 := by
  unfold tailWord_3265258
  simp only [CollatzResearch.WordTrace]
  refine ⟨29773435801133850628449107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79395828803023601675864285 29773435801133850628449107)
  ·
    refine ⟨44660153701700775942673661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29773435801133850628449107 44660153701700775942673661)
    ·
      refine ⟨16747557638137790978502623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44660153701700775942673661 16747557638137790978502623)
      ·
        refine ⟨25121336457206686467753935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16747557638137790978502623 25121336457206686467753935)
        ·
          refine ⟨37682004685810029701630903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25121336457206686467753935 37682004685810029701630903)
          ·
            refine ⟨56523007028715044552446355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37682004685810029701630903 56523007028715044552446355)
            ·
              refine ⟨84784510543072566828669533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56523007028715044552446355 84784510543072566828669533)
              ·
                refine ⟨31794191453652212560751075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84784510543072566828669533 31794191453652212560751075)
                ·
                  refine ⟨47691287180478318841126613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31794191453652212560751075 47691287180478318841126613)
                  ·
                    refine ⟨1117764543292460597838905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47691287180478318841126613 1117764543292460597838905)
                    ·
                      rfl

theorem cell22_3265258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_3265258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265258 prefixEnd_3265258 := by exact prefixLift 3265258
  have htrace : WordTrace (prefixWord ++ tailWord_3265258) baseStart_3265258 baseEnd_3265258 := by
    simpa [prefixWord, tailWord_3265258, baseEnd_3265258] using wordTrace_append hprefix tailTrace_3265258
  have hstable : (prefixWord ++ tailWord_3265258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265258).length < 2 ^ (prefixWord ++ tailWord_3265258).sum := by decide
  have hdescent : baseEnd_3265258 < baseStart_3265258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265341 : List Nat := [1, 4, 1, 4, 2, 2, 2, 1, 1, 4]
def baseStart_3265341 : Nat := 118140960795 + 3265341 * 2 ^ 59
def prefixEnd_3265341 : Nat := 4983230072969 + 3 ^ 40 * 3265341 * 2
def baseEnd_3265341 : Nat := 1117792955888676048013651

theorem tailTrace_3265341 : CollatzResearch.WordTrace tailWord_3265341 prefixEnd_3265341 1117792955888676048013651 := by
  unfold tailWord_3265341
  simp only [CollatzResearch.WordTrace]
  refine ⟨119096770463234707689067877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79397846975489805126045251 119096770463234707689067877)
  ·
    refine ⟨22330644461856507691700227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119096770463234707689067877 22330644461856507691700227)
    ·
      refine ⟨33495966692784761537550341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22330644461856507691700227 33495966692784761537550341)
      ·
        refine ⟨6280493754897142788290689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33495966692784761537550341 6280493754897142788290689)
        ·
          refine ⟨4710370316172857091218017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6280493754897142788290689 4710370316172857091218017)
          ·
            refine ⟨3532777737129642818413513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4710370316172857091218017 3532777737129642818413513)
            ·
              refine ⟨2649583302847232113810135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3532777737129642818413513 2649583302847232113810135)
              ·
                refine ⟨3974374954270848170715203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2649583302847232113810135 3974374954270848170715203)
                ·
                  refine ⟨5961562431406272256072805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3974374954270848170715203 5961562431406272256072805)
                  ·
                    refine ⟨1117792955888676048013651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5961562431406272256072805 1117792955888676048013651)
                    ·
                      rfl

theorem cell22_3265341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_3265341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265341 prefixEnd_3265341 := by exact prefixLift 3265341
  have htrace : WordTrace (prefixWord ++ tailWord_3265341) baseStart_3265341 baseEnd_3265341 := by
    simpa [prefixWord, tailWord_3265341, baseEnd_3265341] using wordTrace_append hprefix tailTrace_3265341
  have hstable : (prefixWord ++ tailWord_3265341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265341).length < 2 ^ (prefixWord ++ tailWord_3265341).sum := by decide
  have hdescent : baseEnd_3265341 < baseStart_3265341 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265363 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 1, 8]
def baseStart_3265363 : Nat := 118140960795 + 3265363 * 2 ^ 59
def prefixEnd_3265363 : Nat := 4983230072969 + 3 ^ 40 * 3265363 * 2
def baseEnd_3265363 : Nat := 1117800486938275323963583

theorem tailTrace_3265363 : CollatzResearch.WordTrace tailWord_3265363 prefixEnd_3265363 1117800486938275323963583 := by
  unfold tailWord_3265363
  simp only [CollatzResearch.WordTrace]
  refine ⟨119097572869155005446368743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79398381912770003630912495 119097572869155005446368743)
  ·
    refine ⟨178646359303732508169553115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119097572869155005446368743 178646359303732508169553115)
    ·
      refine ⟨267969538955598762254329673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178646359303732508169553115 267969538955598762254329673)
      ·
        refine ⟨200977154216699071690747255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 267969538955598762254329673 200977154216699071690747255)
        ·
          refine ⟨301465731325048607536120883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200977154216699071690747255 301465731325048607536120883)
          ·
            refine ⟨452198596987572911304181325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301465731325048607536120883 452198596987572911304181325)
            ·
              refine ⟨169574473870339841739067997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 452198596987572911304181325 169574473870339841739067997)
              ·
                refine ⟨63590427701377440652150499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169574473870339841739067997 63590427701377440652150499)
                ·
                  refine ⟨95385641552066160978225749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63590427701377440652150499 95385641552066160978225749)
                  ·
                    refine ⟨1117800486938275323963583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95385641552066160978225749 1117800486938275323963583)
                    ·
                      rfl

theorem cell22_3265363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 1, 8].length) (baseStart_3265363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265363 prefixEnd_3265363 := by exact prefixLift 3265363
  have htrace : WordTrace (prefixWord ++ tailWord_3265363) baseStart_3265363 baseEnd_3265363 := by
    simpa [prefixWord, tailWord_3265363, baseEnd_3265363] using wordTrace_append hprefix tailTrace_3265363
  have hstable : (prefixWord ++ tailWord_3265363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265363).length < 2 ^ (prefixWord ++ tailWord_3265363).sum := by decide
  have hdescent : baseEnd_3265363 < baseStart_3265363 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265425 : List Nat := [1, 2, 2, 1, 1, 1, 3, 4, 3, 4]
def baseStart_3265425 : Nat := 118140960795 + 3265425 * 2 ^ 59
def prefixEnd_3265425 : Nat := 4983230072969 + 3 ^ 40 * 3265425 * 2
def baseEnd_3265425 : Nat := 1117821710805327828913393

theorem tailTrace_3265425 : CollatzResearch.WordTrace tailWord_3265425 prefixEnd_3265425 1117821710805327828913393 := by
  unfold tailWord_3265425
  simp only [CollatzResearch.WordTrace]
  refine ⟨119099834194930390035125729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79399889463286926690083819 119099834194930390035125729)
  ·
    refine ⟨89324875646197792526344297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119099834194930390035125729 89324875646197792526344297)
    ·
      refine ⟨66993656734648344394758223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89324875646197792526344297 66993656734648344394758223)
      ·
        refine ⟨100490485101972516592137335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 66993656734648344394758223 100490485101972516592137335)
        ·
          refine ⟨150735727652958774888206003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100490485101972516592137335 150735727652958774888206003)
          ·
            refine ⟨226103591479438162332309005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150735727652958774888206003 226103591479438162332309005)
            ·
              refine ⟨84788846804789310874615877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 226103591479438162332309005 84788846804789310874615877)
              ·
                refine ⟨15897908775897995788990477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 84788846804789310874615877 15897908775897995788990477)
                ·
                  refine ⟨5961715790961748420871429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15897908775897995788990477 5961715790961748420871429)
                  ·
                    refine ⟨1117821710805327828913393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5961715790961748420871429 1117821710805327828913393)
                    ·
                      rfl

theorem cell22_3265425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 4].length) (baseStart_3265425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265425 prefixEnd_3265425 := by exact prefixLift 3265425
  have htrace : WordTrace (prefixWord ++ tailWord_3265425) baseStart_3265425 baseEnd_3265425 := by
    simpa [prefixWord, tailWord_3265425, baseEnd_3265425] using wordTrace_append hprefix tailTrace_3265425
  have hstable : (prefixWord ++ tailWord_3265425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265425).length < 2 ^ (prefixWord ++ tailWord_3265425).sum := by decide
  have hdescent : baseEnd_3265425 < baseStart_3265425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265429 : List Nat := [1, 3, 2, 1, 1, 6, 2, 1, 5]
def baseStart_3265429 : Nat := 118140960795 + 3265429 * 2 ^ 59
def prefixEnd_3265429 : Nat := 4983230072969 + 3 ^ 40 * 3265429 * 2
def baseEnd_3265429 : Nat := 372607693362357717271127

theorem tailTrace_3265429 : CollatzResearch.WordTrace tailWord_3265429 prefixEnd_3265429 372607693362357717271127 := by
  unfold tailWord_3265429
  simp only [CollatzResearch.WordTrace]
  refine ⟨119099980086915898718271341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79399986724610599145514227 119099980086915898718271341)
  ·
    refine ⟨44662492532593462019351753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119099980086915898718271341 44662492532593462019351753)
    ·
      refine ⟨33496869399445096514513815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44662492532593462019351753 33496869399445096514513815)
      ·
        refine ⟨50245304099167644771770723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33496869399445096514513815 50245304099167644771770723)
        ·
          refine ⟨75367956148751467157656085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50245304099167644771770723 75367956148751467157656085)
          ·
            refine ⟨3532872944472725023015129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 75367956148751467157656085 3532872944472725023015129)
            ·
              refine ⟨2649654708354543767261347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3532872944472725023015129 2649654708354543767261347)
              ·
                refine ⟨3974482062531815650892021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2649654708354543767261347 3974482062531815650892021)
                ·
                  refine ⟨372607693362357717271127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3974482062531815650892021 372607693362357717271127)
                  ·
                    rfl

theorem cell22_3265429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 1, 5].length) (baseStart_3265429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265429 prefixEnd_3265429 := by exact prefixLift 3265429
  have htrace : WordTrace (prefixWord ++ tailWord_3265429) baseStart_3265429 baseEnd_3265429 := by
    simpa [prefixWord, tailWord_3265429, baseEnd_3265429] using wordTrace_append hprefix tailTrace_3265429
  have hstable : (prefixWord ++ tailWord_3265429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265429).length < 2 ^ (prefixWord ++ tailWord_3265429).sum := by decide
  have hdescent : baseEnd_3265429 < baseStart_3265429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265440 : List Nat := [2, 1, 1, 4, 1, 1, 2, 4, 6]
def baseStart_3265440 : Nat := 118140960795 + 3265440 * 2 ^ 59
def prefixEnd_3265440 : Nat := 4983230072969 + 3 ^ 40 * 3265440 * 2
def baseEnd_3265440 : Nat := 372608948537290929929449

theorem tailTrace_3265440 : CollatzResearch.WordTrace tailWord_3265440 prefixEnd_3265440 372608948537290929929449 := by
  unfold tailWord_3265440
  simp only [CollatzResearch.WordTrace]
  refine ⟨59550190644938023798460887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79400254193250698397947849 59550190644938023798460887)
  ·
    refine ⟨89325285967407035697691331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59550190644938023798460887 89325285967407035697691331)
    ·
      refine ⟨133987928951110553546536997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89325285967407035697691331 133987928951110553546536997)
      ·
        refine ⟨25122736678333228789975687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 133987928951110553546536997 25122736678333228789975687)
        ·
          refine ⟨37684105017499843184963531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25122736678333228789975687 37684105017499843184963531)
          ·
            refine ⟨56526157526249764777445297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37684105017499843184963531 56526157526249764777445297)
            ·
              refine ⟨42394618144687323583083973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56526157526249764777445297 42394618144687323583083973)
              ·
                refine ⟨7948990902128873171828245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42394618144687323583083973 7948990902128873171828245)
                ·
                  refine ⟨372608948537290929929449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7948990902128873171828245 372608948537290929929449)
                  ·
                    rfl

theorem cell22_3265440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 4, 6].length) (baseStart_3265440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265440 prefixEnd_3265440 := by exact prefixLift 3265440
  have htrace : WordTrace (prefixWord ++ tailWord_3265440) baseStart_3265440 baseEnd_3265440 := by
    simpa [prefixWord, tailWord_3265440, baseEnd_3265440] using wordTrace_append hprefix tailTrace_3265440
  have hstable : (prefixWord ++ tailWord_3265440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265440).length < 2 ^ (prefixWord ++ tailWord_3265440).sum := by decide
  have hdescent : baseEnd_3265440 < baseStart_3265440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265598 : List Nat := [4, 2, 1, 3, 1, 3, 2, 1, 5]
def baseStart_3265598 : Nat := 118140960795 + 3265598 * 2 ^ 59
def prefixEnd_3265598 : Nat := 4983230072969 + 3 ^ 40 * 3265598 * 2
def baseEnd_3265598 : Nat := 372626977413604348112621

theorem tailTrace_3265598 : CollatzResearch.WordTrace tailWord_3265598 prefixEnd_3265598 372626977413604348112621 := by
  unfold tailWord_3265598
  simp only [CollatzResearch.WordTrace]
  refine ⟨14888268002912955072646681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79404096015535760387448965 14888268002912955072646681)
  ·
    refine ⟨11166201002184716304485011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14888268002912955072646681 11166201002184716304485011)
    ·
      refine ⟨16749301503277074456727517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11166201002184716304485011 16749301503277074456727517)
      ·
        refine ⟨6280988063728902921272819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16749301503277074456727517 6280988063728902921272819)
        ·
          refine ⟨9421482095593354381909229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6280988063728902921272819 9421482095593354381909229)
          ·
            refine ⟨3533055785847507893215961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9421482095593354381909229 3533055785847507893215961)
            ·
              refine ⟨2649791839385630919911971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3533055785847507893215961 2649791839385630919911971)
              ·
                refine ⟨3974687759078446379867957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2649791839385630919911971 3974687759078446379867957)
                ·
                  refine ⟨372626977413604348112621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3974687759078446379867957 372626977413604348112621)
                  ·
                    rfl

theorem cell22_3265598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_3265598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265598 prefixEnd_3265598 := by exact prefixLift 3265598
  have htrace : WordTrace (prefixWord ++ tailWord_3265598) baseStart_3265598 baseEnd_3265598 := by
    simpa [prefixWord, tailWord_3265598, baseEnd_3265598] using wordTrace_append hprefix tailTrace_3265598
  have hstable : (prefixWord ++ tailWord_3265598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265598).length < 2 ^ (prefixWord ++ tailWord_3265598).sum := by decide
  have hdescent : baseEnd_3265598 < baseStart_3265598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265639 : List Nat := [1, 1, 5, 1, 1, 3, 2, 2, 2, 4]
def baseStart_3265639 : Nat := 118140960795 + 3265639 * 2 ^ 59
def prefixEnd_3265639 : Nat := 4983230072969 + 3 ^ 40 * 3265639 * 2
def baseEnd_3265639 : Nat := 1117894967378702604062737

theorem tailTrace_3265639 : CollatzResearch.WordTrace tailWord_3265639 prefixEnd_3265639 1117894967378702604062737 := by
  unfold tailWord_3265639
  simp only [CollatzResearch.WordTrace]
  refine ⟨119107639416155104583415971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79405092944103403055610647 119107639416155104583415971)
  ·
    refine ⟨178661459124232656875123957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119107639416155104583415971 178661459124232656875123957)
    ·
      refine ⟨16749511792896811582042871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178661459124232656875123957 16749511792896811582042871)
      ·
        refine ⟨25124267689345217373064307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16749511792896811582042871 25124267689345217373064307)
        ·
          refine ⟨37686401534017826059596461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25124267689345217373064307 37686401534017826059596461)
          ·
            refine ⟨14132400575256684772348673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37686401534017826059596461 14132400575256684772348673)
            ·
              refine ⟨10599300431442513579261505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14132400575256684772348673 10599300431442513579261505)
              ·
                refine ⟨7949475323581885184446129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10599300431442513579261505 7949475323581885184446129)
                ·
                  refine ⟨5962106492686413888334597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7949475323581885184446129 5962106492686413888334597)
                  ·
                    refine ⟨1117894967378702604062737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5962106492686413888334597 1117894967378702604062737)
                    ·
                      rfl

theorem cell22_3265639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_3265639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265639 prefixEnd_3265639 := by exact prefixLift 3265639
  have htrace : WordTrace (prefixWord ++ tailWord_3265639) baseStart_3265639 baseEnd_3265639 := by
    simpa [prefixWord, tailWord_3265639, baseEnd_3265639] using wordTrace_append hprefix tailTrace_3265639
  have hstable : (prefixWord ++ tailWord_3265639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265639).length < 2 ^ (prefixWord ++ tailWord_3265639).sum := by decide
  have hdescent : baseEnd_3265639 < baseStart_3265639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265641 : List Nat := [1, 2, 1, 1, 1, 7, 2, 2, 2, 3]
def baseStart_3265641 : Nat := 118140960795 + 3265641 * 2 ^ 59
def prefixEnd_3265641 : Nat := 4983230072969 + 3 ^ 40 * 3265641 * 2
def baseEnd_3265641 : Nat := 1117895652019575265512731

theorem tailTrace_3265641 : CollatzResearch.WordTrace tailWord_3265641 prefixEnd_3265641 1117895652019575265512731 := by
  unfold tailWord_3265641
  simp only [CollatzResearch.WordTrace]
  refine ⟨119107712362147858924988777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79405141574765239283325851 119107712362147858924988777)
  ·
    refine ⟨89330784271610894193741583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119107712362147858924988777 89330784271610894193741583)
    ·
      refine ⟨133996176407416341290612375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89330784271610894193741583 133996176407416341290612375)
      ·
        refine ⟨200994264611124511935918563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 133996176407416341290612375 200994264611124511935918563)
        ·
          refine ⟨301491396916686767903877845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 200994264611124511935918563 301491396916686767903877845)
          ·
            refine ⟨7066204615234846122747137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 301491396916686767903877845 7066204615234846122747137)
            ·
              refine ⟨5299653461426134592060353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7066204615234846122747137 5299653461426134592060353)
              ·
                refine ⟨3974740096069600944045265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5299653461426134592060353 3974740096069600944045265)
                ·
                  refine ⟨2981055072052200708033949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3974740096069600944045265 2981055072052200708033949)
                  ·
                    refine ⟨1117895652019575265512731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2981055072052200708033949 1117895652019575265512731)
                    ·
                      rfl

theorem cell22_3265641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 3].length) (baseStart_3265641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265641 prefixEnd_3265641 := by exact prefixLift 3265641
  have htrace : WordTrace (prefixWord ++ tailWord_3265641) baseStart_3265641 baseEnd_3265641 := by
    simpa [prefixWord, tailWord_3265641, baseEnd_3265641] using wordTrace_append hprefix tailTrace_3265641
  have hstable : (prefixWord ++ tailWord_3265641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265641).length < 2 ^ (prefixWord ++ tailWord_3265641).sum := by decide
  have hdescent : baseEnd_3265641 < baseStart_3265641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265667 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 2, 6]
def baseStart_3265667 : Nat := 118140960795 + 3265667 * 2 ^ 59
def prefixEnd_3265667 : Nat := 4983230072969 + 3 ^ 40 * 3265667 * 2
def baseEnd_3265667 : Nat := 1117904552350919864362651

theorem tailTrace_3265667 : CollatzResearch.WordTrace tailWord_3265667 prefixEnd_3265667 1117904552350919864362651 := by
  unfold tailWord_3265667
  simp only [CollatzResearch.WordTrace]
  refine ⟨119108660660053665365435255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79405773773369110243623503 119108660660053665365435255)
  ·
    refine ⟨178662990990080498048152883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119108660660053665365435255 178662990990080498048152883)
    ·
      refine ⟨267994486485120747072229325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178662990990080498048152883 267994486485120747072229325)
      ·
        refine ⟨100497932431920280152085997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 267994486485120747072229325 100497932431920280152085997)
        ·
          refine ⟨37686724661970105057032249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100497932431920280152085997 37686724661970105057032249)
          ·
            refine ⟨28265043496477578792774187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37686724661970105057032249 28265043496477578792774187)
            ·
              refine ⟨42397565244716368189161281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28265043496477578792774187 42397565244716368189161281)
              ·
                refine ⟨31798173933537276141870961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42397565244716368189161281 31798173933537276141870961)
                ·
                  refine ⟨23848630450152957106403221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31798173933537276141870961 23848630450152957106403221)
                  ·
                    refine ⟨1117904552350919864362651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23848630450152957106403221 1117904552350919864362651)
                    ·
                      rfl

theorem cell22_3265667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 6].length) (baseStart_3265667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265667 prefixEnd_3265667 := by exact prefixLift 3265667
  have htrace : WordTrace (prefixWord ++ tailWord_3265667) baseStart_3265667 baseEnd_3265667 := by
    simpa [prefixWord, tailWord_3265667, baseEnd_3265667] using wordTrace_append hprefix tailTrace_3265667
  have hstable : (prefixWord ++ tailWord_3265667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265667).length < 2 ^ (prefixWord ++ tailWord_3265667).sum := by decide
  have hdescent : baseEnd_3265667 < baseStart_3265667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265703 : List Nat := [1, 1, 6, 2, 1, 2, 2, 1, 3, 3]
def baseStart_3265703 : Nat := 118140960795 + 3265703 * 2 ^ 59
def prefixEnd_3265703 : Nat := 4983230072969 + 3 ^ 40 * 3265703 * 2
def baseEnd_3265703 : Nat := 1117916875886627770462541

theorem tailTrace_3265703 : CollatzResearch.WordTrace tailWord_3265703 prefixEnd_3265703 1117916875886627770462541 := by
  unfold tailWord_3265703
  simp only [CollatzResearch.WordTrace]
  refine ⟨119109973687923243513745763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79406649125282162342497175 119109973687923243513745763)
  ·
    refine ⟨178664960531884865270618645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119109973687923243513745763 178664960531884865270618645)
    ·
      refine ⟨8374920024932103059560249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 178664960531884865270618645 8374920024932103059560249)
      ·
        refine ⟨6281190018699077294670187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8374920024932103059560249 6281190018699077294670187)
        ·
          refine ⟨9421785028048615942005281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6281190018699077294670187 9421785028048615942005281)
          ·
            refine ⟨7066338771036461956503961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9421785028048615942005281 7066338771036461956503961)
            ·
              refine ⟨5299754078277346467377971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7066338771036461956503961 5299754078277346467377971)
              ·
                refine ⟨7949631117416019701066957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5299754078277346467377971 7949631117416019701066957)
                ·
                  refine ⟨2981111669031007387900109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7949631117416019701066957 2981111669031007387900109)
                  ·
                    refine ⟨1117916875886627770462541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2981111669031007387900109 1117916875886627770462541)
                    ·
                      rfl

theorem cell22_3265703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_3265703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265703 prefixEnd_3265703 := by exact prefixLift 3265703
  have htrace : WordTrace (prefixWord ++ tailWord_3265703) baseStart_3265703 baseEnd_3265703 := by
    simpa [prefixWord, tailWord_3265703, baseEnd_3265703] using wordTrace_append hprefix tailTrace_3265703
  have hstable : (prefixWord ++ tailWord_3265703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265703).length < 2 ^ (prefixWord ++ tailWord_3265703).sum := by decide
  have hdescent : baseEnd_3265703 < baseStart_3265703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265714 : List Nat := [3, 2, 1, 1, 1, 4, 2, 1, 2, 5]
def baseStart_3265714 : Nat := 118140960795 + 3265714 * 2 ^ 59
def prefixEnd_3265714 : Nat := 4983230072969 + 3 ^ 40 * 3265714 * 2
def baseEnd_3265714 : Nat := 1117920641411427408437507

theorem tailTrace_3265714 : CollatzResearch.WordTrace tailWord_3265714 prefixEnd_3265714 1117920641411427408437507 := by
  unfold tailWord_3265714
  simp only [CollatzResearch.WordTrace]
  refine ⟨29777593722720848098099049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79406916593922261594930797 29777593722720848098099049)
  ·
    refine ⟨22333195292040636073574287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29777593722720848098099049 22333195292040636073574287)
    ·
      refine ⟨33499792938060954110361431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22333195292040636073574287 33499792938060954110361431)
      ·
        refine ⟨50249689407091431165542147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33499792938060954110361431 50249689407091431165542147)
        ·
          refine ⟨75374534110637146748313221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50249689407091431165542147 75374534110637146748313221)
          ·
            refine ⟨14132725145744465015308729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75374534110637146748313221 14132725145744465015308729)
            ·
              refine ⟨10599543859308348761481547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14132725145744465015308729 10599543859308348761481547)
              ·
                refine ⟨15899315788962523142222321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10599543859308348761481547 15899315788962523142222321)
                ·
                  refine ⟨11924486841721892356666741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15899315788962523142222321 11924486841721892356666741)
                  ·
                    refine ⟨1117920641411427408437507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11924486841721892356666741 1117920641411427408437507)
                    ·
                      rfl

theorem cell22_3265714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_3265714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265714 prefixEnd_3265714 := by exact prefixLift 3265714
  have htrace : WordTrace (prefixWord ++ tailWord_3265714) baseStart_3265714 baseEnd_3265714 := by
    simpa [prefixWord, tailWord_3265714, baseEnd_3265714] using wordTrace_append hprefix tailTrace_3265714
  have hstable : (prefixWord ++ tailWord_3265714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265714).length < 2 ^ (prefixWord ++ tailWord_3265714).sum := by decide
  have hdescent : baseEnd_3265714 < baseStart_3265714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265746 : List Nat := [3, 2, 2, 2, 1, 1, 1, 5, 1, 4]
def baseStart_3265746 : Nat := 118140960795 + 3265746 * 2 ^ 59
def prefixEnd_3265746 : Nat := 4983230072969 + 3 ^ 40 * 3265746 * 2
def baseEnd_3265746 : Nat := 1117931595665389991637409

theorem tailTrace_3265746 : CollatzResearch.WordTrace tailWord_3265746 prefixEnd_3265746 1117931595665389991637409 := by
  unfold tailWord_3265746
  simp only [CollatzResearch.WordTrace]
  refine ⟨29777885506691865464390273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79407694684511641238374061 29777885506691865464390273)
  ·
    refine ⟨22333414130018899098292705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29777885506691865464390273 22333414130018899098292705)
    ·
      refine ⟨16750060597514174323719529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22333414130018899098292705 16750060597514174323719529)
      ·
        refine ⟨12562545448135630742789647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16750060597514174323719529 12562545448135630742789647)
        ·
          refine ⟨18843818172203446114184471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12562545448135630742789647 18843818172203446114184471)
          ·
            refine ⟨28265727258305169171276707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18843818172203446114184471 28265727258305169171276707)
            ·
              refine ⟨42398590887457753756915061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28265727258305169171276707 42398590887457753756915061)
              ·
                refine ⟨3974867895699164414710787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42398590887457753756915061 3974867895699164414710787)
                ·
                  refine ⟨5962301843548746622066181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3974867895699164414710787 5962301843548746622066181)
                  ·
                    refine ⟨1117931595665389991637409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5962301843548746622066181 1117931595665389991637409)
                    ·
                      rfl

theorem cell22_3265746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_3265746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265746 prefixEnd_3265746 := by exact prefixLift 3265746
  have htrace : WordTrace (prefixWord ++ tailWord_3265746) baseStart_3265746 baseEnd_3265746 := by
    simpa [prefixWord, tailWord_3265746, baseEnd_3265746] using wordTrace_append hprefix tailTrace_3265746
  have hstable : (prefixWord ++ tailWord_3265746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265746).length < 2 ^ (prefixWord ++ tailWord_3265746).sum := by decide
  have hdescent : baseEnd_3265746 < baseStart_3265746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265761 : List Nat := [1, 2, 3, 1, 3, 4, 1, 1, 6]
def baseStart_3265761 : Nat := 118140960795 + 3265761 * 2 ^ 59
def prefixEnd_3265761 : Nat := 4983230072969 + 3 ^ 40 * 3265761 * 2
def baseEnd_3265761 : Nat := 372645576823978317504121

theorem tailTrace_3265761 : CollatzResearch.WordTrace tailWord_3265761 prefixEnd_3265761 372645576823978317504121 := by
  unfold tailWord_3265761
  simp only [CollatzResearch.WordTrace]
  refine ⟨119112089121713119419357137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79408059414475412946238091 119112089121713119419357137)
  ·
    refine ⟨89334066841284839564517853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119112089121713119419357137 89334066841284839564517853)
    ·
      refine ⟨33500275065481814836694195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89334066841284839564517853 33500275065481814836694195)
      ·
        refine ⟨50250412598222722255041293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33500275065481814836694195 50250412598222722255041293)
        ·
          refine ⟨18843904724333520845640485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50250412598222722255041293 18843904724333520845640485)
          ·
            refine ⟨3533232135812535158557591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18843904724333520845640485 3533232135812535158557591)
            ·
              refine ⟨5299848203718802737836387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3533232135812535158557591 5299848203718802737836387)
              ·
                refine ⟨7949772305578204106754581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5299848203718802737836387 7949772305578204106754581)
                ·
                  refine ⟨372645576823978317504121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7949772305578204106754581 372645576823978317504121)
                  ·
                    rfl

theorem cell22_3265761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 4, 1, 1, 6].length) (baseStart_3265761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265761 prefixEnd_3265761 := by exact prefixLift 3265761
  have htrace : WordTrace (prefixWord ++ tailWord_3265761) baseStart_3265761 baseEnd_3265761 := by
    simpa [prefixWord, tailWord_3265761, baseEnd_3265761] using wordTrace_append hprefix tailTrace_3265761
  have hstable : (prefixWord ++ tailWord_3265761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265761).length < 2 ^ (prefixWord ++ tailWord_3265761).sum := by decide
  have hdescent : baseEnd_3265761 < baseStart_3265761 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265774 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 3, 6]
def baseStart_3265774 : Nat := 118140960795 + 3265774 * 2 ^ 59
def prefixEnd_3265774 : Nat := 4983230072969 + 3 ^ 40 * 3265774 * 2
def baseEnd_3265774 : Nat := 1117941180637607251937323

theorem tailTrace_3265774 : CollatzResearch.WordTrace tailWord_3265774 prefixEnd_3265774 1117941180637607251937323 := by
  unfold tailWord_3265774
  simp only [CollatzResearch.WordTrace]
  refine ⟨14889070408833252829947547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79408375513777348426386917 14889070408833252829947547)
  ·
    refine ⟨22333605613249879244921321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14889070408833252829947547 22333605613249879244921321)
    ·
      refine ⟨16750204209937409433690991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22333605613249879244921321 16750204209937409433690991)
      ·
        refine ⟨25125306314906114150536487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16750204209937409433690991 25125306314906114150536487)
        ·
          refine ⟨37687959472359171225804731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25125306314906114150536487 37687959472359171225804731)
          ·
            refine ⟨56531939208538756838707097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37687959472359171225804731 56531939208538756838707097)
            ·
              refine ⟨42398954406404067629030323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56531939208538756838707097 42398954406404067629030323)
              ·
                refine ⟨63598431609606101443545485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42398954406404067629030323 63598431609606101443545485)
                ·
                  refine ⟨23849411853602288041329557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63598431609606101443545485 23849411853602288041329557)
                  ·
                    refine ⟨1117941180637607251937323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23849411853602288041329557 1117941180637607251937323)
                    ·
                      rfl

theorem cell22_3265774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_3265774 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265774 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265774 prefixEnd_3265774 := by exact prefixLift 3265774
  have htrace : WordTrace (prefixWord ++ tailWord_3265774) baseStart_3265774 baseEnd_3265774 := by
    simpa [prefixWord, tailWord_3265774, baseEnd_3265774] using wordTrace_append hprefix tailTrace_3265774
  have hstable : (prefixWord ++ tailWord_3265774).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265774).length < 2 ^ (prefixWord ++ tailWord_3265774).sum := by decide
  have hdescent : baseEnd_3265774 < baseStart_3265774 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265791 : List Nat := [1, 1, 2, 2, 1, 6, 2, 1, 2, 4]
def baseStart_3265791 : Nat := 118140960795 + 3265791 * 2 ^ 59
def prefixEnd_3265791 : Nat := 4983230072969 + 3 ^ 40 * 3265791 * 2
def baseEnd_3265791 : Nat := 1117947000085024874262271

theorem tailTrace_3265791 : CollatzResearch.WordTrace tailWord_3265791 prefixEnd_3265791 1117947000085024874262271 := by
  unfold tailWord_3265791
  simp only [CollatzResearch.WordTrace]
  refine ⟨119113183311604434542949227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79408788874402956361966151 119113183311604434542949227)
  ·
    refine ⟨178669774967406651814423841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119113183311604434542949227 178669774967406651814423841)
    ·
      refine ⟨134002331225554988860817881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178669774967406651814423841 134002331225554988860817881)
      ·
        refine ⟨100501748419166241645613411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134002331225554988860817881 100501748419166241645613411)
        ·
          refine ⟨150752622628749362468420117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100501748419166241645613411 150752622628749362468420117)
          ·
            refine ⟨7066529185722626365707193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 150752622628749362468420117 7066529185722626365707193)
            ·
              refine ⟨5299896889291969774280395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7066529185722626365707193 5299896889291969774280395)
              ·
                refine ⟨7949845333937954661420593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5299896889291969774280395 7949845333937954661420593)
                ·
                  refine ⟨5962384000453465996065445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7949845333937954661420593 5962384000453465996065445)
                  ·
                    refine ⟨1117947000085024874262271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5962384000453465996065445 1117947000085024874262271)
                    ·
                      rfl

theorem cell22_3265791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 2, 4].length) (baseStart_3265791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265791 prefixEnd_3265791 := by exact prefixLift 3265791
  have htrace : WordTrace (prefixWord ++ tailWord_3265791) baseStart_3265791 baseEnd_3265791 := by
    simpa [prefixWord, tailWord_3265791, baseEnd_3265791] using wordTrace_append hprefix tailTrace_3265791
  have hstable : (prefixWord ++ tailWord_3265791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265791).length < 2 ^ (prefixWord ++ tailWord_3265791).sum := by decide
  have hdescent : baseEnd_3265791 < baseStart_3265791 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265823 : List Nat := [1, 1, 2, 4, 5, 1, 1, 7]
def baseStart_3265823 : Nat := 118140960795 + 3265823 * 2 ^ 59
def prefixEnd_3265823 : Nat := 4983230072969 + 3 ^ 40 * 3265823 * 2
def baseEnd_3265823 : Nat := 124217550482109717495797

theorem tailTrace_3265823 : CollatzResearch.WordTrace tailWord_3265823 prefixEnd_3265823 124217550482109717495797 := by
  unfold tailWord_3265823
  simp only [CollatzResearch.WordTrace]
  refine ⟨119114350447488504008114123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79409566964992336005409415 119114350447488504008114123)
  ·
    refine ⟨178671525671232756012171185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119114350447488504008114123 178671525671232756012171185)
    ·
      refine ⟨134003644253424567009128389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178671525671232756012171185 134003644253424567009128389)
      ·
        refine ⟨25125683297517106314211573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134003644253424567009128389 25125683297517106314211573)
        ·
          refine ⟨2355532809142228716957335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25125683297517106314211573 2355532809142228716957335)
          ·
            refine ⟨3533299213713343075436003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2355532809142228716957335 3533299213713343075436003)
            ·
              refine ⟨5299948820570014613154005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3533299213713343075436003 5299948820570014613154005)
              ·
                refine ⟨124217550482109717495797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5299948820570014613154005 124217550482109717495797)
                ·
                  rfl

theorem cell22_3265823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 7].length) (baseStart_3265823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265823 prefixEnd_3265823 := by exact prefixLift 3265823
  have htrace : WordTrace (prefixWord ++ tailWord_3265823) baseStart_3265823 baseEnd_3265823 := by
    simpa [prefixWord, tailWord_3265823, baseEnd_3265823] using wordTrace_append hprefix tailTrace_3265823
  have hstable : (prefixWord ++ tailWord_3265823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265823).length < 2 ^ (prefixWord ++ tailWord_3265823).sum := by decide
  have hdescent : baseEnd_3265823 < baseStart_3265823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265855 : List Nat := [1, 1, 2, 2, 4, 3, 2, 3, 1, 3]
def baseStart_3265855 : Nat := 118140960795 + 3265855 * 2 ^ 59
def prefixEnd_3265855 : Nat := 4983230072969 + 3 ^ 40 * 3265855 * 2
def baseEnd_3265855 : Nat := 1117968908592950040662075

theorem tailTrace_3265855 : CollatzResearch.WordTrace tailWord_3265855 prefixEnd_3265855 1117968908592950040662075 := by
  unfold tailWord_3265855
  simp only [CollatzResearch.WordTrace]
  refine ⟨119115517583372573473279019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79410345055581715648852679 119115517583372573473279019)
  ·
    refine ⟨178673276375058860209918529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119115517583372573473279019 178673276375058860209918529)
    ·
      refine ⟨134004957281294145157438897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178673276375058860209918529 134004957281294145157438897)
      ·
        refine ⟨100503717960970608868079173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134004957281294145157438897 100503717960970608868079173)
        ·
          refine ⟨18844447117681989162764845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100503717960970608868079173 18844447117681989162764845)
          ·
            refine ⟨7066667669130745936036817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18844447117681989162764845 7066667669130745936036817)
            ·
              refine ⟨5300000751848059452027613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7066667669130745936036817 5300000751848059452027613)
              ·
                refine ⟨1987500281943022294510355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5300000751848059452027613 1987500281943022294510355)
                ·
                  refine ⟨2981250422914533441765533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1987500281943022294510355 2981250422914533441765533)
                  ·
                    refine ⟨1117968908592950040662075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2981250422914533441765533 1117968908592950040662075)
                    ·
                      rfl

theorem cell22_3265855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 3, 1, 3].length) (baseStart_3265855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265855 prefixEnd_3265855 := by exact prefixLift 3265855
  have htrace : WordTrace (prefixWord ++ tailWord_3265855) baseStart_3265855 baseEnd_3265855 := by
    simpa [prefixWord, tailWord_3265855, baseEnd_3265855] using wordTrace_append hprefix tailTrace_3265855
  have hstable : (prefixWord ++ tailWord_3265855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265855).length < 2 ^ (prefixWord ++ tailWord_3265855).sum := by decide
  have hdescent : baseEnd_3265855 < baseStart_3265855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265868 : List Nat := [2, 2, 1, 3, 2, 4, 1, 2, 5]
def baseStart_3265868 : Nat := 118140960795 + 3265868 * 2 ^ 59
def prefixEnd_3265868 : Nat := 4983230072969 + 3 ^ 40 * 3265868 * 2
def baseEnd_3265868 : Nat := 372657786252874113362345

theorem tailTrace_3265868 : CollatzResearch.WordTrace tailWord_3265868 prefixEnd_3265868 372657786252874113362345 := by
  unfold tailWord_3265868
  simp only [CollatzResearch.WordTrace]
  refine ⟨59557995866162738346751129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79410661154883651129001505 59557995866162738346751129)
  ·
    refine ⟨44668496899622053760063347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59557995866162738346751129 44668496899622053760063347)
    ·
      refine ⟨67002745349433080640095021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44668496899622053760063347 67002745349433080640095021)
      ·
        refine ⟨25126029506037405240035633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67002745349433080640095021 25126029506037405240035633)
        ·
          refine ⟨18844522129528053930026725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25126029506037405240035633 18844522129528053930026725)
          ·
            refine ⟨3533347899286510111880011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18844522129528053930026725 3533347899286510111880011)
            ·
              refine ⟨5300021848929765167820017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3533347899286510111880011 5300021848929765167820017)
              ·
                refine ⟨3975016386697323875865013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5300021848929765167820017 3975016386697323875865013)
                ·
                  refine ⟨372657786252874113362345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3975016386697323875865013 372657786252874113362345)
                  ·
                    rfl

theorem cell22_3265868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 2, 5].length) (baseStart_3265868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265868 prefixEnd_3265868 := by exact prefixLift 3265868
  have htrace : WordTrace (prefixWord ++ tailWord_3265868) baseStart_3265868 baseEnd_3265868 := by
    simpa [prefixWord, tailWord_3265868, baseEnd_3265868] using wordTrace_append hprefix tailTrace_3265868
  have hstable : (prefixWord ++ tailWord_3265868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265868).length < 2 ^ (prefixWord ++ tailWord_3265868).sum := by decide
  have hdescent : baseEnd_3265868 < baseStart_3265868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265911 : List Nat := [1, 1, 3, 1, 1, 2, 3, 1, 6, 3]
def baseStart_3265911 : Nat := 118140960795 + 3265911 * 2 ^ 59
def prefixEnd_3265911 : Nat := 4983230072969 + 3 ^ 40 * 3265911 * 2
def baseEnd_3265911 : Nat := 1117988078537384561261903

theorem tailTrace_3265911 : CollatzResearch.WordTrace tailWord_3265911 prefixEnd_3265911 1117988078537384561261903 := by
  unfold tailWord_3265911
  simp only [CollatzResearch.WordTrace]
  refine ⟨119117560071169695037317587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79411706714113130024878391 119117560071169695037317587)
  ·
    refine ⟨178676340106754542555976381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119117560071169695037317587 178676340106754542555976381)
    ·
      refine ⟨67003627540032953458491143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178676340106754542555976381 67003627540032953458491143)
      ·
        refine ⟨100505441310049430187736715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67003627540032953458491143 100505441310049430187736715)
        ·
          refine ⟨150758161965074145281605073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100505441310049430187736715 150758161965074145281605073)
          ·
            refine ⟨113068621473805608961203805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 150758161965074145281605073 113068621473805608961203805)
            ·
              refine ⟨42400733052677103360451427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113068621473805608961203805 42400733052677103360451427)
              ·
                refine ⟨63601099579015655040677141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42400733052677103360451427 63601099579015655040677141)
                ·
                  refine ⟨2981301542766358830031741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63601099579015655040677141 2981301542766358830031741)
                  ·
                    refine ⟨1117988078537384561261903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2981301542766358830031741 1117988078537384561261903)
                    ·
                      rfl

theorem cell22_3265911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 1, 6, 3].length) (baseStart_3265911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265911 prefixEnd_3265911 := by exact prefixLift 3265911
  have htrace : WordTrace (prefixWord ++ tailWord_3265911) baseStart_3265911 baseEnd_3265911 := by
    simpa [prefixWord, tailWord_3265911, baseEnd_3265911] using wordTrace_append hprefix tailTrace_3265911
  have hstable : (prefixWord ++ tailWord_3265911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265911).length < 2 ^ (prefixWord ++ tailWord_3265911).sum := by decide
  have hdescent : baseEnd_3265911 < baseStart_3265911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265913 : List Nat := [1, 2, 1, 3, 2, 1, 5, 3, 4]
def baseStart_3265913 : Nat := 118140960795 + 3265913 * 2 ^ 59
def prefixEnd_3265913 : Nat := 4983230072969 + 3 ^ 40 * 3265913 * 2
def baseEnd_3265913 : Nat := 372662921059419074237299

theorem tailTrace_3265913 : CollatzResearch.WordTrace tailWord_3265913 prefixEnd_3265913 372662921059419074237299 := by
  unfold tailWord_3265913
  simp only [CollatzResearch.WordTrace]
  refine ⟨119117633017162449378890393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79411755344774966252593595 119117633017162449378890393)
  ·
    refine ⟨89338224762871837034167795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119117633017162449378890393 89338224762871837034167795)
    ·
      refine ⟨134007337144307755551251693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89338224762871837034167795 134007337144307755551251693)
      ·
        refine ⟨50252751429115408331719385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134007337144307755551251693 50252751429115408331719385)
        ·
          refine ⟨37689563571836556248789539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50252751429115408331719385 37689563571836556248789539)
          ·
            refine ⟨56534345357754834373184309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37689563571836556248789539 56534345357754834373184309)
            ·
              refine ⟨5300094877289515722486029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56534345357754834373184309 5300094877289515722486029)
              ·
                refine ⟨1987535578983568395932261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5300094877289515722486029 1987535578983568395932261)
                ·
                  refine ⟨372662921059419074237299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1987535578983568395932261 372662921059419074237299)
                  ·
                    rfl

theorem cell22_3265913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 3, 4].length) (baseStart_3265913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265913 prefixEnd_3265913 := by exact prefixLift 3265913
  have htrace : WordTrace (prefixWord ++ tailWord_3265913) baseStart_3265913 baseEnd_3265913 := by
    simpa [prefixWord, tailWord_3265913, baseEnd_3265913] using wordTrace_append hprefix tailTrace_3265913
  have hstable : (prefixWord ++ tailWord_3265913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265913).length < 2 ^ (prefixWord ++ tailWord_3265913).sum := by decide
  have hdescent : baseEnd_3265913 < baseStart_3265913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265928 : List Nat := [2, 1, 3, 3, 1, 2, 2, 1, 4, 3]
def baseStart_3265928 : Nat := 118140960795 + 3265928 * 2 ^ 59
def prefixEnd_3265928 : Nat := 4983230072969 + 3 ^ 40 * 3265928 * 2
def baseEnd_3265928 : Nat := 1117993897984802183586851

theorem tailTrace_3265928 : CollatzResearch.WordTrace tailWord_3265928 prefixEnd_3265928 1117993897984802183586851 := by
  unfold tailWord_3265928
  simp only [CollatzResearch.WordTrace]
  refine ⟨59559090056054053470343219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79412120074738737960457625 59559090056054053470343219)
  ·
    refine ⟨89338635084081080205514829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59559090056054053470343219 89338635084081080205514829)
    ·
      refine ⟨33501988156530405077068061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89338635084081080205514829 33501988156530405077068061)
      ·
        refine ⟨12563245558698901903900523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33501988156530405077068061 12563245558698901903900523)
        ·
          refine ⟨18844868338048352855850785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12563245558698901903900523 18844868338048352855850785)
          ·
            refine ⟨14133651253536264641888089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18844868338048352855850785 14133651253536264641888089)
            ·
              refine ⟨10600238440152198481416067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14133651253536264641888089 10600238440152198481416067)
              ·
                refine ⟨15900357660228297722124101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10600238440152198481416067 15900357660228297722124101)
                ·
                  refine ⟨2981317061292805822898269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15900357660228297722124101 2981317061292805822898269)
                  ·
                    refine ⟨1117993897984802183586851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2981317061292805822898269 1117993897984802183586851)
                    ·
                      rfl

theorem cell22_3265928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 1, 4, 3].length) (baseStart_3265928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265928 prefixEnd_3265928 := by exact prefixLift 3265928
  have htrace : WordTrace (prefixWord ++ tailWord_3265928) baseStart_3265928 baseEnd_3265928 := by
    simpa [prefixWord, tailWord_3265928, baseEnd_3265928] using wordTrace_append hprefix tailTrace_3265928
  have hstable : (prefixWord ++ tailWord_3265928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265928).length < 2 ^ (prefixWord ++ tailWord_3265928).sum := by decide
  have hdescent : baseEnd_3265928 < baseStart_3265928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265945 : List Nat := [1, 2, 1, 2, 1, 5, 4, 1, 2, 3]
def baseStart_3265945 : Nat := 118140960795 + 3265945 * 2 ^ 59
def prefixEnd_3265945 : Nat := 4983230072969 + 3 ^ 40 * 3265945 * 2
def baseEnd_3265945 : Nat := 1117999717432219805911799

theorem tailTrace_3265945 : CollatzResearch.WordTrace tailWord_3265945 prefixEnd_3265945 1117999717432219805911799 := by
  unfold tailWord_3265945
  simp only [CollatzResearch.WordTrace]
  refine ⟨119118800153046518844055289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79412533435364345896036859 119118800153046518844055289)
  ·
    refine ⟨89339100114784889133041467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119118800153046518844055289 89339100114784889133041467)
    ·
      refine ⟨134008650172177333699562201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89339100114784889133041467 134008650172177333699562201)
      ·
        refine ⟨100506487629133000274671651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134008650172177333699562201 100506487629133000274671651)
        ·
          refine ⟨150759731443699500412007477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100506487629133000274671651 150759731443699500412007477)
          ·
            refine ⟨14133724822846828163625701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150759731443699500412007477 14133724822846828163625701)
            ·
              refine ⟨2650073404283780280679819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14133724822846828163625701 2650073404283780280679819)
              ·
                refine ⟨3975110106425670421019729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2650073404283780280679819 3975110106425670421019729)
                ·
                  refine ⟨2981332579819252815764797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3975110106425670421019729 2981332579819252815764797)
                  ·
                    refine ⟨1117999717432219805911799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2981332579819252815764797 1117999717432219805911799)
                    ·
                      rfl

theorem cell22_3265945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 4, 1, 2, 3].length) (baseStart_3265945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265945 prefixEnd_3265945 := by exact prefixLift 3265945
  have htrace : WordTrace (prefixWord ++ tailWord_3265945) baseStart_3265945 baseEnd_3265945 := by
    simpa [prefixWord, tailWord_3265945, baseEnd_3265945] using wordTrace_append hprefix tailTrace_3265945
  have hstable : (prefixWord ++ tailWord_3265945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265945).length < 2 ^ (prefixWord ++ tailWord_3265945).sum := by decide
  have hdescent : baseEnd_3265945 < baseStart_3265945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3265988 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 2, 6]
def baseStart_3265988 : Nat := 118140960795 + 3265988 * 2 ^ 59
def prefixEnd_3265988 : Nat := 4983230072969 + 3 ^ 40 * 3265988 * 2
def baseEnd_3265988 : Nat := 1118014437210982027086667

theorem tailTrace_3265988 : CollatzResearch.WordTrace tailWord_3265988 prefixEnd_3265988 1118014437210982027086667 := by
  unfold tailWord_3265988
  simp only [CollatzResearch.WordTrace]
  refine ⟨59560184245945368593935309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79413578994593824791913745 59560184245945368593935309)
  ·
    refine ⟨22335069092229513222725741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59560184245945368593935309 22335069092229513222725741)
    ·
      refine ⟨8375650909586067458522153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22335069092229513222725741 8375650909586067458522153)
      ·
        refine ⟨6281738182189550593891615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8375650909586067458522153 6281738182189550593891615)
        ·
          refine ⟨9422607273284325890837423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6281738182189550593891615 9422607273284325890837423)
          ·
            refine ⟨14133910909926488836256135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9422607273284325890837423 14133910909926488836256135)
            ·
              refine ⟨21200866364889733254384203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14133910909926488836256135 21200866364889733254384203)
              ·
                refine ⟨31801299547334599881576305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21200866364889733254384203 31801299547334599881576305)
                ·
                  refine ⟨23850974660500949911182229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31801299547334599881576305 23850974660500949911182229)
                  ·
                    refine ⟨1118014437210982027086667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23850974660500949911182229 1118014437210982027086667)
                    ·
                      rfl

theorem cell22_3265988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_3265988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3265988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3265988 prefixEnd_3265988 := by exact prefixLift 3265988
  have htrace : WordTrace (prefixWord ++ tailWord_3265988) baseStart_3265988 baseEnd_3265988 := by
    simpa [prefixWord, tailWord_3265988, baseEnd_3265988] using wordTrace_append hprefix tailTrace_3265988
  have hstable : (prefixWord ++ tailWord_3265988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3265988).length < 2 ^ (prefixWord ++ tailWord_3265988).sum := by decide
  have hdescent : baseEnd_3265988 < baseStart_3265988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3265988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266037 : List Nat := [1, 3, 5, 1, 1, 3, 1, 2, 5]
def baseStart_3266037 : Nat := 118140960795 + 3266037 * 2 ^ 59
def prefixEnd_3266037 : Nat := 4983230072969 + 3 ^ 40 * 3266037 * 2
def baseEnd_3266037 : Nat := 372677070304120744203839

theorem tailTrace_3266037 : CollatzResearch.WordTrace tailWord_3266037 prefixEnd_3266037 372677070304120744203839 := by
  unfold tailWord_3266037
  simp only [CollatzResearch.WordTrace]
  refine ⟨119122155668713218556404365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79414770445808812370936243 119122155668713218556404365)
  ·
    refine ⟨44670808375767456958651637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119122155668713218556404365 44670808375767456958651637)
    ·
      refine ⟨4187888285228199089873591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44670808375767456958651637 4187888285228199089873591)
      ·
        refine ⟨6281832427842298634810387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4187888285228199089873591 6281832427842298634810387)
        ·
          refine ⟨9422748641763447952215581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6281832427842298634810387 9422748641763447952215581)
          ·
            refine ⟨3533530740661292982080843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9422748641763447952215581 3533530740661292982080843)
            ·
              refine ⟨5300296110991939473121265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3533530740661292982080843 5300296110991939473121265)
              ·
                refine ⟨3975222083243954604840949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5300296110991939473121265 3975222083243954604840949)
                ·
                  refine ⟨372677070304120744203839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3975222083243954604840949 372677070304120744203839)
                  ·
                    rfl

theorem cell22_3266037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 2, 5].length) (baseStart_3266037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266037 prefixEnd_3266037 := by exact prefixLift 3266037
  have htrace : WordTrace (prefixWord ++ tailWord_3266037) baseStart_3266037 baseEnd_3266037 := by
    simpa [prefixWord, tailWord_3266037, baseEnd_3266037] using wordTrace_append hprefix tailTrace_3266037
  have hstable : (prefixWord ++ tailWord_3266037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266037).length < 2 ^ (prefixWord ++ tailWord_3266037).sum := by decide
  have hdescent : baseEnd_3266037 < baseStart_3266037 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266080 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 4, 3]
def baseStart_3266080 : Nat := 118140960795 + 3266080 * 2 ^ 59
def prefixEnd_3266080 : Nat := 4983230072969 + 3 ^ 40 * 3266080 * 2
def baseEnd_3266080 : Nat := 1118045930691124453786385

theorem tailTrace_3266080 : CollatzResearch.WordTrace tailWord_3266080 prefixEnd_3266080 1118045930691124453786385 := by
  unfold tailWord_3266080
  simp only [CollatzResearch.WordTrace]
  refine ⟨59561862003778718450109847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79415816005038291266813129 59561862003778718450109847)
  ·
    refine ⟨89342793005668077675164771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59561862003778718450109847 89342793005668077675164771)
    ·
      refine ⟨134014189508502116512747157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89342793005668077675164771 134014189508502116512747157)
      ·
        refine ⟨6281915133211036711535023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 134014189508502116512747157 6281915133211036711535023)
        ·
          refine ⟨9422872699816555067302535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6281915133211036711535023 9422872699816555067302535)
          ·
            refine ⟨14134309049724832600953803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9422872699816555067302535 14134309049724832600953803)
            ·
              refine ⟨21201463574587248901430705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14134309049724832600953803 21201463574587248901430705)
              ·
                refine ⟨15901097680940436676073029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21201463574587248901430705 15901097680940436676073029)
                ·
                  refine ⟨2981455815176331876763693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15901097680940436676073029 2981455815176331876763693)
                  ·
                    refine ⟨1118045930691124453786385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2981455815176331876763693 1118045930691124453786385)
                    ·
                      rfl

theorem cell22_3266080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 4, 3].length) (baseStart_3266080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266080 prefixEnd_3266080 := by exact prefixLift 3266080
  have htrace : WordTrace (prefixWord ++ tailWord_3266080) baseStart_3266080 baseEnd_3266080 := by
    simpa [prefixWord, tailWord_3266080, baseEnd_3266080] using wordTrace_append hprefix tailTrace_3266080
  have hstable : (prefixWord ++ tailWord_3266080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266080).length < 2 ^ (prefixWord ++ tailWord_3266080).sum := by decide
  have hdescent : baseEnd_3266080 < baseStart_3266080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266183 : List Nat := [1, 1, 4, 2, 1, 3, 1, 1, 8]
def baseStart_3266183 : Nat := 118140960795 + 3266183 * 2 ^ 59
def prefixEnd_3266183 : Nat := 4983230072969 + 3 ^ 40 * 3266183 * 2
def baseEnd_3266183 : Nat := 372693729898688839487023

theorem tailTrace_3266183 : CollatzResearch.WordTrace tailWord_3266183 prefixEnd_3266183 372693729898688839487023 := by
  unfold tailWord_3266183
  simp only [CollatzResearch.WordTrace]
  refine ⟨119127480726184285491219203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79418320484122856994146135 119127480726184285491219203)
  ·
    refine ⟨178691221089276428236828805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119127480726184285491219203 178691221089276428236828805)
    ·
      refine ⟨33504603954239330294405401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178691221089276428236828805 33504603954239330294405401)
      ·
        refine ⟨25128452965679497720804051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33504603954239330294405401 25128452965679497720804051)
        ·
          refine ⟨37692679448519246581206077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25128452965679497720804051 37692679448519246581206077)
          ·
            refine ⟨14134754793194717467952279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37692679448519246581206077 14134754793194717467952279)
            ·
              refine ⟨21202132189792076201928419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14134754793194717467952279 21202132189792076201928419)
              ·
                refine ⟨31803198284688114302892629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21202132189792076201928419 31803198284688114302892629)
                ·
                  refine ⟨372693729898688839487023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31803198284688114302892629 372693729898688839487023)
                  ·
                    rfl

theorem cell22_3266183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 1, 8].length) (baseStart_3266183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266183 prefixEnd_3266183 := by exact prefixLift 3266183
  have htrace : WordTrace (prefixWord ++ tailWord_3266183) baseStart_3266183 baseEnd_3266183 := by
    simpa [prefixWord, tailWord_3266183, baseEnd_3266183] using wordTrace_append hprefix tailTrace_3266183
  have hstable : (prefixWord ++ tailWord_3266183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266183).length < 2 ^ (prefixWord ++ tailWord_3266183).sum := by decide
  have hdescent : baseEnd_3266183 < baseStart_3266183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266335 : List Nat := [1, 1, 2, 4, 2, 1, 2, 3, 6]
def baseStart_3266335 : Nat := 118140960795 + 3266335 * 2 ^ 59
def prefixEnd_3266335 : Nat := 4983230072969 + 3 ^ 40 * 3266335 * 2
def baseEnd_3266335 : Nat := 372711074134129596220201

theorem tailTrace_3266335 : CollatzResearch.WordTrace tailWord_3266335 prefixEnd_3266335 372711074134129596220201 := by
  unfold tailWord_3266335
  simp only [CollatzResearch.WordTrace]
  refine ⟨119133024621633615450752459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79422016414422410300501639 119133024621633615450752459)
  ·
    refine ⟨178699536932450423176128689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119133024621633615450752459 178699536932450423176128689)
    ·
      refine ⟨134024652699337817382096517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178699536932450423176128689 134024652699337817382096517)
      ·
        refine ⟨25129622381125840759143097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134024652699337817382096517 25129622381125840759143097)
        ·
          refine ⟨18847216785844380569357323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25129622381125840759143097 18847216785844380569357323)
          ·
            refine ⟨28270825178766570854035985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18847216785844380569357323 28270825178766570854035985)
            ·
              refine ⟨21203118884074928140526989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28270825178766570854035985 21203118884074928140526989)
              ·
                refine ⟨7951169581528098052697621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21203118884074928140526989 7951169581528098052697621)
                ·
                  refine ⟨372711074134129596220201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7951169581528098052697621 372711074134129596220201)
                  ·
                    rfl

theorem cell22_3266335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 3, 6].length) (baseStart_3266335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266335 prefixEnd_3266335 := by exact prefixLift 3266335
  have htrace : WordTrace (prefixWord ++ tailWord_3266335) baseStart_3266335 baseEnd_3266335 := by
    simpa [prefixWord, tailWord_3266335, baseEnd_3266335] using wordTrace_append hprefix tailTrace_3266335
  have hstable : (prefixWord ++ tailWord_3266335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266335).length < 2 ^ (prefixWord ++ tailWord_3266335).sum := by decide
  have hdescent : baseEnd_3266335 < baseStart_3266335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266414 : List Nat := [4, 1, 2, 3, 1, 1, 4, 6]
def baseStart_3266414 : Nat := 118140960795 + 3266414 * 2 ^ 59
def prefixEnd_3266414 : Nat := 4983230072969 + 3 ^ 40 * 3266414 * 2
def baseEnd_3266414 : Nat := 124240029524095435103929

theorem tailTrace_3266414 : CollatzResearch.WordTrace tailWord_3266414 prefixEnd_3266414 124240029524095435103929 := by
  unfold tailWord_3266414
  simp only [CollatzResearch.WordTrace]
  refine ⟨14891988248543426492859787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79423937325564941295252197 14891988248543426492859787)
  ·
    refine ⟨22337982372815139739289681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14891988248543426492859787 22337982372815139739289681)
    ·
      refine ⟨16753486779611354804467261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22337982372815139739289681 16753486779611354804467261)
      ·
        refine ⟨6282557542354258051675223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16753486779611354804467261 6282557542354258051675223)
        ·
          refine ⟨9423836313531387077512835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6282557542354258051675223 9423836313531387077512835)
          ·
            refine ⟨14135754470297080616269253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9423836313531387077512835 14135754470297080616269253)
            ·
              refine ⟨2650453963180702615550485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14135754470297080616269253 2650453963180702615550485)
              ·
                refine ⟨124240029524095435103929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2650453963180702615550485 124240029524095435103929)
                ·
                  rfl

theorem cell22_3266414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 6].length) (baseStart_3266414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266414 prefixEnd_3266414 := by exact prefixLift 3266414
  have htrace : WordTrace (prefixWord ++ tailWord_3266414) baseStart_3266414 baseEnd_3266414 := by
    simpa [prefixWord, tailWord_3266414, baseEnd_3266414] using wordTrace_append hprefix tailTrace_3266414
  have hstable : (prefixWord ++ tailWord_3266414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266414).length < 2 ^ (prefixWord ++ tailWord_3266414).sum := by decide
  have hdescent : baseEnd_3266414 < baseStart_3266414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266425 : List Nat := [1, 2, 1, 3, 2, 2, 1, 1, 9]
def baseStart_3266425 : Nat := 118140960795 + 3266425 * 2 ^ 59
def prefixEnd_3266425 : Nat := 4983230072969 + 3 ^ 40 * 3266425 * 2
def baseEnd_3266425 : Nat := 372721343747219517970109

theorem tailTrace_3266425 : CollatzResearch.WordTrace tailWord_3266425 prefixEnd_3266425 372721343747219517970109 := by
  unfold tailWord_3266425
  simp only [CollatzResearch.WordTrace]
  refine ⟨119136307191307560821528729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79424204794205040547685819 119136307191307560821528729)
  ·
    refine ⟨89352230393480670616146547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119136307191307560821528729 89352230393480670616146547)
    ·
      refine ⟨134028345590221005924219821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89352230393480670616146547 134028345590221005924219821)
      ·
        refine ⟨50260629596332877221582433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134028345590221005924219821 50260629596332877221582433)
        ·
          refine ⟨37695472197249657916186825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50260629596332877221582433 37695472197249657916186825)
          ·
            refine ⟨28271604147937243437140119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37695472197249657916186825 28271604147937243437140119)
            ·
              refine ⟨42407406221905865155710179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28271604147937243437140119 42407406221905865155710179)
              ·
                refine ⟨63611109332858797733565269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42407406221905865155710179 63611109332858797733565269)
                ·
                  refine ⟨372721343747219517970109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63611109332858797733565269 372721343747219517970109)
                  ·
                    rfl

theorem cell22_3266425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 9].length) (baseStart_3266425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266425 prefixEnd_3266425 := by exact prefixLift 3266425
  have htrace : WordTrace (prefixWord ++ tailWord_3266425) baseStart_3266425 baseEnd_3266425 := by
    simpa [prefixWord, tailWord_3266425, baseEnd_3266425] using wordTrace_append hprefix tailTrace_3266425
  have hstable : (prefixWord ++ tailWord_3266425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266425).length < 2 ^ (prefixWord ++ tailWord_3266425).sum := by decide
  have hdescent : baseEnd_3266425 < baseStart_3266425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266519 : List Nat := [1, 1, 3, 2, 1, 1, 3, 5, 2, 3]
def baseStart_3266519 : Nat := 118140960795 + 3266519 * 2 ^ 59
def prefixEnd_3266519 : Nat := 4983230072969 + 3 ^ 40 * 3266519 * 2
def baseEnd_3266519 : Nat := 1118196209362673642060039

theorem tailTrace_3266519 : CollatzResearch.WordTrace tailWord_3266519 prefixEnd_3266519 1118196209362673642060039 := by
  unfold tailWord_3266519
  simp only [CollatzResearch.WordTrace]
  refine ⟨119139735652967014875450611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79426490435311343250300407 119139735652967014875450611)
  ·
    refine ⟨178709603479450522313175917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119139735652967014875450611 178709603479450522313175917)
    ·
      refine ⟨67016101304793945867440969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178709603479450522313175917 67016101304793945867440969)
      ·
        refine ⟨50262075978595459400580727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67016101304793945867440969 50262075978595459400580727)
        ·
          refine ⟨75393113967893189100871091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50262075978595459400580727 75393113967893189100871091)
          ·
            refine ⟨113089670951839783651306637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75393113967893189100871091 113089670951839783651306637)
            ·
              refine ⟨42408626606939918869239989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113089670951839783651306637 42408626606939918869239989)
              ·
                refine ⟨3975808744400617393991249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42408626606939918869239989 3975808744400617393991249)
                ·
                  refine ⟨2981856558300463045493437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3975808744400617393991249 2981856558300463045493437)
                  ·
                    refine ⟨1118196209362673642060039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2981856558300463045493437 1118196209362673642060039)
                    ·
                      rfl

theorem cell22_3266519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 5, 2, 3].length) (baseStart_3266519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266519 prefixEnd_3266519 := by exact prefixLift 3266519
  have htrace : WordTrace (prefixWord ++ tailWord_3266519) baseStart_3266519 baseEnd_3266519 := by
    simpa [prefixWord, tailWord_3266519, baseEnd_3266519] using wordTrace_append hprefix tailTrace_3266519
  have hstable : (prefixWord ++ tailWord_3266519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266519).length < 2 ^ (prefixWord ++ tailWord_3266519).sum := by decide
  have hdescent : baseEnd_3266519 < baseStart_3266519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266583 : List Nat := [1, 1, 3, 5, 3, 1, 2, 6]
def baseStart_3266583 : Nat := 118140960795 + 3266583 * 2 ^ 59
def prefixEnd_3266583 : Nat := 4983230072969 + 3 ^ 40 * 3266583 * 2
def baseEnd_3266583 : Nat := 124246457541177645384427

theorem tailTrace_3266583 : CollatzResearch.WordTrace tailWord_3266583 prefixEnd_3266583 124246457541177645384427 := by
  unfold tailWord_3266583
  simp only [CollatzResearch.WordTrace]
  refine ⟨119142069924735153805780403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79428046616490102537186935 119142069924735153805780403)
  ·
    refine ⟨178713104887102730708670605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119142069924735153805780403 178713104887102730708670605)
    ·
      refine ⟨67017414332663524015751477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178713104887102730708670605 67017414332663524015751477)
      ·
        refine ⟨6282882593687205376476701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67017414332663524015751477 6282882593687205376476701)
        ·
          refine ⟨2356080972632702016178763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6282882593687205376476701 2356080972632702016178763)
          ·
            refine ⟨3534121458949053024268145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2356080972632702016178763 3534121458949053024268145)
            ·
              refine ⟨2650591094211789768201109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3534121458949053024268145 2650591094211789768201109)
              ·
                refine ⟨124246457541177645384427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2650591094211789768201109 124246457541177645384427)
                ·
                  rfl

theorem cell22_3266583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 6].length) (baseStart_3266583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266583 prefixEnd_3266583 := by exact prefixLift 3266583
  have htrace : WordTrace (prefixWord ++ tailWord_3266583) baseStart_3266583 baseEnd_3266583 := by
    simpa [prefixWord, tailWord_3266583, baseEnd_3266583] using wordTrace_append hprefix tailTrace_3266583
  have hstable : (prefixWord ++ tailWord_3266583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266583).length < 2 ^ (prefixWord ++ tailWord_3266583).sum := by decide
  have hdescent : baseEnd_3266583 < baseStart_3266583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266671 : List Nat := [1, 1, 2, 1, 3, 4, 1, 4, 2, 3]
def baseStart_3266671 : Nat := 118140960795 + 3266671 * 2 ^ 59
def prefixEnd_3266671 : Nat := 4983230072969 + 3 ^ 40 * 3266671 * 2
def baseEnd_3266671 : Nat := 1118248242068995912259573

theorem tailTrace_3266671 : CollatzResearch.WordTrace tailWord_3266671 prefixEnd_3266671 1118248242068995912259573 := by
  unfold tailWord_3266671
  simp only [CollatzResearch.WordTrace]
  refine ⟨119145279548416344834983867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79430186365610896556655911 119145279548416344834983867)
  ·
    refine ⟨178717919322624517252475801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119145279548416344834983867 178717919322624517252475801)
    ·
      refine ⟨134038439491968387939356851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178717919322624517252475801 134038439491968387939356851)
      ·
        refine ⟨201057659237952581909035277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134038439491968387939356851 201057659237952581909035277)
        ·
          refine ⟨75396622214232218215888229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201057659237952581909035277 75396622214232218215888229)
          ·
            refine ⟨14136866665168540915479043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75396622214232218215888229 14136866665168540915479043)
            ·
              refine ⟨21205299997752811373218565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14136866665168540915479043 21205299997752811373218565)
              ·
                refine ⟨3975993749578652132478481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21205299997752811373218565 3975993749578652132478481)
                ·
                  refine ⟨2981995312183989099358861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3975993749578652132478481 2981995312183989099358861)
                  ·
                    refine ⟨1118248242068995912259573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2981995312183989099358861 1118248242068995912259573)
                    ·
                      rfl

theorem cell22_3266671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 4, 2, 3].length) (baseStart_3266671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266671 prefixEnd_3266671 := by exact prefixLift 3266671
  have htrace : WordTrace (prefixWord ++ tailWord_3266671) baseStart_3266671 baseEnd_3266671 := by
    simpa [prefixWord, tailWord_3266671, baseEnd_3266671] using wordTrace_append hprefix tailTrace_3266671
  have hstable : (prefixWord ++ tailWord_3266671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266671).length < 2 ^ (prefixWord ++ tailWord_3266671).sum := by decide
  have hdescent : baseEnd_3266671 < baseStart_3266671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266684 : List Nat := [2, 2, 2, 1, 1, 4, 3, 7]
def baseStart_3266684 : Nat := 118140960795 + 3266684 * 2 ^ 59
def prefixEnd_3266684 : Nat := 4983230072969 + 3 ^ 40 * 3266684 * 2
def baseEnd_3266684 : Nat := 124250299137185356853837

theorem tailTrace_3266684 : CollatzResearch.WordTrace tailWord_3266684 prefixEnd_3266684 124250299137185356853837 := by
  unfold tailWord_3266684
  simp only [CollatzResearch.WordTrace]
  refine ⟨59572876848684624027603553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79430502464912832036804737 59572876848684624027603553)
  ·
    refine ⟨44679657636513468020702665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59572876848684624027603553 44679657636513468020702665)
    ·
      refine ⟨33509743227385101015526999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44679657636513468020702665 33509743227385101015526999)
      ·
        refine ⟨50264614841077651523290499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33509743227385101015526999 50264614841077651523290499)
        ·
          refine ⟨75396922261616477284935749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50264614841077651523290499 75396922261616477284935749)
          ·
            refine ⟨14136922924053089490925453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75396922261616477284935749 14136922924053089490925453)
            ·
              refine ⟨5301346096519908559097045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14136922924053089490925453 5301346096519908559097045)
              ·
                refine ⟨124250299137185356853837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5301346096519908559097045 124250299137185356853837)
                ·
                  rfl

theorem cell22_3266684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 7].length) (baseStart_3266684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266684 prefixEnd_3266684 := by exact prefixLift 3266684
  have htrace : WordTrace (prefixWord ++ tailWord_3266684) baseStart_3266684 baseEnd_3266684 := by
    simpa [prefixWord, tailWord_3266684, baseEnd_3266684] using wordTrace_append hprefix tailTrace_3266684
  have hstable : (prefixWord ++ tailWord_3266684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266684).length < 2 ^ (prefixWord ++ tailWord_3266684).sum := by decide
  have hdescent : baseEnd_3266684 < baseStart_3266684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266716 : List Nat := [2, 2, 3, 2, 1, 1, 1, 2, 5, 3]
def baseStart_3266716 : Nat := 118140960795 + 3266716 * 2 ^ 59
def prefixEnd_3266716 : Nat := 4983230072969 + 3 ^ 40 * 3266716 * 2
def baseEnd_3266716 : Nat := 1118263646488630794884435

theorem tailTrace_3266716 : CollatzResearch.WordTrace tailWord_3266716 prefixEnd_3266716 1118263646488630794884435 := by
  unfold tailWord_3266716
  simp only [CollatzResearch.WordTrace]
  refine ⟨59573460416626658760186001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79431280555502211680248001 59573460416626658760186001)
  ·
    refine ⟨44680095312469994070139501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59573460416626658760186001 44680095312469994070139501)
    ·
      refine ⟨16755035742176247776302313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44680095312469994070139501 16755035742176247776302313)
      ·
        refine ⟨12566276806632185832226735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16755035742176247776302313 12566276806632185832226735)
        ·
          refine ⟨18849415209948278748340103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12566276806632185832226735 18849415209948278748340103)
          ·
            refine ⟨28274122814922418122510155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18849415209948278748340103 28274122814922418122510155)
            ·
              refine ⟨42411184222383627183765233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28274122814922418122510155 42411184222383627183765233)
              ·
                refine ⟨31808388166787720387823925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42411184222383627183765233 31808388166787720387823925)
                ·
                  refine ⟨2982036390636348786358493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31808388166787720387823925 2982036390636348786358493)
                  ·
                    refine ⟨1118263646488630794884435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2982036390636348786358493 1118263646488630794884435)
                    ·
                      rfl

theorem cell22_3266716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_3266716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266716 prefixEnd_3266716 := by exact prefixLift 3266716
  have htrace : WordTrace (prefixWord ++ tailWord_3266716) baseStart_3266716 baseEnd_3266716 := by
    simpa [prefixWord, tailWord_3266716, baseEnd_3266716] using wordTrace_append hprefix tailTrace_3266716
  have hstable : (prefixWord ++ tailWord_3266716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266716).length < 2 ^ (prefixWord ++ tailWord_3266716).sum := by decide
  have hdescent : baseEnd_3266716 < baseStart_3266716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266733 : List Nat := [1, 5, 2, 1, 2, 1, 1, 3, 3, 3]
def baseStart_3266733 : Nat := 118140960795 + 3266733 * 2 ^ 59
def prefixEnd_3266733 : Nat := 4983230072969 + 3 ^ 40 * 3266733 * 2
def baseEnd_3266733 : Nat := 1118269465936048417209383

theorem tailTrace_3266733 : CollatzResearch.WordTrace tailWord_3266733 prefixEnd_3266733 1118269465936048417209383 := by
  unfold tailWord_3266733
  simp only [CollatzResearch.WordTrace]
  refine ⟨119147540874191729423740853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79431693916127819615827235 119147540874191729423740853)
  ·
    refine ⟨11170081956955474633475705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119147540874191729423740853 11170081956955474633475705)
    ·
      refine ⟨8377561467716605975106779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11170081956955474633475705 8377561467716605975106779)
      ·
        refine ⟨12566342201574908962660169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8377561467716605975106779 12566342201574908962660169)
        ·
          refine ⟨9424756651181181721995127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12566342201574908962660169 9424756651181181721995127)
          ·
            refine ⟨14137134976771772582992691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9424756651181181721995127 14137134976771772582992691)
            ·
              refine ⟨21205702465157658874489037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14137134976771772582992691 21205702465157658874489037)
              ·
                refine ⟨7952138424434122077933389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21205702465157658874489037 7952138424434122077933389)
                ·
                  refine ⟨2982051909162795779225021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7952138424434122077933389 2982051909162795779225021)
                  ·
                    refine ⟨1118269465936048417209383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2982051909162795779225021 1118269465936048417209383)
                    ·
                      rfl

theorem cell22_3266733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_3266733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266733 prefixEnd_3266733 := by exact prefixLift 3266733
  have htrace : WordTrace (prefixWord ++ tailWord_3266733) baseStart_3266733 baseEnd_3266733 := by
    simpa [prefixWord, tailWord_3266733, baseEnd_3266733] using wordTrace_append hprefix tailTrace_3266733
  have hstable : (prefixWord ++ tailWord_3266733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266733).length < 2 ^ (prefixWord ++ tailWord_3266733).sum := by decide
  have hdescent : baseEnd_3266733 < baseStart_3266733 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266744 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 2, 5]
def baseStart_3266744 : Nat := 118140960795 + 3266744 * 2 ^ 59
def prefixEnd_3266744 : Nat := 4983230072969 + 3 ^ 40 * 3266744 * 2
def baseEnd_3266744 : Nat := 1118273231460848055184349

theorem tailTrace_3266744 : CollatzResearch.WordTrace tailWord_3266744 prefixEnd_3266744 1118273231460848055184349 := by
  unfold tailWord_3266744
  simp only [CollatzResearch.WordTrace]
  refine ⟨59573971038575939151195643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79431961384767918868260857 59573971038575939151195643)
  ·
    refine ⟨89360956557863908726793465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59573971038575939151195643 89360956557863908726793465)
    ·
      refine ⟨67020717418397931545095099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89360956557863908726793465 67020717418397931545095099)
      ·
        refine ⟨100531076127596897317642649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67020717418397931545095099 100531076127596897317642649)
        ·
          refine ⟨75398307095697672988231987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100531076127596897317642649 75398307095697672988231987)
          ·
            refine ⟨113097460643546509482347981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75398307095697672988231987 113097460643546509482347981)
            ·
              refine ⟨42411547741329941055880493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113097460643546509482347981 42411547741329941055880493)
              ·
                refine ⟨15904330402998727895955185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42411547741329941055880493 15904330402998727895955185)
                ·
                  refine ⟨11928247802249045921966389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15904330402998727895955185 11928247802249045921966389)
                  ·
                    refine ⟨1118273231460848055184349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11928247802249045921966389 1118273231460848055184349)
                    ·
                      rfl

theorem cell22_3266744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 2, 5].length) (baseStart_3266744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266744 prefixEnd_3266744 := by exact prefixLift 3266744
  have htrace : WordTrace (prefixWord ++ tailWord_3266744) baseStart_3266744 baseEnd_3266744 := by
    simpa [prefixWord, tailWord_3266744, baseEnd_3266744] using wordTrace_append hprefix tailTrace_3266744
  have hstable : (prefixWord ++ tailWord_3266744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266744).length < 2 ^ (prefixWord ++ tailWord_3266744).sum := by decide
  have hdescent : baseEnd_3266744 < baseStart_3266744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266797 : List Nat := [1, 5, 1, 2, 4, 1, 2, 1, 5]
def baseStart_3266797 : Nat := 118140960795 + 3266797 * 2 ^ 59
def prefixEnd_3266797 : Nat := 4983230072969 + 3 ^ 40 * 3266797 * 2
def baseEnd_3266797 : Nat := 372763791481324527869729

theorem tailTrace_3266797 : CollatzResearch.WordTrace tailWord_3266797 prefixEnd_3266797 372763791481324527869729 := by
  unfold tailWord_3266797
  simp only [CollatzResearch.WordTrace]
  refine ⟨119149875145959868354070645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79433250097306578902713763 119149875145959868354070645)
  ·
    refine ⟨11170300794933737658194123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119149875145959868354070645 11170300794933737658194123)
    ·
      refine ⟨16755451192400606487291185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11170300794933737658194123 16755451192400606487291185)
      ·
        refine ⟨12566588394300454865468389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16755451192400606487291185 12566588394300454865468389)
        ·
          refine ⟨2356235323931335287275323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12566588394300454865468389 2356235323931335287275323)
          ·
            refine ⟨3534352985897002930912985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2356235323931335287275323 3534352985897002930912985)
            ·
              refine ⟨2650764739422752198184739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3534352985897002930912985 2650764739422752198184739)
              ·
                refine ⟨3976147109134128297277109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2650764739422752198184739 3976147109134128297277109)
                ·
                  refine ⟨372763791481324527869729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3976147109134128297277109 372763791481324527869729)
                  ·
                    rfl

theorem cell22_3266797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 1, 5].length) (baseStart_3266797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266797 prefixEnd_3266797 := by exact prefixLift 3266797
  have htrace : WordTrace (prefixWord ++ tailWord_3266797) baseStart_3266797 baseEnd_3266797 := by
    simpa [prefixWord, tailWord_3266797, baseEnd_3266797] using wordTrace_append hprefix tailTrace_3266797
  have hstable : (prefixWord ++ tailWord_3266797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266797).length < 2 ^ (prefixWord ++ tailWord_3266797).sum := by decide
  have hdescent : baseEnd_3266797 < baseStart_3266797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266819 : List Nat := [1, 1, 1, 3, 2, 3, 1, 10]
def baseStart_3266819 : Nat := 118140960795 + 3266819 * 2 ^ 59
def prefixEnd_3266819 : Nat := 4983230072969 + 3 ^ 40 * 3266819 * 2
def baseEnd_3266819 : Nat := 124255433943730317728791

theorem tailTrace_3266819 : CollatzResearch.WordTrace tailWord_3266819 prefixEnd_3266819 124255433943730317728791 := by
  unfold tailWord_3266819
  simp only [CollatzResearch.WordTrace]
  refine ⟨119150677551880166111371511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79433785034586777407581007 119150677551880166111371511)
  ·
    refine ⟨178726016327820249167057267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119150677551880166111371511 178726016327820249167057267)
    ·
      refine ⟨268089024491730373750585901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178726016327820249167057267 268089024491730373750585901)
      ·
        refine ⟨100533384184398890156469713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268089024491730373750585901 100533384184398890156469713)
        ·
          refine ⟨75400038138299167617352285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100533384184398890156469713 75400038138299167617352285)
          ·
            refine ⟨28275014301862187856507107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75400038138299167617352285 28275014301862187856507107)
            ·
              refine ⟨42412521452793281784760661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28275014301862187856507107 42412521452793281784760661)
              ·
                refine ⟨124255433943730317728791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42412521452793281784760661 124255433943730317728791)
                ·
                  rfl

theorem cell22_3266819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 10].length) (baseStart_3266819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266819 prefixEnd_3266819 := by exact prefixLift 3266819
  have htrace : WordTrace (prefixWord ++ tailWord_3266819) baseStart_3266819 baseEnd_3266819 := by
    simpa [prefixWord, tailWord_3266819, baseEnd_3266819] using wordTrace_append hprefix tailTrace_3266819
  have hstable : (prefixWord ++ tailWord_3266819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266819).length < 2 ^ (prefixWord ++ tailWord_3266819).sum := by decide
  have hdescent : baseEnd_3266819 < baseStart_3266819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266842 : List Nat := [3, 1, 1, 3, 4, 2, 2, 2, 4]
def baseStart_3266842 : Nat := 118140960795 + 3266842 * 2 ^ 59
def prefixEnd_3266842 : Nat := 4983230072969 + 3 ^ 40 * 3266842 * 2
def baseEnd_3266842 : Nat := 372768926287869488744683

theorem tailTrace_3266842 : CollatzResearch.WordTrace tailWord_3266842 prefixEnd_3266842 372768926287869488744683 := by
  unfold tailWord_3266842
  simp only [CollatzResearch.WordTrace]
  refine ⟨29787879107699210259864695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79434344287197894026305853 29787879107699210259864695)
  ·
    refine ⟨44681818661548815389797043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29787879107699210259864695 44681818661548815389797043)
    ·
      refine ⟨67022727992323223084695565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44681818661548815389797043 67022727992323223084695565)
      ·
        refine ⟨25133522997121208656760837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67022727992323223084695565 25133522997121208656760837)
        ·
          refine ⟨4712535561960226623142657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25133522997121208656760837 4712535561960226623142657)
          ·
            refine ⟨3534401671470169967356993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4712535561960226623142657 3534401671470169967356993)
            ·
              refine ⟨2650801253602627475517745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3534401671470169967356993 2650801253602627475517745)
              ·
                refine ⟨1988100940201970606638309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2650801253602627475517745 1988100940201970606638309)
                ·
                  refine ⟨372768926287869488744683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1988100940201970606638309 372768926287869488744683)
                  ·
                    rfl

theorem cell22_3266842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 2, 4].length) (baseStart_3266842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266842 prefixEnd_3266842 := by exact prefixLift 3266842
  have htrace : WordTrace (prefixWord ++ tailWord_3266842) baseStart_3266842 baseEnd_3266842 := by
    simpa [prefixWord, tailWord_3266842, baseEnd_3266842] using wordTrace_append hprefix tailTrace_3266842
  have hstable : (prefixWord ++ tailWord_3266842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266842).length < 2 ^ (prefixWord ++ tailWord_3266842).sum := by decide
  have hdescent : baseEnd_3266842 < baseStart_3266842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266853 : List Nat := [1, 3, 1, 2, 5, 2, 1, 7]
def baseStart_3266853 : Nat := 118140960795 + 3266853 * 2 ^ 59
def prefixEnd_3266853 : Nat := 4983230072969 + 3 ^ 40 * 3266853 * 2
def baseEnd_3266853 : Nat := 124256727154267567134335

theorem tailTrace_3266853 : CollatzResearch.WordTrace tailWord_3266853 prefixEnd_3266853 124256727154267567134335 := by
  unfold tailWord_3266853
  simp only [CollatzResearch.WordTrace]
  refine ⟨119151917633756989918109213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79434611755837993278739475 119151917633756989918109213)
  ·
    refine ⟨44681969112658871219290955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119151917633756989918109213 44681969112658871219290955)
    ·
      refine ⟨67022953668988306828936433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44681969112658871219290955 67022953668988306828936433)
      ·
        refine ⟨50267215251741230121702325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67022953668988306828936433 50267215251741230121702325)
        ·
          refine ⟨4712551429850740323909593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50267215251741230121702325 4712551429850740323909593)
          ·
            refine ⟨3534413572388055242932195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4712551429850740323909593 3534413572388055242932195)
            ·
              refine ⟨5301620358582082864398293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3534413572388055242932195 5301620358582082864398293)
              ·
                refine ⟨124256727154267567134335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5301620358582082864398293 124256727154267567134335)
                ·
                  rfl

theorem cell22_3266853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 7].length) (baseStart_3266853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266853 prefixEnd_3266853 := by exact prefixLift 3266853
  have htrace : WordTrace (prefixWord ++ tailWord_3266853) baseStart_3266853 baseEnd_3266853 := by
    simpa [prefixWord, tailWord_3266853, baseEnd_3266853] using wordTrace_append hprefix tailTrace_3266853
  have hstable : (prefixWord ++ tailWord_3266853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266853).length < 2 ^ (prefixWord ++ tailWord_3266853).sum := by decide
  have hdescent : baseEnd_3266853 < baseStart_3266853 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266896 : List Nat := [2, 1, 1, 1, 1, 6, 1, 2, 2, 5]
def baseStart_3266896 : Nat := 118140960795 + 3266896 * 2 ^ 59
def prefixEnd_3266896 : Nat := 4983230072969 + 3 ^ 40 * 3266896 * 2
def baseEnd_3266896 : Nat := 1118325264167170325383883

theorem tailTrace_3266896 : CollatzResearch.WordTrace tailWord_3266896 prefixEnd_3266896 1118325264167170325383883 := by
  unfold tailWord_3266896
  simp only [CollatzResearch.WordTrace]
  refine ⟨59576742986300604130962271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79435657315067472174616361 59576742986300604130962271)
  ·
    refine ⟨89365114479450906196443407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59576742986300604130962271 89365114479450906196443407)
    ·
      refine ⟨134047671719176359294665111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89365114479450906196443407 134047671719176359294665111)
      ·
        refine ⟨201071507578764538941997667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134047671719176359294665111 201071507578764538941997667)
        ·
          refine ⟨301607261368146808412996501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201071507578764538941997667 301607261368146808412996501)
          ·
            refine ⟨14137840376631881644359211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 301607261368146808412996501 14137840376631881644359211)
            ·
              refine ⟨21206760564947822466538817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14137840376631881644359211 21206760564947822466538817)
              ·
                refine ⟨15905070423710866849904113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21206760564947822466538817 15905070423710866849904113)
                ·
                  refine ⟨11928802817783150137428085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15905070423710866849904113 11928802817783150137428085)
                  ·
                    refine ⟨1118325264167170325383883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11928802817783150137428085 1118325264167170325383883)
                    ·
                      rfl

theorem cell22_3266896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 2, 2, 5].length) (baseStart_3266896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266896 prefixEnd_3266896 := by exact prefixLift 3266896
  have htrace : WordTrace (prefixWord ++ tailWord_3266896) baseStart_3266896 baseEnd_3266896 := by
    simpa [prefixWord, tailWord_3266896, baseEnd_3266896] using wordTrace_append hprefix tailTrace_3266896
  have hstable : (prefixWord ++ tailWord_3266896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266896).length < 2 ^ (prefixWord ++ tailWord_3266896).sum := by decide
  have hdescent : baseEnd_3266896 < baseStart_3266896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266898 : List Nat := [3, 2, 2, 1, 1, 1, 5, 2, 5]
def baseStart_3266898 : Nat := 118140960795 + 3266898 * 2 ^ 59
def prefixEnd_3266898 : Nat := 4983230072969 + 3 ^ 40 * 3266898 * 2
def baseEnd_3266898 : Nat := 372775316269347662277959

theorem tailTrace_3266898 : CollatzResearch.WordTrace tailWord_3266898 prefixEnd_3266898 372775316269347662277959 := by
  unfold tailWord_3266898
  simp only [CollatzResearch.WordTrace]
  refine ⟨29788389729648490650874337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79435705945729308402331565 29788389729648490650874337)
  ·
    refine ⟨22341292297236367988155753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29788389729648490650874337 22341292297236367988155753)
    ·
      refine ⟨16755969222927275991116815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22341292297236367988155753 16755969222927275991116815)
      ·
        refine ⟨25133953834390913986675223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16755969222927275991116815 25133953834390913986675223)
        ·
          refine ⟨37700930751586370980012835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25133953834390913986675223 37700930751586370980012835)
          ·
            refine ⟨56551396127379556470019253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37700930751586370980012835 56551396127379556470019253)
            ·
              refine ⟨5301693386941833419064305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56551396127379556470019253 5301693386941833419064305)
              ·
                refine ⟨3976270040206375064298229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5301693386941833419064305 3976270040206375064298229)
                ·
                  refine ⟨372775316269347662277959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3976270040206375064298229 372775316269347662277959)
                  ·
                    rfl

theorem cell22_3266898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_3266898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266898 prefixEnd_3266898 := by exact prefixLift 3266898
  have htrace : WordTrace (prefixWord ++ tailWord_3266898) baseStart_3266898 baseEnd_3266898 := by
    simpa [prefixWord, tailWord_3266898, baseEnd_3266898] using wordTrace_append hprefix tailTrace_3266898
  have hstable : (prefixWord ++ tailWord_3266898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266898).length < 2 ^ (prefixWord ++ tailWord_3266898).sum := by decide
  have hdescent : baseEnd_3266898 < baseStart_3266898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266911 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 5, 4]
def baseStart_3266911 : Nat := 118140960795 + 3266911 * 2 ^ 59
def prefixEnd_3266911 : Nat := 4983230072969 + 3 ^ 40 * 3266911 * 2
def baseEnd_3266911 : Nat := 1118330398973715286258837

theorem tailTrace_3266911 : CollatzResearch.WordTrace tailWord_3266911 prefixEnd_3266911 1118330398973715286258837 := by
  unfold tailWord_3266911
  simp only [CollatzResearch.WordTrace]
  refine ⟨119154033067546865823720587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79436022045031243882480391 119154033067546865823720587)
  ·
    refine ⟨178731049601320298735580881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119154033067546865823720587 178731049601320298735580881)
    ·
      refine ⟨134048287200990224051685661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178731049601320298735580881 134048287200990224051685661)
      ·
        refine ⟨50268107700371334019382123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134048287200990224051685661 50268107700371334019382123)
        ·
          refine ⟨75402161550557001029073185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50268107700371334019382123 75402161550557001029073185)
          ·
            refine ⟨56551621162917750771804889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75402161550557001029073185 56551621162917750771804889)
            ·
              refine ⟨42413715872188313078853667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56551621162917750771804889 42413715872188313078853667)
              ·
                refine ⟨63620573808282469618280501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42413715872188313078853667 63620573808282469618280501)
                ·
                  refine ⟨5964428794526481526713797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63620573808282469618280501 5964428794526481526713797)
                  ·
                    refine ⟨1118330398973715286258837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5964428794526481526713797 1118330398973715286258837)
                    ·
                      rfl

theorem cell22_3266911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 5, 4].length) (baseStart_3266911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266911 prefixEnd_3266911 := by exact prefixLift 3266911
  have htrace : WordTrace (prefixWord ++ tailWord_3266911) baseStart_3266911 baseEnd_3266911 := by
    simpa [prefixWord, tailWord_3266911, baseEnd_3266911] using wordTrace_append hprefix tailTrace_3266911
  have hstable : (prefixWord ++ tailWord_3266911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266911).length < 2 ^ (prefixWord ++ tailWord_3266911).sum := by decide
  have hdescent : baseEnd_3266911 < baseStart_3266911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266928 : List Nat := [2, 1, 1, 1, 4, 3, 1, 4, 1, 4]
def baseStart_3266928 : Nat := 118140960795 + 3266928 * 2 ^ 59
def prefixEnd_3266928 : Nat := 4983230072969 + 3 ^ 40 * 3266928 * 2
def baseEnd_3266928 : Nat := 1118336218421132908583785

theorem tailTrace_3266928 : CollatzResearch.WordTrace tailWord_3266928 prefixEnd_3266928 1118336218421132908583785 := by
  unfold tailWord_3266928
  simp only [CollatzResearch.WordTrace]
  refine ⟨59577326554242638863544719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79436435405656851818059625 59577326554242638863544719)
  ·
    refine ⟨89365989831363958295317079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59577326554242638863544719 89365989831363958295317079)
    ·
      refine ⟨134048984747045937442975619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89365989831363958295317079 134048984747045937442975619)
      ·
        refine ⟨201073477120568906164463429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134048984747045937442975619 201073477120568906164463429)
        ·
          refine ⟨37701276960106669905836893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201073477120568906164463429 37701276960106669905836893)
          ·
            refine ⟨14137978860040001214688835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37701276960106669905836893 14137978860040001214688835)
            ·
              refine ⟨21206968290060001822033253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14137978860040001214688835 21206968290060001822033253)
              ·
                refine ⟨3976306554386250341631235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21206968290060001822033253 3976306554386250341631235)
                ·
                  refine ⟨5964459831579375512446853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3976306554386250341631235 5964459831579375512446853)
                  ·
                    refine ⟨1118336218421132908583785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5964459831579375512446853 1118336218421132908583785)
                    ·
                      rfl

theorem cell22_3266928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 4, 1, 4].length) (baseStart_3266928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266928 prefixEnd_3266928 := by exact prefixLift 3266928
  have htrace : WordTrace (prefixWord ++ tailWord_3266928) baseStart_3266928 baseEnd_3266928 := by
    simpa [prefixWord, tailWord_3266928, baseEnd_3266928] using wordTrace_append hprefix tailTrace_3266928
  have hstable : (prefixWord ++ tailWord_3266928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266928).length < 2 ^ (prefixWord ++ tailWord_3266928).sum := by decide
  have hdescent : baseEnd_3266928 < baseStart_3266928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266945 : List Nat := [1, 2, 4, 3, 1, 1, 2, 3, 1, 4]
def baseStart_3266945 : Nat := 118140960795 + 3266945 * 2 ^ 59
def prefixEnd_3266945 : Nat := 4983230072969 + 3 ^ 40 * 3266945 * 2
def baseEnd_3266945 : Nat := 1118342037868550530908733

theorem tailTrace_3266945 : CollatzResearch.WordTrace tailWord_3266945 prefixEnd_3266945 1118342037868550530908733 := by
  unfold tailWord_3266945
  simp only [CollatzResearch.WordTrace]
  refine ⟨119155273149423689630458289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79436848766282459753638859 119155273149423689630458289)
  ·
    refine ⟨89366454862067767222843717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119155273149423689630458289 89366454862067767222843717)
    ·
      refine ⟨16756210286637706354283197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89366454862067767222843717 16756210286637706354283197)
      ·
        refine ⟨6283578857489139882856199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16756210286637706354283197 6283578857489139882856199)
        ·
          refine ⟨9425368286233709824284299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6283578857489139882856199 9425368286233709824284299)
          ·
            refine ⟨14138052429350564736426449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9425368286233709824284299 14138052429350564736426449)
            ·
              refine ⟨10603539322012923552319837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14138052429350564736426449 10603539322012923552319837)
              ·
                refine ⟨3976327245754846332119939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10603539322012923552319837 3976327245754846332119939)
                ·
                  refine ⟨5964490868632269498179909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3976327245754846332119939 5964490868632269498179909)
                  ·
                    refine ⟨1118342037868550530908733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5964490868632269498179909 1118342037868550530908733)
                    ·
                      rfl

theorem cell22_3266945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 3, 1, 4].length) (baseStart_3266945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266945 prefixEnd_3266945 := by exact prefixLift 3266945
  have htrace : WordTrace (prefixWord ++ tailWord_3266945) baseStart_3266945 baseEnd_3266945 := by
    simpa [prefixWord, tailWord_3266945, baseEnd_3266945] using wordTrace_append hprefix tailTrace_3266945
  have hstable : (prefixWord ++ tailWord_3266945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266945).length < 2 ^ (prefixWord ++ tailWord_3266945).sum := by decide
  have hdescent : baseEnd_3266945 < baseStart_3266945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266975 : List Nat := [1, 1, 2, 5, 1, 1, 3, 3, 2, 3]
def baseStart_3266975 : Nat := 118140960795 + 3266975 * 2 ^ 59
def prefixEnd_3266975 : Nat := 4983230072969 + 3 ^ 40 * 3266975 * 2
def baseEnd_3266975 : Nat := 1118352307481640452658641

theorem tailTrace_3266975 : CollatzResearch.WordTrace tailWord_3266975 prefixEnd_3266975 1118352307481640452658641 := by
  unfold tailWord_3266975
  simp only [CollatzResearch.WordTrace]
  refine ⟨119156367339315004754050379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79437578226210003169366919 119156367339315004754050379)
  ·
    refine ⟨178734551008972507131075569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119156367339315004754050379 178734551008972507131075569)
    ·
      refine ⟨134050913256729380348306677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178734551008972507131075569 134050913256729380348306677)
      ·
        refine ⟨12567273117818379407653751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134050913256729380348306677 12567273117818379407653751)
        ·
          refine ⟨18850909676727569111480627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12567273117818379407653751 18850909676727569111480627)
          ·
            refine ⟨28276364515091353667220941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18850909676727569111480627 28276364515091353667220941)
            ·
              refine ⟨10603636693159257625207853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28276364515091353667220941 10603636693159257625207853)
              ·
                refine ⟨3976363759934721609452945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10603636693159257625207853 3976363759934721609452945)
                ·
                  refine ⟨2982272819951041207089709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3976363759934721609452945 2982272819951041207089709)
                  ·
                    refine ⟨1118352307481640452658641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2982272819951041207089709 1118352307481640452658641)
                    ·
                      rfl

theorem cell22_3266975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 3, 2, 3].length) (baseStart_3266975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266975 prefixEnd_3266975 := by exact prefixLift 3266975
  have htrace : WordTrace (prefixWord ++ tailWord_3266975) baseStart_3266975 baseEnd_3266975 := by
    simpa [prefixWord, tailWord_3266975, baseEnd_3266975] using wordTrace_append hprefix tailTrace_3266975
  have hstable : (prefixWord ++ tailWord_3266975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266975).length < 2 ^ (prefixWord ++ tailWord_3266975).sum := by decide
  have hdescent : baseEnd_3266975 < baseStart_3266975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3266996 : List Nat := [2, 5, 2, 2, 1, 1, 3, 1, 1, 4]
def baseStart_3266996 : Nat := 118140960795 + 3266996 * 2 ^ 59
def prefixEnd_3266996 : Nat := 4983230072969 + 3 ^ 40 * 3266996 * 2
def baseEnd_3266996 : Nat := 1118359496210803397883577

theorem tailTrace_3266996 : CollatzResearch.WordTrace tailWord_3266996 prefixEnd_3266996 1118359496210803397883577 := by
  unfold tailWord_3266996
  simp only [CollatzResearch.WordTrace]
  refine ⟨59578566636119462670282421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79438088848159283560376561 59578566636119462670282421)
  ·
    refine ⟨5585490622136199625338977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59578566636119462670282421 5585490622136199625338977)
    ·
      refine ⟨4189117966602149719004233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5585490622136199625338977 4189117966602149719004233)
      ·
        refine ⟨3141838474951612289253175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4189117966602149719004233 3141838474951612289253175)
        ·
          refine ⟨4712757712427418433879763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3141838474951612289253175 4712757712427418433879763)
          ·
            refine ⟨7069136568641127650819645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4712757712427418433879763 7069136568641127650819645)
            ·
              refine ⟨2650926213240422869057367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7069136568641127650819645 2650926213240422869057367)
              ·
                refine ⟨3976389319860634303586051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2650926213240422869057367 3976389319860634303586051)
                ·
                  refine ⟨5964583979790951455379077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3976389319860634303586051 5964583979790951455379077)
                  ·
                    refine ⟨1118359496210803397883577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5964583979790951455379077 1118359496210803397883577)
                    ·
                      rfl

theorem cell22_3266996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_3266996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3266996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3266996 prefixEnd_3266996 := by exact prefixLift 3266996
  have htrace : WordTrace (prefixWord ++ tailWord_3266996) baseStart_3266996 baseEnd_3266996 := by
    simpa [prefixWord, tailWord_3266996, baseEnd_3266996] using wordTrace_append hprefix tailTrace_3266996
  have hstable : (prefixWord ++ tailWord_3266996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3266996).length < 2 ^ (prefixWord ++ tailWord_3266996).sum := by decide
  have hdescent : baseEnd_3266996 < baseStart_3266996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3266996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267033 : List Nat := [1, 2, 1, 2, 4, 1, 1, 5, 5]
def baseStart_3267033 : Nat := 118140960795 + 3267033 * 2 ^ 59
def prefixEnd_3267033 : Nat := 4983230072969 + 3 ^ 40 * 3267033 * 2
def baseEnd_3267033 : Nat := 372790720688982544902821

theorem tailTrace_3267033 : CollatzResearch.WordTrace tailWord_3267033 prefixEnd_3267033 372790720688982544902821 := by
  unfold tailWord_3267033
  simp only [CollatzResearch.WordTrace]
  refine ⟨119158482773104880659661753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79438988515403253773107835 119158482773104880659661753)
  ·
    refine ⟨89368862079828660494746315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119158482773104880659661753 89368862079828660494746315)
    ·
      refine ⟨134053293119742990742119473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89368862079828660494746315 134053293119742990742119473)
      ·
        refine ⟨100539969839807243056589605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134053293119742990742119473 100539969839807243056589605)
        ·
          refine ⟨18851244344963858073110551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100539969839807243056589605 18851244344963858073110551)
          ·
            refine ⟨28276866517445787109665827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18851244344963858073110551 28276866517445787109665827)
            ·
              refine ⟨42415299776168680664498741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28276866517445787109665827 42415299776168680664498741)
              ·
                refine ⟨3976434354015813812296757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42415299776168680664498741 3976434354015813812296757)
                ·
                  refine ⟨372790720688982544902821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3976434354015813812296757 372790720688982544902821)
                  ·
                    rfl

theorem cell22_3267033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 5, 5].length) (baseStart_3267033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3267033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3267033 prefixEnd_3267033 := by exact prefixLift 3267033
  have htrace : WordTrace (prefixWord ++ tailWord_3267033) baseStart_3267033 baseEnd_3267033 := by
    simpa [prefixWord, tailWord_3267033, baseEnd_3267033] using wordTrace_append hprefix tailTrace_3267033
  have hstable : (prefixWord ++ tailWord_3267033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267033).length < 2 ^ (prefixWord ++ tailWord_3267033).sum := by decide
  have hdescent : baseEnd_3267033 < baseStart_3267033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267054 : List Nat := [4, 1, 2, 1, 2, 3, 2, 3, 1, 3]
def baseStart_3267054 : Nat := 118140960795 + 3267054 * 2 ^ 59
def prefixEnd_3267054 : Nat := 4983230072969 + 3 ^ 40 * 3267054 * 2
def baseEnd_3267054 : Nat := 1118379350796110579933399

theorem tailTrace_3267054 : CollatzResearch.WordTrace tailWord_3267054 prefixEnd_3267054 1118379350796110579933399 := by
  unfold tailWord_3267054
  simp only [CollatzResearch.WordTrace]
  refine ⟨14894906088253600155772027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79439499137352534164117477 14894906088253600155772027)
  ·
    refine ⟨22342359132380400233658041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14894906088253600155772027 22342359132380400233658041)
    ·
      refine ⟨16756769349285300175243531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22342359132380400233658041 16756769349285300175243531)
      ·
        refine ⟨25135154023927950262865297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16756769349285300175243531 25135154023927950262865297)
        ·
          refine ⟨18851365517945962697148973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25135154023927950262865297 18851365517945962697148973)
          ·
            refine ⟨7069262069229736011430865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18851365517945962697148973 7069262069229736011430865)
            ·
              refine ⟨5301946551922302008573149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7069262069229736011430865 5301946551922302008573149)
              ·
                refine ⟨1988229956970863253214931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5301946551922302008573149 1988229956970863253214931)
                ·
                  refine ⟨2982344935456294879822397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1988229956970863253214931 2982344935456294879822397)
                  ·
                    refine ⟨1118379350796110579933399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2982344935456294879822397 1118379350796110579933399)
                    ·
                      rfl

theorem cell22_3267054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_3267054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3267054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3267054 prefixEnd_3267054 := by exact prefixLift 3267054
  have htrace : WordTrace (prefixWord ++ tailWord_3267054) baseStart_3267054 baseEnd_3267054 := by
    simpa [prefixWord, tailWord_3267054, baseEnd_3267054] using wordTrace_append hprefix tailTrace_3267054
  have hstable : (prefixWord ++ tailWord_3267054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267054).length < 2 ^ (prefixWord ++ tailWord_3267054).sum := by decide
  have hdescent : baseEnd_3267054 < baseStart_3267054 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267125 : List Nat := [1, 3, 3, 1, 1, 2, 3, 2, 2, 4]
def baseStart_3267125 : Nat := 118140960795 + 3267125 * 2 ^ 59
def prefixEnd_3267125 : Nat := 4983230072969 + 3 ^ 40 * 3267125 * 2
def baseEnd_3267125 : Nat := 1118403655547090061408181

theorem tailTrace_3267125 : CollatzResearch.WordTrace tailWord_3267125 prefixEnd_3267125 1118403655547090061408181 := by
  unfold tailWord_3267125
  simp only [CollatzResearch.WordTrace]
  refine ⟨119161838288771580372010829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79441225525847720248007219 119161838288771580372010829)
  ·
    refine ⟨44685689358289342639504061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119161838288771580372010829 44685689358289342639504061)
    ·
      refine ⟨16757133509358503489814023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44685689358289342639504061 16757133509358503489814023)
      ·
        refine ⟨25135700264037755234721035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16757133509358503489814023 25135700264037755234721035)
        ·
          refine ⟨37703550396056632852081553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25135700264037755234721035 37703550396056632852081553)
          ·
            refine ⟨28277662797042474639061165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37703550396056632852081553 28277662797042474639061165)
            ·
              refine ⟨10604123548890927989647937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28277662797042474639061165 10604123548890927989647937)
              ·
                refine ⟨7953092661668195992235953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10604123548890927989647937 7953092661668195992235953)
                ·
                  refine ⟨5964819496251146994176965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7953092661668195992235953 5964819496251146994176965)
                  ·
                    refine ⟨1118403655547090061408181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5964819496251146994176965 1118403655547090061408181)
                    ·
                      rfl

theorem cell22_3267125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2, 4].length) (baseStart_3267125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3267125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3267125 prefixEnd_3267125 := by exact prefixLift 3267125
  have htrace : WordTrace (prefixWord ++ tailWord_3267125) baseStart_3267125 baseEnd_3267125 := by
    simpa [prefixWord, tailWord_3267125, baseEnd_3267125] using wordTrace_append hprefix tailTrace_3267125
  have hstable : (prefixWord ++ tailWord_3267125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267125).length < 2 ^ (prefixWord ++ tailWord_3267125).sum := by decide
  have hdescent : baseEnd_3267125 < baseStart_3267125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267168 : List Nat := [2, 1, 1, 3, 2, 1, 2, 1, 9]
def baseStart_3267168 : Nat := 118140960795 + 3267168 * 2 ^ 59
def prefixEnd_3267168 : Nat := 4983230072969 + 3 ^ 40 * 3267168 * 2
def baseEnd_3267168 : Nat := 372806125108617427527683

theorem tailTrace_3267168 : CollatzResearch.WordTrace tailWord_3267168 prefixEnd_3267168 372806125108617427527683 := by
  unfold tailWord_3267168
  simp only [CollatzResearch.WordTrace]
  refine ⟨59581703313807899357913079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79442271085077199143884105 59581703313807899357913079)
  ·
    refine ⟨89372554970711849036869619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59581703313807899357913079 89372554970711849036869619)
    ·
      refine ⟨134058832456067773555304429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89372554970711849036869619 134058832456067773555304429)
      ·
        refine ⟨50272062171025415083239161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134058832456067773555304429 50272062171025415083239161)
        ·
          refine ⟨37704046628269061312429371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50272062171025415083239161 37704046628269061312429371)
          ·
            refine ⟨56556069942403591968644057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37704046628269061312429371 56556069942403591968644057)
            ·
              refine ⟨42417052456802693976483043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56556069942403591968644057 42417052456802693976483043)
              ·
                refine ⟨63625578685204040964724565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42417052456802693976483043 63625578685204040964724565)
                ·
                  refine ⟨372806125108617427527683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 63625578685204040964724565 372806125108617427527683)
                  ·
                    rfl

theorem cell22_3267168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 1, 9].length) (baseStart_3267168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3267168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3267168 prefixEnd_3267168 := by exact prefixLift 3267168
  have htrace : WordTrace (prefixWord ++ tailWord_3267168) baseStart_3267168 baseEnd_3267168 := by
    simpa [prefixWord, tailWord_3267168, baseEnd_3267168] using wordTrace_append hprefix tailTrace_3267168
  have hstable : (prefixWord ++ tailWord_3267168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267168).length < 2 ^ (prefixWord ++ tailWord_3267168).sum := by decide
  have hdescent : baseEnd_3267168 < baseStart_3267168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267200 : List Nat := [2, 1, 1, 2, 1, 6, 1, 1, 2, 5]
def baseStart_3267200 : Nat := 118140960795 + 3267200 * 2 ^ 59
def prefixEnd_3267200 : Nat := 4983230072969 + 3 ^ 40 * 3267200 * 2
def baseEnd_3267200 : Nat := 1118429329579814865782951

theorem tailTrace_3267200 : CollatzResearch.WordTrace tailWord_3267200 prefixEnd_3267200 1118429329579814865782951 := by
  unfold tailWord_3267200
  simp only [CollatzResearch.WordTrace]
  refine ⟨59582286881749934090495527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79443049175666578787327369 59582286881749934090495527)
  ·
    refine ⟨89373430322624901135743291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59582286881749934090495527 89373430322624901135743291)
    ·
      refine ⟨134060145483937351703614937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89373430322624901135743291 134060145483937351703614937)
      ·
        refine ⟨100545109112953013777711203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134060145483937351703614937 100545109112953013777711203)
        ·
          refine ⟨150817663669429520666566805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100545109112953013777711203 150817663669429520666566805)
          ·
            refine ⟨7069577984504508781245319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 150817663669429520666566805 7069577984504508781245319)
            ·
              refine ⟨10604366976756763171867979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7069577984504508781245319 10604366976756763171867979)
              ·
                refine ⟨15906550465135144757801969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10604366976756763171867979 15906550465135144757801969)
                ·
                  refine ⟨11929912848851358568351477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15906550465135144757801969 11929912848851358568351477)
                  ·
                    refine ⟨1118429329579814865782951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11929912848851358568351477 1118429329579814865782951)
                    ·
                      rfl

theorem cell22_3267200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 1, 2, 5].length) (baseStart_3267200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3267200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3267200 prefixEnd_3267200 := by exact prefixLift 3267200
  have htrace : WordTrace (prefixWord ++ tailWord_3267200) baseStart_3267200 baseEnd_3267200 := by
    simpa [prefixWord, tailWord_3267200, baseEnd_3267200] using wordTrace_append hprefix tailTrace_3267200
  have hstable : (prefixWord ++ tailWord_3267200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267200).length < 2 ^ (prefixWord ++ tailWord_3267200).sum := by decide
  have hdescent : baseEnd_3267200 < baseStart_3267200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267247 : List Nat := [1, 1, 2, 1, 2, 5, 2, 4, 4]
def baseStart_3267247 : Nat := 118140960795 + 3267247 * 2 ^ 59
def prefixEnd_3267247 : Nat := 4983230072969 + 3 ^ 40 * 3267247 * 2
def baseEnd_3267247 : Nat := 372815139546774136619269

theorem tailTrace_3267247 : CollatzResearch.WordTrace tailWord_3267247 prefixEnd_3267247 372815139546774136619269 := by
  unfold tailWord_3267247
  simp only [CollatzResearch.WordTrace]
  refine ⟨119166287994329595207951995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79444191996219730138634663 119166287994329595207951995)
  ·
    refine ⟨178749431991494392811927993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119166287994329595207951995 178749431991494392811927993)
    ·
      refine ⟨134062073993620794608945995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178749431991494392811927993 134062073993620794608945995)
      ·
        refine ⟨201093110990431191913418993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134062073993620794608945995 201093110990431191913418993)
        ·
          refine ⟨150819833242823393935064245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201093110990431191913418993 150819833242823393935064245)
          ·
            refine ⟨14139359366514693181412273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 150819833242823393935064245 14139359366514693181412273)
            ·
              refine ⟨10604519524886019886059205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14139359366514693181412273 10604519524886019886059205)
              ·
                refine ⟨1988347410916128728636101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10604519524886019886059205 1988347410916128728636101)
                ·
                  refine ⟨372815139546774136619269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1988347410916128728636101 372815139546774136619269)
                  ·
                    rfl

theorem cell22_3267247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 4, 4].length) (baseStart_3267247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3267247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3267247 prefixEnd_3267247 := by exact prefixLift 3267247
  have htrace : WordTrace (prefixWord ++ tailWord_3267247) baseStart_3267247 baseEnd_3267247 := by
    simpa [prefixWord, tailWord_3267247, baseEnd_3267247] using wordTrace_append hprefix tailTrace_3267247
  have hstable : (prefixWord ++ tailWord_3267247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267247).length < 2 ^ (prefixWord ++ tailWord_3267247).sum := by decide
  have hdescent : baseEnd_3267247 < baseStart_3267247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267260 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 3, 6]
def baseStart_3267260 : Nat := 118140960795 + 3267260 * 2 ^ 59
def prefixEnd_3267260 : Nat := 4983230072969 + 3 ^ 40 * 3267260 * 2
def baseEnd_3267260 : Nat := 1118449868805994709282767

theorem tailTrace_3267260 : CollatzResearch.WordTrace tailWord_3267260 prefixEnd_3267260 1118449868805994709282767 := by
  unfold tailWord_3267260
  simp only [CollatzResearch.WordTrace]
  refine ⟨59583381071641249214087617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79444508095521665618783489 59583381071641249214087617)
  ·
    refine ⟨44687535803730936910565713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59583381071641249214087617 44687535803730936910565713)
    ·
      refine ⟨33515651852798202682924285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44687535803730936910565713 33515651852798202682924285)
      ·
        refine ⟨12568369444799326006096607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33515651852798202682924285 12568369444799326006096607)
        ·
          refine ⟨18852554167198989009144911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12568369444799326006096607 18852554167198989009144911)
          ·
            refine ⟨28278831250798483513717367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18852554167198989009144911 28278831250798483513717367)
            ·
              refine ⟨42418246876197725270576051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28278831250798483513717367 42418246876197725270576051)
              ·
                refine ⟨63627370314296587905864077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42418246876197725270576051 63627370314296587905864077)
                ·
                  refine ⟨23860263867861220464699029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63627370314296587905864077 23860263867861220464699029)
                  ·
                    refine ⟨1118449868805994709282767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23860263867861220464699029 1118449868805994709282767)
                    ·
                      rfl

theorem cell22_3267260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 3, 6].length) (baseStart_3267260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3267260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3267260 prefixEnd_3267260 := by exact prefixLift 3267260
  have htrace : WordTrace (prefixWord ++ tailWord_3267260) baseStart_3267260 baseEnd_3267260 := by
    simpa [prefixWord, tailWord_3267260, baseEnd_3267260] using wordTrace_append hprefix tailTrace_3267260
  have hstable : (prefixWord ++ tailWord_3267260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267260).length < 2 ^ (prefixWord ++ tailWord_3267260).sum := by decide
  have hdescent : baseEnd_3267260 < baseStart_3267260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267292 : List Nat := [2, 2, 5, 1, 1, 1, 10]
def baseStart_3267292 : Nat := 118140960795 + 3267292 * 2 ^ 59
def prefixEnd_3267292 : Nat := 4983230072969 + 3 ^ 40 * 3267292 * 2
def baseEnd_3267292 : Nat := 41424474928146566388247

theorem tailTrace_3267292 : CollatzResearch.WordTrace tailWord_3267292 prefixEnd_3267292 41424474928146566388247 := by
  unfold tailWord_3267292
  simp only [CollatzResearch.WordTrace]
  refine ⟨59583964639583283946670065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79445286186111045262226753 59583964639583283946670065)
  ·
    refine ⟨44687973479687462960002549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59583964639583283946670065 44687973479687462960002549)
    ·
      refine ⟨4189497513720699652500239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44687973479687462960002549 4189497513720699652500239)
      ·
        refine ⟨6284246270581049478750359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4189497513720699652500239 6284246270581049478750359)
        ·
          refine ⟨9426369405871574218125539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6284246270581049478750359 9426369405871574218125539)
          ·
            refine ⟨14139554108807361327188309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9426369405871574218125539 14139554108807361327188309)
            ·
              refine ⟨41424474928146566388247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14139554108807361327188309 41424474928146566388247)
              ·
                rfl

theorem cell22_3267292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 10].length) (baseStart_3267292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3267292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3267292 prefixEnd_3267292 := by exact prefixLift 3267292
  have htrace : WordTrace (prefixWord ++ tailWord_3267292) baseStart_3267292 baseEnd_3267292 := by
    simpa [prefixWord, tailWord_3267292, baseEnd_3267292] using wordTrace_append hprefix tailTrace_3267292
  have hstable : (prefixWord ++ tailWord_3267292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267292).length < 2 ^ (prefixWord ++ tailWord_3267292).sum := by decide
  have hdescent : baseEnd_3267292 < baseStart_3267292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267401 : List Nat := [1, 2, 1, 1, 2, 7, 2, 1, 1, 4]
def baseStart_3267401 : Nat := 118140960795 + 3267401 * 2 ^ 59
def prefixEnd_3267401 : Nat := 4983230072969 + 3 ^ 40 * 3267401 * 2
def baseEnd_3267401 : Nat := 1118498135987517341507335

theorem tailTrace_3267401 : CollatzResearch.WordTrace tailWord_3267401 prefixEnd_3267401 1118498135987517341507335 := by
  unfold tailWord_3267401
  simp only [CollatzResearch.WordTrace]
  refine ⟨119171904835771679509058057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79447936557181119672705371 119171904835771679509058057)
  ·
    refine ⟨89378928626828759631793543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119171904835771679509058057 89378928626828759631793543)
    ·
      refine ⟨134068392940243139447690315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89378928626828759631793543 134068392940243139447690315)
      ·
        refine ⟨201102589410364709171535473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134068392940243139447690315 201102589410364709171535473)
        ·
          refine ⟨150826942057773531878651605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201102589410364709171535473 150826942057773531878651605)
          ·
            refine ⟨3535006454479067153405897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 150826942057773531878651605 3535006454479067153405897)
            ·
              refine ⟨2651254840859300365054423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3535006454479067153405897 2651254840859300365054423)
              ·
                refine ⟨3976882261288950547581635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2651254840859300365054423 3976882261288950547581635)
                ·
                  refine ⟨5965323391933425821372453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3976882261288950547581635 5965323391933425821372453)
                  ·
                    refine ⟨1118498135987517341507335, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5965323391933425821372453 1118498135987517341507335)
                    ·
                      rfl

theorem cell22_3267401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 2, 1, 1, 4].length) (baseStart_3267401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3267401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3267401 prefixEnd_3267401 := by exact prefixLift 3267401
  have htrace : WordTrace (prefixWord ++ tailWord_3267401) baseStart_3267401 baseEnd_3267401 := by
    simpa [prefixWord, tailWord_3267401, baseEnd_3267401] using wordTrace_append hprefix tailTrace_3267401
  have hstable : (prefixWord ++ tailWord_3267401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267401).length < 2 ^ (prefixWord ++ tailWord_3267401).sum := by decide
  have hdescent : baseEnd_3267401 < baseStart_3267401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267478 : List Nat := [5, 3, 1, 1, 1, 2, 2, 7]
def baseStart_3267478 : Nat := 118140960795 + 3267478 * 2 ^ 59
def prefixEnd_3267478 : Nat := 4983230072969 + 3 ^ 40 * 3267478 * 2
def baseEnd_3267478 : Nat := 124280499406790534148011

theorem tailTrace_3267478 : CollatzResearch.WordTrace tailWord_3267478 prefixEnd_3267478 124280499406790534148011 := by
  unfold tailWord_3267478
  simp only [CollatzResearch.WordTrace]
  refine ⟨7448419578530795103725693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79449808837661814439740725 7448419578530795103725693)
  ·
    refine ⟨2793157341949048163897135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7448419578530795103725693 2793157341949048163897135)
    ·
      refine ⟨4189736012923572245845703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2793157341949048163897135 4189736012923572245845703)
      ·
        refine ⟨6284604019385358368768555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4189736012923572245845703 6284604019385358368768555)
        ·
          refine ⟨9426906029078037553152833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6284604019385358368768555 9426906029078037553152833)
          ·
            refine ⟨7070179521808528164864625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9426906029078037553152833 7070179521808528164864625)
            ·
              refine ⟨5302634641356396123648469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7070179521808528164864625 5302634641356396123648469)
              ·
                refine ⟨124280499406790534148011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5302634641356396123648469 124280499406790534148011)
                ·
                  rfl

theorem cell22_3267478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 7].length) (baseStart_3267478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3267478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3267478 prefixEnd_3267478 := by exact prefixLift 3267478
  have htrace : WordTrace (prefixWord ++ tailWord_3267478) baseStart_3267478 baseEnd_3267478 := by
    simpa [prefixWord, tailWord_3267478, baseEnd_3267478] using wordTrace_append hprefix tailTrace_3267478
  have hstable : (prefixWord ++ tailWord_3267478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267478).length < 2 ^ (prefixWord ++ tailWord_3267478).sum := by decide
  have hdescent : baseEnd_3267478 < baseStart_3267478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267613 : List Nat := [1, 4, 2, 2, 3, 2, 2, 6]
def baseStart_3267613 : Nat := 118140960795 + 3267613 * 2 ^ 59
def prefixEnd_3267613 : Nat := 4983230072969 + 3 ^ 40 * 3267613 * 2
def baseEnd_3267613 : Nat := 124285634213335495022965

theorem tailTrace_3267613 : CollatzResearch.WordTrace tailWord_3267613 prefixEnd_3267613 124285634213335495022965 := by
  unfold tailWord_3267613
  simp only [CollatzResearch.WordTrace]
  refine ⟨119179637111003639715775493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79453091407335759810516995 119179637111003639715775493)
  ·
    refine ⟨22346181958313182446707905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119179637111003639715775493 22346181958313182446707905)
    ·
      refine ⟨16759636468734886835030929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22346181958313182446707905 16759636468734886835030929)
      ·
        refine ⟨12569727351551165126273197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16759636468734886835030929 12569727351551165126273197)
        ·
          refine ⟨4713647756831686922352449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12569727351551165126273197 4713647756831686922352449)
          ·
            refine ⟨3535235817623765191764337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4713647756831686922352449 3535235817623765191764337)
            ·
              refine ⟨2651426863217823893823253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3535235817623765191764337 2651426863217823893823253)
              ·
                refine ⟨124285634213335495022965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2651426863217823893823253 124285634213335495022965)
                ·
                  rfl

theorem cell22_3267613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 6].length) (baseStart_3267613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3267613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3267613 prefixEnd_3267613 := by exact prefixLift 3267613
  have htrace : WordTrace (prefixWord ++ tailWord_3267613) baseStart_3267613 baseEnd_3267613 := by
    simpa [prefixWord, tailWord_3267613, baseEnd_3267613] using wordTrace_append hprefix tailTrace_3267613
  have hstable : (prefixWord ++ tailWord_3267613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267613).length < 2 ^ (prefixWord ++ tailWord_3267613).sum := by decide
  have hdescent : baseEnd_3267613 < baseStart_3267613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267669 : List Nat := [1, 3, 2, 2, 1, 2, 2, 1, 8]
def baseStart_3267669 : Nat := 118140960795 + 3267669 * 2 ^ 59
def prefixEnd_3267669 : Nat := 4983230072969 + 3 ^ 40 * 3267669 * 2
def baseEnd_3267669 : Nat := 372863292621484658602171

theorem tailTrace_3267669 : CollatzResearch.WordTrace tailWord_3267669 prefixEnd_3267669 372863292621484658602171 := by
  unfold tailWord_3267669
  simp only [CollatzResearch.WordTrace]
  refine ⟨119181679598800761279814061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79454453065867174186542707 119181679598800761279814061)
  ·
    refine ⟨44693129849550285479930273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119181679598800761279814061 44693129849550285479930273)
    ·
      refine ⟨33519847387162714109947705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44693129849550285479930273 33519847387162714109947705)
      ·
        refine ⟨25139885540372035582460779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33519847387162714109947705 25139885540372035582460779)
        ·
          refine ⟨37709828310558053373691169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25139885540372035582460779 37709828310558053373691169)
          ·
            refine ⟨28282371232918540030268377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37709828310558053373691169 28282371232918540030268377)
            ·
              refine ⟨21211778424688905022701283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28282371232918540030268377 21211778424688905022701283)
              ·
                refine ⟨31817667637033357534051925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21211778424688905022701283 31817667637033357534051925)
                ·
                  refine ⟨372863292621484658602171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31817667637033357534051925 372863292621484658602171)
                  ·
                    rfl

theorem cell22_3267669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 1, 8].length) (baseStart_3267669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3267669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3267669 prefixEnd_3267669 := by exact prefixLift 3267669
  have htrace : WordTrace (prefixWord ++ tailWord_3267669) baseStart_3267669 baseEnd_3267669 := by
    simpa [prefixWord, tailWord_3267669, baseEnd_3267669] using wordTrace_append hprefix tailTrace_3267669
  have hstable : (prefixWord ++ tailWord_3267669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267669).length < 2 ^ (prefixWord ++ tailWord_3267669).sum := by decide
  have hdescent : baseEnd_3267669 < baseStart_3267669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267782 : List Nat := [6, 1, 2, 2, 1, 1, 1, 8]
def baseStart_3267782 : Nat := 118140960795 + 3267782 * 2 ^ 59
def prefixEnd_3267782 : Nat := 4983230072969 + 3 ^ 40 * 3267782 * 2
def baseEnd_3267782 : Nat := 124292062230417705303463

theorem tailTrace_3267782 : CollatzResearch.WordTrace tailWord_3267782 prefixEnd_3267782 124292062230417705303463 := by
  unfold tailWord_3267782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3724556282730980674333675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 79457200698260921052451733 3724556282730980674333675)
  ·
    refine ⟨5586834424096471011500513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3724556282730980674333675 5586834424096471011500513)
    ·
      refine ⟨4190125818072353258625385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5586834424096471011500513 4190125818072353258625385)
      ·
        refine ⟨3142594363554264943969039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4190125818072353258625385 3142594363554264943969039)
        ·
          refine ⟨4713891545331397415953559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3142594363554264943969039 4713891545331397415953559)
          ·
            refine ⟨7070837317997096123930339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4713891545331397415953559 7070837317997096123930339)
            ·
              refine ⟨10606255976995644185895509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7070837317997096123930339 10606255976995644185895509)
              ·
                refine ⟨124292062230417705303463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10606255976995644185895509 124292062230417705303463)
                ·
                  rfl

theorem cell22_3267782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_3267782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3267782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3267782 prefixEnd_3267782 := by exact prefixLift 3267782
  have htrace : WordTrace (prefixWord ++ tailWord_3267782) baseStart_3267782 baseEnd_3267782 := by
    simpa [prefixWord, tailWord_3267782, baseEnd_3267782] using wordTrace_append hprefix tailTrace_3267782
  have hstable : (prefixWord ++ tailWord_3267782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267782).length < 2 ^ (prefixWord ++ tailWord_3267782).sum := by decide
  have hdescent : baseEnd_3267782 < baseStart_3267782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267797 : List Nat := [1, 3, 2, 4, 1, 1, 3, 3, 1, 3]
def baseStart_3267797 : Nat := 118140960795 + 3267797 * 2 ^ 59
def prefixEnd_3267797 : Nat := 4983230072969 + 3 ^ 40 * 3267797 * 2
def baseEnd_3267797 : Nat := 1118633694880304308606121

theorem tailTrace_3267797 : CollatzResearch.WordTrace tailWord_3267797 prefixEnd_3267797 1118633694880304308606121 := by
  unfold tailWord_3267797
  simp only [CollatzResearch.WordTrace]
  refine ⟨119186348142337039140473645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79457565428224692760315763 119186348142337039140473645)
  ·
    refine ⟨44694880553376389677677617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119186348142337039140473645 44694880553376389677677617)
    ·
      refine ⟨33521160415032292258258213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44694880553376389677677617 33521160415032292258258213)
      ·
        refine ⟨6285217577818554798423415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33521160415032292258258213 6285217577818554798423415)
        ·
          refine ⟨9427826366727832197635123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6285217577818554798423415 9427826366727832197635123)
          ·
            refine ⟨14141739550091748296452685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9427826366727832197635123 14141739550091748296452685)
            ·
              refine ⟨5303152331284405611169757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14141739550091748296452685 5303152331284405611169757)
              ·
                refine ⟨1988682124231652104188659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5303152331284405611169757 1988682124231652104188659)
                ·
                  refine ⟨2983023186347478156282989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1988682124231652104188659 2983023186347478156282989)
                  ·
                    refine ⟨1118633694880304308606121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2983023186347478156282989 1118633694880304308606121)
                    ·
                      rfl

theorem cell22_3267797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 3, 1, 3].length) (baseStart_3267797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3267797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3267797 prefixEnd_3267797 := by exact prefixLift 3267797
  have htrace : WordTrace (prefixWord ++ tailWord_3267797) baseStart_3267797 baseEnd_3267797 := by
    simpa [prefixWord, tailWord_3267797, baseEnd_3267797] using wordTrace_append hprefix tailTrace_3267797
  have hstable : (prefixWord ++ tailWord_3267797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267797).length < 2 ^ (prefixWord ++ tailWord_3267797).sum := by decide
  have hdescent : baseEnd_3267797 < baseStart_3267797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267866 : List Nat := [3, 1, 1, 3, 3, 11]
def baseStart_3267866 : Nat := 118140960795 + 3267866 * 2 ^ 59
def prefixEnd_3267866 : Nat := 4983230072969 + 3 ^ 40 * 3267866 * 2
def baseEnd_3267866 : Nat := 13810584135684088007789

theorem tailTrace_3267866 : CollatzResearch.WordTrace tailWord_3267866 prefixEnd_3267866 13810584135684088007789 := by
  unfold tailWord_3267866
  simp only [CollatzResearch.WordTrace]
  refine ⟨29797216194771765981183863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79459243186058042616490301 29797216194771765981183863)
  ·
    refine ⟨44695824292157648971775795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29797216194771765981183863 44695824292157648971775795)
    ·
      refine ⟨67043736438236473457663693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44695824292157648971775795 67043736438236473457663693)
      ·
        refine ⟨25141401164338677546623885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67043736438236473457663693 25141401164338677546623885)
        ·
          refine ⟨9428025436627004079983957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25141401164338677546623885 9428025436627004079983957)
          ·
            refine ⟨13810584135684088007789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 9428025436627004079983957 13810584135684088007789)
            ·
              rfl

theorem cell22_3267866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 11].length) (baseStart_3267866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3267866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3267866 prefixEnd_3267866 := by exact prefixLift 3267866
  have htrace : WordTrace (prefixWord ++ tailWord_3267866) baseStart_3267866 baseEnd_3267866 := by
    simpa [prefixWord, tailWord_3267866, baseEnd_3267866] using wordTrace_append hprefix tailTrace_3267866
  have hstable : (prefixWord ++ tailWord_3267866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267866).length < 2 ^ (prefixWord ++ tailWord_3267866).sum := by decide
  have hdescent : baseEnd_3267866 < baseStart_3267866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267868 : List Nat := [2, 2, 3, 1, 1, 1, 4, 2, 2, 4]
def baseStart_3267868 : Nat := 118140960795 + 3267868 * 2 ^ 59
def prefixEnd_3267868 : Nat := 4983230072969 + 3 ^ 40 * 3267868 * 2
def baseEnd_3267868 : Nat := 1118657999631283790080903

theorem tailTrace_3267868 : CollatzResearch.WordTrace tailWord_3267868 prefixEnd_3267868 1118657999631283790080903 := by
  unfold tailWord_3267868
  simp only [CollatzResearch.WordTrace]
  refine ⟨59594468862539909133154129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79459291816719878844205505 59594468862539909133154129)
  ·
    refine ⟨44695851646904931849865597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59594468862539909133154129 44695851646904931849865597)
    ·
      refine ⟨16760944367589349443699599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44695851646904931849865597 16760944367589349443699599)
      ·
        refine ⟨25141416551384024165549399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16760944367589349443699599 25141416551384024165549399)
        ·
          refine ⟨37712124827076036248324099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25141416551384024165549399 37712124827076036248324099)
          ·
            refine ⟨56568187240614054372486149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37712124827076036248324099 56568187240614054372486149)
            ·
              refine ⟨10606535107615135194841153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56568187240614054372486149 10606535107615135194841153)
              ·
                refine ⟨7954901330711351396130865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10606535107615135194841153 7954901330711351396130865)
                ·
                  refine ⟨5966175998033513547098149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7954901330711351396130865 5966175998033513547098149)
                  ·
                    refine ⟨1118657999631283790080903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5966175998033513547098149 1118657999631283790080903)
                    ·
                      rfl

theorem cell22_3267868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_3267868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3267868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3267868 prefixEnd_3267868 := by exact prefixLift 3267868
  have htrace : WordTrace (prefixWord ++ tailWord_3267868) baseStart_3267868 baseEnd_3267868 := by
    simpa [prefixWord, tailWord_3267868, baseEnd_3267868] using wordTrace_append hprefix tailTrace_3267868
  have hstable : (prefixWord ++ tailWord_3267868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267868).length < 2 ^ (prefixWord ++ tailWord_3267868).sum := by decide
  have hdescent : baseEnd_3267868 < baseStart_3267868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267896 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 4, 6]
def baseStart_3267896 : Nat := 118140960795 + 3267896 * 2 ^ 59
def prefixEnd_3267896 : Nat := 4983230072969 + 3 ^ 40 * 3267896 * 2
def baseEnd_3267896 : Nat := 1118667584603501050380817

theorem tailTrace_3267896 : CollatzResearch.WordTrace tailWord_3267896 prefixEnd_3267896 1118667584603501050380817 := by
  unfold tailWord_3267896
  simp only [CollatzResearch.WordTrace]
  refine ⟨59594979484489189524163771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79459972645985586032218361 59594979484489189524163771)
  ·
    refine ⟨89392469226733784286245657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59594979484489189524163771 89392469226733784286245657)
    ·
      refine ⟨67044351920050338214684243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89392469226733784286245657 67044351920050338214684243)
      ·
        refine ⟨100566527880075507322026365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67044351920050338214684243 100566527880075507322026365)
        ·
          refine ⟨37712447955028315245759887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100566527880075507322026365 37712447955028315245759887)
          ·
            refine ⟨56568671932542472868639831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37712447955028315245759887 56568671932542472868639831)
            ·
              refine ⟨84853007898813709302959747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56568671932542472868639831 84853007898813709302959747)
              ·
                refine ⟨127279511848220563954439621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84853007898813709302959747 127279511848220563954439621)
                ·
                  refine ⟨23864908471541355741457429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 127279511848220563954439621 23864908471541355741457429)
                  ·
                    refine ⟨1118667584603501050380817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23864908471541355741457429 1118667584603501050380817)
                    ·
                      rfl

theorem cell22_3267896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 4, 6].length) (baseStart_3267896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3267896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3267896 prefixEnd_3267896 := by exact prefixLift 3267896
  have htrace : WordTrace (prefixWord ++ tailWord_3267896) baseStart_3267896 baseEnd_3267896 := by
    simpa [prefixWord, tailWord_3267896, baseEnd_3267896] using wordTrace_append hprefix tailTrace_3267896
  have hstable : (prefixWord ++ tailWord_3267896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267896).length < 2 ^ (prefixWord ++ tailWord_3267896).sum := by decide
  have hdescent : baseEnd_3267896 < baseStart_3267896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267975 : List Nat := [1, 1, 4, 2, 2, 2, 2, 3, 1, 4]
def baseStart_3267975 : Nat := 118140960795 + 3267975 * 2 ^ 59
def prefixEnd_3267975 : Nat := 4983230072969 + 3 ^ 40 * 3267975 * 2
def baseEnd_3267975 : Nat := 1118694627917971177655575

theorem tailTrace_3267975 : CollatzResearch.WordTrace tailWord_3267975 prefixEnd_3267975 1118694627917971177655575 := by
  unfold tailWord_3267975
  simp only [CollatzResearch.WordTrace]
  refine ⟨119192840335692175540453379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79461893557128117026968919 119192840335692175540453379)
  ·
    refine ⟨178789260503538263310680069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119192840335692175540453379 178789260503538263310680069)
    ·
      refine ⟨33522986344413424370752513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178789260503538263310680069 33522986344413424370752513)
      ·
        refine ⟨25142239758310068278064385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33522986344413424370752513 25142239758310068278064385)
        ·
          refine ⟨18856679818732551208548289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25142239758310068278064385 18856679818732551208548289)
          ·
            refine ⟨14142509864049413406411217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18856679818732551208548289 14142509864049413406411217)
            ·
              refine ⟨10606882398037060054808413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14142509864049413406411217 10606882398037060054808413)
              ·
                refine ⟨3977580899263897520553155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10606882398037060054808413 3977580899263897520553155)
                ·
                  refine ⟨5966371348895846280829733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3977580899263897520553155 5966371348895846280829733)
                  ·
                    refine ⟨1118694627917971177655575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5966371348895846280829733 1118694627917971177655575)
                    ·
                      rfl

theorem cell22_3267975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_3267975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3267975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3267975 prefixEnd_3267975 := by exact prefixLift 3267975
  have htrace : WordTrace (prefixWord ++ tailWord_3267975) baseStart_3267975 baseEnd_3267975 := by
    simpa [prefixWord, tailWord_3267975, baseEnd_3267975] using wordTrace_append hprefix tailTrace_3267975
  have hstable : (prefixWord ++ tailWord_3267975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267975).length < 2 ^ (prefixWord ++ tailWord_3267975).sum := by decide
  have hdescent : baseEnd_3267975 < baseStart_3267975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3267996 : List Nat := [2, 2, 3, 4, 2, 1, 2, 1, 5]
def baseStart_3267996 : Nat := 118140960795 + 3267996 * 2 ^ 59
def prefixEnd_3267996 : Nat := 4983230072969 + 3 ^ 40 * 3267996 * 2
def baseEnd_3267996 : Nat := 372900605549044707626837

theorem tailTrace_3267996 : CollatzResearch.WordTrace tailWord_3267996 prefixEnd_3267996 372900605549044707626837 := by
  unfold tailWord_3267996
  simp only [CollatzResearch.WordTrace]
  refine ⟨59596803134308048063483921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79462404179077397417978561 59596803134308048063483921)
  ·
    refine ⟨44697602350731036047612941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59596803134308048063483921 44697602350731036047612941)
    ·
      refine ⟨16761600881524138517854853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44697602350731036047612941 16761600881524138517854853)
      ·
        refine ⟨3142800165285775972097785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16761600881524138517854853 3142800165285775972097785)
        ·
          refine ⟨2357100123964331979073339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3142800165285775972097785 2357100123964331979073339)
          ·
            refine ⟨3535650185946497968610009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2357100123964331979073339 3535650185946497968610009)
            ·
              refine ⟨2651737639459873476457507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3535650185946497968610009 2651737639459873476457507)
              ·
                refine ⟨3977606459189810214686261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2651737639459873476457507 3977606459189810214686261)
                ·
                  refine ⟨372900605549044707626837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3977606459189810214686261 372900605549044707626837)
                  ·
                    rfl

theorem cell22_3267996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 1, 5].length) (baseStart_3267996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3267996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3267996 prefixEnd_3267996 := by exact prefixLift 3267996
  have htrace : WordTrace (prefixWord ++ tailWord_3267996) baseStart_3267996 baseEnd_3267996 := by
    simpa [prefixWord, tailWord_3267996, baseEnd_3267996] using wordTrace_append hprefix tailTrace_3267996
  have hstable : (prefixWord ++ tailWord_3267996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3267996).length < 2 ^ (prefixWord ++ tailWord_3267996).sum := by decide
  have hdescent : baseEnd_3267996 < baseStart_3267996 := by decide
  rcases family_descends (prefixWord ++ tailWord_3267996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268003 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 4, 4]
def baseStart_3268003 : Nat := 118140960795 + 3268003 * 2 ^ 59
def prefixEnd_3268003 : Nat := 4983230072969 + 3 ^ 40 * 3268003 * 2
def baseEnd_3268003 : Nat := 1118704212890188437955489

theorem tailTrace_3268003 : CollatzResearch.WordTrace tailWord_3268003 prefixEnd_3268003 1118704212890188437955489 := by
  unfold tailWord_3268003
  simp only [CollatzResearch.WordTrace]
  refine ⟨119193861579590736322472663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79462574386393824214981775 119193861579590736322472663)
  ·
    refine ⟨178790792369386104483708995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119193861579590736322472663 178790792369386104483708995)
    ·
      refine ⟨268186188554079156725563493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178790792369386104483708995 268186188554079156725563493)
      ·
        refine ⟨50284910353889841886043155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 268186188554079156725563493 50284910353889841886043155)
        ·
          refine ⟨75427365530834762829064733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50284910353889841886043155 75427365530834762829064733)
          ·
            refine ⟨28285262074063036060899275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75427365530834762829064733 28285262074063036060899275)
            ·
              refine ⟨42427893111094554091348913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28285262074063036060899275 42427893111094554091348913)
              ·
                refine ⟨31820919833320915568511685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42427893111094554091348913 31820919833320915568511685)
                ·
                  refine ⟨5966422468747671669095941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31820919833320915568511685 5966422468747671669095941)
                  ·
                    refine ⟨1118704212890188437955489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5966422468747671669095941 1118704212890188437955489)
                    ·
                      rfl

theorem cell22_3268003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 4, 4].length) (baseStart_3268003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3268003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3268003 prefixEnd_3268003 := by exact prefixLift 3268003
  have htrace : WordTrace (prefixWord ++ tailWord_3268003) baseStart_3268003 baseEnd_3268003 := by
    simpa [prefixWord, tailWord_3268003, baseEnd_3268003] using wordTrace_append hprefix tailTrace_3268003
  have hstable : (prefixWord ++ tailWord_3268003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268003).length < 2 ^ (prefixWord ++ tailWord_3268003).sum := by decide
  have hdescent : baseEnd_3268003 < baseStart_3268003 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268034 : List Nat := [3, 5, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_3268034 : Nat := 118140960795 + 3268034 * 2 ^ 59
def prefixEnd_3268034 : Nat := 4983230072969 + 3 ^ 40 * 3268034 * 2
def baseEnd_3268034 : Nat := 1118714824823714690430395

theorem tailTrace_3268034 : CollatzResearch.WordTrace tailWord_3268034 prefixEnd_3268034 1118714824823714690430395 := by
  unfold tailWord_3268034
  simp only [CollatzResearch.WordTrace]
  refine ⟨29798748060619607154212789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79463328161652285744567437 29798748060619607154212789)
  ·
    refine ⟨2793632630683088170707449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 29798748060619607154212789 2793632630683088170707449)
    ·
      refine ⟨2095224473012316128030587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2793632630683088170707449 2095224473012316128030587)
      ·
        refine ⟨3142836709518474192045881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2095224473012316128030587 3142836709518474192045881)
        ·
          refine ⟨2357127532138855644034411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3142836709518474192045881 2357127532138855644034411)
          ·
            refine ⟨3535691298208283466051617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2357127532138855644034411 3535691298208283466051617)
            ·
              refine ⟨2651768473656212599538713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3535691298208283466051617 2651768473656212599538713)
              ·
                refine ⟨1988826355242159449654035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2651768473656212599538713 1988826355242159449654035)
                ·
                  refine ⟨2983239532863239174481053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1988826355242159449654035 2983239532863239174481053)
                  ·
                    refine ⟨1118714824823714690430395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2983239532863239174481053 1118714824823714690430395)
                    ·
                      rfl

theorem cell22_3268034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_3268034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3268034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3268034 prefixEnd_3268034 := by exact prefixLift 3268034
  have htrace : WordTrace (prefixWord ++ tailWord_3268034) baseStart_3268034 baseEnd_3268034 := by
    simpa [prefixWord, tailWord_3268034, baseEnd_3268034] using wordTrace_append hprefix tailTrace_3268034
  have hstable : (prefixWord ++ tailWord_3268034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268034).length < 2 ^ (prefixWord ++ tailWord_3268034).sum := by decide
  have hdescent : baseEnd_3268034 < baseStart_3268034 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268052 : List Nat := [2, 4, 1, 2, 3, 2, 1, 7]
def baseStart_3268052 : Nat := 118140960795 + 3268052 * 2 ^ 59
def prefixEnd_3268052 : Nat := 4983230072969 + 3 ^ 40 * 3268052 * 2
def baseEnd_3268052 : Nat := 124302331843507627053371

theorem tailTrace_3268052 : CollatzResearch.WordTrace tailWord_3268052 prefixEnd_3268052 124302331843507627053371 := by
  unfold tailWord_3268052
  simp only [CollatzResearch.WordTrace]
  refine ⟨59597824378206608845503205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79463765837608811794004273 59597824378206608845503205)
  ·
    refine ⟨11174592070913739158531851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59597824378206608845503205 11174592070913739158531851)
    ·
      refine ⟨16761888106370608737797777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11174592070913739158531851 16761888106370608737797777)
      ·
        refine ⟨12571416079777956553348333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16761888106370608737797777 12571416079777956553348333)
        ·
          refine ⟨4714281029916733707505625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12571416079777956553348333 4714281029916733707505625)
          ·
            refine ⟨3535710772437550280629219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4714281029916733707505625 3535710772437550280629219)
            ·
              refine ⟨5303566158656325420943829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3535710772437550280629219 5303566158656325420943829)
              ·
                refine ⟨124302331843507627053371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5303566158656325420943829 124302331843507627053371)
                ·
                  rfl

theorem cell22_3268052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 7].length) (baseStart_3268052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3268052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3268052 prefixEnd_3268052 := by exact prefixLift 3268052
  have htrace : WordTrace (prefixWord ++ tailWord_3268052) baseStart_3268052 baseEnd_3268052 := by
    simpa [prefixWord, tailWord_3268052, baseEnd_3268052] using wordTrace_append hprefix tailTrace_3268052
  have hstable : (prefixWord ++ tailWord_3268052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268052).length < 2 ^ (prefixWord ++ tailWord_3268052).sum := by decide
  have hdescent : baseEnd_3268052 < baseStart_3268052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268067 : List Nat := [1, 1, 1, 6, 2, 2, 1, 2, 3, 3]
def baseStart_3268067 : Nat := 118140960795 + 3268067 * 2 ^ 59
def prefixEnd_3268067 : Nat := 4983230072969 + 3 ^ 40 * 3268067 * 2
def baseEnd_3268067 : Nat := 1118726121398113604355293

theorem tailTrace_3268067 : CollatzResearch.WordTrace tailWord_3268067 prefixEnd_3268067 1118726121398113604355293 := by
  unfold tailWord_3268067
  simp only [CollatzResearch.WordTrace]
  refine ⟨119196195851358875252802455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79464130567572583501868303 119196195851358875252802455)
  ·
    refine ⟨178794293777038312879203683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119196195851358875252802455 178794293777038312879203683)
    ·
      refine ⟨268191440665557469318805525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178794293777038312879203683 268191440665557469318805525)
      ·
        refine ⟨12571473781198006374319009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 268191440665557469318805525 12571473781198006374319009)
        ·
          refine ⟨9428605335898504780739257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12571473781198006374319009 9428605335898504780739257)
          ·
            refine ⟨7071454001923878585554443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9428605335898504780739257 7071454001923878585554443)
            ·
              refine ⟨10607181002885817878331665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7071454001923878585554443 10607181002885817878331665)
              ·
                refine ⟨7955385752164363408748749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10607181002885817878331665 7955385752164363408748749)
                ·
                  refine ⟨2983269657061636278280781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7955385752164363408748749 2983269657061636278280781)
                  ·
                    refine ⟨1118726121398113604355293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2983269657061636278280781 1118726121398113604355293)
                    ·
                      rfl

theorem cell22_3268067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 2, 3, 3].length) (baseStart_3268067 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3268067 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3268067 prefixEnd_3268067 := by exact prefixLift 3268067
  have htrace : WordTrace (prefixWord ++ tailWord_3268067) baseStart_3268067 baseEnd_3268067 := by
    simpa [prefixWord, tailWord_3268067, baseEnd_3268067] using wordTrace_append hprefix tailTrace_3268067
  have hstable : (prefixWord ++ tailWord_3268067).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268067).length < 2 ^ (prefixWord ++ tailWord_3268067).sum := by decide
  have hdescent : baseEnd_3268067 < baseStart_3268067 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268125 : List Nat := [1, 4, 2, 2, 1, 1, 1, 4, 6]
def baseStart_3268125 : Nat := 118140960795 + 3268125 * 2 ^ 59
def prefixEnd_3268125 : Nat := 4983230072969 + 3 ^ 40 * 3268125 * 2
def baseEnd_3268125 : Nat := 372915325327806928801705

theorem tailTrace_3268125 : CollatzResearch.WordTrace tailWord_3268125 prefixEnd_3268125 372915325327806928801705 := by
  unfold tailWord_3268125
  simp only [CollatzResearch.WordTrace]
  refine ⟨119198311285148751158413829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79465540856765834105609219 119198311285148751158413829)
  ·
    refine ⟨22349683365965390842202593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119198311285148751158413829 22349683365965390842202593)
    ·
      refine ⟨16762262524474043131651945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22349683365965390842202593 16762262524474043131651945)
      ·
        refine ⟨12571696893355532348738959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16762262524474043131651945 12571696893355532348738959)
        ·
          refine ⟨18857545340033298523108439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12571696893355532348738959 18857545340033298523108439)
          ·
            refine ⟨28286318010049947784662659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18857545340033298523108439 28286318010049947784662659)
            ·
              refine ⟨42429477015074921676993989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28286318010049947784662659 42429477015074921676993989)
              ·
                refine ⟨7955526940326547814436373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42429477015074921676993989 7955526940326547814436373)
                ·
                  refine ⟨372915325327806928801705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7955526940326547814436373 372915325327806928801705)
                  ·
                    rfl

theorem cell22_3268125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_3268125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3268125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3268125 prefixEnd_3268125 := by exact prefixLift 3268125
  have htrace : WordTrace (prefixWord ++ tailWord_3268125) baseStart_3268125 baseEnd_3268125 := by
    simpa [prefixWord, tailWord_3268125, baseEnd_3268125] using wordTrace_append hprefix tailTrace_3268125
  have hstable : (prefixWord ++ tailWord_3268125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268125).length < 2 ^ (prefixWord ++ tailWord_3268125).sum := by decide
  have hdescent : baseEnd_3268125 < baseStart_3268125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268159 : List Nat := [1, 1, 2, 2, 3, 4, 3, 2, 4]
def baseStart_3268159 : Nat := 118140960795 + 3268159 * 2 ^ 59
def prefixEnd_3268159 : Nat := 4983230072969 + 3 ^ 40 * 3268159 * 2
def baseEnd_3268159 : Nat := 372919204959418677018337

theorem tailTrace_3268159 : CollatzResearch.WordTrace tailWord_3268159 prefixEnd_3268159 372919204959418677018337 := by
  unfold tailWord_3268159
  simp only [CollatzResearch.WordTrace]
  refine ⟨119199551367025574965151531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79466367578017049976767687 119199551367025574965151531)
  ·
    refine ⟨178799327050538362447727297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119199551367025574965151531 178799327050538362447727297)
    ·
      refine ⟨134099495287903771835795473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178799327050538362447727297 134099495287903771835795473)
      ·
        refine ⟨100574621465927828876846605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134099495287903771835795473 100574621465927828876846605)
        ·
          refine ⟨37715483049722935828817477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100574621465927828876846605 37715483049722935828817477)
          ·
            refine ⟨7071653071823050467903277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37715483049722935828817477 7071653071823050467903277)
            ·
              refine ⟨2651869901933643925463729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7071653071823050467903277 2651869901933643925463729)
              ·
                refine ⟨1988902426450232944097797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2651869901933643925463729 1988902426450232944097797)
                ·
                  refine ⟨372919204959418677018337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1988902426450232944097797 372919204959418677018337)
                  ·
                    rfl

theorem cell22_3268159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 3, 2, 4].length) (baseStart_3268159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3268159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3268159 prefixEnd_3268159 := by exact prefixLift 3268159
  have htrace : WordTrace (prefixWord ++ tailWord_3268159) baseStart_3268159 baseEnd_3268159 := by
    simpa [prefixWord, tailWord_3268159, baseEnd_3268159] using wordTrace_append hprefix tailTrace_3268159
  have hstable : (prefixWord ++ tailWord_3268159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268159).length < 2 ^ (prefixWord ++ tailWord_3268159).sum := by decide
  have hdescent : baseEnd_3268159 < baseStart_3268159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268170 : List Nat := [3, 1, 2, 1, 1, 3, 4, 7]
def baseStart_3268170 : Nat := 118140960795 + 3268170 * 2 ^ 59
def prefixEnd_3268170 : Nat := 4983230072969 + 3 ^ 40 * 3268170 * 2
def baseEnd_3268170 : Nat := 124306820044783963225553

theorem tailTrace_3268170 : CollatzResearch.WordTrace tailWord_3268170 prefixEnd_3268170 124306820044783963225553 := by
  unfold tailWord_3268170
  simp only [CollatzResearch.WordTrace]
  refine ⟨29799988142496430960950491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79466635046657149229201309 29799988142496430960950491)
  ·
    refine ⟨44699982213744646441425737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29799988142496430960950491 44699982213744646441425737)
    ·
      refine ⟨33524986660308484831069303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44699982213744646441425737 33524986660308484831069303)
      ·
        refine ⟨50287479990462727246603955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33524986660308484831069303 50287479990462727246603955)
        ·
          refine ⟨75431219985694090869905933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50287479990462727246603955 75431219985694090869905933)
          ·
            refine ⟨28286707494635284076214725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75431219985694090869905933 28286707494635284076214725)
            ·
              refine ⟨5303757655244115764290261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28286707494635284076214725 5303757655244115764290261)
              ·
                refine ⟨124306820044783963225553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5303757655244115764290261 124306820044783963225553)
                ·
                  rfl

theorem cell22_3268170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 7].length) (baseStart_3268170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3268170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3268170 prefixEnd_3268170 := by exact prefixLift 3268170
  have htrace : WordTrace (prefixWord ++ tailWord_3268170) baseStart_3268170 baseEnd_3268170 := by
    simpa [prefixWord, tailWord_3268170, baseEnd_3268170] using wordTrace_append hprefix tailTrace_3268170
  have hstable : (prefixWord ++ tailWord_3268170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268170).length < 2 ^ (prefixWord ++ tailWord_3268170).sum := by decide
  have hdescent : baseEnd_3268170 < baseStart_3268170 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268219 : List Nat := [1, 1, 1, 1, 1, 4, 5, 4, 1, 3]
def baseStart_3268219 : Nat := 118140960795 + 3268219 * 2 ^ 59
def prefixEnd_3268219 : Nat := 4983230072969 + 3 ^ 40 * 3268219 * 2
def baseEnd_3268219 : Nat := 1118778154104435874554827

theorem tailTrace_3268219 : CollatzResearch.WordTrace tailWord_3268219 prefixEnd_3268219 1118778154104435874554827 := by
  unfold tailWord_3268219
  simp only [CollatzResearch.WordTrace]
  refine ⟨119201739746808205212335711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79467826497872136808223807 119201739746808205212335711)
  ·
    refine ⟨178802609620212307818503567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119201739746808205212335711 178802609620212307818503567)
    ·
      refine ⟨268203914430318461727755351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178802609620212307818503567 268203914430318461727755351)
      ·
        refine ⟨402305871645477692591633027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268203914430318461727755351 402305871645477692591633027)
        ·
          refine ⟨603458807468216538887449541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402305871645477692591633027 603458807468216538887449541)
          ·
            refine ⟨113148526400290601041396789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 603458807468216538887449541 113148526400290601041396789)
            ·
              refine ⟨10607674350027243847630949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 113148526400290601041396789 10607674350027243847630949)
              ·
                refine ⟨1988938940630108221430803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10607674350027243847630949 1988938940630108221430803)
                ·
                  refine ⟨2983408410945162332146205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1988938940630108221430803 2983408410945162332146205)
                  ·
                    refine ⟨1118778154104435874554827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2983408410945162332146205 1118778154104435874554827)
                    ·
                      rfl

theorem cell22_3268219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 4, 1, 3].length) (baseStart_3268219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3268219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3268219 prefixEnd_3268219 := by exact prefixLift 3268219
  have htrace : WordTrace (prefixWord ++ tailWord_3268219) baseStart_3268219 baseEnd_3268219 := by
    simpa [prefixWord, tailWord_3268219, baseEnd_3268219] using wordTrace_append hprefix tailTrace_3268219
  have hstable : (prefixWord ++ tailWord_3268219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268219).length < 2 ^ (prefixWord ++ tailWord_3268219).sum := by decide
  have hdescent : baseEnd_3268219 < baseStart_3268219 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268384 : List Nat := [2, 1, 1, 5, 1, 1, 4, 2, 5]
def baseStart_3268384 : Nat := 118140960795 + 3268384 * 2 ^ 59
def prefixEnd_3268384 : Nat := 4983230072969 + 3 ^ 40 * 3268384 * 2
def baseEnd_3268384 : Nat := 372944878992143481393107

theorem tailTrace_3268384 : CollatzResearch.WordTrace tailWord_3268384 prefixEnd_3268384 372944878992143481393107 := by
  unfold tailWord_3268384
  simp only [CollatzResearch.WordTrace]
  refine ⟨59603878895605219196046103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79471838527473625594728137 59603878895605219196046103)
  ·
    refine ⟨89405818343407828794069155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59603878895605219196046103 89405818343407828794069155)
    ·
      refine ⟨134108727515111743191103733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89405818343407828794069155 134108727515111743191103733)
      ·
        refine ⟨12572693204541725924165975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134108727515111743191103733 12572693204541725924165975)
        ·
          refine ⟨18859039806812588886248963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12572693204541725924165975 18859039806812588886248963)
          ·
            refine ⟨28288559710218883329373445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18859039806812588886248963 28288559710218883329373445)
            ·
              refine ⟨5304104945666040624257521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28288559710218883329373445 5304104945666040624257521)
              ·
                refine ⟨3978078709249530468193141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5304104945666040624257521 3978078709249530468193141)
                ·
                  refine ⟨372944878992143481393107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3978078709249530468193141 372944878992143481393107)
                  ·
                    rfl

theorem cell22_3268384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 2, 5].length) (baseStart_3268384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3268384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3268384 prefixEnd_3268384 := by exact prefixLift 3268384
  have htrace : WordTrace (prefixWord ++ tailWord_3268384) baseStart_3268384 baseEnd_3268384 := by
    simpa [prefixWord, tailWord_3268384, baseEnd_3268384] using wordTrace_append hprefix tailTrace_3268384
  have hstable : (prefixWord ++ tailWord_3268384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268384).length < 2 ^ (prefixWord ++ tailWord_3268384).sum := by decide
  have hdescent : baseEnd_3268384 < baseStart_3268384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268388 : List Nat := [2, 3, 1, 3, 2, 2, 1, 4, 1, 3]
def baseStart_3268388 : Nat := 118140960795 + 3268388 * 2 ^ 59
def prefixEnd_3268388 : Nat := 4983230072969 + 3 ^ 40 * 3268388 * 2
def baseEnd_3268388 : Nat := 1118836006258175767079309

theorem tailTrace_3268388 : CollatzResearch.WordTrace tailWord_3268388 prefixEnd_3268388 1118836006258175767079309 := by
  unfold tailWord_3268388
  simp only [CollatzResearch.WordTrace]
  refine ⟨59603951841597973537618909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79471935788797298050158545 59603951841597973537618909)
  ·
    refine ⟨22351481940599240076607091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59603951841597973537618909 22351481940599240076607091)
    ·
      refine ⟨33527222910898860114910637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22351481940599240076607091 33527222910898860114910637)
      ·
        refine ⟨12572708591587072543091489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33527222910898860114910637 12572708591587072543091489)
        ·
          refine ⟨9429531443690304407318617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12572708591587072543091489 9429531443690304407318617)
          ·
            refine ⟨7072148582767728305488963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9429531443690304407318617 7072148582767728305488963)
            ·
              refine ⟨10608222874151592458233445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7072148582767728305488963 10608222874151592458233445)
              ·
                refine ⟨1989041788903423585918771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10608222874151592458233445 1989041788903423585918771)
                ·
                  refine ⟨2983562683355135378878157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1989041788903423585918771 2983562683355135378878157)
                  ·
                    refine ⟨1118836006258175767079309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2983562683355135378878157 1118836006258175767079309)
                    ·
                      rfl

theorem cell22_3268388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 4, 1, 3].length) (baseStart_3268388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3268388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3268388 prefixEnd_3268388 := by exact prefixLift 3268388
  have htrace : WordTrace (prefixWord ++ tailWord_3268388) baseStart_3268388 baseEnd_3268388 := by
    simpa [prefixWord, tailWord_3268388, baseEnd_3268388] using wordTrace_append hprefix tailTrace_3268388
  have hstable : (prefixWord ++ tailWord_3268388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268388).length < 2 ^ (prefixWord ++ tailWord_3268388).sum := by decide
  have hdescent : baseEnd_3268388 < baseStart_3268388 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268412 : List Nat := [2, 2, 2, 2, 1, 1, 3, 1, 8]
def baseStart_3268412 : Nat := 118140960795 + 3268412 * 2 ^ 59
def prefixEnd_3268412 : Nat := 4983230072969 + 3 ^ 40 * 3268412 * 2
def baseEnd_3268412 : Nat := 372948073982882568159745

theorem tailTrace_3268412 : CollatzResearch.WordTrace tailWord_3268412 prefixEnd_3268412 372948073982882568159745 := by
  unfold tailWord_3268412
  simp only [CollatzResearch.WordTrace]
  refine ⟨59604389517554499587055745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79472519356739332782740993 59604389517554499587055745)
  ·
    refine ⟨44703292138165874690291809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59604389517554499587055745 44703292138165874690291809)
    ·
      refine ⟨33527469103624406017718857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44703292138165874690291809 33527469103624406017718857)
      ·
        refine ⟨25145601827718304513289143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33527469103624406017718857 25145601827718304513289143)
        ·
          refine ⟨37718402741577456769933715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25145601827718304513289143 37718402741577456769933715)
          ·
            refine ⟨56577604112366185154900573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37718402741577456769933715 56577604112366185154900573)
            ·
              refine ⟨21216601542137319433087715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56577604112366185154900573 21216601542137319433087715)
              ·
                refine ⟨31824902313205979149631573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21216601542137319433087715 31824902313205979149631573)
                ·
                  refine ⟨372948073982882568159745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31824902313205979149631573 372948073982882568159745)
                  ·
                    rfl

theorem cell22_3268412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 1, 8].length) (baseStart_3268412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3268412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3268412 prefixEnd_3268412 := by exact prefixLift 3268412
  have htrace : WordTrace (prefixWord ++ tailWord_3268412) baseStart_3268412 baseEnd_3268412 := by
    simpa [prefixWord, tailWord_3268412, baseEnd_3268412] using wordTrace_append hprefix tailTrace_3268412
  have hstable : (prefixWord ++ tailWord_3268412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268412).length < 2 ^ (prefixWord ++ tailWord_3268412).sum := by decide
  have hdescent : baseEnd_3268412 < baseStart_3268412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268422 : List Nat := [6, 1, 1, 2, 1, 2, 2, 3, 1, 3]
def baseStart_3268422 : Nat := 118140960795 + 3268422 * 2 ^ 59
def prefixEnd_3268422 : Nat := 4983230072969 + 3 ^ 40 * 3268422 * 2
def baseEnd_3268422 : Nat := 1118847645153011011729205

theorem tailTrace_3268422 : CollatzResearch.WordTrace tailWord_3268422 prefixEnd_3268422 1118847645153011011729205 := by
  unfold tailWord_3268422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3725285742658524090061735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 79472762510048513921317013 3725285742658524090061735)
  ·
    refine ⟨5587928613987786135092603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3725285742658524090061735 5587928613987786135092603)
    ·
      refine ⟨8381892920981679202638905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5587928613987786135092603 8381892920981679202638905)
      ·
        refine ⟨6286419690736259401979179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8381892920981679202638905 6286419690736259401979179)
        ·
          refine ⟨9429629536104389102968769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6286419690736259401979179 9429629536104389102968769)
          ·
            refine ⟨7072222152078291827226577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9429629536104389102968769 7072222152078291827226577)
            ·
              refine ⟨5304166614058718870419933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7072222152078291827226577 5304166614058718870419933)
              ·
                refine ⟨1989062480272019576407475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5304166614058718870419933 1989062480272019576407475)
                ·
                  refine ⟨2983593720408029364611213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1989062480272019576407475 2983593720408029364611213)
                  ·
                    refine ⟨1118847645153011011729205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2983593720408029364611213 1118847645153011011729205)
                    ·
                      rfl

theorem cell22_3268422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_3268422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3268422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3268422 prefixEnd_3268422 := by exact prefixLift 3268422
  have htrace : WordTrace (prefixWord ++ tailWord_3268422) baseStart_3268422 baseEnd_3268422 := by
    simpa [prefixWord, tailWord_3268422, baseEnd_3268422] using wordTrace_append hprefix tailTrace_3268422
  have hstable : (prefixWord ++ tailWord_3268422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268422).length < 2 ^ (prefixWord ++ tailWord_3268422).sum := by decide
  have hdescent : baseEnd_3268422 < baseStart_3268422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268461 : List Nat := [1, 5, 1, 1, 1, 1, 2, 5, 2, 3]
def baseStart_3268461 : Nat := 118140960795 + 3268461 * 2 ^ 59
def prefixEnd_3268461 : Nat := 4983230072969 + 3 ^ 40 * 3268461 * 2
def baseEnd_3268461 : Nat := 1118860995650027910004085

theorem tailTrace_3268461 : CollatzResearch.WordTrace tailWord_3268461 prefixEnd_3268461 1118860995650027910004085 := by
  unfold tailWord_3268461
  simp only [CollatzResearch.WordTrace]
  refine ⟨119210566211931480542645237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79473710807954320361763491 119210566211931480542645237)
  ·
    refine ⟨11175990582368576300872991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119210566211931480542645237 11175990582368576300872991)
    ·
      refine ⟨16763985873552864451309487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11175990582368576300872991 16763985873552864451309487)
      ·
        refine ⟨25145978810329296676964231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16763985873552864451309487 25145978810329296676964231)
        ·
          refine ⟨37718968215493945015446347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25145978810329296676964231 37718968215493945015446347)
          ·
            refine ⟨56578452323240917523169521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37718968215493945015446347 56578452323240917523169521)
            ·
              refine ⟨42433839242430688142377141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56578452323240917523169521 42433839242430688142377141)
              ·
                refine ⟨3978172428977877013347857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42433839242430688142377141 3978172428977877013347857)
                ·
                  refine ⟨2983629321733407760010893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3978172428977877013347857 2983629321733407760010893)
                  ·
                    refine ⟨1118860995650027910004085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2983629321733407760010893 1118860995650027910004085)
                    ·
                      rfl

theorem cell22_3268461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_3268461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3268461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3268461 prefixEnd_3268461 := by exact prefixLift 3268461
  have htrace : WordTrace (prefixWord ++ tailWord_3268461) baseStart_3268461 baseEnd_3268461 := by
    simpa [prefixWord, tailWord_3268461, baseEnd_3268461] using wordTrace_append hprefix tailTrace_3268461
  have hstable : (prefixWord ++ tailWord_3268461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268461).length < 2 ^ (prefixWord ++ tailWord_3268461).sum := by decide
  have hdescent : baseEnd_3268461 < baseStart_3268461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268474 : List Nat := [3, 1, 1, 1, 1, 1, 8, 6]
def baseStart_3268474 : Nat := 118140960795 + 3268474 * 2 ^ 59
def prefixEnd_3268474 : Nat := 4983230072969 + 3 ^ 40 * 3268474 * 2
def baseEnd_3268474 : Nat := 124318382868411134381005

theorem tailTrace_3268474 : CollatzResearch.WordTrace tailWord_3268474 prefixEnd_3268474 124318382868411134381005 := by
  unfold tailWord_3268474
  simp only [CollatzResearch.WordTrace]
  refine ⟨29802760090221095940717119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79474026907256255841912317 29802760090221095940717119)
  ·
    refine ⟨44704140135331643911075679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29802760090221095940717119 44704140135331643911075679)
    ·
      refine ⟨67056210202997465866613519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44704140135331643911075679 67056210202997465866613519)
      ·
        refine ⟨100584315304496198799920279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67056210202997465866613519 100584315304496198799920279)
        ·
          refine ⟨150876472956744298199880419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100584315304496198799920279 150876472956744298199880419)
          ·
            refine ⟨226314709435116447299820629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150876472956744298199880419 226314709435116447299820629)
            ·
              refine ⟨2652125501192770866794773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 226314709435116447299820629 2652125501192770866794773)
              ·
                refine ⟨124318382868411134381005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2652125501192770866794773 124318382868411134381005)
                ·
                  rfl

theorem cell22_3268474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 6].length) (baseStart_3268474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3268474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3268474 prefixEnd_3268474 := by exact prefixLift 3268474
  have htrace : WordTrace (prefixWord ++ tailWord_3268474) baseStart_3268474 baseEnd_3268474 := by
    simpa [prefixWord, tailWord_3268474, baseEnd_3268474] using wordTrace_append hprefix tailTrace_3268474
  have hstable : (prefixWord ++ tailWord_3268474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268474).length < 2 ^ (prefixWord ++ tailWord_3268474).sum := by decide
  have hdescent : baseEnd_3268474 < baseStart_3268474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268478 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 4, 3]
def baseStart_3268478 : Nat := 118140960795 + 3268478 * 2 ^ 59
def prefixEnd_3268478 : Nat := 4983230072969 + 3 ^ 40 * 3268478 * 2
def baseEnd_3268478 : Nat := 1118866815097445532329033

theorem tailTrace_3268478 : CollatzResearch.WordTrace tailWord_3268478 prefixEnd_3268478 1118866815097445532329033 := by
  unfold tailWord_3268478
  simp only [CollatzResearch.WordTrace]
  refine ⟨14901398281608736555751761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79474124168579928297342725 14901398281608736555751761)
  ·
    refine ⟨11176048711206552416813821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14901398281608736555751761 11176048711206552416813821)
    ·
      refine ⟨4191018266702457156305183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11176048711206552416813821 4191018266702457156305183)
      ·
        refine ⟨6286527400053685734457775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4191018266702457156305183 6286527400053685734457775)
        ·
          refine ⟨9429791100080528601686663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6286527400053685734457775 9429791100080528601686663)
          ·
            refine ⟨14144686650120792902529995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9429791100080528601686663 14144686650120792902529995)
            ·
              refine ⟨21217029975181189353794993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14144686650120792902529995 21217029975181189353794993)
              ·
                refine ⟨15912772481385892015346245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21217029975181189353794993 15912772481385892015346245)
                ·
                  refine ⟨2983644840259854752877421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15912772481385892015346245 2983644840259854752877421)
                  ·
                    refine ⟨1118866815097445532329033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2983644840259854752877421 1118866815097445532329033)
                    ·
                      rfl

theorem cell22_3268478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_3268478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3268478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3268478 prefixEnd_3268478 := by exact prefixLift 3268478
  have htrace : WordTrace (prefixWord ++ tailWord_3268478) baseStart_3268478 baseEnd_3268478 := by
    simpa [prefixWord, tailWord_3268478, baseEnd_3268478] using wordTrace_append hprefix tailTrace_3268478
  have hstable : (prefixWord ++ tailWord_3268478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268478).length < 2 ^ (prefixWord ++ tailWord_3268478).sum := by decide
  have hdescent : baseEnd_3268478 < baseStart_3268478 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268609 : List Nat := [1, 2, 4, 1, 2, 1, 11]
def baseStart_3268609 : Nat := 118140960795 + 3268609 * 2 ^ 59
def prefixEnd_3268609 : Nat := 4983230072969 + 3 ^ 40 * 3268609 * 2
def baseEnd_3268609 : Nat := 41441172558318698418653

theorem tailTrace_3268609 : CollatzResearch.WordTrace tailWord_3268609 prefixEnd_3268609 41441172558318698418653 := by
  unfold tailWord_3268609
  simp only [CollatzResearch.WordTrace]
  refine ⟨119215964215395301819032881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79477309476930201212688587 119215964215395301819032881)
  ·
    refine ⟨89411973161546476364274661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119215964215395301819032881 89411973161546476364274661)
    ·
      refine ⟨16764744967789964318301499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89411973161546476364274661 16764744967789964318301499)
      ·
        refine ⟨25147117451684946477452249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16764744967789964318301499 25147117451684946477452249)
        ·
          refine ⟨18860338088763709858089187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25147117451684946477452249 18860338088763709858089187)
          ·
            refine ⟨28290507133145564787133781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18860338088763709858089187 28290507133145564787133781)
            ·
              refine ⟨41441172558318698418653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 28290507133145564787133781 41441172558318698418653)
              ·
                rfl

theorem cell22_3268609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 11].length) (baseStart_3268609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3268609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3268609 prefixEnd_3268609 := by exact prefixLift 3268609
  have htrace : WordTrace (prefixWord ++ tailWord_3268609) baseStart_3268609 baseEnd_3268609 := by
    simpa [prefixWord, tailWord_3268609, baseEnd_3268609] using wordTrace_append hprefix tailTrace_3268609
  have hstable : (prefixWord ++ tailWord_3268609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268609).length < 2 ^ (prefixWord ++ tailWord_3268609).sum := by decide
  have hdescent : baseEnd_3268609 < baseStart_3268609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268613 : List Nat := [1, 3, 1, 1, 2, 4, 3, 2, 2, 3]
def baseStart_3268613 : Nat := 118140960795 + 3268613 * 2 ^ 59
def prefixEnd_3268613 : Nat := 4983230072969 + 3 ^ 40 * 3268613 * 2
def baseEnd_3268613 : Nat := 1118913028356350180203619

theorem tailTrace_3268613 : CollatzResearch.WordTrace tailWord_3268613 prefixEnd_3268613 1118913028356350180203619 := by
  unfold tailWord_3268613
  simp only [CollatzResearch.WordTrace]
  refine ⟨119216110107380810502178493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79477406738253873668118995 119216110107380810502178493)
  ·
    refine ⟨44706041290267803938316935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119216110107380810502178493 44706041290267803938316935)
    ·
      refine ⟨67059061935401705907475403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44706041290267803938316935 67059061935401705907475403)
      ·
        refine ⟨100588592903102558861213105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67059061935401705907475403 100588592903102558861213105)
        ·
          refine ⟨75441444677326919145909829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100588592903102558861213105 75441444677326919145909829)
          ·
            refine ⟨14145270876998797339858093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75441444677326919145909829 14145270876998797339858093)
            ·
              refine ⟨5304476578874549002446785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14145270876998797339858093 5304476578874549002446785)
              ·
                refine ⟨3978357434155911751835089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5304476578874549002446785 3978357434155911751835089)
                ·
                  refine ⟨2983768075616933813876317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3978357434155911751835089 2983768075616933813876317)
                  ·
                    refine ⟨1118913028356350180203619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2983768075616933813876317 1118913028356350180203619)
                    ·
                      rfl

theorem cell22_3268613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 3].length) (baseStart_3268613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3268613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3268613 prefixEnd_3268613 := by exact prefixLift 3268613
  have htrace : WordTrace (prefixWord ++ tailWord_3268613) baseStart_3268613 baseEnd_3268613 := by
    simpa [prefixWord, tailWord_3268613, baseEnd_3268613] using wordTrace_append hprefix tailTrace_3268613
  have hstable : (prefixWord ++ tailWord_3268613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268613).length < 2 ^ (prefixWord ++ tailWord_3268613).sum := by decide
  have hdescent : baseEnd_3268613 < baseStart_3268613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268660 : List Nat := [2, 5, 1, 2, 3, 1, 8]
def baseStart_3268660 : Nat := 118140960795 + 3268660 * 2 ^ 59
def prefixEnd_3268660 : Nat := 4983230072969 + 3 ^ 40 * 3268660 * 2
def baseEnd_3268660 : Nat := 41441819163587323121425

theorem tailTrace_3268660 : CollatzResearch.WordTrace tailWord_3268660 prefixEnd_3268660 41441819163587323121425 := by
  unfold tailWord_3268660
  simp only [CollatzResearch.WordTrace]
  refine ⟨59608912169105268764569717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79478549558807025019426289 59608912169105268764569717)
  ·
    refine ⟨5588335515853618946678411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 59608912169105268764569717 5588335515853618946678411)
    ·
      refine ⟨8382503273780428420017617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5588335515853618946678411 8382503273780428420017617)
      ·
        refine ⟨6286877455335321315013213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8382503273780428420017617 6286877455335321315013213)
        ·
          refine ⟨2357579045750745493129955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6286877455335321315013213 2357579045750745493129955)
          ·
            refine ⟨3536368568626118239694933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2357579045750745493129955 3536368568626118239694933)
            ·
              refine ⟨41441819163587323121425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3536368568626118239694933 41441819163587323121425)
              ·
                rfl

theorem cell22_3268660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 3, 1, 8].length) (baseStart_3268660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3268660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3268660 prefixEnd_3268660 := by exact prefixLift 3268660
  have htrace : WordTrace (prefixWord ++ tailWord_3268660) baseStart_3268660 baseEnd_3268660 := by
    simpa [prefixWord, tailWord_3268660, baseEnd_3268660] using wordTrace_append hprefix tailTrace_3268660
  have hstable : (prefixWord ++ tailWord_3268660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268660).length < 2 ^ (prefixWord ++ tailWord_3268660).sum := by decide
  have hdescent : baseEnd_3268660 < baseStart_3268660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268812 : List Nat := [2, 2, 1, 6, 1, 2, 2, 6]
def baseStart_3268812 : Nat := 118140960795 + 3268812 * 2 ^ 59
def prefixEnd_3268812 : Nat := 4983230072969 + 3 ^ 40 * 3268812 * 2
def baseEnd_3268812 : Nat := 124331238902575554942001

theorem tailTrace_3268812 : CollatzResearch.WordTrace tailWord_3268812 prefixEnd_3268812 124331238902575554942001 := by
  unfold tailWord_3268812
  simp only [CollatzResearch.WordTrace]
  refine ⟨59611684116829933744336345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79482245489106578325781793 59611684116829933744336345)
  ·
    refine ⟨44708763087622450308252259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59611684116829933744336345 44708763087622450308252259)
    ·
      refine ⟨67063144631433675462378389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44708763087622450308252259 67063144631433675462378389)
      ·
        refine ⟨3143584904598453537298987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67063144631433675462378389 3143584904598453537298987)
        ·
          refine ⟨4715377356897680305948481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3143584904598453537298987 4715377356897680305948481)
          ·
            refine ⟨3536533017673260229461361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4715377356897680305948481 3536533017673260229461361)
            ·
              refine ⟨2652399763254945172096021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3536533017673260229461361 2652399763254945172096021)
              ·
                refine ⟨124331238902575554942001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2652399763254945172096021 124331238902575554942001)
                ·
                  rfl

theorem cell22_3268812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 6].length) (baseStart_3268812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3268812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3268812 prefixEnd_3268812 := by exact prefixLift 3268812
  have htrace : WordTrace (prefixWord ++ tailWord_3268812) baseStart_3268812 baseEnd_3268812 := by
    simpa [prefixWord, tailWord_3268812, baseEnd_3268812] using wordTrace_append hprefix tailTrace_3268812
  have hstable : (prefixWord ++ tailWord_3268812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268812).length < 2 ^ (prefixWord ++ tailWord_3268812).sum := by decide
  have hdescent : baseEnd_3268812 < baseStart_3268812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268883 : List Nat := [1, 1, 1, 2, 1, 3, 1, 3, 6, 3]
def baseStart_3268883 : Nat := 118140960795 + 3268883 * 2 ^ 59
def prefixEnd_3268883 : Nat := 4983230072969 + 3 ^ 40 * 3268883 * 2
def baseEnd_3268883 : Nat := 1119005454874159475952791

theorem tailTrace_3268883 : CollatzResearch.WordTrace tailWord_3268883 prefixEnd_3268883 1119005454874159475952791 := by
  unfold tailWord_3268883
  simp only [CollatzResearch.WordTrace]
  refine ⟨119225957816402646614507303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79483971877601764409671535 119225957816402646614507303)
  ·
    refine ⟨178838936724603969921760955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119225957816402646614507303 178838936724603969921760955)
    ·
      refine ⟨268258405086905954882641433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178838936724603969921760955 268258405086905954882641433)
      ·
        refine ⟨201193803815179466161981075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268258405086905954882641433 201193803815179466161981075)
        ·
          refine ⟨301790705722769199242971613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201193803815179466161981075 301790705722769199242971613)
          ·
            refine ⟨113171514646038449716114355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 301790705722769199242971613 113171514646038449716114355)
            ·
              refine ⟨169757271969057674574171533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113171514646038449716114355 169757271969057674574171533)
              ·
                refine ⟨63658976988396627965314325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169757271969057674574171533 63658976988396627965314325)
                ·
                  refine ⟨2984014546331091935874109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 63658976988396627965314325 2984014546331091935874109)
                  ·
                    refine ⟨1119005454874159475952791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2984014546331091935874109 1119005454874159475952791)
                    ·
                      rfl

theorem cell22_3268883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 3, 6, 3].length) (baseStart_3268883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3268883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3268883 prefixEnd_3268883 := by exact prefixLift 3268883
  have htrace : WordTrace (prefixWord ++ tailWord_3268883) baseStart_3268883 baseEnd_3268883 := by
    simpa [prefixWord, tailWord_3268883, baseEnd_3268883] using wordTrace_append hprefix tailTrace_3268883
  have hstable : (prefixWord ++ tailWord_3268883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268883).length < 2 ^ (prefixWord ++ tailWord_3268883).sum := by decide
  have hdescent : baseEnd_3268883 < baseStart_3268883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268887 : List Nat := [1, 1, 3, 4, 1, 3, 3, 1, 1, 4]
def baseStart_3268887 : Nat := 118140960795 + 3268887 * 2 ^ 59
def prefixEnd_3268887 : Nat := 4983230072969 + 3 ^ 40 * 3268887 * 2
def baseEnd_3268887 : Nat := 1119006824155904798852779

theorem tailTrace_3268887 : CollatzResearch.WordTrace tailWord_3268887 prefixEnd_3268887 1119006824155904798852779 := by
  unfold tailWord_3268887
  simp only [CollatzResearch.WordTrace]
  refine ⟨119226103708388155297652915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79484069138925436865101943 119226103708388155297652915)
  ·
    refine ⟨178839155562582232946479373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119226103708388155297652915 178839155562582232946479373)
    ·
      refine ⟨67064683335968337354929765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178839155562582232946479373 67064683335968337354929765)
      ·
        refine ⟨12574628125494063254049331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67064683335968337354929765 12574628125494063254049331)
        ·
          refine ⟨18861942188241094881073997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12574628125494063254049331 18861942188241094881073997)
          ·
            refine ⟨7073228320590410580402749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18861942188241094881073997 7073228320590410580402749)
            ·
              refine ⟨2652460620221403967651031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7073228320590410580402749 2652460620221403967651031)
              ·
                refine ⟨3978690930332105951476547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2652460620221403967651031 3978690930332105951476547)
                ·
                  refine ⟨5968036395498158927214821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3978690930332105951476547 5968036395498158927214821)
                  ·
                    refine ⟨1119006824155904798852779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5968036395498158927214821 1119006824155904798852779)
                    ·
                      rfl

theorem cell22_3268887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 3, 1, 1, 4].length) (baseStart_3268887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3268887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3268887 prefixEnd_3268887 := by exact prefixLift 3268887
  have htrace : WordTrace (prefixWord ++ tailWord_3268887) baseStart_3268887 baseEnd_3268887 := by
    simpa [prefixWord, tailWord_3268887, baseEnd_3268887] using wordTrace_append hprefix tailTrace_3268887
  have hstable : (prefixWord ++ tailWord_3268887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268887).length < 2 ^ (prefixWord ++ tailWord_3268887).sum := by decide
  have hdescent : baseEnd_3268887 < baseStart_3268887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268932 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 1, 6]
def baseStart_3268932 : Nat := 118140960795 + 3268932 * 2 ^ 59
def prefixEnd_3268932 : Nat := 4983230072969 + 3 ^ 40 * 3268932 * 2
def baseEnd_3268932 : Nat := 1119022228575539681477641

theorem tailTrace_3268932 : CollatzResearch.WordTrace tailWord_3268932 prefixEnd_3268932 1119022228575539681477641 := by
  unfold tailWord_3268932
  simp only [CollatzResearch.WordTrace]
  refine ⟨59613872496612563991520525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79485163328816751988694033 59613872496612563991520525)
  ·
    refine ⟨22355202186229711496820197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59613872496612563991520525 22355202186229711496820197)
    ·
      refine ⟨4191600409918070905653787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22355202186229711496820197 4191600409918070905653787)
      ·
        refine ⟨6287400614877106358480681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4191600409918070905653787 6287400614877106358480681)
        ·
          refine ⟨4715550461157829768860511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6287400614877106358480681 4715550461157829768860511)
          ·
            refine ⟨7073325691736744653290767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4715550461157829768860511 7073325691736744653290767)
            ·
              refine ⟨10609988537605116979936151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7073325691736744653290767 10609988537605116979936151)
              ·
                refine ⟨15914982806407675469904227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10609988537605116979936151 15914982806407675469904227)
                ·
                  refine ⟨23872474209611513204856341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15914982806407675469904227 23872474209611513204856341)
                  ·
                    refine ⟨1119022228575539681477641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23872474209611513204856341 1119022228575539681477641)
                    ·
                      rfl

theorem cell22_3268932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_3268932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3268932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3268932 prefixEnd_3268932 := by exact prefixLift 3268932
  have htrace : WordTrace (prefixWord ++ tailWord_3268932) baseStart_3268932 baseEnd_3268932 := by
    simpa [prefixWord, tailWord_3268932, baseEnd_3268932] using wordTrace_append hprefix tailTrace_3268932
  have hstable : (prefixWord ++ tailWord_3268932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268932).length < 2 ^ (prefixWord ++ tailWord_3268932).sum := by decide
  have hdescent : baseEnd_3268932 < baseStart_3268932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3268962 : List Nat := [3, 3, 2, 1, 1, 2, 1, 3, 3, 3]
def baseStart_3268962 : Nat := 118140960795 + 3268962 * 2 ^ 59
def prefixEnd_3268962 : Nat := 4983230072969 + 3 ^ 40 * 3268962 * 2
def baseEnd_3268962 : Nat := 1119032498188629603227549

theorem tailTrace_3268962 : CollatzResearch.WordTrace tailWord_3268962 prefixEnd_3268962 1119032498188629603227549 := by
  unfold tailWord_3268962
  simp only [CollatzResearch.WordTrace]
  refine ⟨29807209795779110776658285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79485892788744295404422093 29807209795779110776658285)
  ·
    refine ⟨11177703673417166541246857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29807209795779110776658285 11177703673417166541246857)
    ·
      refine ⟨8383277755062874905935143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11177703673417166541246857 8383277755062874905935143)
      ·
        refine ⟨12574916632594312358902715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8383277755062874905935143 12574916632594312358902715)
        ·
          refine ⟨18862374948891468538354073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12574916632594312358902715 18862374948891468538354073)
          ·
            refine ⟨14146781211668601403765555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18862374948891468538354073 14146781211668601403765555)
            ·
              refine ⟨21220171817502902105648333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14146781211668601403765555 21220171817502902105648333)
              ·
                refine ⟨7957564431563588289618125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21220171817502902105648333 7957564431563588289618125)
                ·
                  refine ⟨2984086661836345608606797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7957564431563588289618125 2984086661836345608606797)
                  ·
                    refine ⟨1119032498188629603227549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2984086661836345608606797 1119032498188629603227549)
                    ·
                      rfl

theorem cell22_3268962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 3, 3, 3].length) (baseStart_3268962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3268962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3268962 prefixEnd_3268962 := by exact prefixLift 3268962
  have htrace : WordTrace (prefixWord ++ tailWord_3268962) baseStart_3268962 baseEnd_3268962 := by
    simpa [prefixWord, tailWord_3268962, baseEnd_3268962] using wordTrace_append hprefix tailTrace_3268962
  have hstable : (prefixWord ++ tailWord_3268962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3268962).length < 2 ^ (prefixWord ++ tailWord_3268962).sum := by decide
  have hdescent : baseEnd_3268962 < baseStart_3268962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3268962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269033 : List Nat := [1, 2, 1, 1, 1, 1, 3, 3, 3, 6]
def baseStart_3269033 : Nat := 118140960795 + 3269033 * 2 ^ 59
def prefixEnd_3269033 : Nat := 4983230072969 + 3 ^ 40 * 3269033 * 2
def baseEnd_3269033 : Nat := 1119056802939609084702331

theorem tailTrace_3269033 : CollatzResearch.WordTrace tailWord_3269033 prefixEnd_3269033 1119056802939609084702331 := by
  unfold tailWord_3269033
  simp only [CollatzResearch.WordTrace]
  refine ⟨119231428765859222232467753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79487619177239481488311835 119231428765859222232467753)
  ·
    refine ⟨89423571574394416674350815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119231428765859222232467753 89423571574394416674350815)
    ·
      refine ⟨134135357361591625011526223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89423571574394416674350815 134135357361591625011526223)
      ·
        refine ⟨201203036042387437517289335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134135357361591625011526223 201203036042387437517289335)
        ·
          refine ⟨301804554063581156275934003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201203036042387437517289335 301804554063581156275934003)
          ·
            refine ⟨452706831095371734413901005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301804554063581156275934003 452706831095371734413901005)
            ·
              refine ⟨169765061660764400405212877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 452706831095371734413901005 169765061660764400405212877)
              ·
                refine ⟨63661898122786650151954829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169765061660764400405212877 63661898122786650151954829)
                ·
                  refine ⟨23873211796044993806983061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 63661898122786650151954829 23873211796044993806983061)
                  ·
                    refine ⟨1119056802939609084702331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23873211796044993806983061 1119056802939609084702331)
                    ·
                      rfl

theorem cell22_3269033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 3, 3, 6].length) (baseStart_3269033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269033 prefixEnd_3269033 := by exact prefixLift 3269033
  have htrace : WordTrace (prefixWord ++ tailWord_3269033) baseStart_3269033 baseEnd_3269033 := by
    simpa [prefixWord, tailWord_3269033, baseEnd_3269033] using wordTrace_append hprefix tailTrace_3269033
  have hstable : (prefixWord ++ tailWord_3269033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269033).length < 2 ^ (prefixWord ++ tailWord_3269033).sum := by decide
  have hdescent : baseEnd_3269033 < baseStart_3269033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269052 : List Nat := [2, 2, 2, 4, 1, 2, 1, 2, 1, 5]
def baseStart_3269052 : Nat := 118140960795 + 3269052 * 2 ^ 59
def prefixEnd_3269052 : Nat := 4983230072969 + 3 ^ 40 * 3269052 * 2
def baseEnd_3269052 : Nat := 1119063307027899368477273

theorem tailTrace_3269052 : CollatzResearch.WordTrace tailWord_3269052 prefixEnd_3269052 1119063307027899368477273 := by
  unfold tailWord_3269052
  simp only [CollatzResearch.WordTrace]
  refine ⟨59616060876395194238704705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79488081168526925651606273 59616060876395194238704705)
  ·
    refine ⟨44712045657296395679028529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59616060876395194238704705 44712045657296395679028529)
    ·
      refine ⟨33534034242972296759271397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44712045657296395679028529 33534034242972296759271397)
      ·
        refine ⟨6287631420557305642363387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33534034242972296759271397 6287631420557305642363387)
        ·
          refine ⟨9431447130835958463545081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6287631420557305642363387 9431447130835958463545081)
          ·
            refine ⟨7073585348126968847658811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9431447130835958463545081 7073585348126968847658811)
            ·
              refine ⟨10610378022190453271488217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7073585348126968847658811 10610378022190453271488217)
              ·
                refine ⟨7957783516642839953616163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10610378022190453271488217 7957783516642839953616163)
                ·
                  refine ⟨11936675274964259930424245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7957783516642839953616163 11936675274964259930424245)
                  ·
                    refine ⟨1119063307027899368477273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11936675274964259930424245 1119063307027899368477273)
                    ·
                      rfl

theorem cell22_3269052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_3269052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269052 prefixEnd_3269052 := by exact prefixLift 3269052
  have htrace : WordTrace (prefixWord ++ tailWord_3269052) baseStart_3269052 baseEnd_3269052 := by
    simpa [prefixWord, tailWord_3269052, baseEnd_3269052] using wordTrace_append hprefix tailTrace_3269052
  have hstable : (prefixWord ++ tailWord_3269052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269052).length < 2 ^ (prefixWord ++ tailWord_3269052).sum := by decide
  have hdescent : baseEnd_3269052 < baseStart_3269052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269095 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 2, 6]
def baseStart_3269095 : Nat := 118140960795 + 3269095 * 2 ^ 59
def prefixEnd_3269095 : Nat := 4983230072969 + 3 ^ 40 * 3269095 * 2
def baseEnd_3269095 : Nat := 1119078026806661589652141

theorem tailTrace_3269095 : CollatzResearch.WordTrace tailWord_3269095 prefixEnd_3269095 1119078026806661589652141 := by
  unfold tailWord_3269095
  simp only [CollatzResearch.WordTrace]
  refine ⟨119233690091634606821224739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79489126727756404547483159 119233690091634606821224739)
  ·
    refine ⟨178850535137451910231837109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119233690091634606821224739 178850535137451910231837109)
    ·
      refine ⟨16767237669136116584234729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178850535137451910231837109 16767237669136116584234729)
      ·
        refine ⟨12575428251852087438176047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16767237669136116584234729 12575428251852087438176047)
        ·
          refine ⟨18863142377778131157264071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12575428251852087438176047 18863142377778131157264071)
          ·
            refine ⟨28294713566667196735896107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18863142377778131157264071 28294713566667196735896107)
            ·
              refine ⟨42442070350000795103844161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28294713566667196735896107 42442070350000795103844161)
              ·
                refine ⟨31831552762500596327883121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42442070350000795103844161 31831552762500596327883121)
                ·
                  refine ⟨23873664571875447245912341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 31831552762500596327883121 23873664571875447245912341)
                  ·
                    refine ⟨1119078026806661589652141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23873664571875447245912341 1119078026806661589652141)
                    ·
                      rfl

theorem cell22_3269095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_3269095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269095 prefixEnd_3269095 := by exact prefixLift 3269095
  have htrace : WordTrace (prefixWord ++ tailWord_3269095) baseStart_3269095 baseEnd_3269095 := by
    simpa [prefixWord, tailWord_3269095, baseEnd_3269095] using wordTrace_append hprefix tailTrace_3269095
  have hstable : (prefixWord ++ tailWord_3269095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269095).length < 2 ^ (prefixWord ++ tailWord_3269095).sum := by decide
  have hdescent : baseEnd_3269095 < baseStart_3269095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269125 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 2, 5]
def baseStart_3269125 : Nat := 118140960795 + 3269125 * 2 ^ 59
def prefixEnd_3269125 : Nat := 4983230072969 + 3 ^ 40 * 3269125 * 2
def baseEnd_3269125 : Nat := 1119088296419751511402049

theorem tailTrace_3269125 : CollatzResearch.WordTrace tailWord_3269125 prefixEnd_3269125 1119088296419751511402049 := by
  unfold tailWord_3269125
  simp only [CollatzResearch.WordTrace]
  refine ⟨119234784281525921944816829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79489856187683947963211219 119234784281525921944816829)
  ·
    refine ⟨44713044105572220729306311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119234784281525921944816829 44713044105572220729306311)
    ·
      refine ⟨67069566158358331093959467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44713044105572220729306311 67069566158358331093959467)
      ·
        refine ⟨100604349237537496640939201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67069566158358331093959467 100604349237537496640939201)
        ·
          refine ⟨75453261928153122480704401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100604349237537496640939201 75453261928153122480704401)
          ·
            refine ⟨56589946446114841860528301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75453261928153122480704401 56589946446114841860528301)
            ·
              refine ⟨21221229917293065697698113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56589946446114841860528301 21221229917293065697698113)
              ·
                refine ⟨15915922437969799273273585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21221229917293065697698113 15915922437969799273273585)
                ·
                  refine ⟨11936941828477349454955189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15915922437969799273273585 11936941828477349454955189)
                  ·
                    refine ⟨1119088296419751511402049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11936941828477349454955189 1119088296419751511402049)
                    ·
                      rfl

theorem cell22_3269125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 2, 5].length) (baseStart_3269125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269125 prefixEnd_3269125 := by exact prefixLift 3269125
  have htrace : WordTrace (prefixWord ++ tailWord_3269125) baseStart_3269125 baseEnd_3269125 := by
    simpa [prefixWord, tailWord_3269125, baseEnd_3269125] using wordTrace_append hprefix tailTrace_3269125
  have hstable : (prefixWord ++ tailWord_3269125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269125).length < 2 ^ (prefixWord ++ tailWord_3269125).sum := by decide
  have hdescent : baseEnd_3269125 < baseStart_3269125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269127 : List Nat := [1, 1, 4, 3, 3, 1, 1, 1, 7]
def baseStart_3269127 : Nat := 118140960795 + 3269127 * 2 ^ 59
def prefixEnd_3269127 : Nat := 4983230072969 + 3 ^ 40 * 3269127 * 2
def baseEnd_3269127 : Nat := 373029660353541390950681

theorem tailTrace_3269127 : CollatzResearch.WordTrace tailWord_3269127 prefixEnd_3269127 373029660353541390950681 := by
  unfold tailWord_3269127
  simp only [CollatzResearch.WordTrace]
  refine ⟨119234857227518676286389635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79489904818345784190926423 119234857227518676286389635)
  ·
    refine ⟨178852285841278014429584453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119234857227518676286389635 178852285841278014429584453)
    ·
      refine ⟨33534803595239627705547085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 178852285841278014429584453 33534803595239627705547085)
      ·
        refine ⟨12575551348214860389580157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33534803595239627705547085 12575551348214860389580157)
        ·
          refine ⟨4715831755580572646092559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12575551348214860389580157 4715831755580572646092559)
          ·
            refine ⟨7073747633370858969138839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4715831755580572646092559 7073747633370858969138839)
            ·
              refine ⟨10610621450056288453708259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7073747633370858969138839 10610621450056288453708259)
              ·
                refine ⟨15915932175084432680562389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10610621450056288453708259 15915932175084432680562389)
                ·
                  refine ⟨373029660353541390950681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15915932175084432680562389 373029660353541390950681)
                  ·
                    rfl

theorem cell22_3269127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 1, 7].length) (baseStart_3269127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269127 prefixEnd_3269127 := by exact prefixLift 3269127
  have htrace : WordTrace (prefixWord ++ tailWord_3269127) baseStart_3269127 baseEnd_3269127 := by
    simpa [prefixWord, tailWord_3269127, baseEnd_3269127] using wordTrace_append hprefix tailTrace_3269127
  have hstable : (prefixWord ++ tailWord_3269127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269127).length < 2 ^ (prefixWord ++ tailWord_3269127).sum := by decide
  have hdescent : baseEnd_3269127 < baseStart_3269127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269144 : List Nat := [2, 1, 2, 3, 3, 2, 3, 1, 5]
def baseStart_3269144 : Nat := 118140960795 + 3269144 * 2 ^ 59
def prefixEnd_3269144 : Nat := 4983230072969 + 3 ^ 40 * 3269144 * 2
def baseEnd_3269144 : Nat := 373031600169347265058997

theorem tailTrace_3269144 : CollatzResearch.WordTrace tailWord_3269144 prefixEnd_3269144 373031600169347265058997 := by
  unfold tailWord_3269144
  simp only [CollatzResearch.WordTrace]
  refine ⟨59617738634228544094879243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79490318178971392126505657 59617738634228544094879243)
  ·
    refine ⟨89426607951342816142318865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59617738634228544094879243 89426607951342816142318865)
    ·
      refine ⟨67069955963507112106739149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89426607951342816142318865 67069955963507112106739149)
      ·
        refine ⟨25151233486315167040027181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67069955963507112106739149 25151233486315167040027181)
        ·
          refine ⟨9431712557368187640010193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25151233486315167040027181 9431712557368187640010193)
          ·
            refine ⟨7073784418026140730007645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9431712557368187640010193 7073784418026140730007645)
            ·
              refine ⟨2652669156759802773752867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7073784418026140730007645 2652669156759802773752867)
              ·
                refine ⟨3979003735139704160629301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2652669156759802773752867 3979003735139704160629301)
                ·
                  refine ⟨373031600169347265058997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3979003735139704160629301 373031600169347265058997)
                  ·
                    rfl

theorem cell22_3269144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 1, 5].length) (baseStart_3269144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269144 prefixEnd_3269144 := by exact prefixLift 3269144
  have htrace : WordTrace (prefixWord ++ tailWord_3269144) baseStart_3269144 baseEnd_3269144 := by
    simpa [prefixWord, tailWord_3269144, baseEnd_3269144] using wordTrace_append hprefix tailTrace_3269144
  have hstable : (prefixWord ++ tailWord_3269144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269144).length < 2 ^ (prefixWord ++ tailWord_3269144).sum := by decide
  have hdescent : baseEnd_3269144 < baseStart_3269144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269157 : List Nat := [1, 3, 1, 2, 2, 1, 3, 4, 1, 4]
def baseStart_3269157 : Nat := 118140960795 + 3269157 * 2 ^ 59
def prefixEnd_3269157 : Nat := 4983230072969 + 3 ^ 40 * 3269157 * 2
def baseEnd_3269157 : Nat := 1119099250673714094601951

theorem tailTrace_3269157 : CollatzResearch.WordTrace tailWord_3269157 prefixEnd_3269157 1119099250673714094601951 := by
  unfold tailWord_3269157
  simp only [CollatzResearch.WordTrace]
  refine ⟨119235951417409991409981725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79490634278273327606654483 119235951417409991409981725)
  ·
    refine ⟨44713481781528746778743147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119235951417409991409981725 44713481781528746778743147)
    ·
      refine ⟨67070222672293120168114721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44713481781528746778743147 67070222672293120168114721)
      ·
        refine ⟨50302667004219840126086041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67070222672293120168114721 50302667004219840126086041)
        ·
          refine ⟨37727000253164880094564531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50302667004219840126086041 37727000253164880094564531)
          ·
            refine ⟨56590500379747320141846797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37727000253164880094564531 56590500379747320141846797)
            ·
              refine ⟨21221437642405245053192549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56590500379747320141846797 21221437642405245053192549)
              ·
                refine ⟨3979019557950983447473603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21221437642405245053192549 3979019557950983447473603)
                ·
                  refine ⟨5968529336926475171210405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3979019557950983447473603 5968529336926475171210405)
                  ·
                    refine ⟨1119099250673714094601951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5968529336926475171210405 1119099250673714094601951)
                    ·
                      rfl

theorem cell22_3269157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 4].length) (baseStart_3269157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269157 prefixEnd_3269157 := by exact prefixLift 3269157
  have htrace : WordTrace (prefixWord ++ tailWord_3269157) baseStart_3269157 baseEnd_3269157 := by
    simpa [prefixWord, tailWord_3269157, baseEnd_3269157] using wordTrace_append hprefix tailTrace_3269157
  have hstable : (prefixWord ++ tailWord_3269157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269157).length < 2 ^ (prefixWord ++ tailWord_3269157).sum := by decide
  have hdescent : baseEnd_3269157 < baseStart_3269157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269202 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 4, 4]
def baseStart_3269202 : Nat := 118140960795 + 3269202 * 2 ^ 59
def prefixEnd_3269202 : Nat := 4983230072969 + 3 ^ 40 * 3269202 * 2
def baseEnd_3269202 : Nat := 1119114655093348977226813

theorem tailTrace_3269202 : CollatzResearch.WordTrace tailWord_3269202 prefixEnd_3269202 1119114655093348977226813 := by
  unfold tailWord_3269202
  simp only [CollatzResearch.WordTrace]
  refine ⟨29809398175561741023842465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79491728468164642730246573 29809398175561741023842465)
  ·
    refine ⟨22357048631671305767881849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29809398175561741023842465 22357048631671305767881849)
    ·
      refine ⟨16767786473753479325911387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22357048631671305767881849 16767786473753479325911387)
      ·
        refine ⟨25151679710630218988867081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16767786473753479325911387 25151679710630218988867081)
        ·
          refine ⟨18863759782972664241650311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25151679710630218988867081 18863759782972664241650311)
          ·
            refine ⟨28295639674458996362475467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18863759782972664241650311 28295639674458996362475467)
            ·
              refine ⟨42443459511688494543713201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28295639674458996362475467 42443459511688494543713201)
              ·
                refine ⟨31832594633766370907784901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42443459511688494543713201 31832594633766370907784901)
                ·
                  refine ⟨5968611493831194545209669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31832594633766370907784901 5968611493831194545209669)
                  ·
                    refine ⟨1119114655093348977226813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5968611493831194545209669 1119114655093348977226813)
                    ·
                      rfl

theorem cell22_3269202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_3269202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269202 prefixEnd_3269202 := by exact prefixLift 3269202
  have htrace : WordTrace (prefixWord ++ tailWord_3269202) baseStart_3269202 baseEnd_3269202 := by
    simpa [prefixWord, tailWord_3269202, baseEnd_3269202] using wordTrace_append hprefix tailTrace_3269202
  have hstable : (prefixWord ++ tailWord_3269202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269202).length < 2 ^ (prefixWord ++ tailWord_3269202).sum := by decide
  have hdescent : baseEnd_3269202 < baseStart_3269202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269215 : List Nat := [1, 1, 2, 3, 1, 1, 1, 3, 2, 7]
def baseStart_3269215 : Nat := 118140960795 + 3269215 * 2 ^ 59
def prefixEnd_3269215 : Nat := 4983230072969 + 3 ^ 40 * 3269215 * 2
def baseEnd_3269215 : Nat := 1119119105259021276651773

theorem tailTrace_3269215 : CollatzResearch.WordTrace tailWord_3269215 prefixEnd_3269215 1119119105259021276651773 := by
  unfold tailWord_3269215
  simp only [CollatzResearch.WordTrace]
  refine ⟨119238066851199867315593099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79492044567466578210395399 119238066851199867315593099)
  ·
    refine ⟨178857100276799800973389649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119238066851199867315593099 178857100276799800973389649)
    ·
      refine ⟨134142825207599850730042237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178857100276799800973389649 134142825207599850730042237)
      ·
        refine ⟨50303559452849944023765839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134142825207599850730042237 50303559452849944023765839)
        ·
          refine ⟨75455339179274916035648759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50303559452849944023765839 75455339179274916035648759)
          ·
            refine ⟨113183008768912374053473139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75455339179274916035648759 113183008768912374053473139)
            ·
              refine ⟨169774513153368561080209709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113183008768912374053473139 169774513153368561080209709)
              ·
                refine ⟨63665442432513210405078641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169774513153368561080209709 63665442432513210405078641)
                ·
                  refine ⟨47749081824384907803808981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63665442432513210405078641 47749081824384907803808981)
                  ·
                    refine ⟨1119119105259021276651773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47749081824384907803808981 1119119105259021276651773)
                    ·
                      rfl

theorem cell22_3269215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_3269215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269215 prefixEnd_3269215 := by exact prefixLift 3269215
  have htrace : WordTrace (prefixWord ++ tailWord_3269215) baseStart_3269215 baseEnd_3269215 := by
    simpa [prefixWord, tailWord_3269215, baseEnd_3269215] using wordTrace_append hprefix tailTrace_3269215
  have hstable : (prefixWord ++ tailWord_3269215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269215).length < 2 ^ (prefixWord ++ tailWord_3269215).sum := by decide
  have hdescent : baseEnd_3269215 < baseStart_3269215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269238 : List Nat := [5, 1, 1, 2, 3, 1, 2, 2, 2, 3]
def baseStart_3269238 : Nat := 118140960795 + 3269238 * 2 ^ 59
def prefixEnd_3269238 : Nat := 4983230072969 + 3 ^ 40 * 3269238 * 2
def baseEnd_3269238 : Nat := 1119126978629056883326703

theorem tailTrace_3269238 : CollatzResearch.WordTrace tailWord_3269238 prefixEnd_3269238 1119126978629056883326703 := by
  unfold tailWord_3269238
  simp only [CollatzResearch.WordTrace]
  refine ⟨7452431608132283890230023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79492603820077694829120245 7452431608132283890230023)
  ·
    refine ⟨11178647412198425835345035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7452431608132283890230023 11178647412198425835345035)
    ·
      refine ⟨16767971118297638753017553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11178647412198425835345035 16767971118297638753017553)
      ·
        refine ⟨12575978338723229064763165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16767971118297638753017553 12575978338723229064763165)
        ·
          refine ⟨4715991877021210899286187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12575978338723229064763165 4715991877021210899286187)
          ·
            refine ⟨7073987815531816348929281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4715991877021210899286187 7073987815531816348929281)
            ·
              refine ⟨5305490861648862261696961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7073987815531816348929281 5305490861648862261696961)
              ·
                refine ⟨3979118146236646696272721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5305490861648862261696961 3979118146236646696272721)
                ·
                  refine ⟨2984338609677485022204541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3979118146236646696272721 2984338609677485022204541)
                  ·
                    refine ⟨1119126978629056883326703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2984338609677485022204541 1119126978629056883326703)
                    ·
                      rfl

theorem cell22_3269238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_3269238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269238 prefixEnd_3269238 := by exact prefixLift 3269238
  have htrace : WordTrace (prefixWord ++ tailWord_3269238) baseStart_3269238 baseEnd_3269238 := by
    simpa [prefixWord, tailWord_3269238, baseEnd_3269238] using wordTrace_append hprefix tailTrace_3269238
  have hstable : (prefixWord ++ tailWord_3269238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269238).length < 2 ^ (prefixWord ++ tailWord_3269238).sum := by decide
  have hdescent : baseEnd_3269238 < baseStart_3269238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269249 : List Nat := [1, 2, 4, 2, 1, 1, 2, 3, 3, 3]
def baseStart_3269249 : Nat := 118140960795 + 3269249 * 2 ^ 59
def prefixEnd_3269249 : Nat := 4983230072969 + 3 ^ 40 * 3269249 * 2
def baseEnd_3269249 : Nat := 1119130744153856521301669

theorem tailTrace_3269249 : CollatzResearch.WordTrace tailWord_3269249 prefixEnd_3269249 1119130744153856521301669 := by
  unfold tailWord_3269249
  simp only [CollatzResearch.WordTrace]
  refine ⟨119239306933076691122330801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79492871288717794081553867 119239306933076691122330801)
  ·
    refine ⟨89429480199807518341748101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119239306933076691122330801 89429480199807518341748101)
    ·
      refine ⟨16768027537463909689077769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 89429480199807518341748101 16768027537463909689077769)
      ·
        refine ⟨12576020653097932266808327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16768027537463909689077769 12576020653097932266808327)
        ·
          refine ⟨18864030979646898400212491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12576020653097932266808327 18864030979646898400212491)
          ·
            refine ⟨28296046469470347600318737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18864030979646898400212491 28296046469470347600318737)
            ·
              refine ⟨21222034852102760700239053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28296046469470347600318737 21222034852102760700239053)
              ·
                refine ⟨7958263069538535262589645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21222034852102760700239053 7958263069538535262589645)
                ·
                  refine ⟨2984348651076950723471117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7958263069538535262589645 2984348651076950723471117)
                  ·
                    refine ⟨1119130744153856521301669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2984348651076950723471117 1119130744153856521301669)
                    ·
                      rfl

theorem cell22_3269249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 3].length) (baseStart_3269249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269249 prefixEnd_3269249 := by exact prefixLift 3269249
  have htrace : WordTrace (prefixWord ++ tailWord_3269249) baseStart_3269249 baseEnd_3269249 := by
    simpa [prefixWord, tailWord_3269249, baseEnd_3269249] using wordTrace_append hprefix tailTrace_3269249
  have hstable : (prefixWord ++ tailWord_3269249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269249).length < 2 ^ (prefixWord ++ tailWord_3269249).sum := by decide
  have hdescent : baseEnd_3269249 < baseStart_3269249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269266 : List Nat := [3, 2, 3, 1, 2, 2, 1, 2, 3, 3]
def baseStart_3269266 : Nat := 118140960795 + 3269266 * 2 ^ 59
def prefixEnd_3269266 : Nat := 4983230072969 + 3 ^ 40 * 3269266 * 2
def baseEnd_3269266 : Nat := 1119136563601274143626617

theorem tailTrace_3269266 : CollatzResearch.WordTrace tailWord_3269266 prefixEnd_3269266 1119136563601274143626617 := by
  unfold tailWord_3269266
  simp only [CollatzResearch.WordTrace]
  refine ⟨29809981743503775756424913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79493284649343402017133101 29809981743503775756424913)
  ·
    refine ⟨22357486307627831817318685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29809981743503775756424913 22357486307627831817318685)
    ·
      refine ⟨8384057365360436931494507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22357486307627831817318685 8384057365360436931494507)
      ·
        refine ⟨12576086048040655397241761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8384057365360436931494507 12576086048040655397241761)
        ·
          refine ⟨9432064536030491547931321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12576086048040655397241761 9432064536030491547931321)
          ·
            refine ⟨7074048402022868660948491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9432064536030491547931321 7074048402022868660948491)
            ·
              refine ⟨10611072603034302991422737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7074048402022868660948491 10611072603034302991422737)
              ·
                refine ⟨7958304452275727243567053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10611072603034302991422737 7958304452275727243567053)
                ·
                  refine ⟨2984364169603397716337645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7958304452275727243567053 2984364169603397716337645)
                  ·
                    refine ⟨1119136563601274143626617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2984364169603397716337645 1119136563601274143626617)
                    ·
                      rfl

theorem cell22_3269266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_3269266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269266 prefixEnd_3269266 := by exact prefixLift 3269266
  have htrace : WordTrace (prefixWord ++ tailWord_3269266) baseStart_3269266 baseEnd_3269266 := by
    simpa [prefixWord, tailWord_3269266, baseEnd_3269266] using wordTrace_append hprefix tailTrace_3269266
  have hstable : (prefixWord ++ tailWord_3269266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269266).length < 2 ^ (prefixWord ++ tailWord_3269266).sum := by decide
  have hdescent : baseEnd_3269266 < baseStart_3269266 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269324 : List Nat := [2, 2, 1, 5, 1, 1, 2, 2, 6]
def baseStart_3269324 : Nat := 118140960795 + 3269324 * 2 ^ 59
def prefixEnd_3269324 : Nat := 4983230072969 + 3 ^ 40 * 3269324 * 2
def baseEnd_3269324 : Nat := 373052139395527108558813

theorem tailTrace_3269324 : CollatzResearch.WordTrace tailWord_3269324 prefixEnd_3269324 373052139395527108558813 := by
  unfold tailWord_3269324
  simp only [CollatzResearch.WordTrace]
  refine ⟨59621021203902489465655513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79494694938536652620874017 59621021203902489465655513)
  ·
    refine ⟨44715765902926867099241635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59621021203902489465655513 44715765902926867099241635)
    ·
      refine ⟨67073648854390300648862453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44715765902926867099241635 67073648854390300648862453)
      ·
        refine ⟨6288154580099090685830855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 67073648854390300648862453 6288154580099090685830855)
        ·
          refine ⟨9432231870148636028746283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6288154580099090685830855 9432231870148636028746283)
          ·
            refine ⟨14148347805222954043119425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9432231870148636028746283 14148347805222954043119425)
            ·
              refine ⟨10611260853917215532339569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14148347805222954043119425 10611260853917215532339569)
              ·
                refine ⟨7958445640437911649254677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10611260853917215532339569 7958445640437911649254677)
                ·
                  refine ⟨373052139395527108558813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7958445640437911649254677 373052139395527108558813)
                  ·
                    rfl

theorem cell22_3269324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 2, 6].length) (baseStart_3269324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269324 prefixEnd_3269324 := by exact prefixLift 3269324
  have htrace : WordTrace (prefixWord ++ tailWord_3269324) baseStart_3269324 baseEnd_3269324 := by
    simpa [prefixWord, tailWord_3269324, baseEnd_3269324] using wordTrace_append hprefix tailTrace_3269324
  have hstable : (prefixWord ++ tailWord_3269324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269324).length < 2 ^ (prefixWord ++ tailWord_3269324).sum := by decide
  have hdescent : baseEnd_3269324 < baseStart_3269324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269326 : List Nat := [4, 1, 1, 1, 3, 3, 2, 2, 1, 4]
def baseStart_3269326 : Nat := 118140960795 + 3269326 * 2 ^ 59
def prefixEnd_3269326 : Nat := 4983230072969 + 3 ^ 40 * 3269326 * 2
def baseEnd_3269326 : Nat := 1119157102827453987126433

theorem tailTrace_3269326 : CollatzResearch.WordTrace tailWord_3269326 prefixEnd_3269326 1119157102827453987126433 := by
  unfold tailWord_3269326
  simp only [CollatzResearch.WordTrace]
  refine ⟨14905264419224716659110479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79494743569198488848589221 14905264419224716659110479)
  ·
    refine ⟨22357896628837074988665719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14905264419224716659110479 22357896628837074988665719)
    ·
      refine ⟨33536844943255612482998579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22357896628837074988665719 33536844943255612482998579)
      ·
        refine ⟨50305267414883418724497869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33536844943255612482998579 50305267414883418724497869)
        ·
          refine ⟨18864475280581282021686701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50305267414883418724497869 18864475280581282021686701)
          ·
            refine ⟨7074178230217980758132513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18864475280581282021686701 7074178230217980758132513)
            ·
              refine ⟨5305633672663485568599385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7074178230217980758132513 5305633672663485568599385)
              ·
                refine ⟨3979225254497614176449539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5305633672663485568599385 3979225254497614176449539)
                ·
                  refine ⟨5968837881746421264674309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3979225254497614176449539 5968837881746421264674309)
                  ·
                    refine ⟨1119157102827453987126433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5968837881746421264674309 1119157102827453987126433)
                    ·
                      rfl

theorem cell22_3269326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_3269326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269326 prefixEnd_3269326 := by exact prefixLift 3269326
  have htrace : WordTrace (prefixWord ++ tailWord_3269326) baseStart_3269326 baseEnd_3269326 := by
    simpa [prefixWord, tailWord_3269326, baseEnd_3269326] using wordTrace_append hprefix tailTrace_3269326
  have hstable : (prefixWord ++ tailWord_3269326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269326).length < 2 ^ (prefixWord ++ tailWord_3269326).sum := by decide
  have hdescent : baseEnd_3269326 < baseStart_3269326 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269337 : List Nat := [1, 2, 1, 2, 3, 2, 1, 3, 1, 6]
def baseStart_3269337 : Nat := 118140960795 + 3269337 * 2 ^ 59
def prefixEnd_3269337 : Nat := 4983230072969 + 3 ^ 40 * 3269337 * 2
def baseEnd_3269337 : Nat := 1119160868352253625101399

theorem tailTrace_3269337 : CollatzResearch.WordTrace tailWord_3269337 prefixEnd_3269337 1119160868352253625101399 := by
  unfold tailWord_3269337
  simp only [CollatzResearch.WordTrace]
  refine ⟨119242516556757882151534265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79495011037838588101022843 119242516556757882151534265)
  ·
    refine ⟨89431887417568411613650699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119242516556757882151534265 89431887417568411613650699)
    ·
      refine ⟨134147831126352617420476049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89431887417568411613650699 134147831126352617420476049)
      ·
        refine ⟨100610873344764463065357037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134147831126352617420476049 100610873344764463065357037)
        ·
          refine ⟨37729077504286673649508889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100610873344764463065357037 37729077504286673649508889)
          ·
            refine ⟨28296808128215005237131667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37729077504286673649508889 28296808128215005237131667)
            ·
              refine ⟨42445212192322507855697501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28296808128215005237131667 42445212192322507855697501)
              ·
                refine ⟨15916954572120940445886563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42445212192322507855697501 15916954572120940445886563)
                ·
                  refine ⟨23875431858181410668829845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15916954572120940445886563 23875431858181410668829845)
                  ·
                    refine ⟨1119160868352253625101399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23875431858181410668829845 1119160868352253625101399)
                    ·
                      rfl

theorem cell22_3269337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 6].length) (baseStart_3269337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269337 prefixEnd_3269337 := by exact prefixLift 3269337
  have htrace : WordTrace (prefixWord ++ tailWord_3269337) baseStart_3269337 baseEnd_3269337 := by
    simpa [prefixWord, tailWord_3269337, baseEnd_3269337] using wordTrace_append hprefix tailTrace_3269337
  have hstable : (prefixWord ++ tailWord_3269337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269337).length < 2 ^ (prefixWord ++ tailWord_3269337).sum := by decide
  have hdescent : baseEnd_3269337 < baseStart_3269337 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269358 : List Nat := [4, 1, 2, 1, 1, 4, 3, 2, 4]
def baseStart_3269358 : Nat := 118140960795 + 3269358 * 2 ^ 59
def prefixEnd_3269358 : Nat := 4983230072969 + 3 ^ 40 * 3269358 * 2
def baseEnd_3269358 : Nat := 373056019027138856775445

theorem tailTrace_3269358 : CollatzResearch.WordTrace tailWord_3269358 prefixEnd_3269358 373056019027138856775445 := by
  unfold tailWord_3269358
  simp only [CollatzResearch.WordTrace]
  refine ⟨14905410311210225342256091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79495521659787868492032485 14905410311210225342256091)
  ·
    refine ⟨22358115466815338013384137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14905410311210225342256091 22358115466815338013384137)
    ·
      refine ⟨16768586600111503510038103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22358115466815338013384137 16768586600111503510038103)
      ·
        refine ⟨25152879900167255265057155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16768586600111503510038103 25152879900167255265057155)
        ·
          refine ⟨37729319850250882897585733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25152879900167255265057155 37729319850250882897585733)
          ·
            refine ⟨7074247471922040543297325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37729319850250882897585733 7074247471922040543297325)
            ·
              refine ⟨2652842801970765203736497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7074247471922040543297325 2652842801970765203736497)
              ·
                refine ⟨1989632101478073902802373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2652842801970765203736497 1989632101478073902802373)
                ·
                  refine ⟨373056019027138856775445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1989632101478073902802373 373056019027138856775445)
                  ·
                    rfl

theorem cell22_3269358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_3269358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269358 prefixEnd_3269358 := by exact prefixLift 3269358
  have htrace : WordTrace (prefixWord ++ tailWord_3269358) baseStart_3269358 baseEnd_3269358 := by
    simpa [prefixWord, tailWord_3269358, baseEnd_3269358] using wordTrace_append hprefix tailTrace_3269358
  have hstable : (prefixWord ++ tailWord_3269358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269358).length < 2 ^ (prefixWord ++ tailWord_3269358).sum := by decide
  have hdescent : baseEnd_3269358 < baseStart_3269358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269429 : List Nat := [1, 3, 3, 1, 3, 1, 1, 1, 1, 7]
def baseStart_3269429 : Nat := 118140960795 + 3269429 * 2 ^ 59
def prefixEnd_3269429 : Nat := 4983230072969 + 3 ^ 40 * 3269429 * 2
def baseEnd_3269429 : Nat := 1119192361832396051801117

theorem tailTrace_3269429 : CollatzResearch.WordTrace tailWord_3269429 prefixEnd_3269429 1119192361832396051801117 := by
  unfold tailWord_3269429
  simp only [CollatzResearch.WordTrace]
  refine ⟨119245872072424581863883341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79497248048283054575922227 119245872072424581863883341)
  ·
    refine ⟨44717202027159218198956253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119245872072424581863883341 44717202027159218198956253)
    ·
      refine ⟨16768950760184706824608595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44717202027159218198956253 16768950760184706824608595)
      ·
        refine ⟨25153426140277060236912893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16768950760184706824608595 25153426140277060236912893)
        ·
          refine ⟨9432534802603897588842335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25153426140277060236912893 9432534802603897588842335)
          ·
            refine ⟨14148802203905846383263503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9432534802603897588842335 14148802203905846383263503)
            ·
              refine ⟨21223203305858769574895255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14148802203905846383263503 21223203305858769574895255)
              ·
                refine ⟨31834804958788154362342883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21223203305858769574895255 31834804958788154362342883)
                ·
                  refine ⟨47752207438182231543514325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31834804958788154362342883 47752207438182231543514325)
                  ·
                    refine ⟨1119192361832396051801117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47752207438182231543514325 1119192361832396051801117)
                    ·
                      rfl

theorem cell22_3269429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 7].length) (baseStart_3269429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269429 prefixEnd_3269429 := by exact prefixLift 3269429
  have htrace : WordTrace (prefixWord ++ tailWord_3269429) baseStart_3269429 baseEnd_3269429 := by
    simpa [prefixWord, tailWord_3269429, baseEnd_3269429] using wordTrace_append hprefix tailTrace_3269429
  have hstable : (prefixWord ++ tailWord_3269429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269429).length < 2 ^ (prefixWord ++ tailWord_3269429).sum := by decide
  have hdescent : baseEnd_3269429 < baseStart_3269429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269461 : List Nat := [1, 3, 2, 2, 2, 1, 3, 3, 1, 4]
def baseStart_3269461 : Nat := 118140960795 + 3269461 * 2 ^ 59
def prefixEnd_3269461 : Nat := 4983230072969 + 3 ^ 40 * 3269461 * 2
def baseEnd_3269461 : Nat := 1119203316086358635001019

theorem tailTrace_3269461 : CollatzResearch.WordTrace tailWord_3269461 prefixEnd_3269461 1119203316086358635001019 := by
  unfold tailWord_3269461
  simp only [CollatzResearch.WordTrace]
  refine ⟨119247039208308651329048237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79498026138872434219365491 119247039208308651329048237)
  ·
    refine ⟨44717639703115744248393089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119247039208308651329048237 44717639703115744248393089)
    ·
      refine ⟨33538229777336808186294817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44717639703115744248393089 33538229777336808186294817)
      ·
        refine ⟨25153672333002606139721113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33538229777336808186294817 25153672333002606139721113)
        ·
          refine ⟨18865254249751954604790835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25153672333002606139721113 18865254249751954604790835)
          ·
            refine ⟨28297881374627931907186253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18865254249751954604790835 28297881374627931907186253)
            ·
              refine ⟨10611705515485474465194845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28297881374627931907186253 10611705515485474465194845)
              ·
                refine ⟨3979389568307052924448067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10611705515485474465194845 3979389568307052924448067)
                ·
                  refine ⟨5969084352460579386672101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3979389568307052924448067 5969084352460579386672101)
                  ·
                    refine ⟨1119203316086358635001019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5969084352460579386672101 1119203316086358635001019)
                    ·
                      rfl

theorem cell22_3269461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 3, 3, 1, 4].length) (baseStart_3269461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269461 prefixEnd_3269461 := by exact prefixLift 3269461
  have htrace : WordTrace (prefixWord ++ tailWord_3269461) baseStart_3269461 baseEnd_3269461 := by
    simpa [prefixWord, tailWord_3269461, baseEnd_3269461] using wordTrace_append hprefix tailTrace_3269461
  have hstable : (prefixWord ++ tailWord_3269461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269461).length < 2 ^ (prefixWord ++ tailWord_3269461).sum := by decide
  have hdescent : baseEnd_3269461 < baseStart_3269461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269476 : List Nat := [2, 3, 1, 1, 4, 2, 2, 1, 6]
def baseStart_3269476 : Nat := 118140960795 + 3269476 * 2 ^ 59
def prefixEnd_3269476 : Nat := 4983230072969 + 3 ^ 40 * 3269476 * 2
def baseEnd_3269476 : Nat := 373069483630967865291991

theorem tailTrace_3269476 : CollatzResearch.WordTrace tailWord_3269476 prefixEnd_3269476 373069483630967865291991 := by
  unfold tailWord_3269476
  simp only [CollatzResearch.WordTrace]
  refine ⟨59623793151627154445422141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79498390868836205927229521 59623793151627154445422141)
  ·
    refine ⟨22358922431860182917033303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59623793151627154445422141 22358922431860182917033303)
    ·
      refine ⟨33538383647790274375549955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22358922431860182917033303 33538383647790274375549955)
      ·
        refine ⟨50307575471685411563324933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33538383647790274375549955 50307575471685411563324933)
        ·
          refine ⟨9432670400941014668123425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50307575471685411563324933 9432670400941014668123425)
          ·
            refine ⟨7074502800705761001092569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9432670400941014668123425 7074502800705761001092569)
            ·
              refine ⟨5305877100529320750819427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7074502800705761001092569 5305877100529320750819427)
              ·
                refine ⟨7958815650793981126229141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5305877100529320750819427 7958815650793981126229141)
                ·
                  refine ⟨373069483630967865291991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7958815650793981126229141 373069483630967865291991)
                  ·
                    rfl

theorem cell22_3269476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 1, 6].length) (baseStart_3269476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269476 prefixEnd_3269476 := by exact prefixLift 3269476
  have htrace : WordTrace (prefixWord ++ tailWord_3269476) baseStart_3269476 baseEnd_3269476 := by
    simpa [prefixWord, tailWord_3269476, baseEnd_3269476] using wordTrace_append hprefix tailTrace_3269476
  have hstable : (prefixWord ++ tailWord_3269476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269476).length < 2 ^ (prefixWord ++ tailWord_3269476).sum := by decide
  have hdescent : baseEnd_3269476 < baseStart_3269476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269489 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 1, 6]
def baseStart_3269489 : Nat := 118140960795 + 3269489 * 2 ^ 59
def prefixEnd_3269489 : Nat := 4983230072969 + 3 ^ 40 * 3269489 * 2
def baseEnd_3269489 : Nat := 1119212901058575895300933

theorem tailTrace_3269489 : CollatzResearch.WordTrace tailWord_3269489 prefixEnd_3269489 1119212901058575895300933 := by
  unfold tailWord_3269489
  simp only [CollatzResearch.WordTrace]
  refine ⟨119248060452207212111067521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79498706968138141407378347 119248060452207212111067521)
  ·
    refine ⟨89436045339155409083300641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119248060452207212111067521 89436045339155409083300641)
    ·
      refine ⟨67077034004366556812475481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89436045339155409083300641 67077034004366556812475481)
      ·
        refine ⟨50307775503274917609356611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67077034004366556812475481 50307775503274917609356611)
        ·
          refine ⟨75461663254912376414034917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50307775503274917609356611 75461663254912376414034917)
          ·
            refine ⟨14149061860296070577631547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75461663254912376414034917 14149061860296070577631547)
            ·
              refine ⟨21223592790444105866447321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14149061860296070577631547 21223592790444105866447321)
              ·
                refine ⟨15917694592833079399835491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21223592790444105866447321 15917694592833079399835491)
                ·
                  refine ⟨23876541889249619099753237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15917694592833079399835491 23876541889249619099753237)
                  ·
                    refine ⟨1119212901058575895300933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23876541889249619099753237 1119212901058575895300933)
                    ·
                      rfl

theorem cell22_3269489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 6].length) (baseStart_3269489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269489 prefixEnd_3269489 := by exact prefixLift 3269489
  have htrace : WordTrace (prefixWord ++ tailWord_3269489) baseStart_3269489 baseEnd_3269489 := by
    simpa [prefixWord, tailWord_3269489, baseEnd_3269489] using wordTrace_append hprefix tailTrace_3269489
  have hstable : (prefixWord ++ tailWord_3269489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269489).length < 2 ^ (prefixWord ++ tailWord_3269489).sum := by decide
  have hdescent : baseEnd_3269489 < baseStart_3269489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269491 : List Nat := [1, 1, 1, 2, 2, 1, 4, 5, 2, 3]
def baseStart_3269491 : Nat := 118140960795 + 3269491 * 2 ^ 59
def prefixEnd_3269491 : Nat := 4983230072969 + 3 ^ 40 * 3269491 * 2
def baseEnd_3269491 : Nat := 1119213585699448556750927

theorem tailTrace_3269491 : CollatzResearch.WordTrace tailWord_3269491 prefixEnd_3269491 1119213585699448556750927 := by
  unfold tailWord_3269491
  simp only [CollatzResearch.WordTrace]
  refine ⟨119248133398199966452640327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79498755598799977635093551 119248133398199966452640327)
  ·
    refine ⟨178872200097299949678960491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119248133398199966452640327 178872200097299949678960491)
    ·
      refine ⟨268308300145949924518440737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178872200097299949678960491 268308300145949924518440737)
      ·
        refine ⟨201231225109462443388830553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268308300145949924518440737 201231225109462443388830553)
        ·
          refine ⟨150923418832096832541622915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201231225109462443388830553 150923418832096832541622915)
          ·
            refine ⟨226385128248145248812434373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150923418832096832541622915 226385128248145248812434373)
            ·
              refine ⟨42447211546527234152331445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 226385128248145248812434373 42447211546527234152331445)
              ·
                refine ⟨3979426082486928201781073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42447211546527234152331445 3979426082486928201781073)
                ·
                  refine ⟨2984569561865196151335805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3979426082486928201781073 2984569561865196151335805)
                  ·
                    refine ⟨1119213585699448556750927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2984569561865196151335805 1119213585699448556750927)
                    ·
                      rfl

theorem cell22_3269491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 5, 2, 3].length) (baseStart_3269491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269491 prefixEnd_3269491 := by exact prefixLift 3269491
  have htrace : WordTrace (prefixWord ++ tailWord_3269491) baseStart_3269491 baseEnd_3269491 := by
    simpa [prefixWord, tailWord_3269491, baseEnd_3269491] using wordTrace_append hprefix tailTrace_3269491
  have hstable : (prefixWord ++ tailWord_3269491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269491).length < 2 ^ (prefixWord ++ tailWord_3269491).sum := by decide
  have hdescent : baseEnd_3269491 < baseStart_3269491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269628 : List Nat := [2, 2, 2, 1, 2, 3, 1, 5, 4]
def baseStart_3269628 : Nat := 118140960795 + 3269628 * 2 ^ 59
def prefixEnd_3269628 : Nat := 4983230072969 + 3 ^ 40 * 3269628 * 2
def baseEnd_3269628 : Nat := 373086827866408622025169

theorem tailTrace_3269628 : CollatzResearch.WordTrace tailWord_3269628 prefixEnd_3269628 373086827866408622025169 := by
  unfold tailWord_3269628
  simp only [CollatzResearch.WordTrace]
  refine ⟨59626565099351819425188769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79502086799135759233585025 59626565099351819425188769)
  ·
    refine ⟨44719923824513864568891577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59626565099351819425188769 44719923824513864568891577)
    ·
      refine ⟨33539942868385398426668683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44719923824513864568891577 33539942868385398426668683)
      ·
        refine ⟨50309914302578097640003025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33539942868385398426668683 50309914302578097640003025)
        ·
          refine ⟨37732435726933573230002269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50309914302578097640003025 37732435726933573230002269)
          ·
            refine ⟨14149663397600089961250851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37732435726933573230002269 14149663397600089961250851)
            ·
              refine ⟨21224495096400134941876277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14149663397600089961250851 21224495096400134941876277)
              ·
                refine ⟨1989796415287512650800901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21224495096400134941876277 1989796415287512650800901)
                ·
                  refine ⟨373086827866408622025169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1989796415287512650800901 373086827866408622025169)
                  ·
                    rfl

theorem cell22_3269628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5, 4].length) (baseStart_3269628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269628 prefixEnd_3269628 := by exact prefixLift 3269628
  have htrace : WordTrace (prefixWord ++ tailWord_3269628) baseStart_3269628 baseEnd_3269628 := by
    simpa [prefixWord, tailWord_3269628, baseEnd_3269628] using wordTrace_append hprefix tailTrace_3269628
  have hstable : (prefixWord ++ tailWord_3269628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269628).length < 2 ^ (prefixWord ++ tailWord_3269628).sum := by decide
  have hdescent : baseEnd_3269628 < baseStart_3269628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269634 : List Nat := [3, 4, 1, 3, 2, 1, 1, 2, 5]
def baseStart_3269634 : Nat := 118140960795 + 3269634 * 2 ^ 59
def prefixEnd_3269634 : Nat := 4983230072969 + 3 ^ 40 * 3269634 * 2
def baseEnd_3269634 : Nat := 373087512507281283475163

theorem tailTrace_3269634 : CollatzResearch.WordTrace tailWord_3269634 prefixEnd_3269634 373087512507281283475163 := by
  unfold tailWord_3269634
  simp only [CollatzResearch.WordTrace]
  refine ⟨29813337259170475468773989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79502232691121267916730637 29813337259170475468773989)
  ·
    refine ⟨5590000736094464150395123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 29813337259170475468773989 5590000736094464150395123)
    ·
      refine ⟨8385001104141696225592685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5590000736094464150395123 8385001104141696225592685)
      ·
        refine ⟨3144375414053136084597257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8385001104141696225592685 3144375414053136084597257)
        ·
          refine ⟨2358281560539852063447943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3144375414053136084597257 2358281560539852063447943)
          ·
            refine ⟨3537422340809778095171915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2358281560539852063447943 3537422340809778095171915)
            ·
              refine ⟨5306133511214667142757873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3537422340809778095171915 5306133511214667142757873)
              ·
                refine ⟨3979600133411000357068405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5306133511214667142757873 3979600133411000357068405)
                ·
                  refine ⟨373087512507281283475163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3979600133411000357068405 373087512507281283475163)
                  ·
                    rfl

theorem cell22_3269634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_3269634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269634 prefixEnd_3269634 := by exact prefixLift 3269634
  have htrace : WordTrace (prefixWord ++ tailWord_3269634) baseStart_3269634 baseEnd_3269634 := by
    simpa [prefixWord, tailWord_3269634, baseEnd_3269634] using wordTrace_append hprefix tailTrace_3269634
  have hstable : (prefixWord ++ tailWord_3269634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269634).length < 2 ^ (prefixWord ++ tailWord_3269634).sum := by decide
  have hdescent : baseEnd_3269634 < baseStart_3269634 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269641 : List Nat := [1, 2, 1, 1, 3, 1, 1, 6, 2, 4]
def baseStart_3269641 : Nat := 118140960795 + 3269641 * 2 ^ 59
def prefixEnd_3269641 : Nat := 4983230072969 + 3 ^ 40 * 3269641 * 2
def baseEnd_3269641 : Nat := 1119264933764898165500467

theorem tailTrace_3269641 : CollatzResearch.WordTrace tailWord_3269641 prefixEnd_3269641 1119264933764898165500467 := by
  unfold tailWord_3269641
  simp only [CollatzResearch.WordTrace]
  refine ⟨119253604347656542070600777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79502402898437694713733851 119253604347656542070600777)
  ·
    refine ⟨89440203260742406552950583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119253604347656542070600777 89440203260742406552950583)
    ·
      refine ⟨134160304891113609829425875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89440203260742406552950583 134160304891113609829425875)
      ·
        refine ⟨201240457336670414744138813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134160304891113609829425875 201240457336670414744138813)
        ·
          refine ⟨75465171501251405529052055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201240457336670414744138813 75465171501251405529052055)
          ·
            refine ⟨113197757251877108293578083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75465171501251405529052055 113197757251877108293578083)
            ·
              refine ⟨169796635877815662440367125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113197757251877108293578083 169796635877815662440367125)
              ·
                refine ⟨7959217306772609176892209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 169796635877815662440367125 7959217306772609176892209)
                ·
                  refine ⟨5969412980079456882669157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7959217306772609176892209 5969412980079456882669157)
                  ·
                    refine ⟨1119264933764898165500467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5969412980079456882669157 1119264933764898165500467)
                    ·
                      rfl

theorem cell22_3269641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 6, 2, 4].length) (baseStart_3269641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269641 prefixEnd_3269641 := by exact prefixLift 3269641
  have htrace : WordTrace (prefixWord ++ tailWord_3269641) baseStart_3269641 baseEnd_3269641 := by
    simpa [prefixWord, tailWord_3269641, baseEnd_3269641] using wordTrace_append hprefix tailTrace_3269641
  have hstable : (prefixWord ++ tailWord_3269641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269641).length < 2 ^ (prefixWord ++ tailWord_3269641).sum := by decide
  have hdescent : baseEnd_3269641 < baseStart_3269641 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269643 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 4, 3]
def baseStart_3269643 : Nat := 118140960795 + 3269643 * 2 ^ 59
def prefixEnd_3269643 : Nat := 4983230072969 + 3 ^ 40 * 3269643 * 2
def baseEnd_3269643 : Nat := 1119265618405770826950461

theorem tailTrace_3269643 : CollatzResearch.WordTrace tailWord_3269643 prefixEnd_3269643 1119265618405770826950461 := by
  unfold tailWord_3269643
  simp only [CollatzResearch.WordTrace]
  refine ⟨119253677293649296412173583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79502451529099530941449055 119253677293649296412173583)
  ·
    refine ⟨178880515940473944618260375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119253677293649296412173583 178880515940473944618260375)
    ·
      refine ⟨268320773910710916927390563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178880515940473944618260375 268320773910710916927390563)
      ·
        refine ⟨402481160866066375391085845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268320773910710916927390563 402481160866066375391085845)
        ·
          refine ⟨18866304415596861346457149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 402481160866066375391085845 18866304415596861346457149)
          ·
            refine ⟨7074864155848823004921431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18866304415596861346457149 7074864155848823004921431)
            ·
              refine ⟨10612296233773234507382147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7074864155848823004921431 10612296233773234507382147)
              ·
                refine ⟨15918444350659851761073221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10612296233773234507382147 15918444350659851761073221)
                ·
                  refine ⟨2984708315748722205201229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15918444350659851761073221 2984708315748722205201229)
                  ·
                    refine ⟨1119265618405770826950461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2984708315748722205201229 1119265618405770826950461)
                    ·
                      rfl

theorem cell22_3269643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 3].length) (baseStart_3269643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269643 prefixEnd_3269643 := by exact prefixLift 3269643
  have htrace : WordTrace (prefixWord ++ tailWord_3269643) baseStart_3269643 baseEnd_3269643 := by
    simpa [prefixWord, tailWord_3269643, baseEnd_3269643] using wordTrace_append hprefix tailTrace_3269643
  have hstable : (prefixWord ++ tailWord_3269643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269643).length < 2 ^ (prefixWord ++ tailWord_3269643).sum := by decide
  have hdescent : baseEnd_3269643 < baseStart_3269643 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269660 : List Nat := [2, 2, 3, 1, 4, 2, 1, 1, 1, 5]
def baseStart_3269660 : Nat := 118140960795 + 3269660 * 2 ^ 59
def prefixEnd_3269660 : Nat := 4983230072969 + 3 ^ 40 * 3269660 * 2
def baseEnd_3269660 : Nat := 1119271437853188449275409

theorem tailTrace_3269660 : CollatzResearch.WordTrace tailWord_3269660 prefixEnd_3269660 1119271437853188449275409 := by
  unfold tailWord_3269660
  simp only [CollatzResearch.WordTrace]
  refine ⟨59627148667293854157771217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79502864889725138877028289 59627148667293854157771217)
  ·
    refine ⟨44720361500470390618328413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59627148667293854157771217 44720361500470390618328413)
    ·
      refine ⟨16770135562676396481873155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44720361500470390618328413 16770135562676396481873155)
      ·
        refine ⟨25155203344014594722809733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16770135562676396481873155 25155203344014594722809733)
        ·
          refine ⟨4716600627002736510526825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25155203344014594722809733 4716600627002736510526825)
          ·
            refine ⟨3537450470252052382895119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4716600627002736510526825 3537450470252052382895119)
            ·
              refine ⟨5306175705378078574342679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3537450470252052382895119 5306175705378078574342679)
              ·
                refine ⟨7959263558067117861514019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5306175705378078574342679 7959263558067117861514019)
                ·
                  refine ⟨11938895337100676792271029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7959263558067117861514019 11938895337100676792271029)
                  ·
                    refine ⟨1119271437853188449275409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11938895337100676792271029 1119271437853188449275409)
                    ·
                      rfl

theorem cell22_3269660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_3269660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269660 prefixEnd_3269660 := by exact prefixLift 3269660
  have htrace : WordTrace (prefixWord ++ tailWord_3269660) baseStart_3269660 baseEnd_3269660 := by
    simpa [prefixWord, tailWord_3269660, baseEnd_3269660] using wordTrace_append hprefix tailTrace_3269660
  have hstable : (prefixWord ++ tailWord_3269660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269660).length < 2 ^ (prefixWord ++ tailWord_3269660).sum := by decide
  have hdescent : baseEnd_3269660 < baseStart_3269660 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269701 : List Nat := [1, 3, 1, 1, 1, 3, 4, 1, 7]
def baseStart_3269701 : Nat := 118140960795 + 3269701 * 2 ^ 59
def prefixEnd_3269701 : Nat := 4983230072969 + 3 ^ 40 * 3269701 * 2
def baseEnd_3269701 : Nat := 373095157663692669666761

theorem tailTrace_3269701 : CollatzResearch.WordTrace tailWord_3269701 prefixEnd_3269701 373095157663692669666761 := by
  unfold tailWord_3269701
  simp only [CollatzResearch.WordTrace]
  refine ⟨119255792727439172317784957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79503861818292781545189971 119255792727439172317784957)
  ·
    refine ⟨44720922272789689619169359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119255792727439172317784957 44720922272789689619169359)
    ·
      refine ⟨67081383409184534428754039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44720922272789689619169359 67081383409184534428754039)
      ·
        refine ⟨100622075113776801643131059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67081383409184534428754039 100622075113776801643131059)
        ·
          refine ⟨150933112670665202464696589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100622075113776801643131059 150933112670665202464696589)
          ·
            refine ⟨56599917251499450924261221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 150933112670665202464696589 56599917251499450924261221)
            ·
              refine ⟨10612484484656147048298979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56599917251499450924261221 10612484484656147048298979)
              ·
                refine ⟨15918726726984220572448469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10612484484656147048298979 15918726726984220572448469)
                ·
                  refine ⟨373095157663692669666761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15918726726984220572448469 373095157663692669666761)
                  ·
                    rfl

theorem cell22_3269701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 1, 7].length) (baseStart_3269701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269701 prefixEnd_3269701 := by exact prefixLift 3269701
  have htrace : WordTrace (prefixWord ++ tailWord_3269701) baseStart_3269701 baseEnd_3269701 := by
    simpa [prefixWord, tailWord_3269701, baseEnd_3269701] using wordTrace_append hprefix tailTrace_3269701
  have hstable : (prefixWord ++ tailWord_3269701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269701).length < 2 ^ (prefixWord ++ tailWord_3269701).sum := by decide
  have hdescent : baseEnd_3269701 < baseStart_3269701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269793 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 1, 6]
def baseStart_3269793 : Nat := 118140960795 + 3269793 * 2 ^ 59
def prefixEnd_3269793 : Nat := 4983230072969 + 3 ^ 40 * 3269793 * 2
def baseEnd_3269793 : Nat := 1119316966471220435700001

theorem tailTrace_3269793 : CollatzResearch.WordTrace tailWord_3269793 prefixEnd_3269793 1119316966471220435700001 := by
  unfold tailWord_3269793
  simp only [CollatzResearch.WordTrace]
  refine ⟨119259148243105872030134033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79506098828737248020089355 119259148243105872030134033)
  ·
    refine ⟨89444361182329404022600525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119259148243105872030134033 89444361182329404022600525)
    ·
      refine ⟨33541635443373526508475197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89444361182329404022600525 33541635443373526508475197)
      ·
        refine ⟨12578113291265072440678199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33541635443373526508475197 12578113291265072440678199)
        ·
          refine ⟨18867169936897608661017299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12578113291265072440678199 18867169936897608661017299)
          ·
            refine ⟨28300754905346412991525949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18867169936897608661017299 28300754905346412991525949)
            ·
              refine ⟨10612783089504904871822231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28300754905346412991525949 10612783089504904871822231)
              ·
                refine ⟨15919174634257357307733347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10612783089504904871822231 15919174634257357307733347)
                ·
                  refine ⟨23878761951386035961600021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15919174634257357307733347 23878761951386035961600021)
                  ·
                    refine ⟨1119316966471220435700001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23878761951386035961600021 1119316966471220435700001)
                    ·
                      rfl

theorem cell22_3269793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 1, 6].length) (baseStart_3269793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269793 prefixEnd_3269793 := by exact prefixLift 3269793
  have htrace : WordTrace (prefixWord ++ tailWord_3269793) baseStart_3269793 baseEnd_3269793 := by
    simpa [prefixWord, tailWord_3269793, baseEnd_3269793] using wordTrace_append hprefix tailTrace_3269793
  have hstable : (prefixWord ++ tailWord_3269793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269793).length < 2 ^ (prefixWord ++ tailWord_3269793).sum := by decide
  have hdescent : baseEnd_3269793 < baseStart_3269793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269799 : List Nat := [1, 1, 6, 2, 1, 3, 2, 1, 1, 4]
def baseStart_3269799 : Nat := 118140960795 + 3269799 * 2 ^ 59
def prefixEnd_3269799 : Nat := 4983230072969 + 3 ^ 40 * 3269799 * 2
def baseEnd_3269799 : Nat := 1119319020393838420049983

theorem tailTrace_3269799 : CollatzResearch.WordTrace tailWord_3269799 prefixEnd_3269799 1119319020393838420049983 := by
  unfold tailWord_3269799
  simp only [CollatzResearch.WordTrace]
  refine ⟨119259367081084135054852451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79506244720722756703234967 119259367081084135054852451)
  ·
    refine ⟨178889050621626202582278677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119259367081084135054852451 178889050621626202582278677)
    ·
      refine ⟨8385424247888728246044313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 178889050621626202582278677 8385424247888728246044313)
      ·
        refine ⟨6289068185916546184533235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8385424247888728246044313 6289068185916546184533235)
        ·
          refine ⟨9433602278874819276799853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6289068185916546184533235 9433602278874819276799853)
          ·
            refine ⟨3537600854578057228799945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9433602278874819276799853 3537600854578057228799945)
            ·
              refine ⟨2653200640933542921599959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3537600854578057228799945 2653200640933542921599959)
              ·
                refine ⟨3979800961400314382399939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2653200640933542921599959 3979800961400314382399939)
                ·
                  refine ⟨5969701442100471573599909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3979800961400314382399939 5969701442100471573599909)
                  ·
                    refine ⟨1119319020393838420049983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5969701442100471573599909 1119319020393838420049983)
                    ·
                      rfl

theorem cell22_3269799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_3269799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269799 prefixEnd_3269799 := by exact prefixLift 3269799
  have htrace : WordTrace (prefixWord ++ tailWord_3269799) baseStart_3269799 baseEnd_3269799 := by
    simpa [prefixWord, tailWord_3269799, baseEnd_3269799] using wordTrace_append hprefix tailTrace_3269799
  have hstable : (prefixWord ++ tailWord_3269799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269799).length < 2 ^ (prefixWord ++ tailWord_3269799).sum := by decide
  have hdescent : baseEnd_3269799 < baseStart_3269799 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269814 : List Nat := [5, 1, 3, 2, 1, 1, 2, 1, 6]
def baseStart_3269814 : Nat := 118140960795 + 3269814 * 2 ^ 59
def prefixEnd_3269814 : Nat := 4983230072969 + 3 ^ 40 * 3269814 * 2
def baseEnd_3269814 : Nat := 373108051733461126974979

theorem tailTrace_3269814 : CollatzResearch.WordTrace tailWord_3269814 prefixEnd_3269814 373108051733461126974979 := by
  unfold tailWord_3269814
  simp only [CollatzResearch.WordTrace]
  refine ⟨7453744636001862038540531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79506609450686528411098997 7453744636001862038540531)
  ·
    refine ⟨11180616954002793057810797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7453744636001862038540531 11180616954002793057810797)
    ·
      refine ⟨4192731357751047396679049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11180616954002793057810797 4192731357751047396679049)
      ·
        refine ⟨3144548518313285547509287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4192731357751047396679049 3144548518313285547509287)
        ·
          refine ⟨4716822777469928321263931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3144548518313285547509287 4716822777469928321263931)
          ·
            refine ⟨7075234166204892481895897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4716822777469928321263931 7075234166204892481895897)
            ·
              refine ⟨5306425624653669361421923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7075234166204892481895897 5306425624653669361421923)
              ·
                refine ⟨7959638436980504042132885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5306425624653669361421923 7959638436980504042132885)
                ·
                  refine ⟨373108051733461126974979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7959638436980504042132885 373108051733461126974979)
                  ·
                    rfl

theorem cell22_3269814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 1, 6].length) (baseStart_3269814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269814 prefixEnd_3269814 := by exact prefixLift 3269814
  have htrace : WordTrace (prefixWord ++ tailWord_3269814) baseStart_3269814 baseEnd_3269814 := by
    simpa [prefixWord, tailWord_3269814, baseEnd_3269814] using wordTrace_append hprefix tailTrace_3269814
  have hstable : (prefixWord ++ tailWord_3269814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269814).length < 2 ^ (prefixWord ++ tailWord_3269814).sum := by decide
  have hdescent : baseEnd_3269814 < baseStart_3269814 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269874 : List Nat := [3, 2, 1, 3, 3, 2, 1, 1, 3, 3]
def baseStart_3269874 : Nat := 118140960795 + 3269874 * 2 ^ 59
def prefixEnd_3269874 : Nat := 4983230072969 + 3 ^ 40 * 3269874 * 2
def baseEnd_3269874 : Nat := 1119344694426563224424753

theorem tailTrace_3269874 : CollatzResearch.WordTrace tailWord_3269874 prefixEnd_3269874 1119344694426563224424753 := by
  unfold tailWord_3269874
  simp only [CollatzResearch.WordTrace]
  refine ⟨29815525638953105715958169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79508068370541615242555117 29815525638953105715958169)
  ·
    refine ⟨22361644229214829286968627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29815525638953105715958169 22361644229214829286968627)
    ·
      refine ⟨33542466343822243930452941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22361644229214829286968627 33542466343822243930452941)
      ·
        refine ⟨12578424878933341473919853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33542466343822243930452941 12578424878933341473919853)
        ·
          refine ⟨4716909329600003052719945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12578424878933341473919853 4716909329600003052719945)
          ·
            refine ⟨3537681997200002289539959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4716909329600003052719945 3537681997200002289539959)
            ·
              refine ⟨5306522995800003434309939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3537681997200002289539959 5306522995800003434309939)
              ·
                refine ⟨7959784493700005151464909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5306522995800003434309939 7959784493700005151464909)
                ·
                  refine ⟨2984919185137501931799341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7959784493700005151464909 2984919185137501931799341)
                  ·
                    refine ⟨1119344694426563224424753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2984919185137501931799341 1119344694426563224424753)
                    ·
                      rfl

theorem cell22_3269874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 2, 1, 1, 3, 3].length) (baseStart_3269874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269874 prefixEnd_3269874 := by exact prefixLift 3269874
  have htrace : WordTrace (prefixWord ++ tailWord_3269874) baseStart_3269874 baseEnd_3269874 := by
    simpa [prefixWord, tailWord_3269874, baseEnd_3269874] using wordTrace_append hprefix tailTrace_3269874
  have hstable : (prefixWord ++ tailWord_3269874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269874).length < 2 ^ (prefixWord ++ tailWord_3269874).sum := by decide
  have hdescent : baseEnd_3269874 < baseStart_3269874 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269887 : List Nat := [1, 1, 2, 2, 1, 7, 2, 1, 5]
def baseStart_3269887 : Nat := 118140960795 + 3269887 * 2 ^ 59
def prefixEnd_3269887 : Nat := 4983230072969 + 3 ^ 40 * 3269887 * 2
def baseEnd_3269887 : Nat := 373116381530745174616571

theorem tailTrace_3269887 : CollatzResearch.WordTrace tailWord_3269887 prefixEnd_3269887 373116381530745174616571 := by
  unfold tailWord_3269887
  simp only [CollatzResearch.WordTrace]
  refine ⟨119262576704765326084055915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79508384469843550722703943 119262576704765326084055915)
  ·
    refine ⟨178893865057147989126083873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119262576704765326084055915 178893865057147989126083873)
    ·
      refine ⟨134170398792860991844562905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178893865057147989126083873 134170398792860991844562905)
      ·
        refine ⟨100627799094645743883422179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134170398792860991844562905 100627799094645743883422179)
        ·
          refine ⟨150941698641968615825133269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100627799094645743883422179 150941698641968615825133269)
          ·
            refine ⟨3537696061921139433401561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 150941698641968615825133269 3537696061921139433401561)
            ·
              refine ⟨2653272046440854575051171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3537696061921139433401561 2653272046440854575051171)
              ·
                refine ⟨3979908069661281862576757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2653272046440854575051171 3979908069661281862576757)
                ·
                  refine ⟨373116381530745174616571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3979908069661281862576757 373116381530745174616571)
                  ·
                    rfl

theorem cell22_3269887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 1, 5].length) (baseStart_3269887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269887 prefixEnd_3269887 := by exact prefixLift 3269887
  have htrace : WordTrace (prefixWord ++ tailWord_3269887) baseStart_3269887 baseEnd_3269887 := by
    simpa [prefixWord, tailWord_3269887, baseEnd_3269887] using wordTrace_append hprefix tailTrace_3269887
  have hstable : (prefixWord ++ tailWord_3269887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269887).length < 2 ^ (prefixWord ++ tailWord_3269887).sum := by decide
  have hdescent : baseEnd_3269887 < baseStart_3269887 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269898 : List Nat := [3, 1, 2, 2, 1, 1, 1, 3, 8]
def baseStart_3269898 : Nat := 118140960795 + 3269898 * 2 ^ 59
def prefixEnd_3269898 : Nat := 4983230072969 + 3 ^ 40 * 3269898 * 2
def baseEnd_3269898 : Nat := 373117636705678387274893

theorem tailTrace_3269898 : CollatzResearch.WordTrace tailWord_3269898 prefixEnd_3269898 373117636705678387274893 := by
  unfold tailWord_3269898
  simp only [CollatzResearch.WordTrace]
  refine ⟨29815744476931368740676587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79508651938483649975137565 29815744476931368740676587)
  ·
    refine ⟨44723616715397053111014881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29815744476931368740676587 44723616715397053111014881)
    ·
      refine ⟨33542712536547789833261161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44723616715397053111014881 33542712536547789833261161)
      ·
        refine ⟨25157034402410842374945871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33542712536547789833261161 25157034402410842374945871)
        ·
          refine ⟨37735551603616263562418807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25157034402410842374945871 37735551603616263562418807)
          ·
            refine ⟨56603327405424395343628211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37735551603616263562418807 56603327405424395343628211)
            ·
              refine ⟨84904991108136593015442317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56603327405424395343628211 84904991108136593015442317)
              ·
                refine ⟨31839371665551222380790869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 84904991108136593015442317 31839371665551222380790869)
                ·
                  refine ⟨373117636705678387274893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31839371665551222380790869 373117636705678387274893)
                  ·
                    rfl

theorem cell22_3269898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_3269898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269898 prefixEnd_3269898 := by exact prefixLift 3269898
  have htrace : WordTrace (prefixWord ++ tailWord_3269898) baseStart_3269898 baseEnd_3269898 := by
    simpa [prefixWord, tailWord_3269898, baseEnd_3269898] using wordTrace_append hprefix tailTrace_3269898
  have hstable : (prefixWord ++ tailWord_3269898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269898).length < 2 ^ (prefixWord ++ tailWord_3269898).sum := by decide
  have hdescent : baseEnd_3269898 < baseStart_3269898 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269900 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 3, 4]
def baseStart_3269900 : Nat := 118140960795 + 3269900 * 2 ^ 59
def prefixEnd_3269900 : Nat := 4983230072969 + 3 ^ 40 * 3269900 * 2
def baseEnd_3269900 : Nat := 1119353594757907823274673

theorem tailTrace_3269900 : CollatzResearch.WordTrace tailWord_3269900 prefixEnd_3269900 1119353594757907823274673 := by
  unfold tailWord_3269900
  simp only [CollatzResearch.WordTrace]
  refine ⟨59631525426859114652139577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79508700569145486202852769 59631525426859114652139577)
  ·
    refine ⟨44723644070144335989104683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59631525426859114652139577 44723644070144335989104683)
    ·
      refine ⟨67085466105216503983657025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44723644070144335989104683 67085466105216503983657025)
      ·
        refine ⟨50314099578912377987742769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67085466105216503983657025 50314099578912377987742769)
        ·
          refine ⟨37735574684184283490807077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50314099578912377987742769 37735574684184283490807077)
          ·
            refine ⟨7075420253284553154526327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37735574684184283490807077 7075420253284553154526327)
            ·
              refine ⟨10613130379926829731789491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7075420253284553154526327 10613130379926829731789491)
              ·
                refine ⟨15919695569890244597684237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10613130379926829731789491 15919695569890244597684237)
                ·
                  refine ⟨5969885838708841724131589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15919695569890244597684237 5969885838708841724131589)
                  ·
                    refine ⟨1119353594757907823274673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5969885838708841724131589 1119353594757907823274673)
                    ·
                      rfl

theorem cell22_3269900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 3, 4].length) (baseStart_3269900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269900 prefixEnd_3269900 := by exact prefixLift 3269900
  have htrace : WordTrace (prefixWord ++ tailWord_3269900) baseStart_3269900 baseEnd_3269900 := by
    simpa [prefixWord, tailWord_3269900, baseEnd_3269900] using wordTrace_append hprefix tailTrace_3269900
  have hstable : (prefixWord ++ tailWord_3269900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269900).length < 2 ^ (prefixWord ++ tailWord_3269900).sum := by decide
  have hdescent : baseEnd_3269900 < baseStart_3269900 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269915 : List Nat := [1, 1, 1, 1, 1, 1, 5, 7, 4]
def baseStart_3269915 : Nat := 118140960795 + 3269915 * 2 ^ 59
def prefixEnd_3269915 : Nat := 4983230072969 + 3 ^ 40 * 3269915 * 2
def baseEnd_3269915 : Nat := 373119576521484261383209

theorem tailTrace_3269915 : CollatzResearch.WordTrace tailWord_3269915 prefixEnd_3269915 373119576521484261383209 := by
  unfold tailWord_3269915
  simp only [CollatzResearch.WordTrace]
  refine ⟨119263597948663886866075199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79509065299109257910716799 119263597948663886866075199)
  ·
    refine ⟨178895396922995830299112799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119263597948663886866075199 178895396922995830299112799)
    ·
      refine ⟨268343095384493745448669199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178895396922995830299112799 268343095384493745448669199)
      ·
        refine ⟨402514643076740618173003799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268343095384493745448669199 402514643076740618173003799)
        ·
          refine ⟨603771964615110927259505699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402514643076740618173003799 603771964615110927259505699)
          ·
            refine ⟨905657946922666390889258549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603771964615110927259505699 905657946922666390889258549)
            ·
              refine ⟨84905432523999974145867989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 905657946922666390889258549 84905432523999974145867989)
              ·
                refine ⟨1989971074781249394043781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 84905432523999974145867989 1989971074781249394043781)
                ·
                  refine ⟨373119576521484261383209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1989971074781249394043781 373119576521484261383209)
                  ·
                    rfl

theorem cell22_3269915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 7, 4].length) (baseStart_3269915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269915 prefixEnd_3269915 := by exact prefixLift 3269915
  have htrace : WordTrace (prefixWord ++ tailWord_3269915) baseStart_3269915 baseEnd_3269915 := by
    simpa [prefixWord, tailWord_3269915, baseEnd_3269915] using wordTrace_append hprefix tailTrace_3269915
  have hstable : (prefixWord ++ tailWord_3269915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269915).length < 2 ^ (prefixWord ++ tailWord_3269915).sum := by decide
  have hdescent : baseEnd_3269915 < baseStart_3269915 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3269998 : List Nat := [4, 1, 2, 4, 1, 1, 3, 1, 2, 3]
def baseStart_3269998 : Nat := 118140960795 + 3269998 * 2 ^ 59
def prefixEnd_3269998 : Nat := 4983230072969 + 3 ^ 40 * 3269998 * 2
def baseEnd_3269998 : Nat := 1119387142160668234324373

theorem tailTrace_3269998 : CollatzResearch.WordTrace tailWord_3269998 prefixEnd_3269998 1119387142160668234324373 := by
  unfold tailWord_3269998
  simp only [CollatzResearch.WordTrace]
  refine ⟨14908328150920399005168331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79511083471575461360897765 14908328150920399005168331)
  ·
    refine ⟨22362492226380598507752497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14908328150920399005168331 22362492226380598507752497)
    ·
      refine ⟨16771869169785448880814373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22362492226380598507752497 16771869169785448880814373)
      ·
        refine ⟨3144725469334771665152695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16771869169785448880814373 3144725469334771665152695)
        ·
          refine ⟨4717088204002157497729043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3144725469334771665152695 4717088204002157497729043)
          ·
            refine ⟨7075632306003236246593565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4717088204002157497729043 7075632306003236246593565)
            ·
              refine ⟨2653362114751213592472587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7075632306003236246593565 2653362114751213592472587)
              ·
                refine ⟨3980043172126820388708881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2653362114751213592472587 3980043172126820388708881)
                ·
                  refine ⟨2985032379095115291531661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3980043172126820388708881 2985032379095115291531661)
                  ·
                    refine ⟨1119387142160668234324373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2985032379095115291531661 1119387142160668234324373)
                    ·
                      rfl

theorem cell22_3269998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 1, 2, 3].length) (baseStart_3269998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3269998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3269998 prefixEnd_3269998 := by exact prefixLift 3269998
  have htrace : WordTrace (prefixWord ++ tailWord_3269998) baseStart_3269998 baseEnd_3269998 := by
    simpa [prefixWord, tailWord_3269998, baseEnd_3269998] using wordTrace_append hprefix tailTrace_3269998
  have hstable : (prefixWord ++ tailWord_3269998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3269998).length < 2 ^ (prefixWord ++ tailWord_3269998).sum := by decide
  have hdescent : baseEnd_3269998 < baseStart_3269998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3269998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270069 : List Nat := [1, 3, 3, 2, 2, 1, 3, 2, 1, 4]
def baseStart_3270069 : Nat := 118140960795 + 3270069 * 2 ^ 59
def prefixEnd_3270069 : Nat := 4983230072969 + 3 ^ 40 * 3270069 * 2
def baseEnd_3270069 : Nat := 1119411446911647715799155

theorem tailTrace_3270069 : CollatzResearch.WordTrace tailWord_3270069 prefixEnd_3270069 1119411446911647715799155 := by
  unfold tailWord_3270069
  simp only [CollatzResearch.WordTrace]
  refine ⟨119269214790105971167181261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79512809860070647444787507 119269214790105971167181261)
  ·
    refine ⟨44725955546289739187692973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119269214790105971167181261 44725955546289739187692973)
    ·
      refine ⟨16772233329858652195384865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44725955546289739187692973 16772233329858652195384865)
      ·
        refine ⟨12579174997393989146538649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16772233329858652195384865 12579174997393989146538649)
        ·
          refine ⟨9434381248045491859903987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12579174997393989146538649 9434381248045491859903987)
          ·
            refine ⟨14151571872068237789855981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9434381248045491859903987 14151571872068237789855981)
            ·
              refine ⟨5306839452025589171195993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14151571872068237789855981 5306839452025589171195993)
              ·
                refine ⟨3980129589019191878396995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5306839452025589171195993 3980129589019191878396995)
                ·
                  refine ⟨5970194383528787817595493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3980129589019191878396995 5970194383528787817595493)
                  ·
                    refine ⟨1119411446911647715799155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5970194383528787817595493 1119411446911647715799155)
                    ·
                      rfl

theorem cell22_3270069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 3, 2, 1, 4].length) (baseStart_3270069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270069 prefixEnd_3270069 := by exact prefixLift 3270069
  have htrace : WordTrace (prefixWord ++ tailWord_3270069) baseStart_3270069 baseEnd_3270069 := by
    simpa [prefixWord, tailWord_3270069, baseEnd_3270069] using wordTrace_append hprefix tailTrace_3270069
  have hstable : (prefixWord ++ tailWord_3270069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270069).length < 2 ^ (prefixWord ++ tailWord_3270069).sum := by decide
  have hdescent : baseEnd_3270069 < baseStart_3270069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270080 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 1, 6]
def baseStart_3270080 : Nat := 118140960795 + 3270080 * 2 ^ 59
def prefixEnd_3270080 : Nat := 4983230072969 + 3 ^ 40 * 3270080 * 2
def baseEnd_3270080 : Nat := 1119415212436447353774121

theorem tailTrace_3270080 : CollatzResearch.WordTrace tailWord_3270080 prefixEnd_3270080 1119415212436447353774121 := by
  unfold tailWord_3270080
  simp only [CollatzResearch.WordTrace]
  refine ⟨59634807996533060022915847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79513077328710746697221129 59634807996533060022915847)
  ·
    refine ⟨89452211994799590034373771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59634807996533060022915847 89452211994799590034373771)
    ·
      refine ⟨134178317992199385051560657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89452211994799590034373771 134178317992199385051560657)
      ·
        refine ⟨100633738494149538788670493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134178317992199385051560657 100633738494149538788670493)
        ·
          refine ⟨37737651935306077045751435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100633738494149538788670493 37737651935306077045751435)
          ·
            refine ⟨56606477902959115568627153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37737651935306077045751435 56606477902959115568627153)
            ·
              refine ⟨42454858427219336676470365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56606477902959115568627153 42454858427219336676470365)
              ·
                refine ⟨15920571910207251253676387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42454858427219336676470365 15920571910207251253676387)
                ·
                  refine ⟨23880857865310876880514581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15920571910207251253676387 23880857865310876880514581)
                  ·
                    refine ⟨1119415212436447353774121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23880857865310876880514581 1119415212436447353774121)
                    ·
                      rfl

theorem cell22_3270080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 1, 6].length) (baseStart_3270080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270080 prefixEnd_3270080 := by exact prefixLift 3270080
  have htrace : WordTrace (prefixWord ++ tailWord_3270080) baseStart_3270080 baseEnd_3270080 := by
    simpa [prefixWord, tailWord_3270080, baseEnd_3270080] using wordTrace_append hprefix tailTrace_3270080
  have hstable : (prefixWord ++ tailWord_3270080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270080).length < 2 ^ (prefixWord ++ tailWord_3270080).sum := by decide
  have hdescent : baseEnd_3270080 < baseStart_3270080 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270127 : List Nat := [1, 1, 2, 1, 4, 1, 3, 1, 5, 3]
def baseStart_3270127 : Nat := 118140960795 + 3270127 * 2 ^ 59
def prefixEnd_3270127 : Nat := 4983230072969 + 3 ^ 40 * 3270127 * 2
def baseEnd_3270127 : Nat := 1119431301496954897848977

theorem tailTrace_3270127 : CollatzResearch.WordTrace tailWord_3270127 prefixEnd_3270127 1119431301496954897848977 := by
  unfold tailWord_3270127
  simp only [CollatzResearch.WordTrace]
  refine ⟨119271330223895847072792635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79514220149263898048528423 119271330223895847072792635)
  ·
    refine ⟨178906995335843770609188953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119271330223895847072792635 178906995335843770609188953)
    ·
      refine ⟨134180246501882827956891715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178906995335843770609188953 134180246501882827956891715)
      ·
        refine ⟨201270369752824241935337573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134180246501882827956891715 201270369752824241935337573)
        ·
          refine ⟨37738194328654545362875795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201270369752824241935337573 37738194328654545362875795)
          ·
            refine ⟨56607291492981818044313693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37738194328654545362875795 56607291492981818044313693)
            ·
              refine ⟨21227734309868181766617635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56607291492981818044313693 21227734309868181766617635)
              ·
                refine ⟨31841601464802272649926453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21227734309868181766617635 31841601464802272649926453)
                ·
                  refine ⟨2985150137325213060930605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 31841601464802272649926453 2985150137325213060930605)
                  ·
                    refine ⟨1119431301496954897848977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2985150137325213060930605 1119431301496954897848977)
                    ·
                      rfl

theorem cell22_3270127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 1, 5, 3].length) (baseStart_3270127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270127 prefixEnd_3270127 := by exact prefixLift 3270127
  have htrace : WordTrace (prefixWord ++ tailWord_3270127) baseStart_3270127 baseEnd_3270127 := by
    simpa [prefixWord, tailWord_3270127, baseEnd_3270127] using wordTrace_append hprefix tailTrace_3270127
  have hstable : (prefixWord ++ tailWord_3270127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270127).length < 2 ^ (prefixWord ++ tailWord_3270127).sum := by decide
  have hdescent : baseEnd_3270127 < baseStart_3270127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270150 : List Nat := [6, 2, 1, 1, 2, 1, 1, 1, 4, 3]
def baseStart_3270150 : Nat := 118140960795 + 3270150 * 2 ^ 59
def prefixEnd_3270150 : Nat := 4983230072969 + 3 ^ 40 * 3270150 * 2
def baseEnd_3270150 : Nat := 1119439174866990504523907

theorem tailTrace_3270150 : CollatzResearch.WordTrace tailWord_3270150 prefixEnd_3270150 1119439174866990504523907 := by
  unfold tailWord_3270150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3727255284462891312527497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 79514779401875014667253269 3727255284462891312527497)
  ·
    refine ⟨2795441463347168484395623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3727255284462891312527497 2795441463347168484395623)
    ·
      refine ⟨4193162195020752726593435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2795441463347168484395623 4193162195020752726593435)
      ·
        refine ⟨6289743292531129089890153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4193162195020752726593435 6289743292531129089890153)
        ·
          refine ⟨4717307469398346817417615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6289743292531129089890153 4717307469398346817417615)
          ·
            refine ⟨7075961204097520226126423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4717307469398346817417615 7075961204097520226126423)
            ·
              refine ⟨10613941806146280339189635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7075961204097520226126423 10613941806146280339189635)
              ·
                refine ⟨15920912709219420508784453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10613941806146280339189635 15920912709219420508784453)
                ·
                  refine ⟨2985171132978641345397085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15920912709219420508784453 2985171132978641345397085)
                  ·
                    refine ⟨1119439174866990504523907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2985171132978641345397085 1119439174866990504523907)
                    ·
                      rfl

theorem cell22_3270150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_3270150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270150 prefixEnd_3270150 := by exact prefixLift 3270150
  have htrace : WordTrace (prefixWord ++ tailWord_3270150) baseStart_3270150 baseEnd_3270150 := by
    simpa [prefixWord, tailWord_3270150, baseEnd_3270150] using wordTrace_append hprefix tailTrace_3270150
  have hstable : (prefixWord ++ tailWord_3270150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270150).length < 2 ^ (prefixWord ++ tailWord_3270150).sum := by decide
  have hdescent : baseEnd_3270150 < baseStart_3270150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270172 : List Nat := [2, 2, 3, 1, 2, 1, 1, 3, 2, 5]
def baseStart_3270172 : Nat := 118140960795 + 3270172 * 2 ^ 59
def prefixEnd_3270172 : Nat := 4983230072969 + 3 ^ 40 * 3270172 * 2
def baseEnd_3270172 : Nat := 1119446705916589780473839

theorem tailTrace_3270172 : CollatzResearch.WordTrace tailWord_3270172 prefixEnd_3270172 1119446705916589780473839 := by
  unfold tailWord_3270172
  simp only [CollatzResearch.WordTrace]
  refine ⟨59636485754366409879090385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79515314339155213172120513 59636485754366409879090385)
  ·
    refine ⟨44727364315774807409317789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59636485754366409879090385 44727364315774807409317789)
    ·
      refine ⟨16772761618415552778494171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44727364315774807409317789 16772761618415552778494171)
      ·
        refine ⟨25159142427623329167741257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16772761618415552778494171 25159142427623329167741257)
        ·
          refine ⟨18869356820717496875805943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25159142427623329167741257 18869356820717496875805943)
          ·
            refine ⟨28304035231076245313708915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18869356820717496875805943 28304035231076245313708915)
            ·
              refine ⟨42456052846614367970563373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28304035231076245313708915 42456052846614367970563373)
              ·
                refine ⟨15921019817480387988961265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42456052846614367970563373 15921019817480387988961265)
                ·
                  refine ⟨11940764863110290991720949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15921019817480387988961265 11940764863110290991720949)
                  ·
                    refine ⟨1119446705916589780473839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11940764863110290991720949 1119446705916589780473839)
                    ·
                      rfl

theorem cell22_3270172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_3270172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270172 prefixEnd_3270172 := by exact prefixLift 3270172
  have htrace : WordTrace (prefixWord ++ tailWord_3270172) baseStart_3270172 baseEnd_3270172 := by
    simpa [prefixWord, tailWord_3270172, baseEnd_3270172] using wordTrace_append hprefix tailTrace_3270172
  have hstable : (prefixWord ++ tailWord_3270172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270172).length < 2 ^ (prefixWord ++ tailWord_3270172).sum := by decide
  have hdescent : baseEnd_3270172 < baseStart_3270172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270232 : List Nat := [2, 1, 2, 2, 1, 2, 1, 1, 6, 4]
def baseStart_3270232 : Nat := 118140960795 + 3270232 * 2 ^ 59
def prefixEnd_3270232 : Nat := 4983230072969 + 3 ^ 40 * 3270232 * 2
def baseEnd_3270232 : Nat := 1119467245142769623973655

theorem tailTrace_3270232 : CollatzResearch.WordTrace tailWord_3270232 prefixEnd_3270232 1119467245142769623973655 := by
  unfold tailWord_3270232
  simp only [CollatzResearch.WordTrace]
  refine ⟨59637579944257725002682475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79516773259010300003576633 59637579944257725002682475)
  ·
    refine ⟨89456369916386587504023713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59637579944257725002682475 89456369916386587504023713)
    ·
      refine ⟨67092277437289940628017785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89456369916386587504023713 67092277437289940628017785)
      ·
        refine ⟨50319208077967455471013339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67092277437289940628017785 50319208077967455471013339)
        ·
          refine ⟨75478812116951183206520009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50319208077967455471013339 75478812116951183206520009)
          ·
            refine ⟨56609109087713387404890007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75478812116951183206520009 56609109087713387404890007)
            ·
              refine ⟨84913663631570081107335011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 56609109087713387404890007 84913663631570081107335011)
              ·
                refine ⟨127370495447355121661002517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84913663631570081107335011 127370495447355121661002517)
                ·
                  refine ⟨5970491974094771327859493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 127370495447355121661002517 5970491974094771327859493)
                  ·
                    refine ⟨1119467245142769623973655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5970491974094771327859493 1119467245142769623973655)
                    ·
                      rfl

theorem cell22_3270232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 1, 6, 4].length) (baseStart_3270232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270232 prefixEnd_3270232 := by exact prefixLift 3270232
  have htrace : WordTrace (prefixWord ++ tailWord_3270232) baseStart_3270232 baseEnd_3270232 := by
    simpa [prefixWord, tailWord_3270232, baseEnd_3270232] using wordTrace_append hprefix tailTrace_3270232
  have hstable : (prefixWord ++ tailWord_3270232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270232).length < 2 ^ (prefixWord ++ tailWord_3270232).sum := by decide
  have hdescent : baseEnd_3270232 < baseStart_3270232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270247 : List Nat := [1, 1, 5, 1, 1, 1, 4, 8]
def baseStart_3270247 : Nat := 118140960795 + 3270247 * 2 ^ 59
def prefixEnd_3270247 : Nat := 4983230072969 + 3 ^ 40 * 3270247 * 2
def baseEnd_3270247 : Nat := 124385819994368287205401

theorem tailTrace_3270247 : CollatzResearch.WordTrace tailWord_3270247 prefixEnd_3270247 124385819994368287205401 := by
  unfold tailWord_3270247
  simp only [CollatzResearch.WordTrace]
  refine ⟨119275706983461107567160995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79517137988974071711440663 119275706983461107567160995)
  ·
    refine ⟨178913560475191661350741493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119275706983461107567160995 178913560475191661350741493)
    ·
      refine ⟨16773146294549218251632015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 178913560475191661350741493 16773146294549218251632015)
      ·
        refine ⟨25159719441823827377448023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16773146294549218251632015 25159719441823827377448023)
        ·
          refine ⟨37739579162735741066172035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25159719441823827377448023 37739579162735741066172035)
          ·
            refine ⟨56609368744103611599258053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37739579162735741066172035 56609368744103611599258053)
            ·
              refine ⟨10614256639519427174860885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56609368744103611599258053 10614256639519427174860885)
              ·
                refine ⟨124385819994368287205401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10614256639519427174860885 124385819994368287205401)
                ·
                  rfl

theorem cell22_3270247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 8].length) (baseStart_3270247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270247 prefixEnd_3270247 := by exact prefixLift 3270247
  have htrace : WordTrace (prefixWord ++ tailWord_3270247) baseStart_3270247 baseEnd_3270247 := by
    simpa [prefixWord, tailWord_3270247, baseEnd_3270247] using wordTrace_append hprefix tailTrace_3270247
  have hstable : (prefixWord ++ tailWord_3270247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270247).length < 2 ^ (prefixWord ++ tailWord_3270247).sum := by decide
  have hdescent : baseEnd_3270247 < baseStart_3270247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270277 : List Nat := [1, 3, 1, 1, 4, 1, 1, 1, 1, 8]
def baseStart_3270277 : Nat := 118140960795 + 3270277 * 2 ^ 59
def prefixEnd_3270277 : Nat := 4983230072969 + 3 ^ 40 * 3270277 * 2
def baseEnd_3270277 : Nat := 1119482649562404506598517

theorem tailTrace_3270277 : CollatzResearch.WordTrace tailWord_3270277 prefixEnd_3270277 1119482649562404506598517 := by
  unfold tailWord_3270277
  simp only [CollatzResearch.WordTrace]
  refine ⟨119276801173352422690753085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79517867448901615127168723 119276801173352422690753085)
  ·
    refine ⟨44728800440007158509032407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119276801173352422690753085 44728800440007158509032407)
    ·
      refine ⟨67093200660010737763548611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44728800440007158509032407 67093200660010737763548611)
      ·
        refine ⟨100639800990016106645322917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67093200660010737763548611 100639800990016106645322917)
        ·
          refine ⟨18869962685628019995998047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100639800990016106645322917 18869962685628019995998047)
          ·
            refine ⟨28304944028442029993997071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18869962685628019995998047 28304944028442029993997071)
            ·
              refine ⟨42457416042663044990995607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28304944028442029993997071 42457416042663044990995607)
              ·
                refine ⟨63686124063994567486493411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42457416042663044990995607 63686124063994567486493411)
                ·
                  refine ⟨95529186095991851229740117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 63686124063994567486493411 95529186095991851229740117)
                  ·
                    refine ⟨1119482649562404506598517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 95529186095991851229740117 1119482649562404506598517)
                    ·
                      rfl

theorem cell22_3270277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 8].length) (baseStart_3270277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270277 prefixEnd_3270277 := by exact prefixLift 3270277
  have htrace : WordTrace (prefixWord ++ tailWord_3270277) baseStart_3270277 baseEnd_3270277 := by
    simpa [prefixWord, tailWord_3270277, baseEnd_3270277] using wordTrace_append hprefix tailTrace_3270277
  have hstable : (prefixWord ++ tailWord_3270277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270277).length < 2 ^ (prefixWord ++ tailWord_3270277).sum := by decide
  have hdescent : baseEnd_3270277 < baseStart_3270277 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270296 : List Nat := [2, 1, 2, 4, 1, 3, 1, 2, 3, 3]
def baseStart_3270296 : Nat := 118140960795 + 3270296 * 2 ^ 59
def prefixEnd_3270296 : Nat := 4983230072969 + 3 ^ 40 * 3270296 * 2
def baseEnd_3270296 : Nat := 1119489153650694790373459

theorem tailTrace_3270296 : CollatzResearch.WordTrace tailWord_3270296 prefixEnd_3270296 1119489153650694790373459 := by
  unfold tailWord_3270296
  simp only [CollatzResearch.WordTrace]
  refine ⟨59638747080141794467847371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79518329440189059290463161 59638747080141794467847371)
  ·
    refine ⟨89458120620212691701771057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59638747080141794467847371 89458120620212691701771057)
    ·
      refine ⟨67093590465159518776328293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89458120620212691701771057 67093590465159518776328293)
      ·
        refine ⟨12580048212217409770561555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67093590465159518776328293 12580048212217409770561555)
        ·
          refine ⟨18870072318326114655842333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12580048212217409770561555 18870072318326114655842333)
          ·
            refine ⟨7076277119372292995940875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18870072318326114655842333 7076277119372292995940875)
            ·
              refine ⟨10614415679058439493911313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7076277119372292995940875 10614415679058439493911313)
              ·
                refine ⟨7960811759293829620433485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10614415679058439493911313 7960811759293829620433485)
                ·
                  refine ⟨2985304409735186107662557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7960811759293829620433485 2985304409735186107662557)
                  ·
                    refine ⟨1119489153650694790373459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2985304409735186107662557 1119489153650694790373459)
                    ·
                      rfl

theorem cell22_3270296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 2, 3, 3].length) (baseStart_3270296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270296 prefixEnd_3270296 := by exact prefixLift 3270296
  have htrace : WordTrace (prefixWord ++ tailWord_3270296) baseStart_3270296 baseEnd_3270296 := by
    simpa [prefixWord, tailWord_3270296, baseEnd_3270296] using wordTrace_append hprefix tailTrace_3270296
  have hstable : (prefixWord ++ tailWord_3270296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270296).length < 2 ^ (prefixWord ++ tailWord_3270296).sum := by decide
  have hdescent : baseEnd_3270296 < baseStart_3270296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270307 : List Nat := [1, 1, 1, 4, 1, 1, 3, 2, 1, 7]
def baseStart_3270307 : Nat := 118140960795 + 3270307 * 2 ^ 59
def prefixEnd_3270307 : Nat := 4983230072969 + 3 ^ 40 * 3270307 * 2
def baseEnd_3270307 : Nat := 1119492919175494428348425

theorem tailTrace_3270307 : CollatzResearch.WordTrace tailWord_3270307 prefixEnd_3270307 1119492919175494428348425 := by
  unfold tailWord_3270307
  simp only [CollatzResearch.WordTrace]
  refine ⟨119277895363243737814345175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79518596908829158542896783 119277895363243737814345175)
  ·
    refine ⟨178916843044865606721517763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119277895363243737814345175 178916843044865606721517763)
    ·
      refine ⟨268375264567298410082276645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178916843044865606721517763 268375264567298410082276645)
      ·
        refine ⟨50320362106368451890426871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 268375264567298410082276645 50320362106368451890426871)
        ·
          refine ⟨75480543159552677835640307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50320362106368451890426871 75480543159552677835640307)
          ·
            refine ⟨113220814739329016753460461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75480543159552677835640307 113220814739329016753460461)
            ·
              refine ⟨42457805527248381282547673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113220814739329016753460461 42457805527248381282547673)
              ·
                refine ⟨31843354145436285961910755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42457805527248381282547673 31843354145436285961910755)
                ·
                  refine ⟨47765031218154428942866133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31843354145436285961910755 47765031218154428942866133)
                  ·
                    refine ⟨1119492919175494428348425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47765031218154428942866133 1119492919175494428348425)
                    ·
                      rfl

theorem cell22_3270307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 2, 1, 7].length) (baseStart_3270307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270307 prefixEnd_3270307 := by exact prefixLift 3270307
  have htrace : WordTrace (prefixWord ++ tailWord_3270307) baseStart_3270307 baseEnd_3270307 := by
    simpa [prefixWord, tailWord_3270307, baseEnd_3270307] using wordTrace_append hprefix tailTrace_3270307
  have hstable : (prefixWord ++ tailWord_3270307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270307).length < 2 ^ (prefixWord ++ tailWord_3270307).sum := by decide
  have hdescent : baseEnd_3270307 < baseStart_3270307 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270364 : List Nat := [2, 2, 5, 1, 3, 1, 1, 3, 1, 3]
def baseStart_3270364 : Nat := 118140960795 + 3270364 * 2 ^ 59
def prefixEnd_3270364 : Nat := 4983230072969 + 3 ^ 40 * 3270364 * 2
def baseEnd_3270364 : Nat := 1119512431440365279673251

theorem tailTrace_3270364 : CollatzResearch.WordTrace tailWord_3270364 prefixEnd_3270364 1119512431440365279673251 := by
  unfold tailWord_3270364
  simp only [CollatzResearch.WordTrace]
  refine ⟨59639987162018618274585073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79519982882691491032780097 59639987162018618274585073)
  ·
    refine ⟨44729990371513963705938805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59639987162018618274585073 44729990371513963705938805)
    ·
      refine ⟨4193436597329434097431763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 44729990371513963705938805 4193436597329434097431763)
      ·
        refine ⟨6290154895994151146147645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4193436597329434097431763 6290154895994151146147645)
        ·
          refine ⟨2358808085997806679805367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6290154895994151146147645 2358808085997806679805367)
          ·
            refine ⟨3538212128996710019708051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2358808085997806679805367 3538212128996710019708051)
            ·
              refine ⟨5307318193495065029562077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3538212128996710019708051 5307318193495065029562077)
              ·
                refine ⟨1990244322560649386085779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5307318193495065029562077 1990244322560649386085779)
                ·
                  refine ⟨2985366483840974079128669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1990244322560649386085779 2985366483840974079128669)
                  ·
                    refine ⟨1119512431440365279673251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2985366483840974079128669 1119512431440365279673251)
                    ·
                      rfl

theorem cell22_3270364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_3270364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270364 prefixEnd_3270364 := by exact prefixLift 3270364
  have htrace : WordTrace (prefixWord ++ tailWord_3270364) baseStart_3270364 baseEnd_3270364 := by
    simpa [prefixWord, tailWord_3270364, baseEnd_3270364] using wordTrace_append hprefix tailTrace_3270364
  have hstable : (prefixWord ++ tailWord_3270364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270364).length < 2 ^ (prefixWord ++ tailWord_3270364).sum := by decide
  have hdescent : baseEnd_3270364 < baseStart_3270364 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270386 : List Nat := [3, 2, 1, 3, 1, 1, 1, 3, 4, 3]
def baseStart_3270386 : Nat := 118140960795 + 3270386 * 2 ^ 59
def prefixEnd_3270386 : Nat := 4983230072969 + 3 ^ 40 * 3270386 * 2
def baseEnd_3270386 : Nat := 1119519962489964555623183

theorem tailTrace_3270386 : CollatzResearch.WordTrace tailWord_3270386 prefixEnd_3270386 1119519962489964555623183 := by
  unfold tailWord_3270386
  simp only [CollatzResearch.WordTrace]
  refine ⟨29820194182489383576617753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79520517819971689537647341 29820194182489383576617753)
  ·
    refine ⟨22365145636867037682463315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29820194182489383576617753 22365145636867037682463315)
    ·
      refine ⟨33547718455300556523694973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22365145636867037682463315 33547718455300556523694973)
      ·
        refine ⟨12580394420737708696385615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33547718455300556523694973 12580394420737708696385615)
        ·
          refine ⟨18870591631106563044578423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12580394420737708696385615 18870591631106563044578423)
          ·
            refine ⟨28305887446659844566867635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18870591631106563044578423 28305887446659844566867635)
            ·
              refine ⟨42458831169989766850301453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28305887446659844566867635 42458831169989766850301453)
              ·
                refine ⟨15922061688746162568863045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42458831169989766850301453 15922061688746162568863045)
                ·
                  refine ⟨2985386566639905481661821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15922061688746162568863045 2985386566639905481661821)
                  ·
                    refine ⟨1119519962489964555623183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2985386566639905481661821 1119519962489964555623183)
                    ·
                      rfl

theorem cell22_3270386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_3270386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270386 prefixEnd_3270386 := by exact prefixLift 3270386
  have htrace : WordTrace (prefixWord ++ tailWord_3270386) baseStart_3270386 baseEnd_3270386 := by
    simpa [prefixWord, tailWord_3270386, baseEnd_3270386] using wordTrace_append hprefix tailTrace_3270386
  have hstable : (prefixWord ++ tailWord_3270386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270386).length < 2 ^ (prefixWord ++ tailWord_3270386).sum := by decide
  have hdescent : baseEnd_3270386 < baseStart_3270386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270403 : List Nat := [1, 1, 1, 3, 2, 2, 6, 1, 2, 3]
def baseStart_3270403 : Nat := 118140960795 + 3270403 * 2 ^ 59
def prefixEnd_3270403 : Nat := 4983230072969 + 3 ^ 40 * 3270403 * 2
def baseEnd_3270403 : Nat := 1119525781937382177948131

theorem tailTrace_3270403 : CollatzResearch.WordTrace tailWord_3270403 prefixEnd_3270403 1119525781937382177948131 := by
  unfold tailWord_3270403
  simp only [CollatzResearch.WordTrace]
  refine ⟨119281396770895946209839863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79520931180597297473226575 119281396770895946209839863)
  ·
    refine ⟨178922095156343919314759795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119281396770895946209839863 178922095156343919314759795)
    ·
      refine ⟨268383142734515878972139693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178922095156343919314759795 268383142734515878972139693)
      ·
        refine ⟨100643678525443454614552385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268383142734515878972139693 100643678525443454614552385)
        ·
          refine ⟨75482758894082590960914289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100643678525443454614552385 75482758894082590960914289)
          ·
            refine ⟨56612069170561943220685717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75482758894082590960914289 56612069170561943220685717)
            ·
              refine ⟨2653690742370091088469643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 56612069170561943220685717 2653690742370091088469643)
              ·
                refine ⟨3980536113555136632704465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2653690742370091088469643 3980536113555136632704465)
                ·
                  refine ⟨2985402085166352474528349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3980536113555136632704465 2985402085166352474528349)
                  ·
                    refine ⟨1119525781937382177948131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2985402085166352474528349 1119525781937382177948131)
                    ·
                      rfl

theorem cell22_3270403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 6, 1, 2, 3].length) (baseStart_3270403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270403 prefixEnd_3270403 := by exact prefixLift 3270403
  have htrace : WordTrace (prefixWord ++ tailWord_3270403) baseStart_3270403 baseEnd_3270403 := by
    simpa [prefixWord, tailWord_3270403, baseEnd_3270403] using wordTrace_append hprefix tailTrace_3270403
  have hstable : (prefixWord ++ tailWord_3270403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270403).length < 2 ^ (prefixWord ++ tailWord_3270403).sum := by decide
  have hdescent : baseEnd_3270403 < baseStart_3270403 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270414 : List Nat := [4, 1, 1, 2, 1, 1, 2, 1, 2, 7]
def baseStart_3270414 : Nat := 118140960795 + 3270414 * 2 ^ 59
def prefixEnd_3270414 : Nat := 4983230072969 + 3 ^ 40 * 3270414 * 2
def baseEnd_3270414 : Nat := 1119529547462181815923097

theorem tailTrace_3270414 : CollatzResearch.WordTrace tailWord_3270414 prefixEnd_3270414 1119529547462181815923097 := by
  unfold tailWord_3270414
  simp only [CollatzResearch.WordTrace]
  refine ⟨14910224746732011886061287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79521198649237396725660197 14910224746732011886061287)
  ·
    refine ⟨22365337120098017829091931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14910224746732011886061287 22365337120098017829091931)
    ·
      refine ⟨33548005680147026743637897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22365337120098017829091931 33548005680147026743637897)
      ·
        refine ⟨25161004260110270057728423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33548005680147026743637897 25161004260110270057728423)
        ·
          refine ⟨37741506390165405086592635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25161004260110270057728423 37741506390165405086592635)
          ·
            refine ⟨56612259585248107629888953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37741506390165405086592635 56612259585248107629888953)
            ·
              refine ⟨42459194688936080722416715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56612259585248107629888953 42459194688936080722416715)
              ·
                refine ⟨63688792033404121083625073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42459194688936080722416715 63688792033404121083625073)
                ·
                  refine ⟨47766594025053090812718805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63688792033404121083625073 47766594025053090812718805)
                  ·
                    refine ⟨1119529547462181815923097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47766594025053090812718805 1119529547462181815923097)
                    ·
                      rfl

theorem cell22_3270414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 2, 1, 2, 7].length) (baseStart_3270414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270414 prefixEnd_3270414 := by exact prefixLift 3270414
  have htrace : WordTrace (prefixWord ++ tailWord_3270414) baseStart_3270414 baseEnd_3270414 := by
    simpa [prefixWord, tailWord_3270414, baseEnd_3270414] using wordTrace_append hprefix tailTrace_3270414
  have hstable : (prefixWord ++ tailWord_3270414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270414).length < 2 ^ (prefixWord ++ tailWord_3270414).sum := by decide
  have hdescent : baseEnd_3270414 < baseStart_3270414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270418 : List Nat := [3, 2, 4, 1, 1, 1, 1, 3, 2, 4]
def baseStart_3270418 : Nat := 118140960795 + 3270418 * 2 ^ 59
def prefixEnd_3270418 : Nat := 4983230072969 + 3 ^ 40 * 3270418 * 2
def baseEnd_3270418 : Nat := 1119530916743927138823085

theorem tailTrace_3270418 : CollatzResearch.WordTrace tailWord_3270418 prefixEnd_3270418 1119530916743927138823085 := by
  unfold tailWord_3270418
  simp only [CollatzResearch.WordTrace]
  refine ⟨29820485966460400942908977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79521295910561069181090605 29820485966460400942908977)
  ·
    refine ⟨22365364474845300707181733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29820485966460400942908977 22365364474845300707181733)
    ·
      refine ⟨4193505839033493882596575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22365364474845300707181733 4193505839033493882596575)
      ·
        refine ⟨6290258758550240823894863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4193505839033493882596575 6290258758550240823894863)
        ·
          refine ⟨9435388137825361235842295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6290258758550240823894863 9435388137825361235842295)
          ·
            refine ⟨14153082206738041853763443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9435388137825361235842295 14153082206738041853763443)
            ·
              refine ⟨21229623310107062780645165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14153082206738041853763443 21229623310107062780645165)
              ·
                refine ⟨7961108741290148542741937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21229623310107062780645165 7961108741290148542741937)
                ·
                  refine ⟨5970831555967611407056453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7961108741290148542741937 5970831555967611407056453)
                  ·
                    refine ⟨1119530916743927138823085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5970831555967611407056453 1119530916743927138823085)
                    ·
                      rfl

theorem cell22_3270418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 2, 4].length) (baseStart_3270418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270418 prefixEnd_3270418 := by exact prefixLift 3270418
  have htrace : WordTrace (prefixWord ++ tailWord_3270418) baseStart_3270418 baseEnd_3270418 := by
    simpa [prefixWord, tailWord_3270418, baseEnd_3270418] using wordTrace_append hprefix tailTrace_3270418
  have hstable : (prefixWord ++ tailWord_3270418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270418).length < 2 ^ (prefixWord ++ tailWord_3270418).sum := by decide
  have hdescent : baseEnd_3270418 < baseStart_3270418 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270489 : List Nat := [1, 2, 1, 2, 2, 3, 1, 2, 8]
def baseStart_3270489 : Nat := 118140960795 + 3270489 * 2 ^ 59
def prefixEnd_3270489 : Nat := 4983230072969 + 3 ^ 40 * 3270489 * 2
def baseEnd_3270489 : Nat := 373185073831635540099289

theorem tailTrace_3270489 : CollatzResearch.WordTrace tailWord_3270489 prefixEnd_3270489 373185073831635540099289 := by
  unfold tailWord_3270489
  simp only [CollatzResearch.WordTrace]
  refine ⟨119284533448584382897470521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79523022299056255264980347 119284533448584382897470521)
  ·
    refine ⟨89463400086438287173102891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119284533448584382897470521 89463400086438287173102891)
    ·
      refine ⟨134195100129657430759654337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89463400086438287173102891 134195100129657430759654337)
      ·
        refine ⟨100646325097243073069740753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134195100129657430759654337 100646325097243073069740753)
        ·
          refine ⟨75484743822932304802305565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100646325097243073069740753 75484743822932304802305565)
          ·
            refine ⟨28306778933599614300864587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75484743822932304802305565 28306778933599614300864587)
            ·
              refine ⟨42460168400399421451296881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28306778933599614300864587 42460168400399421451296881)
              ·
                refine ⟨31845126300299566088472661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42460168400399421451296881 31845126300299566088472661)
                ·
                  refine ⟨373185073831635540099289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31845126300299566088472661 373185073831635540099289)
                  ·
                    rfl

theorem cell22_3270489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 2, 8].length) (baseStart_3270489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270489 prefixEnd_3270489 := by exact prefixLift 3270489
  have htrace : WordTrace (prefixWord ++ tailWord_3270489) baseStart_3270489 baseEnd_3270489 := by
    simpa [prefixWord, tailWord_3270489, baseEnd_3270489] using wordTrace_append hprefix tailTrace_3270489
  have hstable : (prefixWord ++ tailWord_3270489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270489).length < 2 ^ (prefixWord ++ tailWord_3270489).sum := by decide
  have hdescent : baseEnd_3270489 < baseStart_3270489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270551 : List Nat := [1, 1, 3, 3, 1, 5, 8]
def baseStart_3270551 : Nat := 118140960795 + 3270551 * 2 ^ 59
def prefixEnd_3270551 : Nat := 4983230072969 + 3 ^ 40 * 3270551 * 2
def baseEnd_3270551 : Nat := 41465794272665152786951

theorem tailTrace_3270551 : CollatzResearch.WordTrace tailWord_3270551 prefixEnd_3270551 41465794272665152786951 := by
  unfold tailWord_3270551
  simp only [CollatzResearch.WordTrace]
  refine ⟨119286794774359767486227507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79524529849573178324151671 119286794774359767486227507)
  ·
    refine ⟨178930192161539651229341261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119286794774359767486227507 178930192161539651229341261)
    ·
      refine ⟨67098822060577369211002973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 178930192161539651229341261 67098822060577369211002973)
      ·
        refine ⟨25162058272716513454126115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67098822060577369211002973 25162058272716513454126115)
        ·
          refine ⟨37743087409074770181189173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25162058272716513454126115 37743087409074770181189173)
          ·
            refine ⟨3538414444600759704486485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37743087409074770181189173 3538414444600759704486485)
            ·
              refine ⟨41465794272665152786951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3538414444600759704486485 41465794272665152786951)
              ·
                rfl

theorem cell22_3270551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 8].length) (baseStart_3270551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270551 prefixEnd_3270551 := by exact prefixLift 3270551
  have htrace : WordTrace (prefixWord ++ tailWord_3270551) baseStart_3270551 baseEnd_3270551 := by
    simpa [prefixWord, tailWord_3270551, baseEnd_3270551] using wordTrace_append hprefix tailTrace_3270551
  have hstable : (prefixWord ++ tailWord_3270551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270551).length < 2 ^ (prefixWord ++ tailWord_3270551).sum := by decide
  have hdescent : baseEnd_3270551 < baseStart_3270551 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270613 : List Nat := [1, 3, 2, 3, 2, 1, 1, 4, 5]
def baseStart_3270613 : Nat := 118140960795 + 3270613 * 2 ^ 59
def prefixEnd_3270613 : Nat := 4983230072969 + 3 ^ 40 * 3270613 * 2
def baseEnd_3270613 : Nat := 373199223076337210065829

theorem tailTrace_3270613 : CollatzResearch.WordTrace tailWord_3270613 prefixEnd_3270613 373199223076337210065829 := by
  unfold tailWord_3270613
  simp only [CollatzResearch.WordTrace]
  refine ⟨119289056100135152074984493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79526037400090101383322995 119289056100135152074984493)
  ·
    refine ⟨44733396037550682028119185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119289056100135152074984493 44733396037550682028119185)
    ·
      refine ⟨33550047028163011521089389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44733396037550682028119185 33550047028163011521089389)
      ·
        refine ⟨12581267635561129320408521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33550047028163011521089389 12581267635561129320408521)
        ·
          refine ⟨9435950726670846990306391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12581267635561129320408521 9435950726670846990306391)
          ·
            refine ⟨14153926090006270485459587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9435950726670846990306391 14153926090006270485459587)
            ·
              refine ⟨21230889135009405728189381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14153926090006270485459587 21230889135009405728189381)
              ·
                refine ⟨3980791712814263574035509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21230889135009405728189381 3980791712814263574035509)
                ·
                  refine ⟨373199223076337210065829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3980791712814263574035509 373199223076337210065829)
                  ·
                    rfl

theorem cell22_3270613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 4, 5].length) (baseStart_3270613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270613 prefixEnd_3270613 := by exact prefixLift 3270613
  have htrace : WordTrace (prefixWord ++ tailWord_3270613) baseStart_3270613 baseEnd_3270613 := by
    simpa [prefixWord, tailWord_3270613, baseEnd_3270613] using wordTrace_append hprefix tailTrace_3270613
  have hstable : (prefixWord ++ tailWord_3270613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270613).length < 2 ^ (prefixWord ++ tailWord_3270613).sum := by decide
  have hdescent : baseEnd_3270613 < baseStart_3270613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270617 : List Nat := [1, 2, 1, 2, 6, 1, 1, 4, 1, 3]
def baseStart_3270617 : Nat := 118140960795 + 3270617 * 2 ^ 59
def prefixEnd_3270617 : Nat := 4983230072969 + 3 ^ 40 * 3270617 * 2
def baseEnd_3270617 : Nat := 1119599038510756953097475

theorem tailTrace_3270617 : CollatzResearch.WordTrace tailWord_3270617 prefixEnd_3270617 1119599038510756953097475 := by
  unfold tailWord_3270617
  simp only [CollatzResearch.WordTrace]
  refine ⟨119289201992120660758130105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79526134661413773838753403 119289201992120660758130105)
  ·
    refine ⟨89466901494090495568597579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119289201992120660758130105 89466901494090495568597579)
    ·
      refine ⟨134200352241135743352896369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89466901494090495568597579 134200352241135743352896369)
      ·
        refine ⟨100650264180851807514672277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134200352241135743352896369 100650264180851807514672277)
        ·
          refine ⟨4717981133477428477250263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 100650264180851807514672277 4717981133477428477250263)
          ·
            refine ⟨7076971700216142715875395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4717981133477428477250263 7076971700216142715875395)
            ·
              refine ⟨10615457550324214073813093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7076971700216142715875395 10615457550324214073813093)
              ·
                refine ⟨1990398290685790138839955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10615457550324214073813093 1990398290685790138839955)
                ·
                  refine ⟨2985597436028685208259933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1990398290685790138839955 2985597436028685208259933)
                  ·
                    refine ⟨1119599038510756953097475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2985597436028685208259933 1119599038510756953097475)
                    ·
                      rfl

theorem cell22_3270617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 4, 1, 3].length) (baseStart_3270617 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270617 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270617 prefixEnd_3270617 := by exact prefixLift 3270617
  have htrace : WordTrace (prefixWord ++ tailWord_3270617) baseStart_3270617 baseEnd_3270617 := by
    simpa [prefixWord, tailWord_3270617, baseEnd_3270617] using wordTrace_append hprefix tailTrace_3270617
  have hstable : (prefixWord ++ tailWord_3270617).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270617).length < 2 ^ (prefixWord ++ tailWord_3270617).sum := by decide
  have hdescent : baseEnd_3270617 < baseStart_3270617 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270656 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 3, 5]
def baseStart_3270656 : Nat := 118140960795 + 3270656 * 2 ^ 59
def prefixEnd_3270656 : Nat := 4983230072969 + 3 ^ 40 * 3270656 * 2
def baseEnd_3270656 : Nat := 1119612389007773851372355

theorem tailTrace_3270656 : CollatzResearch.WordTrace tailWord_3270656 prefixEnd_3270656 1119612389007773851372355 := by
  unfold tailWord_3270656
  simp only [CollatzResearch.WordTrace]
  refine ⟨59645312219489685209399911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79527082959319580279199881 59645312219489685209399911)
  ·
    refine ⟨89467968329234527814099867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59645312219489685209399911 89467968329234527814099867)
    ·
      refine ⟨134201952493851791721149801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89467968329234527814099867 134201952493851791721149801)
      ·
        refine ⟨100651464370388843790862351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134201952493851791721149801 100651464370388843790862351)
        ·
          refine ⟨150977196555583265686293527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100651464370388843790862351 150977196555583265686293527)
          ·
            refine ⟨226465794833374898529440291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 150977196555583265686293527 226465794833374898529440291)
            ·
              refine ⟨339698692250062347794160437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 226465794833374898529440291 339698692250062347794160437)
              ·
                refine ⟨31846752398443345105702541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 339698692250062347794160437 31846752398443345105702541)
                ·
                  refine ⟨11942532149416254414638453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31846752398443345105702541 11942532149416254414638453)
                  ·
                    refine ⟨1119612389007773851372355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11942532149416254414638453 1119612389007773851372355)
                    ·
                      rfl

theorem cell22_3270656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 3, 5].length) (baseStart_3270656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270656 prefixEnd_3270656 := by exact prefixLift 3270656
  have htrace : WordTrace (prefixWord ++ tailWord_3270656) baseStart_3270656 baseEnd_3270656 := by
    simpa [prefixWord, tailWord_3270656, baseEnd_3270656] using wordTrace_append hprefix tailTrace_3270656
  have hstable : (prefixWord ++ tailWord_3270656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270656).length < 2 ^ (prefixWord ++ tailWord_3270656).sum := by decide
  have hdescent : baseEnd_3270656 < baseStart_3270656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270793 : List Nat := [1, 2, 1, 1, 4, 2, 2, 3, 6]
def baseStart_3270793 : Nat := 118140960795 + 3270793 * 2 ^ 59
def prefixEnd_3270793 : Nat := 4983230072969 + 3 ^ 40 * 3270793 * 2
def baseEnd_3270793 : Nat := 373219762302517053565645

theorem tailTrace_3270793 : CollatzResearch.WordTrace tailWord_3270793 prefixEnd_3270793 373219762302517053565645 := by
  unfold tailWord_3270793
  simp only [CollatzResearch.WordTrace]
  refine ⟨119295621239483042816537033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79530414159655361877691355 119295621239483042816537033)
  ·
    refine ⟨89471715929612282112402775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119295621239483042816537033 89471715929612282112402775)
    ·
      refine ⟨134207573894418423168604163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89471715929612282112402775 134207573894418423168604163)
      ·
        refine ⟨201311360841627634752906245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134207573894418423168604163 201311360841627634752906245)
        ·
          refine ⟨37745880157805181516169921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201311360841627634752906245 37745880157805181516169921)
          ·
            refine ⟨28309410118353886137127441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37745880157805181516169921 28309410118353886137127441)
            ·
              refine ⟨21232057588765414602845581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28309410118353886137127441 21232057588765414602845581)
              ·
                refine ⟨7962021595787030476067093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21232057588765414602845581 7962021595787030476067093)
                ·
                  refine ⟨373219762302517053565645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7962021595787030476067093 373219762302517053565645)
                  ·
                    rfl

theorem cell22_3270793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 3, 6].length) (baseStart_3270793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270793 prefixEnd_3270793 := by exact prefixLift 3270793
  have htrace : WordTrace (prefixWord ++ tailWord_3270793) baseStart_3270793 baseEnd_3270793 := by
    simpa [prefixWord, tailWord_3270793, baseEnd_3270793] using wordTrace_append hprefix tailTrace_3270793
  have hstable : (prefixWord ++ tailWord_3270793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270793).length < 2 ^ (prefixWord ++ tailWord_3270793).sum := by decide
  have hdescent : baseEnd_3270793 < baseStart_3270793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270829 : List Nat := [1, 5, 2, 1, 2, 1, 4, 1, 1, 4]
def baseStart_3270829 : Nat := 118140960795 + 3270829 * 2 ^ 59
def prefixEnd_3270829 : Nat := 4983230072969 + 3 ^ 40 * 3270829 * 2
def baseEnd_3270829 : Nat := 1119671610443259066796825

theorem tailTrace_3270829 : CollatzResearch.WordTrace tailWord_3270829 prefixEnd_3270829 1119671610443259066796825 := by
  unfold tailWord_3270829
  simp only [CollatzResearch.WordTrace]
  refine ⟨119296934267352620964847541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79531289511568413976565027 119296934267352620964847541)
  ·
    refine ⟨11184087587564308215454457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119296934267352620964847541 11184087587564308215454457)
    ·
      refine ⟨8388065690673231161590843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11184087587564308215454457 8388065690673231161590843)
      ·
        refine ⟨12582098536009846742386265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8388065690673231161590843 12582098536009846742386265)
        ·
          refine ⟨9436573902007385056789699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12582098536009846742386265 9436573902007385056789699)
          ·
            refine ⟨14154860853011077585184549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9436573902007385056789699 14154860853011077585184549)
            ·
              refine ⟨2654036409939577047222103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14154860853011077585184549 2654036409939577047222103)
              ·
                refine ⟨3981054614909365570833155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2654036409939577047222103 3981054614909365570833155)
                ·
                  refine ⟨5971581922364048356249733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3981054614909365570833155 5971581922364048356249733)
                  ·
                    refine ⟨1119671610443259066796825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5971581922364048356249733 1119671610443259066796825)
                    ·
                      rfl

theorem cell22_3270829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_3270829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270829 prefixEnd_3270829 := by exact prefixLift 3270829
  have htrace : WordTrace (prefixWord ++ tailWord_3270829) baseStart_3270829 baseEnd_3270829 := by
    simpa [prefixWord, tailWord_3270829, baseEnd_3270829] using wordTrace_append hprefix tailTrace_3270829
  have hstable : (prefixWord ++ tailWord_3270829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270829).length < 2 ^ (prefixWord ++ tailWord_3270829).sum := by decide
  have hdescent : baseEnd_3270829 < baseStart_3270829 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270842 : List Nat := [3, 1, 1, 1, 2, 2, 5, 2, 2, 3]
def baseStart_3270842 : Nat := 118140960795 + 3270842 * 2 ^ 59
def prefixEnd_3270842 : Nat := 4983230072969 + 3 ^ 40 * 3270842 * 2
def baseEnd_3270842 : Nat := 1119676060608931366221785

theorem tailTrace_3270842 : CollatzResearch.WordTrace tailWord_3270842 prefixEnd_3270842 1119676060608931366221785 := by
  unfold tailWord_3270842
  simp only [CollatzResearch.WordTrace]
  refine ⟨29824352104076381046267695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79531605610870349456713853 29824352104076381046267695)
  ·
    refine ⟨44736528156114571569401543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29824352104076381046267695 44736528156114571569401543)
    ·
      refine ⟨67104792234171857354102315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44736528156114571569401543 67104792234171857354102315)
      ·
        refine ⟨100657188351257786031153473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67104792234171857354102315 100657188351257786031153473)
        ·
          refine ⟨75492891263443339523365105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100657188351257786031153473 75492891263443339523365105)
          ·
            refine ⟨56619668447582504642523829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75492891263443339523365105 56619668447582504642523829)
            ·
              refine ⟨5308093916960859810236609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56619668447582504642523829 5308093916960859810236609)
              ·
                refine ⟨3981070437720644857677457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5308093916960859810236609 3981070437720644857677457)
                ·
                  refine ⟨2985802828290483643258093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3981070437720644857677457 2985802828290483643258093)
                  ·
                    refine ⟨1119676060608931366221785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2985802828290483643258093 1119676060608931366221785)
                    ·
                      rfl

theorem cell22_3270842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 2, 2, 3].length) (baseStart_3270842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270842 prefixEnd_3270842 := by exact prefixLift 3270842
  have htrace : WordTrace (prefixWord ++ tailWord_3270842) baseStart_3270842 baseEnd_3270842 := by
    simpa [prefixWord, tailWord_3270842, baseEnd_3270842] using wordTrace_append hprefix tailTrace_3270842
  have hstable : (prefixWord ++ tailWord_3270842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270842).length < 2 ^ (prefixWord ++ tailWord_3270842).sum := by decide
  have hdescent : baseEnd_3270842 < baseStart_3270842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270872 : List Nat := [2, 1, 2, 2, 4, 3, 2, 6]
def baseStart_3270872 : Nat := 118140960795 + 3270872 * 2 ^ 59
def prefixEnd_3270872 : Nat := 4983230072969 + 3 ^ 40 * 3270872 * 2
def baseEnd_3270872 : Nat := 124409592246891254219077

theorem tailTrace_3270872 : CollatzResearch.WordTrace tailWord_3270872 prefixEnd_3270872 124409592246891254219077 := by
  unfold tailWord_3270872
  simp only [CollatzResearch.WordTrace]
  refine ⟨59649251303098419654331435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79532335070797892872441913 59649251303098419654331435)
  ·
    refine ⟨89473876954647629481497153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59649251303098419654331435 89473876954647629481497153)
    ·
      refine ⟨67105407715985722111122865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89473876954647629481497153 67105407715985722111122865)
      ·
        refine ⟨50329055786989291583342149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67105407715985722111122865 50329055786989291583342149)
        ·
          refine ⟨9436697960060492171876653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50329055786989291583342149 9436697960060492171876653)
          ·
            refine ⟨3538761735022684564453745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9436697960060492171876653 3538761735022684564453745)
            ·
              refine ⟨2654071301267013423340309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3538761735022684564453745 2654071301267013423340309)
              ·
                refine ⟨124409592246891254219077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2654071301267013423340309 124409592246891254219077)
                ·
                  rfl

theorem cell22_3270872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 6].length) (baseStart_3270872 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270872 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270872 prefixEnd_3270872 := by exact prefixLift 3270872
  have htrace : WordTrace (prefixWord ++ tailWord_3270872) baseStart_3270872 baseEnd_3270872 := by
    simpa [prefixWord, tailWord_3270872, baseEnd_3270872] using wordTrace_append hprefix tailTrace_3270872
  have hstable : (prefixWord ++ tailWord_3270872).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270872).length < 2 ^ (prefixWord ++ tailWord_3270872).sum := by decide
  have hdescent : baseEnd_3270872 < baseStart_3270872 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270975 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 1, 6]
def baseStart_3270975 : Nat := 118140960795 + 3270975 * 2 ^ 59
def prefixEnd_3270975 : Nat := 4983230072969 + 3 ^ 40 * 3270975 * 2
def baseEnd_3270975 : Nat := 1119721589226963352646377

theorem tailTrace_3270975 : CollatzResearch.WordTrace tailWord_3270975 prefixEnd_3270975 1119721589226963352646377 := by
  unfold tailWord_3270975
  simp only [CollatzResearch.WordTrace]
  refine ⟨119302259324823687899662379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79534839549882458599774919 119302259324823687899662379)
  ·
    refine ⟨178953388987235531849493569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119302259324823687899662379 178953388987235531849493569)
    ·
      refine ⟨134215041740426648887120177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178953388987235531849493569 134215041740426648887120177)
      ·
        refine ⟨100661281305319986665340133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134215041740426648887120177 100661281305319986665340133)
        ·
          refine ⟨18873990244747497499751275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 100661281305319986665340133 18873990244747497499751275)
          ·
            refine ⟨28310985367121246249626913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18873990244747497499751275 28310985367121246249626913)
            ·
              refine ⟨21233239025340934687220185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28310985367121246249626913 21233239025340934687220185)
              ·
                refine ⟨15924929269005701015415139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21233239025340934687220185 15924929269005701015415139)
                ·
                  refine ⟨23887393903508551523122709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15924929269005701015415139 23887393903508551523122709)
                  ·
                    refine ⟨1119721589226963352646377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23887393903508551523122709 1119721589226963352646377)
                    ·
                      rfl

theorem cell22_3270975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 1, 6].length) (baseStart_3270975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270975 prefixEnd_3270975 := by exact prefixLift 3270975
  have htrace : WordTrace (prefixWord ++ tailWord_3270975) baseStart_3270975 baseEnd_3270975 := by
    simpa [prefixWord, tailWord_3270975, baseEnd_3270975] using wordTrace_append hprefix tailTrace_3270975
  have hstable : (prefixWord ++ tailWord_3270975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270975).length < 2 ^ (prefixWord ++ tailWord_3270975).sum := by decide
  have hdescent : baseEnd_3270975 < baseStart_3270975 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3270992 : List Nat := [2, 1, 1, 1, 1, 6, 3, 1, 2, 4]
def baseStart_3270992 : Nat := 118140960795 + 3270992 * 2 ^ 59
def prefixEnd_3270992 : Nat := 4983230072969 + 3 ^ 40 * 3270992 * 2
def baseEnd_3270992 : Nat := 1119727408674380974971325

theorem tailTrace_3270992 : CollatzResearch.WordTrace tailWord_3270992 prefixEnd_3270992 1119727408674380974971325 := by
  unfold tailWord_3270992
  simp only [CollatzResearch.WordTrace]
  refine ⟨59651439682881049901515615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79535252910508066535354153 59651439682881049901515615)
  ·
    refine ⟨89477159524321574852273423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59651439682881049901515615 89477159524321574852273423)
    ·
      refine ⟨134215739286482362278410135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89477159524321574852273423 134215739286482362278410135)
      ·
        refine ⟨201323608929723543417615203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134215739286482362278410135 201323608929723543417615203)
        ·
          refine ⟨301985413394585315126422805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201323608929723543417615203 301985413394585315126422805)
          ·
            refine ⟨14155566252871186646551069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 301985413394585315126422805 14155566252871186646551069)
            ·
              refine ⟨5308337344826694992456651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14155566252871186646551069 5308337344826694992456651)
              ·
                refine ⟨7962506017240042488684977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5308337344826694992456651 7962506017240042488684977)
                ·
                  refine ⟨5971879512930031866513733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7962506017240042488684977 5971879512930031866513733)
                  ·
                    refine ⟨1119727408674380974971325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5971879512930031866513733 1119727408674380974971325)
                    ·
                      rfl

theorem cell22_3270992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 2, 4].length) (baseStart_3270992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3270992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3270992 prefixEnd_3270992 := by exact prefixLift 3270992
  have htrace : WordTrace (prefixWord ++ tailWord_3270992) baseStart_3270992 baseEnd_3270992 := by
    simpa [prefixWord, tailWord_3270992, baseEnd_3270992] using wordTrace_append hprefix tailTrace_3270992
  have hstable : (prefixWord ++ tailWord_3270992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3270992).length < 2 ^ (prefixWord ++ tailWord_3270992).sum := by decide
  have hdescent : baseEnd_3270992 < baseStart_3270992 := by decide
  rcases family_descends (prefixWord ++ tailWord_3270992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271073 : List Nat := [1, 2, 3, 5, 1, 2, 1, 1, 3, 3]
def baseStart_3271073 : Nat := 118140960795 + 3271073 * 2 ^ 59
def prefixEnd_3271073 : Nat := 4983230072969 + 3 ^ 40 * 3271073 * 2
def baseEnd_3271073 : Nat := 1119755136629723763696077

theorem tailTrace_3271073 : CollatzResearch.WordTrace tailWord_3271073 prefixEnd_3271073 1119755136629723763696077 := by
  unfold tailWord_3271073
  simp only [CollatzResearch.WordTrace]
  refine ⟨119305833678468650636729873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79537222452312433757819915 119305833678468650636729873)
  ·
    refine ⟨89479375258851487977547405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119305833678468650636729873 89479375258851487977547405)
    ·
      refine ⟨33554765722069307991580277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89479375258851487977547405 33554765722069307991580277)
      ·
        refine ⟨3145759286443997624210651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33554765722069307991580277 3145759286443997624210651)
        ·
          refine ⟨4718638929665996436315977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3145759286443997624210651 4718638929665996436315977)
          ·
            refine ⟨3538979197249497327236983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4718638929665996436315977 3538979197249497327236983)
            ·
              refine ⟨5308468795874245990855475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3538979197249497327236983 5308468795874245990855475)
              ·
                refine ⟨7962703193811368986283213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5308468795874245990855475 7962703193811368986283213)
                ·
                  refine ⟨2986013697679263369856205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7962703193811368986283213 2986013697679263369856205)
                  ·
                    refine ⟨1119755136629723763696077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2986013697679263369856205 1119755136629723763696077)
                    ·
                      rfl

theorem cell22_3271073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 3].length) (baseStart_3271073 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271073 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271073 prefixEnd_3271073 := by exact prefixLift 3271073
  have htrace : WordTrace (prefixWord ++ tailWord_3271073) baseStart_3271073 baseEnd_3271073 := by
    simpa [prefixWord, tailWord_3271073, baseEnd_3271073] using wordTrace_append hprefix tailTrace_3271073
  have hstable : (prefixWord ++ tailWord_3271073).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271073).length < 2 ^ (prefixWord ++ tailWord_3271073).sum := by decide
  have hdescent : baseEnd_3271073 < baseStart_3271073 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271112 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 3, 5]
def baseStart_3271112 : Nat := 118140960795 + 3271112 * 2 ^ 59
def prefixEnd_3271112 : Nat := 4983230072969 + 3 ^ 40 * 3271112 * 2
def baseEnd_3271112 : Nat := 1119768487126740661970957

theorem tailTrace_3271112 : CollatzResearch.WordTrace tailWord_3271112 prefixEnd_3271112 1119768487126740661970957 := by
  unfold tailWord_3271112
  simp only [CollatzResearch.WordTrace]
  refine ⟨59653628062663680148699795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79538170750218240198266393 59653628062663680148699795)
  ·
    refine ⟨89480442093995520223049693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59653628062663680148699795 89480442093995520223049693)
    ·
      refine ⟨33555165785248320083643635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89480442093995520223049693 33555165785248320083643635)
      ·
        refine ⟨50332748677872480125465453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33555165785248320083643635 50332748677872480125465453)
        ·
          refine ⟨18874780754202180047049545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50332748677872480125465453 18874780754202180047049545)
          ·
            refine ⟨14156085565651635035287159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18874780754202180047049545 14156085565651635035287159)
            ·
              refine ⟨21234128348477452552930739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14156085565651635035287159 21234128348477452552930739)
              ·
                refine ⟨31851192522716178829396109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21234128348477452552930739 31851192522716178829396109)
                ·
                  refine ⟨11944197196018567061023541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 31851192522716178829396109 11944197196018567061023541)
                  ·
                    refine ⟨1119768487126740661970957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11944197196018567061023541 1119768487126740661970957)
                    ·
                      rfl

theorem cell22_3271112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_3271112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271112 prefixEnd_3271112 := by exact prefixLift 3271112
  have htrace : WordTrace (prefixWord ++ tailWord_3271112) baseStart_3271112 baseEnd_3271112 := by
    simpa [prefixWord, tailWord_3271112, baseEnd_3271112] using wordTrace_append hprefix tailTrace_3271112
  have hstable : (prefixWord ++ tailWord_3271112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271112).length < 2 ^ (prefixWord ++ tailWord_3271112).sum := by decide
  have hdescent : baseEnd_3271112 < baseStart_3271112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271114 : List Nat := [3, 1, 2, 1, 2, 2, 2, 5, 4]
def baseStart_3271114 : Nat := 118140960795 + 3271114 * 2 ^ 59
def prefixEnd_3271114 : Nat := 4983230072969 + 3 ^ 40 * 3271114 * 2
def baseEnd_3271114 : Nat := 373256390589204441140317

theorem tailTrace_3271114 : CollatzResearch.WordTrace tailWord_3271114 prefixEnd_3271114 373256390589204441140317 := by
  unfold tailWord_3271114
  simp only [CollatzResearch.WordTrace]
  refine ⟨29826832267830028659743099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79538219380880076425981597 29826832267830028659743099)
  ·
    refine ⟨44740248401745042989614649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29826832267830028659743099 44740248401745042989614649)
    ·
      refine ⟨33555186301308782242210987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44740248401745042989614649 33555186301308782242210987)
      ·
        refine ⟨50332779451963173363316481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33555186301308782242210987 50332779451963173363316481)
        ·
          refine ⟨37749584588972380022487361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50332779451963173363316481 37749584588972380022487361)
          ·
            refine ⟨28312188441729285016865521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37749584588972380022487361 28312188441729285016865521)
            ·
              refine ⟨21234141331296963762649141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28312188441729285016865521 21234141331296963762649141)
              ·
                refine ⟨1990700749809090352748357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21234141331296963762649141 1990700749809090352748357)
                ·
                  refine ⟨373256390589204441140317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1990700749809090352748357 373256390589204441140317)
                  ·
                    rfl

theorem cell22_3271114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 5, 4].length) (baseStart_3271114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271114 prefixEnd_3271114 := by exact prefixLift 3271114
  have htrace : WordTrace (prefixWord ++ tailWord_3271114) baseStart_3271114 baseEnd_3271114 := by
    simpa [prefixWord, tailWord_3271114, baseEnd_3271114] using wordTrace_append hprefix tailTrace_3271114
  have hstable : (prefixWord ++ tailWord_3271114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271114).length < 2 ^ (prefixWord ++ tailWord_3271114).sum := by decide
  have hdescent : baseEnd_3271114 < baseStart_3271114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271146 : List Nat := [3, 1, 3, 1, 3, 1, 2, 3, 2, 3]
def baseStart_3271146 : Nat := 118140960795 + 3271146 * 2 ^ 59
def prefixEnd_3271146 : Nat := 4983230072969 + 3 ^ 40 * 3271146 * 2
def baseEnd_3271146 : Nat := 1119780126021575906620853

theorem tailTrace_3271146 : CollatzResearch.WordTrace tailWord_3271146 prefixEnd_3271146 1119780126021575906620853 := by
  unfold tailWord_3271146
  simp only [CollatzResearch.WordTrace]
  refine ⟨29827124051801046026034323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79538997471469456069424861 29827124051801046026034323)
  ·
    refine ⟨44740686077701569039051485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29827124051801046026034323 44740686077701569039051485)
    ·
      refine ⟨16777757279138088389644307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44740686077701569039051485 16777757279138088389644307)
      ·
        refine ⟨25166635918707132584466461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16777757279138088389644307 25166635918707132584466461)
        ·
          refine ⟨9437488469515174719174923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25166635918707132584466461 9437488469515174719174923)
          ·
            refine ⟨14156232704272762078762385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9437488469515174719174923 14156232704272762078762385)
            ·
              refine ⟨10617174528204571559071789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14156232704272762078762385 10617174528204571559071789)
              ·
                refine ⟨3981440448076714334651921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10617174528204571559071789 3981440448076714334651921)
                ·
                  refine ⟨2986080336057535750988941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3981440448076714334651921 2986080336057535750988941)
                  ·
                    refine ⟨1119780126021575906620853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2986080336057535750988941 1119780126021575906620853)
                    ·
                      rfl

theorem cell22_3271146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_3271146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271146 prefixEnd_3271146 := by exact prefixLift 3271146
  have htrace : WordTrace (prefixWord ++ tailWord_3271146) baseStart_3271146 baseEnd_3271146 := by
    simpa [prefixWord, tailWord_3271146, baseEnd_3271146] using wordTrace_append hprefix tailTrace_3271146
  have hstable : (prefixWord ++ tailWord_3271146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271146).length < 2 ^ (prefixWord ++ tailWord_3271146).sum := by decide
  have hdescent : baseEnd_3271146 < baseStart_3271146 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271187 : List Nat := [1, 1, 1, 2, 1, 5, 3, 1, 7]
def baseStart_3271187 : Nat := 118140960795 + 3271187 * 2 ^ 59
def prefixEnd_3271187 : Nat := 4983230072969 + 3 ^ 40 * 3271187 * 2
def baseEnd_3271187 : Nat := 373264720386488488781909

theorem tailTrace_3271187 : CollatzResearch.WordTrace tailWord_3271187 prefixEnd_3271187 373264720386488488781909 := by
  unfold tailWord_3271187
  simp only [CollatzResearch.WordTrace]
  refine ⟨119309991600055648106379815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79539994400037098737586543 119309991600055648106379815)
  ·
    refine ⟨178964987400083472159569723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119309991600055648106379815 178964987400083472159569723)
    ·
      refine ⟨268447481100125208239354585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178964987400083472159569723 268447481100125208239354585)
      ·
        refine ⟨201335610825093906179515939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268447481100125208239354585 201335610825093906179515939)
        ·
          refine ⟨302003416237640859269273909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201335610825093906179515939 302003416237640859269273909)
          ·
            refine ⟨28312820272278830556494429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 302003416237640859269273909 28312820272278830556494429)
            ·
              refine ⟨10617307602104561458685411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28312820272278830556494429 10617307602104561458685411)
              ·
                refine ⟨15925961403156842188028117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10617307602104561458685411 15925961403156842188028117)
                ·
                  refine ⟨373264720386488488781909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15925961403156842188028117 373264720386488488781909)
                  ·
                    rfl

theorem cell22_3271187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 1, 7].length) (baseStart_3271187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271187 prefixEnd_3271187 := by exact prefixLift 3271187
  have htrace : WordTrace (prefixWord ++ tailWord_3271187) baseStart_3271187 baseEnd_3271187 := by
    simpa [prefixWord, tailWord_3271187, baseEnd_3271187] using wordTrace_append hprefix tailTrace_3271187
  have hstable : (prefixWord ++ tailWord_3271187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271187).length < 2 ^ (prefixWord ++ tailWord_3271187).sum := by decide
  have hdescent : baseEnd_3271187 < baseStart_3271187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271232 : List Nat := [2, 1, 1, 2, 2, 2, 2, 2, 8]
def baseStart_3271232 : Nat := 118140960795 + 3271232 * 2 ^ 59
def prefixEnd_3271232 : Nat := 4983230072969 + 3 ^ 40 * 3271232 * 2
def baseEnd_3271232 : Nat := 373269855193033449656863

theorem tailTrace_3271232 : CollatzResearch.WordTrace tailWord_3271232 prefixEnd_3271232 373269855193033449656863 := by
  unfold tailWord_3271232
  simp only [CollatzResearch.WordTrace]
  refine ⟨59655816442446310395883975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79541088589928413861178633 59655816442446310395883975)
  ·
    refine ⟨89483724663669465593825963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59655816442446310395883975 89483724663669465593825963)
    ·
      refine ⟨134225586995504198390738945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89483724663669465593825963 134225586995504198390738945)
      ·
        refine ⟨100669190246628148793054209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134225586995504198390738945 100669190246628148793054209)
        ·
          refine ⟨75501892684971111594790657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100669190246628148793054209 75501892684971111594790657)
          ·
            refine ⟨56626419513728333696092993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75501892684971111594790657 56626419513728333696092993)
            ·
              refine ⟨42469814635296250272069745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56626419513728333696092993 42469814635296250272069745)
              ·
                refine ⟨31852360976472187704052309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42469814635296250272069745 31852360976472187704052309)
                ·
                  refine ⟨373269855193033449656863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 31852360976472187704052309 373269855193033449656863)
                  ·
                    rfl

theorem cell22_3271232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 2, 8].length) (baseStart_3271232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271232 prefixEnd_3271232 := by exact prefixLift 3271232
  have htrace : WordTrace (prefixWord ++ tailWord_3271232) baseStart_3271232 baseEnd_3271232 := by
    simpa [prefixWord, tailWord_3271232, baseEnd_3271232] using wordTrace_append hprefix tailTrace_3271232
  have hstable : (prefixWord ++ tailWord_3271232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271232).length < 2 ^ (prefixWord ++ tailWord_3271232).sum := by decide
  have hdescent : baseEnd_3271232 < baseStart_3271232 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271249 : List Nat := [1, 2, 2, 1, 3, 3, 3, 1, 6]
def baseStart_3271249 : Nat := 118140960795 + 3271249 * 2 ^ 59
def prefixEnd_3271249 : Nat := 4983230072969 + 3 ^ 40 * 3271249 * 2
def baseEnd_3271249 : Nat := 373271795008839323765179

theorem tailTrace_3271249 : CollatzResearch.WordTrace tailWord_3271249 prefixEnd_3271249 373271795008839323765179 := by
  unfold tailWord_3271249
  simp only [CollatzResearch.WordTrace]
  refine ⟨119312252925831032695136801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79541501950554021796757867 119312252925831032695136801)
  ·
    refine ⟨89484189694373274521352601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119312252925831032695136801 89484189694373274521352601)
    ·
      refine ⟨67113142270779955891014451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89484189694373274521352601 67113142270779955891014451)
      ·
        refine ⟨100669713406169933836521677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67113142270779955891014451 100669713406169933836521677)
        ·
          refine ⟨37751142527313725188695629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100669713406169933836521677 37751142527313725188695629)
          ·
            refine ⟨14156678447742646945760861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37751142527313725188695629 14156678447742646945760861)
            ·
              refine ⟨5308754417903492604660323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14156678447742646945760861 5308754417903492604660323)
              ·
                refine ⟨7963131626855238906990485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5308754417903492604660323 7963131626855238906990485)
                ·
                  refine ⟨373271795008839323765179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7963131626855238906990485 373271795008839323765179)
                  ·
                    rfl

theorem cell22_3271249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 1, 6].length) (baseStart_3271249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271249 prefixEnd_3271249 := by exact prefixLift 3271249
  have htrace : WordTrace (prefixWord ++ tailWord_3271249) baseStart_3271249 baseEnd_3271249 := by
    simpa [prefixWord, tailWord_3271249, baseEnd_3271249] using wordTrace_append hprefix tailTrace_3271249
  have hstable : (prefixWord ++ tailWord_3271249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271249).length < 2 ^ (prefixWord ++ tailWord_3271249).sum := by decide
  have hdescent : baseEnd_3271249 < baseStart_3271249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271279 : List Nat := [1, 1, 2, 1, 3, 2, 3, 3, 2, 4]
def baseStart_3271279 : Nat := 118140960795 + 3271279 * 2 ^ 59
def prefixEnd_3271279 : Nat := 4983230072969 + 3 ^ 40 * 3271279 * 2
def baseEnd_3271279 : Nat := 1119825654639607893045445

theorem tailTrace_3271279 : CollatzResearch.WordTrace tailWord_3271279 prefixEnd_3271279 1119825654639607893045445 := by
  unfold tailWord_3271279
  simp only [CollatzResearch.WordTrace]
  refine ⟨119313347115722347818728891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79542231410481565212485927 119313347115722347818728891)
  ·
    refine ⟨178970020673583521728093337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119313347115722347818728891 178970020673583521728093337)
    ·
      refine ⟨134227515505187641296070003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178970020673583521728093337 134227515505187641296070003)
      ·
        refine ⟨201341273257781461944105005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134227515505187641296070003 201341273257781461944105005)
        ·
          refine ⟨75502977471668048229039377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201341273257781461944105005 75502977471668048229039377)
          ·
            refine ⟨56627233103751036171779533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75502977471668048229039377 56627233103751036171779533)
            ·
              refine ⟨21235212413906638564417325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56627233103751036171779533 21235212413906638564417325)
              ·
                refine ⟨7963204655214989461656497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21235212413906638564417325 7963204655214989461656497)
                ·
                  refine ⟨5972403491411242096242373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7963204655214989461656497 5972403491411242096242373)
                  ·
                    refine ⟨1119825654639607893045445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5972403491411242096242373 1119825654639607893045445)
                    ·
                      rfl

theorem cell22_3271279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 4].length) (baseStart_3271279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271279 prefixEnd_3271279 := by exact prefixLift 3271279
  have htrace : WordTrace (prefixWord ++ tailWord_3271279) baseStart_3271279 baseEnd_3271279 := by
    simpa [prefixWord, tailWord_3271279, baseEnd_3271279] using wordTrace_append hprefix tailTrace_3271279
  have hstable : (prefixWord ++ tailWord_3271279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271279).length < 2 ^ (prefixWord ++ tailWord_3271279).sum := by decide
  have hdescent : baseEnd_3271279 < baseStart_3271279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271285 : List Nat := [1, 3, 4, 2, 2, 1, 3, 1, 1, 4]
def baseStart_3271285 : Nat := 118140960795 + 3271285 * 2 ^ 59
def prefixEnd_3271285 : Nat := 4983230072969 + 3 ^ 40 * 3271285 * 2
def baseEnd_3271285 : Nat := 1119827708562225877395427

theorem tailTrace_3271285 : CollatzResearch.WordTrace tailWord_3271285 prefixEnd_3271285 1119827708562225877395427 := by
  unfold tailWord_3271285
  simp only [CollatzResearch.WordTrace]
  refine ⟨119313565953700610843447309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79542377302467073895631539 119313565953700610843447309)
  ·
    refine ⟨44742587232637729066292741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119313565953700610843447309 44742587232637729066292741)
    ·
      refine ⟨8389235106119574199929889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 44742587232637729066292741 8389235106119574199929889)
      ·
        refine ⟨6291926329589680649947417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8389235106119574199929889 6291926329589680649947417)
        ·
          refine ⟨4718944747192260487460563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6291926329589680649947417 4718944747192260487460563)
          ·
            refine ⟨7078417120788390731190845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4718944747192260487460563 7078417120788390731190845)
            ·
              refine ⟨2654406420295646524196567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7078417120788390731190845 2654406420295646524196567)
              ·
                refine ⟨3981609630443469786294851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2654406420295646524196567 3981609630443469786294851)
                ·
                  refine ⟨5972414445665204679442277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3981609630443469786294851 5972414445665204679442277)
                  ·
                    refine ⟨1119827708562225877395427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5972414445665204679442277 1119827708562225877395427)
                    ·
                      rfl

theorem cell22_3271285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_3271285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271285 prefixEnd_3271285 := by exact prefixLift 3271285
  have htrace : WordTrace (prefixWord ++ tailWord_3271285) baseStart_3271285 baseEnd_3271285 := by
    simpa [prefixWord, tailWord_3271285, baseEnd_3271285] using wordTrace_append hprefix tailTrace_3271285
  have hstable : (prefixWord ++ tailWord_3271285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271285).length < 2 ^ (prefixWord ++ tailWord_3271285).sum := by decide
  have hdescent : baseEnd_3271285 < baseStart_3271285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271300 : List Nat := [2, 3, 2, 1, 3, 3, 2, 2, 4]
def baseStart_3271300 : Nat := 118140960795 + 3271300 * 2 ^ 59
def prefixEnd_3271300 : Nat := 4983230072969 + 3 ^ 40 * 3271300 * 2
def baseEnd_3271300 : Nat := 373277614456256946090127

theorem tailTrace_3271300 : CollatzResearch.WordTrace tailWord_3271300 prefixEnd_3271300 373277614456256946090127 := by
  unfold tailWord_3271300
  simp only [CollatzResearch.WordTrace]
  refine ⟨59657056524323134202621677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79542742032430845603495569 59657056524323134202621677)
  ·
    refine ⟨22371396196621175325983129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59657056524323134202621677 22371396196621175325983129)
    ·
      refine ⟨16778547147465881494487347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22371396196621175325983129 16778547147465881494487347)
      ·
        refine ⟨25167820721198822241731021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16778547147465881494487347 25167820721198822241731021)
        ·
          refine ⟨9437932770449558340649133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25167820721198822241731021 9437932770449558340649133)
          ·
            refine ⟨3539224788918584377743425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9437932770449558340649133 3539224788918584377743425)
            ·
              refine ⟨2654418591688938283307569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3539224788918584377743425 2654418591688938283307569)
              ·
                refine ⟨1990813943766703712480677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2654418591688938283307569 1990813943766703712480677)
                ·
                  refine ⟨373277614456256946090127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1990813943766703712480677 373277614456256946090127)
                  ·
                    rfl

theorem cell22_3271300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 2, 4].length) (baseStart_3271300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271300 prefixEnd_3271300 := by exact prefixLift 3271300
  have htrace : WordTrace (prefixWord ++ tailWord_3271300) baseStart_3271300 baseEnd_3271300 := by
    simpa [prefixWord, tailWord_3271300, baseEnd_3271300] using wordTrace_append hprefix tailTrace_3271300
  have hstable : (prefixWord ++ tailWord_3271300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271300).length < 2 ^ (prefixWord ++ tailWord_3271300).sum := by decide
  have hdescent : baseEnd_3271300 < baseStart_3271300 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271343 : List Nat := [1, 1, 2, 1, 2, 5, 1, 5, 1, 3]
def baseStart_3271343 : Nat := 118140960795 + 3271343 * 2 ^ 59
def prefixEnd_3271343 : Nat := 4983230072969 + 3 ^ 40 * 3271343 * 2
def baseEnd_3271343 : Nat := 1119847563147533059445249

theorem tailTrace_3271343 : CollatzResearch.WordTrace tailWord_3271343 prefixEnd_3271343 1119847563147533059445249 := by
  unfold tailWord_3271343
  simp only [CollatzResearch.WordTrace]
  refine ⟨119315681387490486749058683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79543787591660324499372455 119315681387490486749058683)
  ·
    refine ⟨178973522081235730123588025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119315681387490486749058683 178973522081235730123588025)
    ·
      refine ⟨134230141560926797592691019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178973522081235730123588025 134230141560926797592691019)
      ·
        refine ⟨201345212341390196389036529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134230141560926797592691019 201345212341390196389036529)
        ·
          refine ⟨151008909256042647291777397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201345212341390196389036529 151008909256042647291777397)
          ·
            refine ⟨14157085242753998183604131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 151008909256042647291777397 14157085242753998183604131)
            ·
              refine ⟨21235627864130997275406197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14157085242753998183604131 21235627864130997275406197)
              ·
                refine ⟨1990840112262280994569331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21235627864130997275406197 1990840112262280994569331)
                ·
                  refine ⟨2986260168393421491853997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1990840112262280994569331 2986260168393421491853997)
                  ·
                    refine ⟨1119847563147533059445249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2986260168393421491853997 1119847563147533059445249)
                    ·
                      rfl

theorem cell22_3271343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 1, 3].length) (baseStart_3271343 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271343 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271343 prefixEnd_3271343 := by exact prefixLift 3271343
  have htrace : WordTrace (prefixWord ++ tailWord_3271343) baseStart_3271343 baseEnd_3271343 := by
    simpa [prefixWord, tailWord_3271343, baseEnd_3271343] using wordTrace_append hprefix tailTrace_3271343
  have hstable : (prefixWord ++ tailWord_3271343).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271343).length < 2 ^ (prefixWord ++ tailWord_3271343).sum := by decide
  have hdescent : baseEnd_3271343 < baseStart_3271343 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271354 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 4, 5]
def baseStart_3271354 : Nat := 118140960795 + 3271354 * 2 ^ 59
def prefixEnd_3271354 : Nat := 4983230072969 + 3 ^ 40 * 3271354 * 2
def baseEnd_3271354 : Nat := 1119851328672332697420215

theorem tailTrace_3271354 : CollatzResearch.WordTrace tailWord_3271354 prefixEnd_3271354 1119851328672332697420215 := by
  unfold tailWord_3271354
  simp only [CollatzResearch.WordTrace]
  refine ⟨29829020647612658906927279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79544055060300423751806077 29829020647612658906927279)
  ·
    refine ⟨44743530971418988360390919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29829020647612658906927279 44743530971418988360390919)
    ·
      refine ⟨67115296457128482540586379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44743530971418988360390919 67115296457128482540586379)
      ·
        refine ⟨100672944685692723810879569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67115296457128482540586379 100672944685692723810879569)
        ·
          refine ⟨75504708514269542858159677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100672944685692723810879569 75504708514269542858159677)
          ·
            refine ⟨28314265692851078571809879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75504708514269542858159677 28314265692851078571809879)
            ·
              refine ⟨42471398539276617857714819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28314265692851078571809879 42471398539276617857714819)
              ·
                refine ⟨63707097808914926786572229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 42471398539276617857714819 63707097808914926786572229)
                ·
                  refine ⟨11945080839171548772482293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 63707097808914926786572229 11945080839171548772482293)
                  ·
                    refine ⟨1119851328672332697420215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11945080839171548772482293 1119851328672332697420215)
                    ·
                      rfl

theorem cell22_3271354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_3271354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271354 prefixEnd_3271354 := by exact prefixLift 3271354
  have htrace : WordTrace (prefixWord ++ tailWord_3271354) baseStart_3271354 baseEnd_3271354 := by
    simpa [prefixWord, tailWord_3271354, baseEnd_3271354] using wordTrace_append hprefix tailTrace_3271354
  have hstable : (prefixWord ++ tailWord_3271354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271354).length < 2 ^ (prefixWord ++ tailWord_3271354).sum := by decide
  have hdescent : baseEnd_3271354 < baseStart_3271354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271416 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 4, 3]
def baseStart_3271416 : Nat := 118140960795 + 3271416 * 2 ^ 59
def prefixEnd_3271416 : Nat := 4983230072969 + 3 ^ 40 * 3271416 * 2
def baseEnd_3271416 : Nat := 1119872552539385202370025

theorem tailTrace_3271416 : CollatzResearch.WordTrace tailWord_3271416 prefixEnd_3271416 1119872552539385202370025 := by
  unfold tailWord_3271416
  simp only [CollatzResearch.WordTrace]
  refine ⟨59659171958113010108233051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79545562610817346810977401 59659171958113010108233051)
  ·
    refine ⟨89488757937169515162349577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59659171958113010108233051 89488757937169515162349577)
    ·
      refine ⟨67116568452877136371762183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89488757937169515162349577 67116568452877136371762183)
      ·
        refine ⟨100674852679315704557643275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67116568452877136371762183 100674852679315704557643275)
        ·
          refine ⟨151012279018973556836464913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100674852679315704557643275 151012279018973556836464913)
          ·
            refine ⟨113259209264230167627348685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 151012279018973556836464913 113259209264230167627348685)
            ·
              refine ⟨42472203474086312860255757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 113259209264230167627348685 42472203474086312860255757)
              ·
                refine ⟨15927076302782367322595909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42472203474086312860255757 15927076302782367322595909)
                ·
                  refine ⟨2986326806771693872986733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15927076302782367322595909 2986326806771693872986733)
                  ·
                    refine ⟨1119872552539385202370025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2986326806771693872986733 1119872552539385202370025)
                    ·
                      rfl

theorem cell22_3271416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 4, 3].length) (baseStart_3271416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271416 prefixEnd_3271416 := by exact prefixLift 3271416
  have htrace : WordTrace (prefixWord ++ tailWord_3271416) baseStart_3271416 baseEnd_3271416 := by
    simpa [prefixWord, tailWord_3271416, baseEnd_3271416] using wordTrace_append hprefix tailTrace_3271416
  have hstable : (prefixWord ++ tailWord_3271416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271416).length < 2 ^ (prefixWord ++ tailWord_3271416).sum := by decide
  have hdescent : baseEnd_3271416 < baseStart_3271416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271491 : List Nat := [1, 1, 1, 3, 1, 4, 1, 5, 5]
def baseStart_3271491 : Nat := 118140960795 + 3271491 * 2 ^ 59
def prefixEnd_3271491 : Nat := 4983230072969 + 3 ^ 40 * 3271491 * 2
def baseEnd_3271491 : Nat := 373299408857370002248265

theorem tailTrace_3271491 : CollatzResearch.WordTrace tailWord_3271491 prefixEnd_3271491 373299408857370002248265 := by
  unfold tailWord_3271491
  simp only [CollatzResearch.WordTrace]
  refine ⟨119321079390954308025446327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79547386260636205350297551 119321079390954308025446327)
  ·
    refine ⟨178981619086431462038169491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119321079390954308025446327 178981619086431462038169491)
    ·
      refine ⟨268472428629647193057254237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 178981619086431462038169491 268472428629647193057254237)
      ·
        refine ⟨100677160736117697396470339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 268472428629647193057254237 100677160736117697396470339)
        ·
          refine ⟨151015741104176546094705509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100677160736117697396470339 151015741104176546094705509)
          ·
            refine ⟨28315451457033102392757283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151015741104176546094705509 28315451457033102392757283)
            ·
              refine ⟨42473177185549653589135925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28315451457033102392757283 42473177185549653589135925)
              ·
                refine ⟨3981860361145280023981493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42473177185549653589135925 3981860361145280023981493)
                ·
                  refine ⟨373299408857370002248265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3981860361145280023981493 373299408857370002248265)
                  ·
                    rfl

theorem cell22_3271491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 5, 5].length) (baseStart_3271491 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271491 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271491 prefixEnd_3271491 := by exact prefixLift 3271491
  have htrace : WordTrace (prefixWord ++ tailWord_3271491) baseStart_3271491 baseEnd_3271491 := by
    simpa [prefixWord, tailWord_3271491, baseEnd_3271491] using wordTrace_append hprefix tailTrace_3271491
  have hstable : (prefixWord ++ tailWord_3271491).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271491).length < 2 ^ (prefixWord ++ tailWord_3271491).sum := by decide
  have hdescent : baseEnd_3271491 < baseStart_3271491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271506 : List Nat := [3, 2, 2, 1, 1, 2, 1, 2, 1, 7]
def baseStart_3271506 : Nat := 118140960795 + 3271506 * 2 ^ 59
def prefixEnd_3271506 : Nat := 4983230072969 + 3 ^ 40 * 3271506 * 2
def baseEnd_3271506 : Nat := 1119903361378654967619749

theorem tailTrace_3271506 : CollatzResearch.WordTrace tailWord_3271506 prefixEnd_3271506 1119903361378654967619749 := by
  unfold tailWord_3271506
  simp only [CollatzResearch.WordTrace]
  refine ⟨29830406621474991396810593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79547750990599977058161581 29830406621474991396810593)
  ·
    refine ⟨22372804966106243547607945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29830406621474991396810593 22372804966106243547607945)
    ·
      refine ⟨16779603724579682660705959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22372804966106243547607945 16779603724579682660705959)
      ·
        refine ⟨25169405586869523991058939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16779603724579682660705959 25169405586869523991058939)
        ·
          refine ⟨37754108380304285986588409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25169405586869523991058939 37754108380304285986588409)
          ·
            refine ⟨28315581285228214489941307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37754108380304285986588409 28315581285228214489941307)
            ·
              refine ⟨42473371927842321734911961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28315581285228214489941307 42473371927842321734911961)
              ·
                refine ⟨31855028945881741301183971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 42473371927842321734911961 31855028945881741301183971)
                ·
                  refine ⟨47782543418822611951775957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31855028945881741301183971 47782543418822611951775957)
                  ·
                    refine ⟨1119903361378654967619749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47782543418822611951775957 1119903361378654967619749)
                    ·
                      rfl

theorem cell22_3271506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 2, 1, 7].length) (baseStart_3271506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271506 prefixEnd_3271506 := by exact prefixLift 3271506
  have htrace : WordTrace (prefixWord ++ tailWord_3271506) baseStart_3271506 baseEnd_3271506 := by
    simpa [prefixWord, tailWord_3271506, baseEnd_3271506] using wordTrace_append hprefix tailTrace_3271506
  have hstable : (prefixWord ++ tailWord_3271506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271506).length < 2 ^ (prefixWord ++ tailWord_3271506).sum := by decide
  have hdescent : baseEnd_3271506 < baseStart_3271506 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271521 : List Nat := [1, 2, 3, 1, 1, 1, 2, 2, 5, 4]
def baseStart_3271521 : Nat := 118140960795 + 3271521 * 2 ^ 59
def prefixEnd_3271521 : Nat := 4983230072969 + 3 ^ 40 * 3271521 * 2
def baseEnd_3271521 : Nat := 1119908496185199928494703

theorem tailTrace_3271521 : CollatzResearch.WordTrace tailWord_3271521 prefixEnd_3271521 1119908496185199928494703 := by
  unfold tailWord_3271521
  simp only [CollatzResearch.WordTrace]
  refine ⟨119322173580845623149038417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79548115720563748766025611 119322173580845623149038417)
  ·
    refine ⟨89491630185634217361778813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119322173580845623149038417 89491630185634217361778813)
    ·
      refine ⟨33559361319612831510667055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89491630185634217361778813 33559361319612831510667055)
      ·
        refine ⟨50339041979419247266000583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33559361319612831510667055 50339041979419247266000583)
        ·
          refine ⟨75508562969128870899000875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50339041979419247266000583 75508562969128870899000875)
          ·
            refine ⟨113262844453693306348501313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75508562969128870899000875 113262844453693306348501313)
            ·
              refine ⟨84947133340269979761375985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113262844453693306348501313 84947133340269979761375985)
              ·
                refine ⟨63710350005202484821031989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 84947133340269979761375985 63710350005202484821031989)
                ·
                  refine ⟨5972845312987732951971749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 63710350005202484821031989 5972845312987732951971749)
                  ·
                    refine ⟨1119908496185199928494703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5972845312987732951971749 1119908496185199928494703)
                    ·
                      rfl

theorem cell22_3271521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 4].length) (baseStart_3271521 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271521 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271521 prefixEnd_3271521 := by exact prefixLift 3271521
  have htrace : WordTrace (prefixWord ++ tailWord_3271521) baseStart_3271521 baseEnd_3271521 := by
    simpa [prefixWord, tailWord_3271521, baseEnd_3271521] using wordTrace_append hprefix tailTrace_3271521
  have hstable : (prefixWord ++ tailWord_3271521).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271521).length < 2 ^ (prefixWord ++ tailWord_3271521).sum := by decide
  have hdescent : baseEnd_3271521 < baseStart_3271521 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271536 : List Nat := [2, 1, 1, 1, 4, 1, 3, 3, 6]
def baseStart_3271536 : Nat := 118140960795 + 3271536 * 2 ^ 59
def prefixEnd_3271536 : Nat := 4983230072969 + 3 ^ 40 * 3271536 * 2
def baseEnd_3271536 : Nat := 373304543663914963123219

theorem tailTrace_3271536 : CollatzResearch.WordTrace tailWord_3271536 prefixEnd_3271536 373304543663914963123219 := by
  unfold tailWord_3271536
  simp only [CollatzResearch.WordTrace]
  refine ⟨59661360337895640355417231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79548480450527520473889641 59661360337895640355417231)
  ·
    refine ⟨89492040506843460533125847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59661360337895640355417231 89492040506843460533125847)
    ·
      refine ⟨134238060760265190799688771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89492040506843460533125847 134238060760265190799688771)
      ·
        refine ⟨201357091140397786199533157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134238060760265190799688771 201357091140397786199533157)
        ·
          refine ⟨37754454588824584912412467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 201357091140397786199533157 37754454588824584912412467)
          ·
            refine ⟨56631681883236877368618701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37754454588824584912412467 56631681883236877368618701)
            ·
              refine ⟨21236880706213829013232013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56631681883236877368618701 21236880706213829013232013)
              ·
                refine ⟨7963830264830185879962005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21236880706213829013232013 7963830264830185879962005)
                ·
                  refine ⟨373304543663914963123219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7963830264830185879962005 373304543663914963123219)
                  ·
                    rfl

theorem cell22_3271536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 3, 6].length) (baseStart_3271536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271536 prefixEnd_3271536 := by exact prefixLift 3271536
  have htrace : WordTrace (prefixWord ++ tailWord_3271536) baseStart_3271536 baseEnd_3271536 := by
    simpa [prefixWord, tailWord_3271536, baseEnd_3271536] using wordTrace_append hprefix tailTrace_3271536
  have hstable : (prefixWord ++ tailWord_3271536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271536).length < 2 ^ (prefixWord ++ tailWord_3271536).sum := by decide
  have hdescent : baseEnd_3271536 < baseStart_3271536 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271542 : List Nat := [5, 1, 1, 3, 1, 2, 3, 1, 5]
def baseStart_3271542 : Nat := 118140960795 + 3271542 * 2 ^ 59
def prefixEnd_3271542 : Nat := 4983230072969 + 3 ^ 40 * 3271542 * 2
def baseEnd_3271542 : Nat := 373305228304787624573213

theorem tailTrace_3271542 : CollatzResearch.WordTrace tailWord_3271542 prefixEnd_3271542 373305228304787624573213 := by
  unfold tailWord_3271542
  simp only [CollatzResearch.WordTrace]
  refine ⟨7457683719610596483472055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79548626342513029157035253 7457683719610596483472055)
  ·
    refine ⟨11186525579415894725208083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7457683719610596483472055 11186525579415894725208083)
    ·
      refine ⟨16779788369123842087812125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11186525579415894725208083 16779788369123842087812125)
      ·
        refine ⟨6292420638421440782929547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16779788369123842087812125 6292420638421440782929547)
        ·
          refine ⟨9438630957632161174394321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6292420638421440782929547 9438630957632161174394321)
          ·
            refine ⟨7078973218224120880795741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9438630957632161174394321 7078973218224120880795741)
            ·
              refine ⟨2654614956834045330298403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7078973218224120880795741 2654614956834045330298403)
              ·
                refine ⟨3981922435251067995447605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2654614956834045330298403 3981922435251067995447605)
                ·
                  refine ⟨373305228304787624573213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3981922435251067995447605 373305228304787624573213)
                  ·
                    rfl

theorem cell22_3271542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 1, 5].length) (baseStart_3271542 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271542 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271542 prefixEnd_3271542 := by exact prefixLift 3271542
  have htrace : WordTrace (prefixWord ++ tailWord_3271542) baseStart_3271542 baseEnd_3271542 := by
    simpa [prefixWord, tailWord_3271542, baseEnd_3271542] using wordTrace_append hprefix tailTrace_3271542
  have hstable : (prefixWord ++ tailWord_3271542).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271542).length < 2 ^ (prefixWord ++ tailWord_3271542).sum := by decide
  have hdescent : baseEnd_3271542 < baseStart_3271542 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271583 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 4, 4]
def baseStart_3271583 : Nat := 118140960795 + 3271583 * 2 ^ 59
def prefixEnd_3271583 : Nat := 4983230072969 + 3 ^ 40 * 3271583 * 2
def baseEnd_3271583 : Nat := 1119929720052252433444513

theorem tailTrace_3271583 : CollatzResearch.WordTrace tailWord_3271583 prefixEnd_3271583 1119929720052252433444513 := by
  unfold tailWord_3271583
  simp only [CollatzResearch.WordTrace]
  refine ⟨119324434906621007737795403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79549623271080671825196935 119324434906621007737795403)
  ·
    refine ⟨178986652359931511606693105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119324434906621007737795403 178986652359931511606693105)
    ·
      refine ⟨134239989269948633705019829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 178986652359931511606693105 134239989269948633705019829)
      ·
        refine ⟨12584998994057684409845609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 134239989269948633705019829 12584998994057684409845609)
        ·
          refine ⟨9438749245543263307384207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12584998994057684409845609 9438749245543263307384207)
          ·
            refine ⟨14158123868314894961076311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9438749245543263307384207 14158123868314894961076311)
            ·
              refine ⟨21237185802472342441614467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14158123868314894961076311 21237185802472342441614467)
              ·
                refine ⟨31855778703708513662421701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21237185802472342441614467 31855778703708513662421701)
                ·
                  refine ⟨5972958506945346311704069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31855778703708513662421701 5972958506945346311704069)
                  ·
                    refine ⟨1119929720052252433444513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5972958506945346311704069 1119929720052252433444513)
                    ·
                      rfl

theorem cell22_3271583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 4, 4].length) (baseStart_3271583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271583 prefixEnd_3271583 := by exact prefixLift 3271583
  have htrace : WordTrace (prefixWord ++ tailWord_3271583) baseStart_3271583 baseEnd_3271583 := by
    simpa [prefixWord, tailWord_3271583, baseEnd_3271583] using wordTrace_append hprefix tailTrace_3271583
  have hstable : (prefixWord ++ tailWord_3271583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271583).length < 2 ^ (prefixWord ++ tailWord_3271583).sum := by decide
  have hdescent : baseEnd_3271583 < baseStart_3271583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271585 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 4, 3]
def baseStart_3271585 : Nat := 118140960795 + 3271585 * 2 ^ 59
def prefixEnd_3271585 : Nat := 4983230072969 + 3 ^ 40 * 3271585 * 2
def baseEnd_3271585 : Nat := 1119930404693125094894507

theorem tailTrace_3271585 : CollatzResearch.WordTrace tailWord_3271585 prefixEnd_3271585 1119930404693125094894507 := by
  unfold tailWord_3271585
  simp only [CollatzResearch.WordTrace]
  refine ⟨119324507852613762079368209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79549671901742508052912139 119324507852613762079368209)
  ·
    refine ⟨89493380889460321559526157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119324507852613762079368209 89493380889460321559526157)
    ·
      refine ⟨33560017833547620584822309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89493380889460321559526157 33560017833547620584822309)
      ·
        refine ⟨6292503343790178859654183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33560017833547620584822309 6292503343790178859654183)
        ·
          refine ⟨9438755015685268289481275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6292503343790178859654183 9438755015685268289481275)
          ·
            refine ⟨14158132523527902434221913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9438755015685268289481275 14158132523527902434221913)
            ·
              refine ⟨10618599392645926825666435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14158132523527902434221913 10618599392645926825666435)
              ·
                refine ⟨15927899088968890238499653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10618599392645926825666435 15927899088968890238499653)
                ·
                  refine ⟨2986481079181666919718685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 15927899088968890238499653 2986481079181666919718685)
                  ·
                    refine ⟨1119930404693125094894507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2986481079181666919718685 1119930404693125094894507)
                    ·
                      rfl

theorem cell22_3271585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 4, 3].length) (baseStart_3271585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271585 prefixEnd_3271585 := by exact prefixLift 3271585
  have htrace : WordTrace (prefixWord ++ tailWord_3271585) baseStart_3271585 baseEnd_3271585 := by
    simpa [prefixWord, tailWord_3271585, baseEnd_3271585] using wordTrace_append hprefix tailTrace_3271585
  have hstable : (prefixWord ++ tailWord_3271585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271585).length < 2 ^ (prefixWord ++ tailWord_3271585).sum := by decide
  have hdescent : baseEnd_3271585 < baseStart_3271585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271658 : List Nat := [3, 1, 3, 1, 2, 2, 1, 1, 1, 7]
def baseStart_3271658 : Nat := 118140960795 + 3271658 * 2 ^ 59
def prefixEnd_3271658 : Nat := 4983230072969 + 3 ^ 40 * 3271658 * 2
def baseEnd_3271658 : Nat := 1119955394084977237819283

theorem tailTrace_3271658 : CollatzResearch.WordTrace tailWord_3271658 prefixEnd_3271658 1119955394084977237819283 := by
  unfold tailWord_3271658
  simp only [CollatzResearch.WordTrace]
  refine ⟨29831792595337323886693907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79551446920899530364517085 29831792595337323886693907)
  ·
    refine ⟨44747688893005985830040861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29831792595337323886693907 44747688893005985830040861)
    ·
      refine ⟨16780383334877244686265323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44747688893005985830040861 16780383334877244686265323)
      ·
        refine ⟨25170575002315867029397985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16780383334877244686265323 25170575002315867029397985)
        ·
          refine ⟨18877931251736900272048489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25170575002315867029397985 18877931251736900272048489)
          ·
            refine ⟨14158448438802675204036367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18877931251736900272048489 14158448438802675204036367)
            ·
              refine ⟨21237672658204012806054551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14158448438802675204036367 21237672658204012806054551)
              ·
                refine ⟨31856508987306019209081827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21237672658204012806054551 31856508987306019209081827)
                ·
                  refine ⟨47784763480959028813622741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31856508987306019209081827 47784763480959028813622741)
                  ·
                    refine ⟨1119955394084977237819283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47784763480959028813622741 1119955394084977237819283)
                    ·
                      rfl

theorem cell22_3271658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_3271658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271658 prefixEnd_3271658 := by exact prefixLift 3271658
  have htrace : WordTrace (prefixWord ++ tailWord_3271658) baseStart_3271658 baseEnd_3271658 := by
    simpa [prefixWord, tailWord_3271658, baseEnd_3271658] using wordTrace_append hprefix tailTrace_3271658
  have hstable : (prefixWord ++ tailWord_3271658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271658).length < 2 ^ (prefixWord ++ tailWord_3271658).sum := by decide
  have hdescent : baseEnd_3271658 < baseStart_3271658 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271668 : List Nat := [2, 6, 2, 1, 1, 2, 1, 1, 2, 4]
def baseStart_3271668 : Nat := 118140960795 + 3271668 * 2 ^ 59
def prefixEnd_3271668 : Nat := 4983230072969 + 3 ^ 40 * 3271668 * 2
def baseEnd_3271668 : Nat := 1119958817289340545069253

theorem tailTrace_3271668 : CollatzResearch.WordTrace tailWord_3271668 prefixEnd_3271668 1119958817289340545069253 := by
  unfold tailWord_3271668
  simp only [CollatzResearch.WordTrace]
  refine ⟨59663767555656533627319829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79551690074208711503093105 59663767555656533627319829)
  ·
    refine ⟨2796739104171400013780617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 59663767555656533627319829 2796739104171400013780617)
    ·
      refine ⟨2097554328128550010335463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2796739104171400013780617 2097554328128550010335463)
      ·
        refine ⟨3146331492192825015503195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2097554328128550010335463 3146331492192825015503195)
        ·
          refine ⟨4719497238289237523254793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3146331492192825015503195 4719497238289237523254793)
          ·
            refine ⟨3539622928716928142441095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4719497238289237523254793 3539622928716928142441095)
            ·
              refine ⟨5309434393075392213661643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3539622928716928142441095 5309434393075392213661643)
              ·
                refine ⟨7964151589613088320492465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5309434393075392213661643 7964151589613088320492465)
                ·
                  refine ⟨5973113692209816240369349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7964151589613088320492465 5973113692209816240369349)
                  ·
                    refine ⟨1119958817289340545069253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5973113692209816240369349 1119958817289340545069253)
                    ·
                      rfl

theorem cell22_3271668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_3271668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271668 prefixEnd_3271668 := by exact prefixLift 3271668
  have htrace : WordTrace (prefixWord ++ tailWord_3271668) baseStart_3271668 baseEnd_3271668 := by
    simpa [prefixWord, tailWord_3271668, baseEnd_3271668] using wordTrace_append hprefix tailTrace_3271668
  have hstable : (prefixWord ++ tailWord_3271668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271668).length < 2 ^ (prefixWord ++ tailWord_3271668).sum := by decide
  have hdescent : baseEnd_3271668 < baseStart_3271668 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271673 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 3, 4]
def baseStart_3271673 : Nat := 118140960795 + 3271673 * 2 ^ 59
def prefixEnd_3271673 : Nat := 4983230072969 + 3 ^ 40 * 3271673 * 2
def baseEnd_3271673 : Nat := 1119960528891522198694237

theorem tailTrace_3271673 : CollatzResearch.WordTrace tailWord_3271673 prefixEnd_3271673 1119960528891522198694237 := by
  unfold tailWord_3271673
  simp only [CollatzResearch.WordTrace]
  refine ⟨119327717476294953108571673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79551811650863302072381115 119327717476294953108571673)
  ·
    refine ⟨89495788107221214831428755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119327717476294953108571673 89495788107221214831428755)
    ·
      refine ⟨134243682160831822247143133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89495788107221214831428755 134243682160831822247143133)
      ·
        refine ⟨50341380810311933342678675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134243682160831822247143133 50341380810311933342678675)
        ·
          refine ⟨75512071215467900014018013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50341380810311933342678675 75512071215467900014018013)
          ·
            refine ⟨28317026705800462505256755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75512071215467900014018013 28317026705800462505256755)
            ·
              refine ⟨42475540058700693757885133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28317026705800462505256755 42475540058700693757885133)
              ·
                refine ⟨15928327522012760159206925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42475540058700693757885133 15928327522012760159206925)
                ·
                  refine ⟨5973122820754785059702597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15928327522012760159206925 5973122820754785059702597)
                  ·
                    refine ⟨1119960528891522198694237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5973122820754785059702597 1119960528891522198694237)
                    ·
                      rfl

theorem cell22_3271673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 4].length) (baseStart_3271673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271673 prefixEnd_3271673 := by exact prefixLift 3271673
  have htrace : WordTrace (prefixWord ++ tailWord_3271673) baseStart_3271673 baseEnd_3271673 := by
    simpa [prefixWord, tailWord_3271673, baseEnd_3271673] using wordTrace_append hprefix tailTrace_3271673
  have hstable : (prefixWord ++ tailWord_3271673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271673).length < 2 ^ (prefixWord ++ tailWord_3271673).sum := by decide
  have hdescent : baseEnd_3271673 < baseStart_3271673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271705 : List Nat := [1, 2, 1, 2, 1, 1, 6, 4, 4]
def baseStart_3271705 : Nat := 118140960795 + 3271705 * 2 ^ 59
def prefixEnd_3271705 : Nat := 4983230072969 + 3 ^ 40 * 3271705 * 2
def baseEnd_3271705 : Nat := 373323827715161593964713

theorem tailTrace_3271705 : CollatzResearch.WordTrace tailWord_3271705 prefixEnd_3271705 373323827715161593964713 := by
  unfold tailWord_3271705
  simp only [CollatzResearch.WordTrace]
  refine ⟨119328884612179022573736569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79552589741452681715824379 119328884612179022573736569)
  ·
    refine ⟨89496663459134266930302427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119328884612179022573736569 89496663459134266930302427)
    ·
      refine ⟨134244995188701400395453641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89496663459134266930302427 134244995188701400395453641)
      ·
        refine ⟨100683746391526050296590231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134244995188701400395453641 100683746391526050296590231)
        ·
          refine ⟨151025619587289075444885347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100683746391526050296590231 151025619587289075444885347)
          ·
            refine ⟨226538429380933613167328021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151025619587289075444885347 226538429380933613167328021)
            ·
              refine ⟨10618988877231263117218501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 226538429380933613167328021 10618988877231263117218501)
              ·
                refine ⟨1991060414480861834478469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10618988877231263117218501 1991060414480861834478469)
                ·
                  refine ⟨373323827715161593964713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1991060414480861834478469 373323827715161593964713)
                  ·
                    rfl

theorem cell22_3271705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 6, 4, 4].length) (baseStart_3271705 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271705 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271705 prefixEnd_3271705 := by exact prefixLift 3271705
  have htrace : WordTrace (prefixWord ++ tailWord_3271705) baseStart_3271705 baseEnd_3271705 := by
    simpa [prefixWord, tailWord_3271705, baseEnd_3271705] using wordTrace_append hprefix tailTrace_3271705
  have hstable : (prefixWord ++ tailWord_3271705).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271705).length < 2 ^ (prefixWord ++ tailWord_3271705).sum := by decide
  have hdescent : baseEnd_3271705 < baseStart_3271705 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271793 : List Nat := [1, 2, 2, 2, 1, 1, 2, 1, 3, 7]
def baseStart_3271793 : Nat := 118140960795 + 3271793 * 2 ^ 59
def prefixEnd_3271793 : Nat := 4983230072969 + 3 ^ 40 * 3271793 * 2
def baseEnd_3271793 : Nat := 1120001607343881885693869

theorem tailTrace_3271793 : CollatzResearch.WordTrace tailWord_3271793 prefixEnd_3271793 1120001607343881885693869 := by
  unfold tailWord_3271793
  simp only [CollatzResearch.WordTrace]
  refine ⟨119332094235860213602940033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79554729490573475735293355 119332094235860213602940033)
  ·
    refine ⟨89499070676895160202205025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119332094235860213602940033 89499070676895160202205025)
    ·
      refine ⟨67124303007671370151653769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89499070676895160202205025 67124303007671370151653769)
      ·
        refine ⟨50343227255753527613740327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67124303007671370151653769 50343227255753527613740327)
        ·
          refine ⟨75514840883630291420610491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50343227255753527613740327 75514840883630291420610491)
          ·
            refine ⟨113272261325445437130915737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75514840883630291420610491 113272261325445437130915737)
            ·
              refine ⟨84954195994084077848186803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113272261325445437130915737 84954195994084077848186803)
              ·
                refine ⟨127431293991126116772280205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 84954195994084077848186803 127431293991126116772280205)
                ·
                  refine ⟨47786735246672293789605077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 127431293991126116772280205 47786735246672293789605077)
                  ·
                    refine ⟨1120001607343881885693869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47786735246672293789605077 1120001607343881885693869)
                    ·
                      rfl

theorem cell22_3271793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 7].length) (baseStart_3271793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271793 prefixEnd_3271793 := by exact prefixLift 3271793
  have htrace : WordTrace (prefixWord ++ tailWord_3271793) baseStart_3271793 baseEnd_3271793 := by
    simpa [prefixWord, tailWord_3271793, baseEnd_3271793] using wordTrace_append hprefix tailTrace_3271793
  have hstable : (prefixWord ++ tailWord_3271793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271793).length < 2 ^ (prefixWord ++ tailWord_3271793).sum := by decide
  have hdescent : baseEnd_3271793 < baseStart_3271793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271812 : List Nat := [2, 3, 2, 1, 2, 3, 2, 2, 5]
def baseStart_3271812 : Nat := 118140960795 + 3271812 * 2 ^ 59
def prefixEnd_3271812 : Nat := 4983230072969 + 3 ^ 40 * 3271812 * 2
def baseEnd_3271812 : Nat := 373336037144057389822937

theorem tailTrace_3271812 : CollatzResearch.WordTrace tailWord_3271812 prefixEnd_3271812 373336037144057389822937 := by
  unfold tailWord_3271812
  simp only [CollatzResearch.WordTrace]
  refine ⟨59666393611395689923940845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79555191481860919898587793 59666393611395689923940845)
  ·
    refine ⟨22374897604273383721477817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59666393611395689923940845 22374897604273383721477817)
    ·
      refine ⟨16781173203205037791108363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22374897604273383721477817 16781173203205037791108363)
      ·
        refine ⟨25171759804807556686662545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16781173203205037791108363 25171759804807556686662545)
        ·
          refine ⟨18878819853605667514996909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25171759804807556686662545 18878819853605667514996909)
          ·
            refine ⟨7079557445102125318123841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18878819853605667514996909 7079557445102125318123841)
            ·
              refine ⟨5309668083826593988592881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7079557445102125318123841 5309668083826593988592881)
              ·
                refine ⟨3982251062869945491444661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5309668083826593988592881 3982251062869945491444661)
                ·
                  refine ⟨373336037144057389822937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3982251062869945491444661 373336037144057389822937)
                  ·
                    rfl

theorem cell22_3271812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 2, 5].length) (baseStart_3271812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271812 prefixEnd_3271812 := by exact prefixLift 3271812
  have htrace : WordTrace (prefixWord ++ tailWord_3271812) baseStart_3271812 baseEnd_3271812 := by
    simpa [prefixWord, tailWord_3271812, baseEnd_3271812] using wordTrace_append hprefix tailTrace_3271812
  have hstable : (prefixWord ++ tailWord_3271812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271812).length < 2 ^ (prefixWord ++ tailWord_3271812).sum := by decide
  have hdescent : baseEnd_3271812 < baseStart_3271812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271816 : List Nat := [2, 1, 3, 4, 2, 1, 1, 4, 1, 3]
def baseStart_3271816 : Nat := 118140960795 + 3271816 * 2 ^ 59
def prefixEnd_3271816 : Nat := 4983230072969 + 3 ^ 40 * 3271816 * 2
def baseEnd_3271816 : Nat := 1120009480713917492368799

theorem tailTrace_3271816 : CollatzResearch.WordTrace tailWord_3271816 prefixEnd_3271816 1120009480713917492368799 := by
  unfold tailWord_3271816
  simp only [CollatzResearch.WordTrace]
  refine ⟨59666466557388444265513651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79555288743184592354018201 59666466557388444265513651)
  ·
    refine ⟨89499699836082666398270477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59666466557388444265513651 89499699836082666398270477)
    ·
      refine ⟨33562387438530999899351429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89499699836082666398270477 33562387438530999899351429)
      ·
        refine ⟨6292947644724562481128393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33562387438530999899351429 6292947644724562481128393)
        ·
          refine ⟨4719710733543421860846295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6292947644724562481128393 4719710733543421860846295)
          ·
            refine ⟨7079566100315132791269443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4719710733543421860846295 7079566100315132791269443)
            ·
              refine ⟨10619349150472699186904165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7079566100315132791269443 10619349150472699186904165)
              ·
                refine ⟨1991127965713631097544531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10619349150472699186904165 1991127965713631097544531)
                ·
                  refine ⟨2986691948570446646316797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1991127965713631097544531 2986691948570446646316797)
                  ·
                    refine ⟨1120009480713917492368799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2986691948570446646316797 1120009480713917492368799)
                    ·
                      rfl

theorem cell22_3271816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 1, 3].length) (baseStart_3271816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271816 prefixEnd_3271816 := by exact prefixLift 3271816
  have htrace : WordTrace (prefixWord ++ tailWord_3271816) baseStart_3271816 baseEnd_3271816 := by
    simpa [prefixWord, tailWord_3271816, baseEnd_3271816] using wordTrace_append hprefix tailTrace_3271816
  have hstable : (prefixWord ++ tailWord_3271816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271816).length < 2 ^ (prefixWord ++ tailWord_3271816).sum := by decide
  have hdescent : baseEnd_3271816 < baseStart_3271816 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271840 : List Nat := [2, 1, 1, 4, 2, 1, 3, 2, 6]
def baseStart_3271840 : Nat := 118140960795 + 3271840 * 2 ^ 59
def prefixEnd_3271840 : Nat := 4983230072969 + 3 ^ 40 * 3271840 * 2
def baseEnd_3271840 : Nat := 373339232134796476589575

theorem tailTrace_3271840 : CollatzResearch.WordTrace tailWord_3271840 prefixEnd_3271840 373339232134796476589575 := by
  unfold tailWord_3271840
  simp only [CollatzResearch.WordTrace]
  refine ⟨59666904233344970314950487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79555872311126627086600649 59666904233344970314950487)
  ·
    refine ⟨89500356350017455472425731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59666904233344970314950487 89500356350017455472425731)
    ·
      refine ⟨134250534525026183208638597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89500356350017455472425731 134250534525026183208638597)
      ·
        refine ⟨25171975223442409351619737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134250534525026183208638597 25171975223442409351619737)
        ·
          refine ⟨18878981417581807013714803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25171975223442409351619737 18878981417581807013714803)
          ·
            refine ⟨28318472126372710520572205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18878981417581807013714803 28318472126372710520572205)
            ·
              refine ⟨10619427047389766445214577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28318472126372710520572205 10619427047389766445214577)
              ·
                refine ⟨7964570285542324833910933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10619427047389766445214577 7964570285542324833910933)
                ·
                  refine ⟨373339232134796476589575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7964570285542324833910933 373339232134796476589575)
                  ·
                    rfl

theorem cell22_3271840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 2, 6].length) (baseStart_3271840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271840 prefixEnd_3271840 := by exact prefixLift 3271840
  have htrace : WordTrace (prefixWord ++ tailWord_3271840) baseStart_3271840 baseEnd_3271840 := by
    simpa [prefixWord, tailWord_3271840, baseEnd_3271840] using wordTrace_append hprefix tailTrace_3271840
  have hstable : (prefixWord ++ tailWord_3271840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271840).length < 2 ^ (prefixWord ++ tailWord_3271840).sum := by decide
  have hdescent : baseEnd_3271840 < baseStart_3271840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271855 : List Nat := [1, 1, 2, 1, 2, 3, 4, 2, 1, 5]
def baseStart_3271855 : Nat := 118140960795 + 3271855 * 2 ^ 59
def prefixEnd_3271855 : Nat := 4983230072969 + 3 ^ 40 * 3271855 * 2
def baseEnd_3271855 : Nat := 1120022831210934390643679

theorem tailTrace_3271855 : CollatzResearch.WordTrace tailWord_3271855 prefixEnd_3271855 1120022831210934390643679 := by
  unfold tailWord_3271855
  simp only [CollatzResearch.WordTrace]
  refine ⟨119334355561635598191697019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79556237041090398794464679 119334355561635598191697019)
  ·
    refine ⟨179001533342453397287545529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119334355561635598191697019 179001533342453397287545529)
    ·
      refine ⟨134251150006840047965659147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179001533342453397287545529 134251150006840047965659147)
      ·
        refine ⟨201376725010260071948488721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134251150006840047965659147 201376725010260071948488721)
        ·
          refine ⟨151032543757695053961366541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 201376725010260071948488721 151032543757695053961366541)
          ·
            refine ⟨56637203909135645235512453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 151032543757695053961366541 56637203909135645235512453)
            ·
              refine ⟨10619475732962933481658585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56637203909135645235512453 10619475732962933481658585)
              ·
                refine ⟨7964606799722200111243939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10619475732962933481658585 7964606799722200111243939)
                ·
                  refine ⟨11946910199583300166865909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7964606799722200111243939 11946910199583300166865909)
                  ·
                    refine ⟨1120022831210934390643679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11946910199583300166865909 1120022831210934390643679)
                    ·
                      rfl

theorem cell22_3271855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 5].length) (baseStart_3271855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271855 prefixEnd_3271855 := by exact prefixLift 3271855
  have htrace : WordTrace (prefixWord ++ tailWord_3271855) baseStart_3271855 baseEnd_3271855 := by
    simpa [prefixWord, tailWord_3271855, baseEnd_3271855] using wordTrace_append hprefix tailTrace_3271855
  have hstable : (prefixWord ++ tailWord_3271855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271855).length < 2 ^ (prefixWord ++ tailWord_3271855).sum := by decide
  have hdescent : baseEnd_3271855 < baseStart_3271855 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271930 : List Nat := [3, 1, 1, 1, 1, 4, 1, 3, 7]
def baseStart_3271930 : Nat := 118140960795 + 3271930 * 2 ^ 59
def prefixEnd_3271930 : Nat := 4983230072969 + 3 ^ 40 * 3271930 * 2
def baseEnd_3271930 : Nat := 373349501747886398339483

theorem tailTrace_3271930 : CollatzResearch.WordTrace tailWord_3271930 prefixEnd_3271930 373349501747886398339483 := by
  unfold tailWord_3271930
  simp only [CollatzResearch.WordTrace]
  refine ⟨29834272759090971500169311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79558060690909257333784829 29834272759090971500169311)
  ·
    refine ⟨44751409138636457250253967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29834272759090971500169311 44751409138636457250253967)
    ·
      refine ⟨67127113707954685875380951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44751409138636457250253967 67127113707954685875380951)
      ·
        refine ⟨100690670561932028813071427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67127113707954685875380951 100690670561932028813071427)
        ·
          refine ⟨151036005842898043219607141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100690670561932028813071427 151036005842898043219607141)
          ·
            refine ⟨28319251095543383103676339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 151036005842898043219607141 28319251095543383103676339)
            ·
              refine ⟨42478876643315074655514509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28319251095543383103676339 42478876643315074655514509)
              ·
                refine ⟨15929578741243152995817941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42478876643315074655514509 15929578741243152995817941)
                ·
                  refine ⟨373349501747886398339483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15929578741243152995817941 373349501747886398339483)
                  ·
                    rfl

theorem cell22_3271930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 3, 7].length) (baseStart_3271930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271930 prefixEnd_3271930 := by exact prefixLift 3271930
  have htrace : WordTrace (prefixWord ++ tailWord_3271930) baseStart_3271930 baseEnd_3271930 := by
    simpa [prefixWord, tailWord_3271930, baseEnd_3271930] using wordTrace_append hprefix tailTrace_3271930
  have hstable : (prefixWord ++ tailWord_3271930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271930).length < 2 ^ (prefixWord ++ tailWord_3271930).sum := by decide
  have hdescent : baseEnd_3271930 < baseStart_3271930 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271945 : List Nat := [1, 2, 1, 1, 3, 3, 2, 1, 1, 7]
def baseStart_3271945 : Nat := 118140960795 + 3271945 * 2 ^ 59
def prefixEnd_3271945 : Nat := 4983230072969 + 3 ^ 40 * 3271945 * 2
def baseEnd_3271945 : Nat := 1120053640050204155893403

theorem tailTrace_3271945 : CollatzResearch.WordTrace tailWord_3271945 prefixEnd_3271945 1120053640050204155893403 := by
  unfold tailWord_3271945
  simp only [CollatzResearch.WordTrace]
  refine ⟨119337638131309543562473289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79558425420873029041648859 119337638131309543562473289)
  ·
    refine ⟨89503228598482157671854967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119337638131309543562473289 89503228598482157671854967)
    ·
      refine ⟨134254842897723236507782451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89503228598482157671854967 134254842897723236507782451)
      ·
        refine ⟨201382264346584854761673677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134254842897723236507782451 201382264346584854761673677)
        ·
          refine ⟨75518349129969320535627629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201382264346584854761673677 75518349129969320535627629)
          ·
            refine ⟨28319380923738495200860361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 75518349129969320535627629 28319380923738495200860361)
            ·
              refine ⟨21239535692803871400645271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28319380923738495200860361 21239535692803871400645271)
              ·
                refine ⟨31859303539205807100967907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21239535692803871400645271 31859303539205807100967907)
                ·
                  refine ⟨47788955308808710651451861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31859303539205807100967907 47788955308808710651451861)
                  ·
                    refine ⟨1120053640050204155893403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47788955308808710651451861 1120053640050204155893403)
                    ·
                      rfl

theorem cell22_3271945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 1, 1, 7].length) (baseStart_3271945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271945 prefixEnd_3271945 := by exact prefixLift 3271945
  have htrace : WordTrace (prefixWord ++ tailWord_3271945) baseStart_3271945 baseEnd_3271945 := by
    simpa [prefixWord, tailWord_3271945, baseEnd_3271945] using wordTrace_append hprefix tailTrace_3271945
  have hstable : (prefixWord ++ tailWord_3271945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271945).length < 2 ^ (prefixWord ++ tailWord_3271945).sum := by decide
  have hdescent : baseEnd_3271945 < baseStart_3271945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271947 : List Nat := [1, 1, 1, 1, 5, 4, 1, 3, 5]
def baseStart_3271947 : Nat := 118140960795 + 3271947 * 2 ^ 59
def prefixEnd_3271947 : Nat := 4983230072969 + 3 ^ 40 * 3271947 * 2
def baseEnd_3271947 : Nat := 373351441563692272447799

theorem tailTrace_3271947 : CollatzResearch.WordTrace tailWord_3271947 prefixEnd_3271947 373351441563692272447799 := by
  unfold tailWord_3271947
  simp only [CollatzResearch.WordTrace]
  refine ⟨119337711077302297904046095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79558474051534865269364063 119337711077302297904046095)
  ·
    refine ⟨179006566615953446856069143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119337711077302297904046095 179006566615953446856069143)
    ·
      refine ⟨268509849923930170284103715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179006566615953446856069143 268509849923930170284103715)
      ·
        refine ⟨402764774885895255426155573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268509849923930170284103715 402764774885895255426155573)
        ·
          refine ⟨37759197645552680196202085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 402764774885895255426155573 37759197645552680196202085)
          ·
            refine ⟨7079849558541127536787891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37759197645552680196202085 7079849558541127536787891)
            ·
              refine ⟨10619774337811691305181837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7079849558541127536787891 10619774337811691305181837)
              ·
                refine ⟨3982415376679384239443189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10619774337811691305181837 3982415376679384239443189)
                ·
                  refine ⟨373351441563692272447799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3982415376679384239443189 373351441563692272447799)
                  ·
                    rfl

theorem cell22_3271947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 3, 5].length) (baseStart_3271947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271947 prefixEnd_3271947 := by exact prefixLift 3271947
  have htrace : WordTrace (prefixWord ++ tailWord_3271947) baseStart_3271947 baseEnd_3271947 := by
    simpa [prefixWord, tailWord_3271947, baseEnd_3271947] using wordTrace_append hprefix tailTrace_3271947
  have hstable : (prefixWord ++ tailWord_3271947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271947).length < 2 ^ (prefixWord ++ tailWord_3271947).sum := by decide
  have hdescent : baseEnd_3271947 < baseStart_3271947 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3271981 : List Nat := [1, 5, 3, 1, 1, 2, 2, 2, 5]
def baseStart_3271981 : Nat := 118140960795 + 3271981 * 2 ^ 59
def prefixEnd_3271981 : Nat := 4983230072969 + 3 ^ 40 * 3271981 * 2
def baseEnd_3271981 : Nat := 373355321195304020664431

theorem tailTrace_3271981 : CollatzResearch.WordTrace tailWord_3271981 prefixEnd_3271981 373355321195304020664431 := by
  unfold tailWord_3271981
  simp only [CollatzResearch.WordTrace]
  refine ⟨119338951159179121710783797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79559300772786081140522531 119338951159179121710783797)
  ·
    refine ⟨11188026671173042660385981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119338951159179121710783797 11188026671173042660385981)
    ·
      refine ⟨4195510001689890997644743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11188026671173042660385981 4195510001689890997644743)
      ·
        refine ⟨6293265002534836496467115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4195510001689890997644743 6293265002534836496467115)
        ·
          refine ⟨9439897503802254744700673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6293265002534836496467115 9439897503802254744700673)
          ·
            refine ⟨7079923127851691058525505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9439897503802254744700673 7079923127851691058525505)
            ·
              refine ⟨5309942345888768293894129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7079923127851691058525505 5309942345888768293894129)
              ·
                refine ⟨3982456759416576220420597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5309942345888768293894129 3982456759416576220420597)
                ·
                  refine ⟨373355321195304020664431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3982456759416576220420597 373355321195304020664431)
                  ·
                    rfl

theorem cell22_3271981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 2, 5].length) (baseStart_3271981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3271981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3271981 prefixEnd_3271981 := by exact prefixLift 3271981
  have htrace : WordTrace (prefixWord ++ tailWord_3271981) baseStart_3271981 baseEnd_3271981 := by
    simpa [prefixWord, tailWord_3271981, baseEnd_3271981] using wordTrace_append hprefix tailTrace_3271981
  have hstable : (prefixWord ++ tailWord_3271981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3271981).length < 2 ^ (prefixWord ++ tailWord_3271981).sum := by decide
  have hdescent : baseEnd_3271981 < baseStart_3271981 := by decide
  rcases family_descends (prefixWord ++ tailWord_3271981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272007 : List Nat := [1, 1, 4, 1, 2, 3, 1, 3, 1, 5]
def baseStart_3272007 : Nat := 118140960795 + 3272007 * 2 ^ 59
def prefixEnd_3272007 : Nat := 4983230072969 + 3 ^ 40 * 3272007 * 2
def baseEnd_3272007 : Nat := 1120074863917256660843213

theorem tailTrace_3272007 : CollatzResearch.WordTrace tailWord_3272007 prefixEnd_3272007 1120074863917256660843213 := by
  unfold tailWord_3272007
  simp only [CollatzResearch.WordTrace]
  refine ⟨119339899457084928151230275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79559932971389952100820183 119339899457084928151230275)
  ·
    refine ⟨179009849185627392226845413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119339899457084928151230275 179009849185627392226845413)
    ·
      refine ⟨33564346722305136042533515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 179009849185627392226845413 33564346722305136042533515)
      ·
        refine ⟨50346520083457704063800273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33564346722305136042533515 50346520083457704063800273)
        ·
          refine ⟨37759890062593278047850205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50346520083457704063800273 37759890062593278047850205)
          ·
            refine ⟨14159958773472479267943827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37759890062593278047850205 14159958773472479267943827)
            ·
              refine ⟨21239938160208718901915741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14159958773472479267943827 21239938160208718901915741)
              ·
                refine ⟨7964976810078269588218403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21239938160208718901915741 7964976810078269588218403)
                ·
                  refine ⟨11947465215117404382327605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7964976810078269588218403 11947465215117404382327605)
                  ·
                    refine ⟨1120074863917256660843213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11947465215117404382327605 1120074863917256660843213)
                    ·
                      rfl

theorem cell22_3272007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_3272007 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272007 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272007 prefixEnd_3272007 := by exact prefixLift 3272007
  have htrace : WordTrace (prefixWord ++ tailWord_3272007) baseStart_3272007 baseEnd_3272007 := by
    simpa [prefixWord, tailWord_3272007, baseEnd_3272007] using wordTrace_append hprefix tailTrace_3272007
  have hstable : (prefixWord ++ tailWord_3272007).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272007).length < 2 ^ (prefixWord ++ tailWord_3272007).sum := by decide
  have hdescent : baseEnd_3272007 < baseStart_3272007 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272069 : List Nat := [1, 3, 1, 1, 3, 1, 4, 2, 3, 3]
def baseStart_3272069 : Nat := 118140960795 + 3272069 * 2 ^ 59
def prefixEnd_3272069 : Nat := 4983230072969 + 3 ^ 40 * 3272069 * 2
def baseEnd_3272069 : Nat := 1120096087784309165793023

theorem tailTrace_3272069 : CollatzResearch.WordTrace tailWord_3272069 prefixEnd_3272069 1120096087784309165793023 := by
  unfold tailWord_3272069
  simp only [CollatzResearch.WordTrace]
  refine ⟨119342160782860312739987261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79561440521906875159991507 119342160782860312739987261)
  ·
    refine ⟨44753310293572617277495223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119342160782860312739987261 44753310293572617277495223)
    ·
      refine ⟨67129965440358925916242835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44753310293572617277495223 67129965440358925916242835)
      ·
        refine ⟨100694948160538388874364253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67129965440358925916242835 100694948160538388874364253)
        ·
          refine ⟨37760605560201895827886595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100694948160538388874364253 37760605560201895827886595)
          ·
            refine ⟨56640908340302843741829893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37760605560201895827886595 56640908340302843741829893)
            ·
              refine ⟨10620170313806783201593105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 56640908340302843741829893 10620170313806783201593105)
              ·
                refine ⟨7965127735355087401194829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10620170313806783201593105 7965127735355087401194829)
                ·
                  refine ⟨2986922900758157775448061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7965127735355087401194829 2986922900758157775448061)
                  ·
                    refine ⟨1120096087784309165793023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2986922900758157775448061 1120096087784309165793023)
                    ·
                      rfl

theorem cell22_3272069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 3, 3].length) (baseStart_3272069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272069 prefixEnd_3272069 := by exact prefixLift 3272069
  have htrace : WordTrace (prefixWord ++ tailWord_3272069) baseStart_3272069 baseEnd_3272069 := by
    simpa [prefixWord, tailWord_3272069, baseEnd_3272069] using wordTrace_append hprefix tailTrace_3272069
  have hstable : (prefixWord ++ tailWord_3272069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272069).length < 2 ^ (prefixWord ++ tailWord_3272069).sum := by decide
  have hdescent : baseEnd_3272069 < baseStart_3272069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272127 : List Nat := [1, 1, 2, 2, 2, 1, 1, 6, 6]
def baseStart_3272127 : Nat := 118140960795 + 3272127 * 2 ^ 59
def prefixEnd_3272127 : Nat := 4983230072969 + 3 ^ 40 * 3272127 * 2
def baseEnd_3272127 : Nat := 373371980789872115947615

theorem tailTrace_3272127 : CollatzResearch.WordTrace tailWord_3272127 prefixEnd_3272127 373371980789872115947615 := by
  unfold tailWord_3272127
  simp only [CollatzResearch.WordTrace]
  refine ⟨119344276216650188645598635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79562850811100125763732423 119344276216650188645598635)
  ·
    refine ⟨179016414324975282968397953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119344276216650188645598635 179016414324975282968397953)
    ·
      refine ⟨134262310743731462226298465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179016414324975282968397953 134262310743731462226298465)
      ·
        refine ⟨100696733057798596669723849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134262310743731462226298465 100696733057798596669723849)
        ·
          refine ⟨75522549793348947502292887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100696733057798596669723849 75522549793348947502292887)
          ·
            refine ⟨113283824690023421253439331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75522549793348947502292887 113283824690023421253439331)
            ·
              refine ⟨169925737035035131880158997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113283824690023421253439331 169925737035035131880158997)
              ·
                refine ⟨7965268923517271806882453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 169925737035035131880158997 7965268923517271806882453)
                ·
                  refine ⟨373371980789872115947615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7965268923517271806882453 373371980789872115947615)
                  ·
                    rfl

theorem cell22_3272127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 6, 6].length) (baseStart_3272127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272127 prefixEnd_3272127 := by exact prefixLift 3272127
  have htrace : WordTrace (prefixWord ++ tailWord_3272127) baseStart_3272127 baseEnd_3272127 := by
    simpa [prefixWord, tailWord_3272127, baseEnd_3272127] using wordTrace_append hprefix tailTrace_3272127
  have hstable : (prefixWord ++ tailWord_3272127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272127).length < 2 ^ (prefixWord ++ tailWord_3272127).sum := by decide
  have hdescent : baseEnd_3272127 < baseStart_3272127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272161 : List Nat := [1, 2, 3, 1, 2, 4, 1, 4, 4]
def baseStart_3272161 : Nat := 118140960795 + 3272161 * 2 ^ 59
def prefixEnd_3272161 : Nat := 4983230072969 + 3 ^ 40 * 3272161 * 2
def baseEnd_3272161 : Nat := 373375860421483864164247

theorem tailTrace_3272161 : CollatzResearch.WordTrace tailWord_3272161 prefixEnd_3272161 373375860421483864164247 := by
  unfold tailWord_3272161
  simp only [CollatzResearch.WordTrace]
  refine ⟨119345516298527012452336337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79563677532351341634890891 119345516298527012452336337)
  ·
    refine ⟨89509137223895259339252253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119345516298527012452336337 89509137223895259339252253)
    ·
      refine ⟨33565926458960722252219595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89509137223895259339252253 33565926458960722252219595)
      ·
        refine ⟨50348889688441083378329393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33565926458960722252219595 50348889688441083378329393)
        ·
          refine ⟨37761667266330812533747045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50348889688441083378329393 37761667266330812533747045)
          ·
            refine ⟨7080312612437027350077571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 37761667266330812533747045 7080312612437027350077571)
            ·
              refine ⟨10620468918655541025116357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7080312612437027350077571 10620468918655541025116357)
              ·
                refine ⟨1991337922247913942209317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10620468918655541025116357 1991337922247913942209317)
                ·
                  refine ⟨373375860421483864164247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1991337922247913942209317 373375860421483864164247)
                  ·
                    rfl

theorem cell22_3272161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4, 4].length) (baseStart_3272161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272161 prefixEnd_3272161 := by exact prefixLift 3272161
  have htrace : WordTrace (prefixWord ++ tailWord_3272161) baseStart_3272161 baseEnd_3272161 := by
    simpa [prefixWord, tailWord_3272161, baseEnd_3272161] using wordTrace_append hprefix tailTrace_3272161
  have hstable : (prefixWord ++ tailWord_3272161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272161).length < 2 ^ (prefixWord ++ tailWord_3272161).sum := by decide
  have hdescent : baseEnd_3272161 < baseStart_3272161 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272172 : List Nat := [2, 2, 1, 1, 2, 1, 2, 11]
def baseStart_3272172 : Nat := 118140960795 + 3272172 * 2 ^ 59
def prefixEnd_3272172 : Nat := 4983230072969 + 3 ^ 40 * 3272172 * 2
def baseEnd_3272172 : Nat := 124459038532139025607523

theorem tailTrace_3272172 : CollatzResearch.WordTrace tailWord_3272172 prefixEnd_3272172 124459038532139025607523 := by
  unfold tailWord_3272172
  simp only [CollatzResearch.WordTrace]
  refine ⟨59672958750743580665493385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79563945000991440887324513 59672958750743580665493385)
  ·
    refine ⟨44754719063057685499120039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59672958750743580665493385 44754719063057685499120039)
    ·
      refine ⟨67132078594586528248680059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44754719063057685499120039 67132078594586528248680059)
      ·
        refine ⟨100698117891879792373020089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67132078594586528248680059 100698117891879792373020089)
        ·
          refine ⟨75523588418909844279765067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100698117891879792373020089 75523588418909844279765067)
          ·
            refine ⟨113285382628364766419647601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75523588418909844279765067 113285382628364766419647601)
            ·
              refine ⟨84964036971273574814735701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 113285382628364766419647601 84964036971273574814735701)
              ·
                refine ⟨124459038532139025607523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 84964036971273574814735701 124459038532139025607523)
                ·
                  rfl

theorem cell22_3272172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 11].length) (baseStart_3272172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272172 prefixEnd_3272172 := by exact prefixLift 3272172
  have htrace : WordTrace (prefixWord ++ tailWord_3272172) baseStart_3272172 baseEnd_3272172 := by
    simpa [prefixWord, tailWord_3272172, baseEnd_3272172] using wordTrace_append hprefix tailTrace_3272172
  have hstable : (prefixWord ++ tailWord_3272172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272172).length < 2 ^ (prefixWord ++ tailWord_3272172).sum := by decide
  have hdescent : baseEnd_3272172 < baseStart_3272172 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272174 : List Nat := [4, 1, 2, 1, 2, 1, 2, 2, 1, 6]
def baseStart_3272174 : Nat := 118140960795 + 3272174 * 2 ^ 59
def prefixEnd_3272174 : Nat := 4983230072969 + 3 ^ 40 * 3272174 * 2
def baseEnd_3272174 : Nat := 1120132031430123891917701

theorem tailTrace_3272174 : CollatzResearch.WordTrace tailWord_3272174 prefixEnd_3272174 1120132031430123891917701 := by
  unfold tailWord_3272174
  simp only [CollatzResearch.WordTrace]
  refine ⟨14918248805934989459069947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79563993631653277115039717 14918248805934989459069947)
  ·
    refine ⟨22377373208902484188604921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14918248805934989459069947 22377373208902484188604921)
    ·
      refine ⟨16783029906676863141453691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22377373208902484188604921 16783029906676863141453691)
      ·
        refine ⟨25174544860015294712180537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16783029906676863141453691 25174544860015294712180537)
        ·
          refine ⟨18880908645011471034135403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25174544860015294712180537 18880908645011471034135403)
          ·
            refine ⟨28321362967517206551203105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18880908645011471034135403 28321362967517206551203105)
            ·
              refine ⟨21241022225637904913402329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28321362967517206551203105 21241022225637904913402329)
              ·
                refine ⟨15930766669228428685051747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21241022225637904913402329 15930766669228428685051747)
                ·
                  refine ⟨23896150003842643027577621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15930766669228428685051747 23896150003842643027577621)
                  ·
                    refine ⟨1120132031430123891917701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23896150003842643027577621 1120132031430123891917701)
                    ·
                      rfl

theorem cell22_3272174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 2, 2, 1, 6].length) (baseStart_3272174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272174 prefixEnd_3272174 := by exact prefixLift 3272174
  have htrace : WordTrace (prefixWord ++ tailWord_3272174) baseStart_3272174 baseEnd_3272174 := by
    simpa [prefixWord, tailWord_3272174, baseEnd_3272174] using wordTrace_append hprefix tailTrace_3272174
  have hstable : (prefixWord ++ tailWord_3272174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272174).length < 2 ^ (prefixWord ++ tailWord_3272174).sum := by decide
  have hdescent : baseEnd_3272174 < baseStart_3272174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272176 : List Nat := [2, 1, 1, 1, 3, 4, 2, 3, 2, 3]
def baseStart_3272176 : Nat := 118140960795 + 3272176 * 2 ^ 59
def prefixEnd_3272176 : Nat := 4983230072969 + 3 ^ 40 * 3272176 * 2
def baseEnd_3272176 : Nat := 1120132716070996553367695

theorem tailTrace_3272176 : CollatzResearch.WordTrace tailWord_3272176 prefixEnd_3272176 1120132716070996553367695 := by
  unfold tailWord_3272176
  simp only [CollatzResearch.WordTrace]
  refine ⟨59673031696736335007066191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79564042262315113342754921 59673031696736335007066191)
  ·
    refine ⟨89509547545104502510599287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59673031696736335007066191 89509547545104502510599287)
    ·
      refine ⟨134264321317656753765898931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89509547545104502510599287 134264321317656753765898931)
      ·
        refine ⟨201396481976485130648848397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134264321317656753765898931 201396481976485130648848397)
        ·
          refine ⟨75523680741181923993318149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201396481976485130648848397 75523680741181923993318149)
          ·
            refine ⟨14160690138971610748747153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75523680741181923993318149 14160690138971610748747153)
            ·
              refine ⟨10620517604228708061560365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14160690138971610748747153 10620517604228708061560365)
              ·
                refine ⟨3982694101585765523085137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10620517604228708061560365 3982694101585765523085137)
                ·
                  refine ⟨2987020576189324142313853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3982694101585765523085137 2987020576189324142313853)
                  ·
                    refine ⟨1120132716070996553367695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2987020576189324142313853 1120132716070996553367695)
                    ·
                      rfl

theorem cell22_3272176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 2, 3].length) (baseStart_3272176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272176 prefixEnd_3272176 := by exact prefixLift 3272176
  have htrace : WordTrace (prefixWord ++ tailWord_3272176) baseStart_3272176 baseEnd_3272176 := by
    simpa [prefixWord, tailWord_3272176, baseEnd_3272176] using wordTrace_append hprefix tailTrace_3272176
  have hstable : (prefixWord ++ tailWord_3272176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272176).length < 2 ^ (prefixWord ++ tailWord_3272176).sum := by decide
  have hdescent : baseEnd_3272176 < baseStart_3272176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272187 : List Nat := [1, 1, 1, 1, 1, 3, 2, 3, 2, 7]
def baseStart_3272187 : Nat := 118140960795 + 3272187 * 2 ^ 59
def prefixEnd_3272187 : Nat := 4983230072969 + 3 ^ 40 * 3272187 * 2
def baseEnd_3272187 : Nat := 1120136481595796191342661

theorem tailTrace_3272187 : CollatzResearch.WordTrace tailWord_3272187 prefixEnd_3272187 1120136481595796191342661 := by
  unfold tailWord_3272187
  simp only [CollatzResearch.WordTrace]
  refine ⟨119346464596432818892782815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79564309730955212595188543 119346464596432818892782815)
  ·
    refine ⟨179019696894649228339174223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119346464596432818892782815 179019696894649228339174223)
    ·
      refine ⟨268529545341973842508761335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179019696894649228339174223 268529545341973842508761335)
      ·
        refine ⟨402794318012960763763142003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268529545341973842508761335 402794318012960763763142003)
        ·
          refine ⟨604191477019441145644713005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402794318012960763763142003 604191477019441145644713005)
          ·
            refine ⟨226571803882290429616767377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 604191477019441145644713005 226571803882290429616767377)
            ·
              refine ⟨169928852911717822212575533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226571803882290429616767377 169928852911717822212575533)
              ·
                refine ⟨63723319841894183329715825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 169928852911717822212575533 63723319841894183329715825)
                ·
                  refine ⟨47792489881420637497286869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 63723319841894183329715825 47792489881420637497286869)
                  ·
                    refine ⟨1120136481595796191342661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47792489881420637497286869 1120136481595796191342661)
                    ·
                      rfl

theorem cell22_3272187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 7].length) (baseStart_3272187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272187 prefixEnd_3272187 := by exact prefixLift 3272187
  have htrace : WordTrace (prefixWord ++ tailWord_3272187) baseStart_3272187 baseEnd_3272187 := by
    simpa [prefixWord, tailWord_3272187, baseEnd_3272187] using wordTrace_append hprefix tailTrace_3272187
  have hstable : (prefixWord ++ tailWord_3272187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272187).length < 2 ^ (prefixWord ++ tailWord_3272187).sum := by decide
  have hdescent : baseEnd_3272187 < baseStart_3272187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272238 : List Nat := [4, 1, 3, 1, 2, 1, 2, 2, 3, 3]
def baseStart_3272238 : Nat := 118140960795 + 3272238 * 2 ^ 59
def prefixEnd_3272238 : Nat := 4983230072969 + 3 ^ 40 * 3272238 * 2
def baseEnd_3272238 : Nat := 1120153939938049058317505

theorem tailTrace_3272238 : CollatzResearch.WordTrace tailWord_3272238 prefixEnd_3272238 1120153939938049058317505 := by
  unfold tailWord_3272238
  simp only [CollatzResearch.WordTrace]
  refine ⟨14918540589906006825361171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79565549812832036401926245 14918540589906006825361171)
  ·
    refine ⟨22377810884859010238041757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14918540589906006825361171 22377810884859010238041757)
    ·
      refine ⟨8391679081822128839265659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22377810884859010238041757 8391679081822128839265659)
      ·
        refine ⟨12587518622733193258898489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8391679081822128839265659 12587518622733193258898489)
        ·
          refine ⟨9440638967049894944173867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12587518622733193258898489 9440638967049894944173867)
          ·
            refine ⟨14160958450574842416260801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9440638967049894944173867 14160958450574842416260801)
            ·
              refine ⟨10620718837931131812195601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14160958450574842416260801 10620718837931131812195601)
              ·
                refine ⟨7965539128448348859146701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10620718837931131812195601 7965539128448348859146701)
                ·
                  refine ⟨2987077173168130822180013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7965539128448348859146701 2987077173168130822180013)
                  ·
                    refine ⟨1120153939938049058317505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2987077173168130822180013 1120153939938049058317505)
                    ·
                      rfl

theorem cell22_3272238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_3272238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272238 prefixEnd_3272238 := by exact prefixLift 3272238
  have htrace : WordTrace (prefixWord ++ tailWord_3272238) baseStart_3272238 baseEnd_3272238 := by
    simpa [prefixWord, tailWord_3272238, baseEnd_3272238] using wordTrace_append hprefix tailTrace_3272238
  have hstable : (prefixWord ++ tailWord_3272238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272238).length < 2 ^ (prefixWord ++ tailWord_3272238).sum := by decide
  have hdescent : baseEnd_3272238 < baseStart_3272238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272255 : List Nat := [1, 1, 2, 2, 3, 5, 1, 3, 1, 3]
def baseStart_3272255 : Nat := 118140960795 + 3272255 * 2 ^ 59
def prefixEnd_3272255 : Nat := 4983230072969 + 3 ^ 40 * 3272255 * 2
def baseEnd_3272255 : Nat := 1120159759385466680642453

theorem tailTrace_3272255 : CollatzResearch.WordTrace tailWord_3272255 prefixEnd_3272255 1120159759385466680642453 := by
  unfold tailWord_3272255
  simp only [CollatzResearch.WordTrace]
  refine ⟨119348944760186466506258219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79565963173457644337505479 119348944760186466506258219)
  ·
    refine ⟨179023417140279699759387329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119348944760186466506258219 179023417140279699759387329)
    ·
      refine ⟨134267562855209774819540497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179023417140279699759387329 134267562855209774819540497)
      ·
        refine ⟨100700672141407331114655373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 134267562855209774819540497 100700672141407331114655373)
        ·
          refine ⟨37762752053027749167995765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 100700672141407331114655373 37762752053027749167995765)
          ·
            refine ⟨3540258004971351484499603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 37762752053027749167995765 3540258004971351484499603)
            ·
              refine ⟨5310387007457027226749405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3540258004971351484499603 5310387007457027226749405)
              ·
                refine ⟨1991395127796385210031027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5310387007457027226749405 1991395127796385210031027)
                ·
                  refine ⟨2987092691694577815046541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1991395127796385210031027 2987092691694577815046541)
                  ·
                    refine ⟨1120159759385466680642453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2987092691694577815046541 1120159759385466680642453)
                    ·
                      rfl

theorem cell22_3272255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 1, 3].length) (baseStart_3272255 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272255 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272255 prefixEnd_3272255 := by exact prefixLift 3272255
  have htrace : WordTrace (prefixWord ++ tailWord_3272255) baseStart_3272255 baseEnd_3272255 := by
    simpa [prefixWord, tailWord_3272255, baseEnd_3272255] using wordTrace_append hprefix tailTrace_3272255
  have hstable : (prefixWord ++ tailWord_3272255).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272255).length < 2 ^ (prefixWord ++ tailWord_3272255).sum := by decide
  have hdescent : baseEnd_3272255 < baseStart_3272255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272264 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 7, 4]
def baseStart_3272264 : Nat := 118140960795 + 3272264 * 2 ^ 59
def prefixEnd_3272264 : Nat := 4983230072969 + 3 ^ 40 * 3272264 * 2
def baseEnd_3272264 : Nat := 1120162840269393657167425

theorem tailTrace_3272264 : CollatzResearch.WordTrace tailWord_3272264 prefixEnd_3272264 1120162840269393657167425 := by
  unfold tailWord_3272264
  simp only [CollatzResearch.WordTrace]
  refine ⟨59674636508576930521667923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79566182011435907362223897 59674636508576930521667923)
  ·
    refine ⟨89511954762865395782501885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59674636508576930521667923 89511954762865395782501885)
    ·
      refine ⟨33566983036074523418438207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89511954762865395782501885 33566983036074523418438207)
      ·
        refine ⟨50350474554111785127657311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33566983036074523418438207 50350474554111785127657311)
        ·
          refine ⟨75525711831167677691485967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50350474554111785127657311 75525711831167677691485967)
          ·
            refine ⟨113288567746751516537228951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 75525711831167677691485967 113288567746751516537228951)
            ·
              refine ⟨169932851620127274805843427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 113288567746751516537228951 169932851620127274805843427)
              ·
                refine ⟨254899277430190912208765141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169932851620127274805843427 254899277430190912208765141)
                ·
                  refine ⟨5974201814770099504892933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 254899277430190912208765141 5974201814770099504892933)
                  ·
                    refine ⟨1120162840269393657167425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5974201814770099504892933 1120162840269393657167425)
                    ·
                      rfl

theorem cell22_3272264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_3272264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272264 prefixEnd_3272264 := by exact prefixLift 3272264
  have htrace : WordTrace (prefixWord ++ tailWord_3272264) baseStart_3272264 baseEnd_3272264 := by
    simpa [prefixWord, tailWord_3272264, baseEnd_3272264] using wordTrace_append hprefix tailTrace_3272264
  have hstable : (prefixWord ++ tailWord_3272264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272264).length < 2 ^ (prefixWord ++ tailWord_3272264).sum := by decide
  have hdescent : baseEnd_3272264 < baseStart_3272264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272285 : List Nat := [1, 4, 4, 2, 1, 1, 1, 3, 5]
def baseStart_3272285 : Nat := 118140960795 + 3272285 * 2 ^ 59
def prefixEnd_3272285 : Nat := 4983230072969 + 3 ^ 40 * 3272285 * 2
def baseEnd_3272285 : Nat := 373390009666185534130787

theorem tailTrace_3272285 : CollatzResearch.WordTrace tailWord_3272285 prefixEnd_3272285 373390009666185534130787 := by
  unfold tailWord_3272285
  simp only [CollatzResearch.WordTrace]
  refine ⟨119350038950077781629850309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79566692633385187753233539 119350038950077781629850309)
  ·
    refine ⟨22378132303139584055596933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119350038950077781629850309 22378132303139584055596933)
    ·
      refine ⟨4195899806838672010424425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22378132303139584055596933 4195899806838672010424425)
      ·
        refine ⟨3146924855129004007818319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4195899806838672010424425 3146924855129004007818319)
        ·
          refine ⟨4720387282693506011727479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3146924855129004007818319 4720387282693506011727479)
          ·
            refine ⟨7080580924040259017591219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4720387282693506011727479 7080580924040259017591219)
            ·
              refine ⟨10620871386060388526386829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7080580924040259017591219 10620871386060388526386829)
              ·
                refine ⟨3982826769772645697395061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10620871386060388526386829 3982826769772645697395061)
                ·
                  refine ⟨373390009666185534130787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3982826769772645697395061 373390009666185534130787)
                  ·
                    rfl

theorem cell22_3272285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 3, 5].length) (baseStart_3272285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272285 prefixEnd_3272285 := by exact prefixLift 3272285
  have htrace : WordTrace (prefixWord ++ tailWord_3272285) baseStart_3272285 baseEnd_3272285 := by
    simpa [prefixWord, tailWord_3272285, baseEnd_3272285] using wordTrace_append hprefix tailTrace_3272285
  have hstable : (prefixWord ++ tailWord_3272285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272285).length < 2 ^ (prefixWord ++ tailWord_3272285).sum := by decide
  have hdescent : baseEnd_3272285 < baseStart_3272285 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272298 : List Nat := [3, 1, 3, 2, 1, 2, 3, 2, 1, 4]
def baseStart_3272298 : Nat := 118140960795 + 3272298 * 2 ^ 59
def prefixEnd_3272298 : Nat := 4983230072969 + 3 ^ 40 * 3272298 * 2
def baseEnd_3272298 : Nat := 1120174479164228901817321

theorem tailTrace_3272298 : CollatzResearch.WordTrace tailWord_3272298 prefixEnd_3272298 1120174479164228901817321 := by
  unfold tailWord_3272298
  simp only [CollatzResearch.WordTrace]
  refine ⟨29837628274757671212518387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79567008732687123233382365 29837628274757671212518387)
  ·
    refine ⟨44756442412136506818777581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29837628274757671212518387 44756442412136506818777581)
    ·
      refine ⟨16783665904551190057041593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44756442412136506818777581 16783665904551190057041593)
      ·
        refine ⟨12587749428413392542781195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16783665904551190057041593 12587749428413392542781195)
        ·
          refine ⟨18881624142620088814171793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12587749428413392542781195 18881624142620088814171793)
          ·
            refine ⟨14161218106965066610628845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18881624142620088814171793 14161218106965066610628845)
            ·
              refine ⟨5310456790111899978985817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14161218106965066610628845 5310456790111899978985817)
              ·
                refine ⟨3982842592583924984239363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5310456790111899978985817 3982842592583924984239363)
                ·
                  refine ⟨5974263888875887476359045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3982842592583924984239363 5974263888875887476359045)
                  ·
                    refine ⟨1120174479164228901817321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5974263888875887476359045 1120174479164228901817321)
                    ·
                      rfl

theorem cell22_3272298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_3272298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272298 prefixEnd_3272298 := by exact prefixLift 3272298
  have htrace : WordTrace (prefixWord ++ tailWord_3272298) baseStart_3272298 baseEnd_3272298 := by
    simpa [prefixWord, tailWord_3272298, baseEnd_3272298] using wordTrace_append hprefix tailTrace_3272298
  have hstable : (prefixWord ++ tailWord_3272298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272298).length < 2 ^ (prefixWord ++ tailWord_3272298).sum := by decide
  have hdescent : baseEnd_3272298 < baseStart_3272298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272324 : List Nat := [2, 3, 2, 1, 14]
def baseStart_3272324 : Nat := 118140960795 + 3272324 * 2 ^ 59
def prefixEnd_3272324 : Nat := 4983230072969 + 3 ^ 40 * 3272324 * 2
def baseEnd_3272324 : Nat := 4609808146072318932787

theorem tailTrace_3272324 : CollatzResearch.WordTrace tailWord_3272324 prefixEnd_3272324 4609808146072318932787 := by
  unfold tailWord_3272324
  simp only [CollatzResearch.WordTrace]
  refine ⟨59675730698468245645260013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79567640931290994193680017 59675730698468245645260013)
  ·
    refine ⟨22378399011925592116972505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 59675730698468245645260013 22378399011925592116972505)
    ·
      refine ⟨16783799258944194087729379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22378399011925592116972505 16783799258944194087729379)
      ·
        refine ⟨25175698888416291131594069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16783799258944194087729379 25175698888416291131594069)
        ·
          refine ⟨4609808146072318932787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 25175698888416291131594069 4609808146072318932787)
          ·
            rfl

theorem cell22_3272324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 14].length) (baseStart_3272324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272324 prefixEnd_3272324 := by exact prefixLift 3272324
  have htrace : WordTrace (prefixWord ++ tailWord_3272324) baseStart_3272324 baseEnd_3272324 := by
    simpa [prefixWord, tailWord_3272324, baseEnd_3272324] using wordTrace_append hprefix tailTrace_3272324
  have hstable : (prefixWord ++ tailWord_3272324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272324).length < 2 ^ (prefixWord ++ tailWord_3272324).sum := by decide
  have hdescent : baseEnd_3272324 < baseStart_3272324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272330 : List Nat := [3, 1, 2, 3, 2, 1, 4, 2, 4]
def baseStart_3272330 : Nat := 118140960795 + 3272330 * 2 ^ 59
def prefixEnd_3272330 : Nat := 4983230072969 + 3 ^ 40 * 3272330 * 2
def baseEnd_3272330 : Nat := 373395144472730495005741

theorem tailTrace_3272330 : CollatzResearch.WordTrace tailWord_3272330 prefixEnd_3272330 373395144472730495005741 := by
  unfold tailWord_3272330
  simp only [CollatzResearch.WordTrace]
  refine ⟨29837920058728688578809611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79567786823276502876825629 29837920058728688578809611)
  ·
    refine ⟨44756880088093032868214417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29837920058728688578809611 44756880088093032868214417)
    ·
      refine ⟨33567660066069774651160813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44756880088093032868214417 33567660066069774651160813)
      ·
        refine ⟨12587872524776165494185305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33567660066069774651160813 12587872524776165494185305)
        ·
          refine ⟨9440904393582124120638979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12587872524776165494185305 9440904393582124120638979)
          ·
            refine ⟨14161356590373186180958469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9440904393582124120638979 14161356590373186180958469)
            ·
              refine ⟨2655254360694972408929713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14161356590373186180958469 2655254360694972408929713)
              ·
                refine ⟨1991440770521229306697285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2655254360694972408929713 1991440770521229306697285)
                ·
                  refine ⟨373395144472730495005741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1991440770521229306697285 373395144472730495005741)
                  ·
                    rfl

theorem cell22_3272330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 4, 2, 4].length) (baseStart_3272330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272330 prefixEnd_3272330 := by exact prefixLift 3272330
  have htrace : WordTrace (prefixWord ++ tailWord_3272330) baseStart_3272330 baseEnd_3272330 := by
    simpa [prefixWord, tailWord_3272330, baseEnd_3272330] using wordTrace_append hprefix tailTrace_3272330
  have hstable : (prefixWord ++ tailWord_3272330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272330).length < 2 ^ (prefixWord ++ tailWord_3272330).sum := by decide
  have hdescent : baseEnd_3272330 < baseStart_3272330 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272401 : List Nat := [1, 2, 2, 1, 2, 4, 2, 1, 2, 5]
def baseStart_3272401 : Nat := 118140960795 + 3272401 * 2 ^ 59
def prefixEnd_3272401 : Nat := 4983230072969 + 3 ^ 40 * 3272401 * 2
def baseEnd_3272401 : Nat := 1120209738169170966492005

theorem tailTrace_3272401 : CollatzResearch.WordTrace tailWord_3272401 prefixEnd_3272401 1120209738169170966492005 := by
  unfold tailWord_3272401
  simp only [CollatzResearch.WordTrace]
  refine ⟨119354269817657533441073057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79569513211771688960715371 119354269817657533441073057)
  ·
    refine ⟨89515702363243150080804793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119354269817657533441073057 89515702363243150080804793)
    ·
      refine ⟨67136776772432362560603595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89515702363243150080804793 67136776772432362560603595)
      ·
        refine ⟨100705165158648543840905393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67136776772432362560603595 100705165158648543840905393)
        ·
          refine ⟨75528873868986407880679045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100705165158648543840905393 75528873868986407880679045)
          ·
            refine ⟨14161663850434951477627321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 75528873868986407880679045 14161663850434951477627321)
            ·
              refine ⟨10621247887826213608220491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14161663850434951477627321 10621247887826213608220491)
              ·
                refine ⟨15931871831739320412330737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10621247887826213608220491 15931871831739320412330737)
                ·
                  refine ⟨11948903873804490309248053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15931871831739320412330737 11948903873804490309248053)
                  ·
                    refine ⟨1120209738169170966492005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11948903873804490309248053 1120209738169170966492005)
                    ·
                      rfl

theorem cell22_3272401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 5].length) (baseStart_3272401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272401 prefixEnd_3272401 := by exact prefixLift 3272401
  have htrace : WordTrace (prefixWord ++ tailWord_3272401) baseStart_3272401 baseEnd_3272401 := by
    simpa [prefixWord, tailWord_3272401, baseEnd_3272401] using wordTrace_append hprefix tailTrace_3272401
  have hstable : (prefixWord ++ tailWord_3272401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272401).length < 2 ^ (prefixWord ++ tailWord_3272401).sum := by decide
  have hdescent : baseEnd_3272401 < baseStart_3272401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272416 : List Nat := [2, 1, 1, 3, 1, 2, 2, 3, 3, 4]
def baseStart_3272416 : Nat := 118140960795 + 3272416 * 2 ^ 59
def prefixEnd_3272416 : Nat := 4983230072969 + 3 ^ 40 * 3272416 * 2
def baseEnd_3272416 : Nat := 1120214872975715927366959

theorem tailTrace_3272416 : CollatzResearch.WordTrace tailWord_3272416 prefixEnd_3272416 1120214872975715927366959 := by
  unfold tailWord_3272416
  simp only [CollatzResearch.WordTrace]
  refine ⟨59677408456301595501434551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79569877941735460668579401 59677408456301595501434551)
  ·
    refine ⟨89516112684452393252151827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59677408456301595501434551 89516112684452393252151827)
    ·
      refine ⟨134274169026678589878227741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89516112684452393252151827 134274169026678589878227741)
      ·
        refine ⟨50352813385004471204335403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 134274169026678589878227741 50352813385004471204335403)
        ·
          refine ⟨75529220077506706806503105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50352813385004471204335403 75529220077506706806503105)
          ·
            refine ⟨56646915058130030104877329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75529220077506706806503105 56646915058130030104877329)
            ·
              refine ⟨42485186293597522578657997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56646915058130030104877329 42485186293597522578657997)
              ·
                refine ⟨15931944860099070966996749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42485186293597522578657997 15931944860099070966996749)
                ·
                  refine ⟨5974479322537151612623781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15931944860099070966996749 5974479322537151612623781)
                  ·
                    refine ⟨1120214872975715927366959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5974479322537151612623781 1120214872975715927366959)
                    ·
                      rfl

theorem cell22_3272416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 2, 3, 3, 4].length) (baseStart_3272416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272416 prefixEnd_3272416 := by exact prefixLift 3272416
  have htrace : WordTrace (prefixWord ++ tailWord_3272416) baseStart_3272416 baseEnd_3272416 := by
    simpa [prefixWord, tailWord_3272416, baseEnd_3272416] using wordTrace_append hprefix tailTrace_3272416
  have hstable : (prefixWord ++ tailWord_3272416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272416).length < 2 ^ (prefixWord ++ tailWord_3272416).sum := by decide
  have hdescent : baseEnd_3272416 < baseStart_3272416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272433 : List Nat := [1, 2, 2, 2, 2, 3, 2, 3, 1, 4]
def baseStart_3272433 : Nat := 118140960795 + 3272433 * 2 ^ 59
def prefixEnd_3272433 : Nat := 4983230072969 + 3 ^ 40 * 3272433 * 2
def baseEnd_3272433 : Nat := 1120220692423133549691907

theorem tailTrace_3272433 : CollatzResearch.WordTrace tailWord_3272433 prefixEnd_3272433 1120220692423133549691907 := by
  unfold tailWord_3272433
  simp only [CollatzResearch.WordTrace]
  refine ⟨119355436953541602906237953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79570291302361068604158635 119355436953541602906237953)
  ·
    refine ⟨89516577715156202179678465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119355436953541602906237953 89516577715156202179678465)
    ·
      refine ⟨67137433286367151634758849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89516577715156202179678465 67137433286367151634758849)
      ·
        refine ⟨50353074964775363726069137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67137433286367151634758849 50353074964775363726069137)
        ·
          refine ⟨37764806223581522794551853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50353074964775363726069137 37764806223581522794551853)
          ·
            refine ⟨14161802333843071047956945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 37764806223581522794551853 14161802333843071047956945)
            ·
              refine ⟨10621351750382303285967709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14161802333843071047956945 10621351750382303285967709)
              ·
                refine ⟨3983006906393363732237891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10621351750382303285967709 3983006906393363732237891)
                ·
                  refine ⟨5974510359590045598356837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3983006906393363732237891 5974510359590045598356837)
                  ·
                    refine ⟨1120220692423133549691907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5974510359590045598356837 1120220692423133549691907)
                    ·
                      rfl

theorem cell22_3272433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 2, 3, 1, 4].length) (baseStart_3272433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272433 prefixEnd_3272433 := by exact prefixLift 3272433
  have htrace : WordTrace (prefixWord ++ tailWord_3272433) baseStart_3272433 baseEnd_3272433 := by
    simpa [prefixWord, tailWord_3272433, baseEnd_3272433] using wordTrace_append hprefix tailTrace_3272433
  have hstable : (prefixWord ++ tailWord_3272433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272433).length < 2 ^ (prefixWord ++ tailWord_3272433).sum := by decide
  have hdescent : baseEnd_3272433 < baseStart_3272433 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272476 : List Nat := [2, 2, 3, 1, 1, 2, 1, 10]
def baseStart_3272476 : Nat := 118140960795 + 3272476 * 2 ^ 59
def prefixEnd_3272476 : Nat := 4983230072969 + 3 ^ 40 * 3272476 * 2
def baseEnd_3272476 : Nat := 124470601355766196762975

theorem tailTrace_3272476 : CollatzResearch.WordTrace tailWord_3272476 prefixEnd_3272476 124470601355766196762975 := by
  unfold tailWord_3272476
  simp only [CollatzResearch.WordTrace]
  refine ⟨59678502646192910625026641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79571336861590547500035521 59678502646192910625026641)
  ·
    refine ⟨44758876984644682968769981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59678502646192910625026641 44758876984644682968769981)
    ·
      refine ⟨16784578869241756113288743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 44758876984644682968769981 16784578869241756113288743)
      ·
        refine ⟨25176868303862634169933115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16784578869241756113288743 25176868303862634169933115)
        ·
          refine ⟨37765302455793951254899673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25176868303862634169933115 37765302455793951254899673)
          ·
            refine ⟨28323976841845463441174755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37765302455793951254899673 28323976841845463441174755)
            ·
              refine ⟨42485965262768195161762133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28323976841845463441174755 42485965262768195161762133)
              ·
                refine ⟨124470601355766196762975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 42485965262768195161762133 124470601355766196762975)
                ·
                  rfl

theorem cell22_3272476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 10].length) (baseStart_3272476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272476 prefixEnd_3272476 := by exact prefixLift 3272476
  have htrace : WordTrace (prefixWord ++ tailWord_3272476) baseStart_3272476 baseEnd_3272476 := by
    simpa [prefixWord, tailWord_3272476, baseEnd_3272476] using wordTrace_append hprefix tailTrace_3272476
  have hstable : (prefixWord ++ tailWord_3272476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272476).length < 2 ^ (prefixWord ++ tailWord_3272476).sum := by decide
  have hdescent : baseEnd_3272476 < baseStart_3272476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272499 : List Nat := [1, 1, 1, 2, 8, 1, 2, 2, 4]
def baseStart_3272499 : Nat := 118140960795 + 3272499 * 2 ^ 59
def prefixEnd_3272499 : Nat := 4983230072969 + 3 ^ 40 * 3272499 * 2
def baseEnd_3272499 : Nat := 373414428523977125847235

theorem tailTrace_3272499 : CollatzResearch.WordTrace tailWord_3272499 prefixEnd_3272499 373414428523977125847235 := by
  unfold tailWord_3272499
  simp only [CollatzResearch.WordTrace]
  refine ⟨119357844171302496178140551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79571896114201664118760367 119357844171302496178140551)
  ·
    refine ⟨179036766256953744267210827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119357844171302496178140551 179036766256953744267210827)
    ·
      refine ⟨268555149385430616400816241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179036766256953744267210827 268555149385430616400816241)
      ·
        refine ⟨201416362039072962300612181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 268555149385430616400816241 201416362039072962300612181)
        ·
          refine ⟨2360347992645386276960299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 201416362039072962300612181 2360347992645386276960299)
          ·
            refine ⟨3540521988968079415440449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2360347992645386276960299 3540521988968079415440449)
            ·
              refine ⟨2655391491726059561580337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3540521988968079415440449 2655391491726059561580337)
              ·
                refine ⟨1991543618794544671185253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2655391491726059561580337 1991543618794544671185253)
                ·
                  refine ⟨373414428523977125847235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1991543618794544671185253 373414428523977125847235)
                  ·
                    rfl

theorem cell22_3272499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 8, 1, 2, 2, 4].length) (baseStart_3272499 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272499 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272499 prefixEnd_3272499 := by exact prefixLift 3272499
  have htrace : WordTrace (prefixWord ++ tailWord_3272499) baseStart_3272499 baseEnd_3272499 := by
    simpa [prefixWord, tailWord_3272499, baseEnd_3272499] using wordTrace_append hprefix tailTrace_3272499
  have hstable : (prefixWord ++ tailWord_3272499).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272499).length < 2 ^ (prefixWord ++ tailWord_3272499).sum := by decide
  have hdescent : baseEnd_3272499 < baseStart_3272499 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272510 : List Nat := [4, 2, 1, 2, 2, 3, 1, 7]
def baseStart_3272510 : Nat := 118140960795 + 3272510 * 2 ^ 59
def prefixEnd_3272510 : Nat := 4983230072969 + 3 ^ 40 * 3272510 * 2
def baseEnd_3272510 : Nat := 124471894566303446168519

theorem tailTrace_3272510 : CollatzResearch.WordTrace tailWord_3272510 prefixEnd_3272510 124471894566303446168519 := by
  unfold tailWord_3272510
  simp only [CollatzResearch.WordTrace]
  refine ⟨14919780671782830632098873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79572163582841763371193989 14919780671782830632098873)
  ·
    refine ⟨11189835503837122974074155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14919780671782830632098873 11189835503837122974074155)
    ·
      refine ⟨16784753255755684461111233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11189835503837122974074155 16784753255755684461111233)
      ·
        refine ⟨12588564941816763345833425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16784753255755684461111233 12588564941816763345833425)
        ·
          refine ⟨9441423706362572509375069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12588564941816763345833425 9441423706362572509375069)
          ·
            refine ⟨3540533889885964691015651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9441423706362572509375069 3540533889885964691015651)
            ·
              refine ⟨5310800834828947036523477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3540533889885964691015651 5310800834828947036523477)
              ·
                refine ⟨124471894566303446168519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5310800834828947036523477 124471894566303446168519)
                ·
                  rfl

theorem cell22_3272510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 7].length) (baseStart_3272510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272510 prefixEnd_3272510 := by exact prefixLift 3272510
  have htrace : WordTrace (prefixWord ++ tailWord_3272510) baseStart_3272510 baseEnd_3272510 := by
    simpa [prefixWord, tailWord_3272510, baseEnd_3272510] using wordTrace_append hprefix tailTrace_3272510
  have hstable : (prefixWord ++ tailWord_3272510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272510).length < 2 ^ (prefixWord ++ tailWord_3272510).sum := by decide
  have hdescent : baseEnd_3272510 < baseStart_3272510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272585 : List Nat := [1, 2, 1, 1, 5, 1, 4, 2, 1, 4]
def baseStart_3272585 : Nat := 118140960795 + 3272585 * 2 ^ 59
def prefixEnd_3272585 : Nat := 4983230072969 + 3 ^ 40 * 3272585 * 2
def baseEnd_3272585 : Nat := 1120272725129455819891441

theorem tailTrace_3272585 : CollatzResearch.WordTrace tailWord_3272585 prefixEnd_3272585 1120272725129455819891441 := by
  unfold tailWord_3272585
  simp only [CollatzResearch.WordTrace]
  refine ⟨119360980848990932865771209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79573987232660621910514139 119360980848990932865771209)
  ·
    refine ⟨89520735636743199649328407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119360980848990932865771209 89520735636743199649328407)
    ·
      refine ⟨134281103455114799473992611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89520735636743199649328407 134281103455114799473992611)
      ·
        refine ⟨201421655182672199210988917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134281103455114799473992611 201421655182672199210988917)
        ·
          refine ⟨18883280173375518676030211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 201421655182672199210988917 18883280173375518676030211)
          ·
            refine ⟨28324920260063278014045317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18883280173375518676030211 28324920260063278014045317)
            ·
              refine ⟨5310922548761864627633497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28324920260063278014045317 5310922548761864627633497)
              ·
                refine ⟨3983191911571398470725123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5310922548761864627633497 3983191911571398470725123)
                ·
                  refine ⟨5974787867357097706087685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3983191911571398470725123 5974787867357097706087685)
                  ·
                    refine ⟨1120272725129455819891441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5974787867357097706087685 1120272725129455819891441)
                    ·
                      rfl

theorem cell22_3272585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 4, 2, 1, 4].length) (baseStart_3272585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272585 prefixEnd_3272585 := by exact prefixLift 3272585
  have htrace : WordTrace (prefixWord ++ tailWord_3272585) baseStart_3272585 baseEnd_3272585 := by
    simpa [prefixWord, tailWord_3272585, baseEnd_3272585] using wordTrace_append hprefix tailTrace_3272585
  have hstable : (prefixWord ++ tailWord_3272585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272585).length < 2 ^ (prefixWord ++ tailWord_3272585).sum := by decide
  have hdescent : baseEnd_3272585 < baseStart_3272585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272636 : List Nat := [2, 2, 2, 5, 2, 1, 1, 2, 1, 4]
def baseStart_3272636 : Nat := 118140960795 + 3272636 * 2 ^ 59
def prefixEnd_3272636 : Nat := 4983230072969 + 3 ^ 40 * 3272636 * 2
def baseEnd_3272636 : Nat := 1120290183471708686866285

theorem tailTrace_3272636 : CollatzResearch.WordTrace tailWord_3272636 prefixEnd_3272636 1120290183471708686866285 := by
  unfold tailWord_3272636
  simp only [CollatzResearch.WordTrace]
  refine ⟨59681420485903084287938881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79575227314537445717251841 59681420485903084287938881)
  ·
    refine ⟨44761065364427313215954161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 59681420485903084287938881 44761065364427313215954161)
    ·
      refine ⟨33570799023320484911965621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44761065364427313215954161 33570799023320484911965621)
      ·
        refine ⟨3147262408436295460496777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33570799023320484911965621 3147262408436295460496777)
        ·
          refine ⟨2360446806327221595372583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3147262408436295460496777 2360446806327221595372583)
          ·
            refine ⟨3540670209490832393058875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2360446806327221595372583 3540670209490832393058875)
            ·
              refine ⟨5311005314236248589588313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3540670209490832393058875 5311005314236248589588313)
              ·
                refine ⟨3983253985677186442191235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5311005314236248589588313 3983253985677186442191235)
                ·
                  refine ⟨5974880978515779663286853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3983253985677186442191235 5974880978515779663286853)
                  ·
                    refine ⟨1120290183471708686866285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5974880978515779663286853 1120290183471708686866285)
                    ·
                      rfl

theorem cell22_3272636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 2, 1, 1, 2, 1, 4].length) (baseStart_3272636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272636 prefixEnd_3272636 := by exact prefixLift 3272636
  have htrace : WordTrace (prefixWord ++ tailWord_3272636) baseStart_3272636 baseEnd_3272636 := by
    simpa [prefixWord, tailWord_3272636, baseEnd_3272636] using wordTrace_append hprefix tailTrace_3272636
  have hstable : (prefixWord ++ tailWord_3272636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272636).length < 2 ^ (prefixWord ++ tailWord_3272636).sum := by decide
  have hdescent : baseEnd_3272636 < baseStart_3272636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272662 : List Nat := [5, 2, 1, 1, 4, 9]
def baseStart_3272662 : Nat := 118140960795 + 3272662 * 2 ^ 59
def prefixEnd_3272662 : Nat := 4983230072969 + 3 ^ 40 * 3272662 * 2
def baseEnd_3272662 : Nat := 13830852886457447971805

theorem tailTrace_3272662 : CollatzResearch.WordTrace tailWord_3272662 prefixEnd_3272662 13830852886457447971805 := by
  unfold tailWord_3272662
  simp only [CollatzResearch.WordTrace]
  refine ⟨7460236829356998438520265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79575859513141316677549493 7460236829356998438520265)
  ·
    refine ⟨5595177622017748828890199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7460236829356998438520265 5595177622017748828890199)
    ·
      refine ⟨8392766433026623243335299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5595177622017748828890199 8392766433026623243335299)
      ·
        refine ⟨12589149649539934865002949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8392766433026623243335299 12589149649539934865002949)
        ·
          refine ⟨2360465559288737787188053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12589149649539934865002949 2360465559288737787188053)
          ·
            refine ⟨13830852886457447971805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2360465559288737787188053 13830852886457447971805)
            ·
              rfl

theorem cell22_3272662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 4, 9].length) (baseStart_3272662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272662 prefixEnd_3272662 := by exact prefixLift 3272662
  have htrace : WordTrace (prefixWord ++ tailWord_3272662) baseStart_3272662 baseEnd_3272662 := by
    simpa [prefixWord, tailWord_3272662, baseEnd_3272662] using wordTrace_append hprefix tailTrace_3272662
  have hstable : (prefixWord ++ tailWord_3272662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272662).length < 2 ^ (prefixWord ++ tailWord_3272662).sum := by decide
  have hdescent : baseEnd_3272662 < baseStart_3272662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272673 : List Nat := [1, 2, 3, 1, 2, 1, 2, 3, 7]
def baseStart_3272673 : Nat := 118140960795 + 3272673 * 2 ^ 59
def prefixEnd_3272673 : Nat := 4983230072969 + 3 ^ 40 * 3272673 * 2
def baseEnd_3272673 : Nat := 373434283109284307897057

theorem tailTrace_3272673 : CollatzResearch.WordTrace tailWord_3272673 prefixEnd_3272673 373434283109284307897057 := by
  unfold tailWord_3272673
  simp only [CollatzResearch.WordTrace]
  refine ⟨119364190472672123894974673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79576126981781415929983115 119364190472672123894974673)
  ·
    refine ⟨89523142854504092921231005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119364190472672123894974673 89523142854504092921231005)
    ·
      refine ⟨33571178570439034845461627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 89523142854504092921231005 33571178570439034845461627)
      ·
        refine ⟨50356767855658552268192441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33571178570439034845461627 50356767855658552268192441)
        ·
          refine ⟨37767575891743914201144331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50356767855658552268192441 37767575891743914201144331)
          ·
            refine ⟨56651363837615871301716497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 37767575891743914201144331 56651363837615871301716497)
            ·
              refine ⟨42488522878211903476287373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 56651363837615871301716497 42488522878211903476287373)
              ·
                refine ⟨15933196079329463803607765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42488522878211903476287373 15933196079329463803607765)
                ·
                  refine ⟨373434283109284307897057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15933196079329463803607765 373434283109284307897057)
                  ·
                    rfl

theorem cell22_3272673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 3, 7].length) (baseStart_3272673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272673 prefixEnd_3272673 := by exact prefixLift 3272673
  have htrace : WordTrace (prefixWord ++ tailWord_3272673) baseStart_3272673 baseEnd_3272673 := by
    simpa [prefixWord, tailWord_3272673, baseEnd_3272673] using wordTrace_append hprefix tailTrace_3272673
  have hstable : (prefixWord ++ tailWord_3272673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272673).length < 2 ^ (prefixWord ++ tailWord_3272673).sum := by decide
  have hdescent : baseEnd_3272673 < baseStart_3272673 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272688 : List Nat := [2, 1, 1, 1, 3, 2, 3, 1, 1, 7]
def baseStart_3272688 : Nat := 118140960795 + 3272688 * 2 ^ 59
def prefixEnd_3272688 : Nat := 4983230072969 + 3 ^ 40 * 3272688 * 2
def baseEnd_3272688 : Nat := 1120307984134397884566125

theorem tailTrace_3272688 : CollatzResearch.WordTrace tailWord_3272688 prefixEnd_3272688 1120307984134397884566125 := by
  unfold tailWord_3272688
  simp only [CollatzResearch.WordTrace]
  refine ⟨59682368783808890728385359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79576491711745187637847145 59682368783808890728385359)
  ·
    refine ⟨89523553175713336092578039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59682368783808890728385359 89523553175713336092578039)
    ·
      refine ⟨134285329763570004138867059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89523553175713336092578039 134285329763570004138867059)
      ·
        refine ⟨201427994645355006208300589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134285329763570004138867059 201427994645355006208300589)
        ·
          refine ⟨75535497992008127328112721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 201427994645355006208300589 75535497992008127328112721)
          ·
            refine ⟨56651623494006095496084541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75535497992008127328112721 56651623494006095496084541)
            ·
              refine ⟨21244358810252285811031703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 56651623494006095496084541 21244358810252285811031703)
              ·
                refine ⟨31866538215378428716547555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21244358810252285811031703 31866538215378428716547555)
                ·
                  refine ⟨47799807323067643074821333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 31866538215378428716547555 47799807323067643074821333)
                  ·
                    refine ⟨1120307984134397884566125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47799807323067643074821333 1120307984134397884566125)
                    ·
                      rfl

theorem cell22_3272688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 1, 1, 7].length) (baseStart_3272688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272688 prefixEnd_3272688 := by exact prefixLift 3272688
  have htrace : WordTrace (prefixWord ++ tailWord_3272688) baseStart_3272688 baseEnd_3272688 := by
    simpa [prefixWord, tailWord_3272688, baseEnd_3272688] using wordTrace_append hprefix tailTrace_3272688
  have hstable : (prefixWord ++ tailWord_3272688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272688).length < 2 ^ (prefixWord ++ tailWord_3272688).sum := by decide
  have hdescent : baseEnd_3272688 < baseStart_3272688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272694 : List Nat := [5, 1, 1, 1, 4, 1, 1, 2, 3, 3]
def baseStart_3272694 : Nat := 118140960795 + 3272694 * 2 ^ 59
def prefixEnd_3272694 : Nat := 4983230072969 + 3 ^ 40 * 3272694 * 2
def baseEnd_3272694 : Nat := 1120310038057015868916107

theorem tailTrace_3272694 : CollatzResearch.WordTrace tailWord_3272694 prefixEnd_3272694 1120310038057015868916107 := by
  unfold tailWord_3272694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7460309775349752780093071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 79576637603730696320992757 7460309775349752780093071)
  ·
    refine ⟨11190464663024629170139607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7460309775349752780093071 11190464663024629170139607)
    ·
      refine ⟨16785696994536943755209411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11190464663024629170139607 16785696994536943755209411)
      ·
        refine ⟨25178545491805415632814117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16785696994536943755209411 25178545491805415632814117)
        ·
          refine ⟨4720977279713515431152647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25178545491805415632814117 4720977279713515431152647)
          ·
            refine ⟨7081465919570273146728971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4720977279713515431152647 7081465919570273146728971)
            ·
              refine ⟨10622198879355409720093457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7081465919570273146728971 10622198879355409720093457)
              ·
                refine ⟨7966649159516557290070093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10622198879355409720093457 7966649159516557290070093)
                ·
                  refine ⟨2987493434818708983776285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7966649159516557290070093 2987493434818708983776285)
                  ·
                    refine ⟨1120310038057015868916107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2987493434818708983776285 1120310038057015868916107)
                    ·
                      rfl

theorem cell22_3272694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 3, 3].length) (baseStart_3272694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272694 prefixEnd_3272694 := by exact prefixLift 3272694
  have htrace : WordTrace (prefixWord ++ tailWord_3272694) baseStart_3272694 baseEnd_3272694 := by
    simpa [prefixWord, tailWord_3272694, baseEnd_3272694] using wordTrace_append hprefix tailTrace_3272694
  have hstable : (prefixWord ++ tailWord_3272694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272694).length < 2 ^ (prefixWord ++ tailWord_3272694).sum := by decide
  have hdescent : baseEnd_3272694 < baseStart_3272694 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272720 : List Nat := [2, 1, 1, 1, 1, 1, 1, 9, 1, 4]
def baseStart_3272720 : Nat := 118140960795 + 3272720 * 2 ^ 59
def prefixEnd_3272720 : Nat := 4983230072969 + 3 ^ 40 * 3272720 * 2
def baseEnd_3272720 : Nat := 1120318938388360467766027

theorem tailTrace_3272720 : CollatzResearch.WordTrace tailWord_3272720 prefixEnd_3272720 1120318938388360467766027 := by
  unfold tailWord_3272720
  simp only [CollatzResearch.WordTrace]
  refine ⟨59682952351750925460967807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79577269802334567281290409 59682952351750925460967807)
  ·
    refine ⟨89524428527626388191451711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59682952351750925460967807 89524428527626388191451711)
    ·
      refine ⟨134286642791439582287177567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 89524428527626388191451711 134286642791439582287177567)
      ·
        refine ⟨201429964187159373430766351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 134286642791439582287177567 201429964187159373430766351)
        ·
          refine ⟨302144946280739060146149527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 201429964187159373430766351 302144946280739060146149527)
          ·
            refine ⟨453217419421108590219224291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302144946280739060146149527 453217419421108590219224291)
            ·
              refine ⟨679826129131662885328836437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453217419421108590219224291 679826129131662885328836437)
              ·
                refine ⟨3983356225380837218723651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 679826129131662885328836437 3983356225380837218723651)
                ·
                  refine ⟨5975034338071255828085477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3983356225380837218723651 5975034338071255828085477)
                  ·
                    refine ⟨1120318938388360467766027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5975034338071255828085477 1120318938388360467766027)
                    ·
                      rfl

theorem cell22_3272720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 9, 1, 4].length) (baseStart_3272720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272720 prefixEnd_3272720 := by exact prefixLift 3272720
  have htrace : WordTrace (prefixWord ++ tailWord_3272720) baseStart_3272720 baseEnd_3272720 := by
    simpa [prefixWord, tailWord_3272720, baseEnd_3272720] using wordTrace_append hprefix tailTrace_3272720
  have hstable : (prefixWord ++ tailWord_3272720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272720).length < 2 ^ (prefixWord ++ tailWord_3272720).sum := by decide
  have hdescent : baseEnd_3272720 < baseStart_3272720 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272724 : List Nat := [2, 4, 3, 2, 1, 1, 1, 1, 7]
def baseStart_3272724 : Nat := 118140960795 + 3272724 * 2 ^ 59
def prefixEnd_3272724 : Nat := 4983230072969 + 3 ^ 40 * 3272724 * 2
def baseEnd_3272724 : Nat := 373440102556701930222005

theorem tailTrace_3272724 : CollatzResearch.WordTrace tailWord_3272724 prefixEnd_3272724 373440102556701930222005 := by
  unfold tailWord_3272724
  simp only [CollatzResearch.WordTrace]
  refine ⟨59683025297743679802540613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79577367063658239736720817 59683025297743679802540613)
  ·
    refine ⟨11190567243326939962976365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 59683025297743679802540613 11190567243326939962976365)
    ·
      refine ⟨4196462716247602486116137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11190567243326939962976365 4196462716247602486116137)
      ·
        refine ⟨3147347037185701864587103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4196462716247602486116137 3147347037185701864587103)
        ·
          refine ⟨4721020555778552796880655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3147347037185701864587103 4721020555778552796880655)
          ·
            refine ⟨7081530833667829195320983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4721020555778552796880655 7081530833667829195320983)
            ·
              refine ⟨10622296250501743792981475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7081530833667829195320983 10622296250501743792981475)
              ·
                refine ⟨15933444375752615689472213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10622296250501743792981475 15933444375752615689472213)
                ·
                  refine ⟨373440102556701930222005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15933444375752615689472213 373440102556701930222005)
                  ·
                    rfl

theorem cell22_3272724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_3272724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272724 prefixEnd_3272724 := by exact prefixLift 3272724
  have htrace : WordTrace (prefixWord ++ tailWord_3272724) baseStart_3272724 baseEnd_3272724 := by
    simpa [prefixWord, tailWord_3272724, baseEnd_3272724] using wordTrace_append hprefix tailTrace_3272724
  have hstable : (prefixWord ++ tailWord_3272724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272724).length < 2 ^ (prefixWord ++ tailWord_3272724).sum := by decide
  have hdescent : baseEnd_3272724 < baseStart_3272724 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272735 : List Nat := [1, 1, 2, 4, 1, 2, 4, 1, 6]
def baseStart_3272735 : Nat := 118140960795 + 3272735 * 2 ^ 59
def prefixEnd_3272735 : Nat := 4983230072969 + 3 ^ 40 * 3272735 * 2
def baseEnd_3272735 : Nat := 373441357731635142880327

theorem tailTrace_3272735 : CollatzResearch.WordTrace tailWord_3272735 prefixEnd_3272735 373441357731635142880327 := by
  unfold tailWord_3272735
  simp only [CollatzResearch.WordTrace]
  refine ⟨119366451798447508483731659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79577634532298338989154439 119366451798447508483731659)
  ·
    refine ⟨179049677697671262725597489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119366451798447508483731659 179049677697671262725597489)
    ·
      refine ⟨134287258273253447044198117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 179049677697671262725597489 134287258273253447044198117)
      ·
        refine ⟨25178860926235021320787147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 134287258273253447044198117 25178860926235021320787147)
        ·
          refine ⟨37768291389352531981180721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25178860926235021320787147 37768291389352531981180721)
          ·
            refine ⟨28326218542014398985885541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37768291389352531981180721 28326218542014398985885541)
            ·
              refine ⟨5311165976627699809853539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28326218542014398985885541 5311165976627699809853539)
              ·
                refine ⟨7966748964941549714780309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5311165976627699809853539 7966748964941549714780309)
                ·
                  refine ⟨373441357731635142880327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7966748964941549714780309 373441357731635142880327)
                  ·
                    rfl

theorem cell22_3272735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 4, 1, 6].length) (baseStart_3272735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272735 prefixEnd_3272735 := by exact prefixLift 3272735
  have htrace : WordTrace (prefixWord ++ tailWord_3272735) baseStart_3272735 baseEnd_3272735 := by
    simpa [prefixWord, tailWord_3272735, baseEnd_3272735] using wordTrace_append hprefix tailTrace_3272735
  have hstable : (prefixWord ++ tailWord_3272735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272735).length < 2 ^ (prefixWord ++ tailWord_3272735).sum := by decide
  have hdescent : baseEnd_3272735 < baseStart_3272735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272763 : List Nat := [1, 1, 1, 1, 1, 2, 1, 14]
def baseStart_3272763 : Nat := 118140960795 + 3272763 * 2 ^ 59
def prefixEnd_3272763 : Nat := 4983230072969 + 3 ^ 40 * 3272763 * 2
def baseEnd_3272763 : Nat := 124481517574124743215655

theorem tailTrace_3272763 : CollatzResearch.WordTrace tailWord_3272763 prefixEnd_3272763 124481517574124743215655 := by
  unfold tailWord_3272763
  simp only [CollatzResearch.WordTrace]
  refine ⟨119367473042346069265750943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79578315361564046177167295 119367473042346069265750943)
  ·
    refine ⟨179051209563519103898626415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 119367473042346069265750943 179051209563519103898626415)
    ·
      refine ⟨268576814345278655847939623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 179051209563519103898626415 268576814345278655847939623)
      ·
        refine ⟨402865221517917983771909435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268576814345278655847939623 402865221517917983771909435)
        ·
          refine ⟨604297832276876975657864153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402865221517917983771909435 604297832276876975657864153)
          ·
            refine ⟨453223374207657731743398115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 604297832276876975657864153 453223374207657731743398115)
            ·
              refine ⟨679835061311486597615097173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453223374207657731743398115 679835061311486597615097173)
              ·
                refine ⟨124481517574124743215655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 679835061311486597615097173 124481517574124743215655)
                ·
                  rfl

theorem cell22_3272763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 14].length) (baseStart_3272763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272763 prefixEnd_3272763 := by exact prefixLift 3272763
  have htrace : WordTrace (prefixWord ++ tailWord_3272763) baseStart_3272763 baseEnd_3272763 := by
    simpa [prefixWord, tailWord_3272763, baseEnd_3272763] using wordTrace_append hprefix tailTrace_3272763
  have hstable : (prefixWord ++ tailWord_3272763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272763).length < 2 ^ (prefixWord ++ tailWord_3272763).sum := by decide
  have hdescent : baseEnd_3272763 < baseStart_3272763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272765 : List Nat := [1, 4, 1, 3, 1, 1, 1, 3, 1, 6]
def baseStart_3272765 : Nat := 118140960795 + 3272765 * 2 ^ 59
def prefixEnd_3272765 : Nat := 4983230072969 + 3 ^ 40 * 3272765 * 2
def baseEnd_3272765 : Nat := 1120334342807995350390889

theorem tailTrace_3272765 : CollatzResearch.WordTrace tailWord_3272765 prefixEnd_3272765 1120334342807995350390889 := by
  unfold tailWord_3272765
  simp only [CollatzResearch.WordTrace]
  refine ⟨119367545988338823607323749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79578363992225882404882499 119367545988338823607323749)
  ·
    refine ⟨22381414872813529426373203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119367545988338823607323749 22381414872813529426373203)
    ·
      refine ⟨33572122309220294139559805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22381414872813529426373203 33572122309220294139559805)
      ·
        refine ⟨12589545865957610302334927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33572122309220294139559805 12589545865957610302334927)
        ·
          refine ⟨18884318798936415453502391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12589545865957610302334927 18884318798936415453502391)
          ·
            refine ⟨28326478198404623180253587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18884318798936415453502391 28326478198404623180253587)
            ·
              refine ⟨42489717297606934770380381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28326478198404623180253587 42489717297606934770380381)
              ·
                refine ⟨15933643986602600538892643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42489717297606934770380381 15933643986602600538892643)
                ·
                  refine ⟨23900465979903900808338965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15933643986602600538892643 23900465979903900808338965)
                  ·
                    refine ⟨1120334342807995350390889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23900465979903900808338965 1120334342807995350390889)
                    ·
                      rfl

theorem cell22_3272765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_3272765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272765 prefixEnd_3272765 := by exact prefixLift 3272765
  have htrace : WordTrace (prefixWord ++ tailWord_3272765) baseStart_3272765 baseEnd_3272765 := by
    simpa [prefixWord, tailWord_3272765, baseEnd_3272765] using wordTrace_append hprefix tailTrace_3272765
  have hstable : (prefixWord ++ tailWord_3272765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272765).length < 2 ^ (prefixWord ++ tailWord_3272765).sum := by decide
  have hdescent : baseEnd_3272765 < baseStart_3272765 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272769 : List Nat := [1, 2, 5, 1, 2, 1, 3, 3, 4]
def baseStart_3272769 : Nat := 118140960795 + 3272769 * 2 ^ 59
def prefixEnd_3272769 : Nat := 4983230072969 + 3 ^ 40 * 3272769 * 2
def baseEnd_3272769 : Nat := 373445237363246891096959

theorem tailTrace_3272769 : CollatzResearch.WordTrace tailWord_3272769 prefixEnd_3272769 373445237363246891096959 := by
  unfold tailWord_3272769
  simp only [CollatzResearch.WordTrace]
  refine ⟨119367691880324332290469361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79578461253549554860312907 119367691880324332290469361)
  ·
    refine ⟨89525768910243249217852021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 119367691880324332290469361 89525768910243249217852021)
    ·
      refine ⟨8393040835335304614173627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 89525768910243249217852021 8393040835335304614173627)
      ·
        refine ⟨12589561253002956921260441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8393040835335304614173627 12589561253002956921260441)
        ·
          refine ⟨9442170939752217690945331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12589561253002956921260441 9442170939752217690945331)
          ·
            refine ⟨14163256409628326536417997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9442170939752217690945331 14163256409628326536417997)
            ·
              refine ⟨5311221153610622451156749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14163256409628326536417997 5311221153610622451156749)
              ·
                refine ⟨1991707932603983419183781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5311221153610622451156749 1991707932603983419183781)
                ·
                  refine ⟨373445237363246891096959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1991707932603983419183781 373445237363246891096959)
                  ·
                    rfl

theorem cell22_3272769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 3, 3, 4].length) (baseStart_3272769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272769 prefixEnd_3272769 := by exact prefixLift 3272769
  have htrace : WordTrace (prefixWord ++ tailWord_3272769) baseStart_3272769 baseEnd_3272769 := by
    simpa [prefixWord, tailWord_3272769, baseEnd_3272769] using wordTrace_append hprefix tailTrace_3272769
  have hstable : (prefixWord ++ tailWord_3272769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272769).length < 2 ^ (prefixWord ++ tailWord_3272769).sum := by decide
  have hdescent : baseEnd_3272769 < baseStart_3272769 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272782 : List Nat := [4, 1, 1, 1, 1, 5, 1, 2, 2, 4]
def baseStart_3272782 : Nat := 118140960795 + 3272782 * 2 ^ 59
def prefixEnd_3272782 : Nat := 4983230072969 + 3 ^ 40 * 3272782 * 2
def baseEnd_3272782 : Nat := 1120340162255412972715837

theorem tailTrace_3272782 : CollatzResearch.WordTrace tailWord_3272782 prefixEnd_3272782 1120340162255412972715837 := by
  unfold tailWord_3272782
  simp only [CollatzResearch.WordTrace]
  refine ⟨14921020753659654438836575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 79578777352851490340461733 14921020753659654438836575)
  ·
    refine ⟨22381531130489481658254863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14921020753659654438836575 22381531130489481658254863)
    ·
      refine ⟨33572296695734222487382295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22381531130489481658254863 33572296695734222487382295)
      ·
        refine ⟨50358445043601333731073443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33572296695734222487382295 50358445043601333731073443)
        ·
          refine ⟨75537667565402000596610165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50358445043601333731073443 75537667565402000596610165)
          ·
            refine ⟨7081656334256437555932203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 75537667565402000596610165 7081656334256437555932203)
            ·
              refine ⟨10622484501384656333898305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7081656334256437555932203 10622484501384656333898305)
              ·
                refine ⟨7966863376038492250423729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10622484501384656333898305 7966863376038492250423729)
                ·
                  refine ⟨5975147532028869187817797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7966863376038492250423729 5975147532028869187817797)
                  ·
                    refine ⟨1120340162255412972715837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5975147532028869187817797 1120340162255412972715837)
                    ·
                      rfl

theorem cell22_3272782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 2, 2, 4].length) (baseStart_3272782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272782 prefixEnd_3272782 := by exact prefixLift 3272782
  have htrace : WordTrace (prefixWord ++ tailWord_3272782) baseStart_3272782 baseEnd_3272782 := by
    simpa [prefixWord, tailWord_3272782, baseEnd_3272782] using wordTrace_append hprefix tailTrace_3272782
  have hstable : (prefixWord ++ tailWord_3272782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272782).length < 2 ^ (prefixWord ++ tailWord_3272782).sum := by decide
  have hdescent : baseEnd_3272782 < baseStart_3272782 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272786 : List Nat := [3, 2, 2, 1, 4, 1, 3, 2, 4]
def baseStart_3272786 : Nat := 118140960795 + 3272786 * 2 ^ 59
def prefixEnd_3272786 : Nat := 4983230072969 + 3 ^ 40 * 3272786 * 2
def baseEnd_3272786 : Nat := 373447177179052765205275

theorem tailTrace_3272786 : CollatzResearch.WordTrace tailWord_3272786 prefixEnd_3272786 373447177179052765205275 := by
  unfold tailWord_3272786
  simp only [CollatzResearch.WordTrace]
  refine ⟨29842077980315686048459553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79578874614175162795892141 29842077980315686048459553)
  ·
    refine ⟨22381558485236764536344665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 29842077980315686048459553 22381558485236764536344665)
    ·
      refine ⟨16786168863927573402258499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22381558485236764536344665 16786168863927573402258499)
      ·
        refine ⟨25179253295891360103387749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16786168863927573402258499 25179253295891360103387749)
        ·
          refine ⟨4721109992979630019385203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25179253295891360103387749 4721109992979630019385203)
          ·
            refine ⟨7081664989469445029077805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4721109992979630019385203 7081664989469445029077805)
            ·
              refine ⟨2655624371051041885904177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7081664989469445029077805 2655624371051041885904177)
              ·
                refine ⟨1991718278288281414428133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2655624371051041885904177 1991718278288281414428133)
                ·
                  refine ⟨373447177179052765205275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1991718278288281414428133 373447177179052765205275)
                  ·
                    rfl

theorem cell22_3272786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_3272786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272786 prefixEnd_3272786 := by exact prefixLift 3272786
  have htrace : WordTrace (prefixWord ++ tailWord_3272786) baseStart_3272786 baseEnd_3272786 := by
    simpa [prefixWord, tailWord_3272786, baseEnd_3272786] using wordTrace_append hprefix tailTrace_3272786
  have hstable : (prefixWord ++ tailWord_3272786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272786).length < 2 ^ (prefixWord ++ tailWord_3272786).sum := by decide
  have hdescent : baseEnd_3272786 < baseStart_3272786 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272797 : List Nat := [1, 4, 4, 1, 1, 1, 1, 9]
def baseStart_3272797 : Nat := 118140960795 + 3272797 * 2 ^ 59
def prefixEnd_3272797 : Nat := 4983230072969 + 3 ^ 40 * 3272797 * 2
def baseEnd_3272797 : Nat := 124482810784661992621199

theorem tailTrace_3272797 : CollatzResearch.WordTrace tailWord_3272797 prefixEnd_3272797 124482810784661992621199 := by
  unfold tailWord_3272797
  simp only [CollatzResearch.WordTrace]
  refine ⟨119368713124222893072488645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79579142082815262048325763 119368713124222893072488645)
  ·
    refine ⟨22381633710791792451091621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 119368713124222893072488645 22381633710791792451091621)
    ·
      refine ⟨4196556320773461084579679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22381633710791792451091621 4196556320773461084579679)
      ·
        refine ⟨6294834481160191626869519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4196556320773461084579679 6294834481160191626869519)
        ·
          refine ⟨9442251721740287440304279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6294834481160191626869519 9442251721740287440304279)
          ·
            refine ⟨14163377582610431160456419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9442251721740287440304279 14163377582610431160456419)
            ·
              refine ⟨21245066373915646740684629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14163377582610431160456419 21245066373915646740684629)
              ·
                refine ⟨124482810784661992621199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21245066373915646740684629 124482810784661992621199)
                ·
                  rfl

theorem cell22_3272797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 9].length) (baseStart_3272797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272797 prefixEnd_3272797 := by exact prefixLift 3272797
  have htrace : WordTrace (prefixWord ++ tailWord_3272797) baseStart_3272797 baseEnd_3272797 := by
    simpa [prefixWord, tailWord_3272797, baseEnd_3272797] using wordTrace_append hprefix tailTrace_3272797
  have hstable : (prefixWord ++ tailWord_3272797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272797).length < 2 ^ (prefixWord ++ tailWord_3272797).sum := by decide
  have hdescent : baseEnd_3272797 < baseStart_3272797 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3272842 : List Nat := [3, 1, 2, 3, 1, 2, 1, 4, 5]
def baseStart_3272842 : Nat := 118140960795 + 3272842 * 2 ^ 59
def prefixEnd_3272842 : Nat := 4983230072969 + 3 ^ 40 * 3272842 * 2
def baseEnd_3272842 : Nat := 373453567160530938738551

theorem tailTrace_3272842 : CollatzResearch.WordTrace tailWord_3272842 prefixEnd_3272842 373453567160530938738551 := by
  unfold tailWord_3272842
  simp only [CollatzResearch.WordTrace]
  refine ⟨29842588602264966439469195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79580236272706577171917853 29842588602264966439469195)
  ·
    refine ⟨44763882903397449659203793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29842588602264966439469195 44763882903397449659203793)
    ·
      refine ⟨33572912177548087244402845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 44763882903397449659203793 33572912177548087244402845)
      ·
        refine ⟨12589842066580532716651067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33572912177548087244402845 12589842066580532716651067)
        ·
          refine ⟨18884763099870799074976601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12589842066580532716651067 18884763099870799074976601)
          ·
            refine ⟨14163572324903099306232451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18884763099870799074976601 14163572324903099306232451)
            ·
              refine ⟨21245358487354648959348677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14163572324903099306232451 21245358487354648959348677)
              ·
                refine ⟨3983504716378996679877877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21245358487354648959348677 3983504716378996679877877)
                ·
                  refine ⟨373453567160530938738551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3983504716378996679877877 373453567160530938738551)
                  ·
                    rfl

theorem cell22_3272842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 4, 5].length) (baseStart_3272842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3272842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3272842 prefixEnd_3272842 := by exact prefixLift 3272842
  have htrace : WordTrace (prefixWord ++ tailWord_3272842) baseStart_3272842 baseEnd_3272842 := by
    simpa [prefixWord, tailWord_3272842, baseEnd_3272842] using wordTrace_append hprefix tailTrace_3272842
  have hstable : (prefixWord ++ tailWord_3272842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3272842).length < 2 ^ (prefixWord ++ tailWord_3272842).sum := by decide
  have hdescent : baseEnd_3272842 < baseStart_3272842 := by decide
  rcases family_descends (prefixWord ++ tailWord_3272842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273058 : List Nat := [3, 3, 2, 1, 1, 2, 4, 1, 1, 4]
def baseStart_3273058 : Nat := 118140960795 + 3273058 * 2 ^ 59
def prefixEnd_3273058 : Nat := 4983230072969 + 3 ^ 40 * 3273058 * 2
def baseEnd_3273058 : Nat := 1120434642695840252814991

theorem tailTrace_3273058 : CollatzResearch.WordTrace tailWord_3273058 prefixEnd_3273058 1120434642695840252814991 := by
  unfold tailWord_3273058
  simp only [CollatzResearch.WordTrace]
  refine ⟨29844558144069333661934957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79585488384184889765159885 29844558144069333661934957)
  ·
    refine ⟨11191709304026000123225609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 29844558144069333661934957 11191709304026000123225609)
    ·
      refine ⟨8393781978019500092419207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11191709304026000123225609 8393781978019500092419207)
      ·
        refine ⟨12590672967029250138628811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8393781978019500092419207 12590672967029250138628811)
        ·
          refine ⟨18886009450543875207943217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12590672967029250138628811 18886009450543875207943217)
          ·
            refine ⟨14164507087907906405957413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18886009450543875207943217 14164507087907906405957413)
            ·
              refine ⟨2655845078982732451117015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14164507087907906405957413 2655845078982732451117015)
              ·
                refine ⟨3983767618474098676675523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2655845078982732451117015 3983767618474098676675523)
                ·
                  refine ⟨5975651427711148015013285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3983767618474098676675523 5975651427711148015013285)
                  ·
                    refine ⟨1120434642695840252814991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5975651427711148015013285 1120434642695840252814991)
                    ·
                      rfl

theorem cell22_3273058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 4, 1, 1, 4].length) (baseStart_3273058 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273058 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273058 prefixEnd_3273058 := by exact prefixLift 3273058
  have htrace : WordTrace (prefixWord ++ tailWord_3273058) baseStart_3273058 baseEnd_3273058 := by
    simpa [prefixWord, tailWord_3273058, baseEnd_3273058] using wordTrace_append hprefix tailTrace_3273058
  have hstable : (prefixWord ++ tailWord_3273058).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273058).length < 2 ^ (prefixWord ++ tailWord_3273058).sum := by decide
  have hdescent : baseEnd_3273058 < baseStart_3273058 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273069 : List Nat := [1, 5, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_3273069 : Nat := 118140960795 + 3273069 * 2 ^ 59
def prefixEnd_3273069 : Nat := 4983230072969 + 3 ^ 40 * 3273069 * 2
def baseEnd_3273069 : Nat := 1120438408220639890789957

theorem tailTrace_3273069 : CollatzResearch.WordTrace tailWord_3273069 prefixEnd_3273069 1120438408220639890789957 := by
  unfold tailWord_3273069
  simp only [CollatzResearch.WordTrace]
  refine ⟨119378633779237483526390261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79585755852824989017593507 119378633779237483526390261)
  ·
    refine ⟨11191746916803514080599087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 119378633779237483526390261 11191746916803514080599087)
    ·
      refine ⟨16787620375205271120898631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11191746916803514080599087 16787620375205271120898631)
      ·
        refine ⟨25181430562807906681347947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16787620375205271120898631 25181430562807906681347947)
        ·
          refine ⟨37772145844211860022021921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25181430562807906681347947 37772145844211860022021921)
          ·
            refine ⟨28329109383158895016516441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 37772145844211860022021921 28329109383158895016516441)
            ·
              refine ⟨21246832037369171262387331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28329109383158895016516441 21246832037369171262387331)
              ·
                refine ⟨31870248056053756893580997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21246832037369171262387331 31870248056053756893580997)
                ·
                  refine ⟨5975671510510079417546437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 31870248056053756893580997 5975671510510079417546437)
                  ·
                    refine ⟨1120438408220639890789957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5975671510510079417546437 1120438408220639890789957)
                    ·
                      rfl

theorem cell22_3273069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_3273069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273069 prefixEnd_3273069 := by exact prefixLift 3273069
  have htrace : WordTrace (prefixWord ++ tailWord_3273069) baseStart_3273069 baseEnd_3273069 := by
    simpa [prefixWord, tailWord_3273069, baseEnd_3273069] using wordTrace_append hprefix tailTrace_3273069
  have hstable : (prefixWord ++ tailWord_3273069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273069).length < 2 ^ (prefixWord ++ tailWord_3273069).sum := by decide
  have hdescent : baseEnd_3273069 < baseStart_3273069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273082 : List Nat := [3, 1, 1, 1, 1, 1, 2, 1, 4, 7]
def baseStart_3273082 : Nat := 118140960795 + 3273082 * 2 ^ 59
def prefixEnd_3273082 : Nat := 4983230072969 + 3 ^ 40 * 3273082 * 2
def baseEnd_3273082 : Nat := 1120442858386312190214917

theorem tailTrace_3273082 : CollatzResearch.WordTrace tailWord_3273082 prefixEnd_3273082 1120442858386312190214917 := by
  unfold tailWord_3273082
  simp only [CollatzResearch.WordTrace]
  refine ⟨29844776982047596686653375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 79586071952126924497742333 29844776982047596686653375)
  ·
    refine ⟨44767165473071395029980063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 29844776982047596686653375 44767165473071395029980063)
    ·
      refine ⟨67150748209607092544970095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44767165473071395029980063 67150748209607092544970095)
      ·
        refine ⟨100726122314410638817455143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67150748209607092544970095 100726122314410638817455143)
        ·
          refine ⟨151089183471615958226182715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 100726122314410638817455143 151089183471615958226182715)
          ·
            refine ⟨226633775207423937339274073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 151089183471615958226182715 226633775207423937339274073)
            ·
              refine ⟨169975331405567953004455555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 226633775207423937339274073 169975331405567953004455555)
              ·
                refine ⟨254962997108351929506683333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 169975331405567953004455555 254962997108351929506683333)
                ·
                  refine ⟨47805561957815986782503125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 254962997108351929506683333 47805561957815986782503125)
                  ·
                    refine ⟨1120442858386312190214917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 47805561957815986782503125 1120442858386312190214917)
                    ·
                      rfl

theorem cell22_3273082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_3273082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273082 prefixEnd_3273082 := by exact prefixLift 3273082
  have htrace : WordTrace (prefixWord ++ tailWord_3273082) baseStart_3273082 baseEnd_3273082 := by
    simpa [prefixWord, tailWord_3273082, baseEnd_3273082] using wordTrace_append hprefix tailTrace_3273082
  have hstable : (prefixWord ++ tailWord_3273082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273082).length < 2 ^ (prefixWord ++ tailWord_3273082).sum := by decide
  have hdescent : baseEnd_3273082 < baseStart_3273082 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273221 : List Nat := [1, 3, 1, 1, 2, 2, 5, 1, 2, 4]
def baseStart_3273221 : Nat := 118140960795 + 3273221 * 2 ^ 59
def prefixEnd_3273221 : Nat := 4983230072969 + 3 ^ 40 * 3273221 * 2
def baseEnd_3273221 : Nat := 1120490440926962160989491

theorem tailTrace_3273221 : CollatzResearch.WordTrace tailWord_3273221 prefixEnd_3273221 1120490440926962160989491 := by
  unfold tailWord_3273221
  simp only [CollatzResearch.WordTrace]
  refine ⟨119384177674686813485923517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 79589451783124542323949011 119384177674686813485923517)
  ·
    refine ⟨44769066628007555057221319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 119384177674686813485923517 44769066628007555057221319)
    ·
      refine ⟨67153599942011332585831979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 44769066628007555057221319 67153599942011332585831979)
      ·
        refine ⟨100730399913016998878747969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 67153599942011332585831979 100730399913016998878747969)
        ·
          refine ⟨75547799934762749159060977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 100730399913016998878747969 75547799934762749159060977)
          ·
            refine ⟨56660849951072061869295733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 75547799934762749159060977 56660849951072061869295733)
            ·
              refine ⟨5311954682913005800246475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 56660849951072061869295733 5311954682913005800246475)
              ·
                refine ⟨7967932024369508700369713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5311954682913005800246475 7967932024369508700369713)
                ·
                  refine ⟨5975949018277131525277285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7967932024369508700369713 5975949018277131525277285)
                  ·
                    refine ⟨1120490440926962160989491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5975949018277131525277285 1120490440926962160989491)
                    ·
                      rfl

theorem cell22_3273221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 5, 1, 2, 4].length) (baseStart_3273221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273221 prefixEnd_3273221 := by exact prefixLift 3273221
  have htrace : WordTrace (prefixWord ++ tailWord_3273221) baseStart_3273221 baseEnd_3273221 := by
    simpa [prefixWord, tailWord_3273221, baseEnd_3273221] using wordTrace_append hprefix tailTrace_3273221
  have hstable : (prefixWord ++ tailWord_3273221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273221).length < 2 ^ (prefixWord ++ tailWord_3273221).sum := by decide
  have hdescent : baseEnd_3273221 < baseStart_3273221 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3273240 : List Nat := [2, 1, 2, 3, 3, 3, 1, 2, 2, 3]
def baseStart_3273240 : Nat := 118140960795 + 3273240 * 2 ^ 59
def prefixEnd_3273240 : Nat := 4983230072969 + 3 ^ 40 * 3273240 * 2
def baseEnd_3273240 : Nat := 1120496945015252444764433

theorem tailTrace_3273240 : CollatzResearch.WordTrace tailWord_3273240 prefixEnd_3273240 1120496945015252444764433 := by
  unfold tailWord_3273240
  simp only [CollatzResearch.WordTrace]
  refine ⟨59692435330808989865432587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 79589913774411986487243449 59692435330808989865432587)
  ·
    refine ⟨89538652996213484798148881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 59692435330808989865432587 89538652996213484798148881)
    ·
      refine ⟨67153989747160113598611661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 89538652996213484798148881 67153989747160113598611661)
      ·
        refine ⟨25182746155185042599479373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 67153989747160113598611661 25182746155185042599479373)
        ·
          refine ⟨9443529808194390974804765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25182746155185042599479373 9443529808194390974804765)
          ·
            refine ⟨3541323678072896615551787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9443529808194390974804765 3541323678072896615551787)
            ·
              refine ⟨5311985517109344923327681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3541323678072896615551787 5311985517109344923327681)
              ·
                refine ⟨3983989137832008692495761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5311985517109344923327681 3983989137832008692495761)
                ·
                  refine ⟨2987991853374006519371821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3983989137832008692495761 2987991853374006519371821)
                  ·
                    refine ⟨1120496945015252444764433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2987991853374006519371821 1120496945015252444764433)
                    ·
                      rfl

theorem cell22_3273240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 2, 3].length) (baseStart_3273240 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3273240 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3273240 prefixEnd_3273240 := by exact prefixLift 3273240
  have htrace : WordTrace (prefixWord ++ tailWord_3273240) baseStart_3273240 baseEnd_3273240 := by
    simpa [prefixWord, tailWord_3273240, baseEnd_3273240] using wordTrace_append hprefix tailTrace_3273240
  have hstable : (prefixWord ++ tailWord_3273240).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3273240).length < 2 ^ (prefixWord ++ tailWord_3273240).sum := by decide
  have hdescent : baseEnd_3273240 < baseStart_3273240 := by decide
  rcases family_descends (prefixWord ++ tailWord_3273240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
