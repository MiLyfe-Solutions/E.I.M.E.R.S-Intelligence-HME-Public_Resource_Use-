import V185TrunkScan23Chunk0227

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1348915 : List Nat := [1, 1, 1, 2, 5, 2, 2, 4, 1, 4]
def baseStart_1348915 : Nat := 118140960795 + 1348915 * 2 ^ 59
def prefixEnd_1348915 : Nat := 4983230072969 + 3 ^ 40 * 1348915 * 2
def baseEnd_1348915 : Nat := 230880585686565032519653

theorem tailTrace_1348915 : CollatzResearch.WordTrace tailWord_1348915 prefixEnd_1348915 230880585686565032519653 := by
  unfold tailWord_1348915
  simp only [CollatzResearch.WordTrace]
  refine ⟨49198971908118806185912199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32799314605412537457274799 49198971908118806185912199)
  ·
    refine ⟨73798457862178209278868299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49198971908118806185912199 73798457862178209278868299)
    ·
      refine ⟨110697686793267313918302449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73798457862178209278868299 110697686793267313918302449)
      ·
        refine ⟨83023265094950485438726837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110697686793267313918302449 83023265094950485438726837)
        ·
          refine ⟨7783431102651608009880641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83023265094950485438726837 7783431102651608009880641)
          ·
            refine ⟨5837573326988706007410481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7783431102651608009880641 5837573326988706007410481)
            ·
              refine ⟨4378179995241529505557861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5837573326988706007410481 4378179995241529505557861)
              ·
                refine ⟨820908749107786782292099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4378179995241529505557861 820908749107786782292099)
                ·
                  refine ⟨1231363123661680173438149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 820908749107786782292099 1231363123661680173438149)
                  ·
                    refine ⟨230880585686565032519653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1231363123661680173438149 230880585686565032519653)
                    ·
                      rfl

theorem cell23_1348915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 2, 4, 1, 4].length) (baseStart_1348915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348915 prefixEnd_1348915 := by exact prefixLift 1348915
  have htrace : WordTrace (prefixWord ++ tailWord_1348915) baseStart_1348915 baseEnd_1348915 := by
    simpa [prefixWord, tailWord_1348915, baseEnd_1348915] using wordTrace_append hprefix tailTrace_1348915
  have hstable : (prefixWord ++ tailWord_1348915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348915).length < 2 ^ (prefixWord ++ tailWord_1348915).sum := by decide
  have hdescent : baseEnd_1348915 < baseStart_1348915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348928 : List Nat := [2, 1, 1, 2, 2, 1, 7, 1, 6]
def baseStart_1348928 : Nat := 118140960795 + 1348928 * 2 ^ 59
def prefixEnd_1348928 : Nat := 4983230072969 + 3 ^ 40 * 1348928 * 2
def baseEnd_1348928 : Nat := 76960936923133727410711

theorem tailTrace_1348928 : CollatzResearch.WordTrace tailWord_1348928 prefixEnd_1348928 76960936923133727410711 := by
  unfold tailWord_1348928
  simp only [CollatzResearch.WordTrace]
  refine ⟨24599723028535854703067719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32799630704714472937423625 24599723028535854703067719)
  ·
    refine ⟨36899584542803782054601579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24599723028535854703067719 36899584542803782054601579)
    ·
      refine ⟨55349376814205673081902369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36899584542803782054601579 55349376814205673081902369)
      ·
        refine ⟨41512032610654254811426777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55349376814205673081902369 41512032610654254811426777)
        ·
          refine ⟨31134024457990691108570083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41512032610654254811426777 31134024457990691108570083)
          ·
            refine ⟨46701036686986036662855125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31134024457990691108570083 46701036686986036662855125)
            ·
              refine ⟨1094555547351235234285667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 46701036686986036662855125 1094555547351235234285667)
              ·
                refine ⟨1641833321026852851428501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1094555547351235234285667 1641833321026852851428501)
                ·
                  refine ⟨76960936923133727410711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1641833321026852851428501 76960936923133727410711)
                  ·
                    rfl

theorem cell23_1348928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 6].length) (baseStart_1348928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348928 prefixEnd_1348928 := by exact prefixLift 1348928
  have htrace : WordTrace (prefixWord ++ tailWord_1348928) baseStart_1348928 baseEnd_1348928 := by
    simpa [prefixWord, tailWord_1348928, baseEnd_1348928] using wordTrace_append hprefix tailTrace_1348928
  have hstable : (prefixWord ++ tailWord_1348928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348928).length < 2 ^ (prefixWord ++ tailWord_1348928).sum := by decide
  have hdescent : baseEnd_1348928 < baseStart_1348928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348965 : List Nat := [1, 3, 1, 3, 1, 2, 3, 2, 2, 3, 2]
def baseStart_1348965 : Nat := 118140960795 + 1348965 * 2 ^ 59
def prefixEnd_1348965 : Nat := 4983230072969 + 3 ^ 40 * 1348965 * 2
def baseEnd_1348965 : Nat := 692667431092419901933729

theorem tailTrace_1348965 : CollatzResearch.WordTrace tailWord_1348965 prefixEnd_1348965 692667431092419901933729 := by
  unfold tailWord_1348965
  simp only [CollatzResearch.WordTrace]
  refine ⟨49200795557937664725232349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32800530371958443150154899 49200795557937664725232349)
  ·
    refine ⟨18450298334226624271962131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49200795557937664725232349 18450298334226624271962131)
    ·
      refine ⟨27675447501339936407943197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18450298334226624271962131 27675447501339936407943197)
      ·
        refine ⟨10378292813002476152978699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27675447501339936407943197 10378292813002476152978699)
        ·
          refine ⟨15567439219503714229468049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10378292813002476152978699 15567439219503714229468049)
          ·
            refine ⟨11675579414627785672101037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15567439219503714229468049 11675579414627785672101037)
            ·
              refine ⟨4378342280485419627037889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11675579414627785672101037 4378342280485419627037889)
              ·
                refine ⟨3283756710364064720278417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4378342280485419627037889 3283756710364064720278417)
                ·
                  refine ⟨2462817532773048540208813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3283756710364064720278417 2462817532773048540208813)
                  ·
                    refine ⟨923556574789893202578305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2462817532773048540208813 923556574789893202578305)
                    ·
                      refine ⟨692667431092419901933729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 923556574789893202578305 692667431092419901933729)
                      ·
                        rfl

theorem cell23_1348965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 3, 2].length) (baseStart_1348965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348965 prefixEnd_1348965 := by exact prefixLift 1348965
  have htrace : WordTrace (prefixWord ++ tailWord_1348965) baseStart_1348965 baseEnd_1348965 := by
    simpa [prefixWord, tailWord_1348965, baseEnd_1348965] using wordTrace_append hprefix tailTrace_1348965
  have hstable : (prefixWord ++ tailWord_1348965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348965).length < 2 ^ (prefixWord ++ tailWord_1348965).sum := by decide
  have hdescent : baseEnd_1348965 < baseStart_1348965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348972 : List Nat := [2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 3]
def baseStart_1348972 : Nat := 118140960795 + 1348972 * 2 ^ 59
def prefixEnd_1348972 : Nat := 4983230072969 + 3 ^ 40 * 1348972 * 2
def baseEnd_1348972 : Nat := 692671025457001374546197

theorem tailTrace_1348972 : CollatzResearch.WordTrace tailWord_1348972 prefixEnd_1348972 692671025457001374546197 := by
  unfold tailWord_1348972
  simp only [CollatzResearch.WordTrace]
  refine ⟨24600525434456152460368585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32800700579274869947158113 24600525434456152460368585)
  ·
    refine ⟨18450394075842114345276439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24600525434456152460368585 18450394075842114345276439)
    ·
      refine ⟨27675591113763171517914659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18450394075842114345276439 27675591113763171517914659)
      ·
        refine ⟨41513386670644757276871989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27675591113763171517914659 41513386670644757276871989)
        ·
          refine ⟨3891880000372945994706749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41513386670644757276871989 3891880000372945994706749)
          ·
            refine ⟨1459455000139854748015031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3891880000372945994706749 1459455000139854748015031)
            ·
              refine ⟨2189182500209782122022547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1459455000139854748015031 2189182500209782122022547)
              ·
                refine ⟨3283773750314673183033821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2189182500209782122022547 3283773750314673183033821)
                ·
                  refine ⟨1231415156368002443637683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3283773750314673183033821 1231415156368002443637683)
                  ·
                    refine ⟨1847122734552003665456525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1231415156368002443637683 1847122734552003665456525)
                    ·
                      refine ⟨692671025457001374546197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1847122734552003665456525 692671025457001374546197)
                      ·
                        rfl

theorem cell23_1348972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 1, 3].length) (baseStart_1348972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348972 prefixEnd_1348972 := by exact prefixLift 1348972
  have htrace : WordTrace (prefixWord ++ tailWord_1348972) baseStart_1348972 baseEnd_1348972 := by
    simpa [prefixWord, tailWord_1348972, baseEnd_1348972] using wordTrace_append hprefix tailTrace_1348972
  have hstable : (prefixWord ++ tailWord_1348972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348972).length < 2 ^ (prefixWord ++ tailWord_1348972).sum := by decide
  have hdescent : baseEnd_1348972 < baseStart_1348972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348978 : List Nat := [3, 2, 1, 2, 1, 2, 2, 2, 3, 1, 4]
def baseStart_1348978 : Nat := 118140960795 + 1348978 * 2 ^ 59
def prefixEnd_1348978 : Nat := 4983230072969 + 3 ^ 40 * 1348978 * 2
def baseEnd_1348978 : Nat := 692674106340928351071169

theorem tailTrace_1348978 : CollatzResearch.WordTrace tailWord_1348978 prefixEnd_1348978 692674106340928351071169 := by
  unfold tailWord_1348978
  simp only [CollatzResearch.WordTrace]
  refine ⟨12300317426722641986363897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32800846471260378630303725 12300317426722641986363897)
  ·
    refine ⟨9225238070041981489772923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12300317426722641986363897 9225238070041981489772923)
    ·
      refine ⟨13837857105062972234659385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9225238070041981489772923 13837857105062972234659385)
      ·
        refine ⟨10378392828797229175994539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13837857105062972234659385 10378392828797229175994539)
        ·
          refine ⟨15567589243195843763991809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10378392828797229175994539 15567589243195843763991809)
          ·
            refine ⟨11675691932396882822993857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15567589243195843763991809 11675691932396882822993857)
            ·
              refine ⟨8756768949297662117245393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11675691932396882822993857 8756768949297662117245393)
              ·
                refine ⟨6567576711973246587934045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8756768949297662117245393 6567576711973246587934045)
                ·
                  refine ⟨2462841266989967470475267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6567576711973246587934045 2462841266989967470475267)
                  ·
                    refine ⟨3694261900484951205712901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2462841266989967470475267 3694261900484951205712901)
                    ·
                      refine ⟨692674106340928351071169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3694261900484951205712901 692674106340928351071169)
                      ·
                        rfl

theorem cell23_1348978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_1348978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348978 prefixEnd_1348978 := by exact prefixLift 1348978
  have htrace : WordTrace (prefixWord ++ tailWord_1348978) baseStart_1348978 baseEnd_1348978 := by
    simpa [prefixWord, tailWord_1348978, baseEnd_1348978] using wordTrace_append hprefix tailTrace_1348978
  have hstable : (prefixWord ++ tailWord_1348978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348978).length < 2 ^ (prefixWord ++ tailWord_1348978).sum := by decide
  have hdescent : baseEnd_1348978 < baseStart_1348978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1348995 : List Nat := [1, 1, 1, 3, 5, 1, 3, 2, 1, 1, 4]
def baseStart_1348995 : Nat := 118140960795 + 1348995 * 2 ^ 59
def prefixEnd_1348995 : Nat := 4983230072969 + 3 ^ 40 * 1348995 * 2
def baseEnd_1348995 : Nat := 692682835512054784558591

theorem tailTrace_1348995 : CollatzResearch.WordTrace tailWord_1348995 prefixEnd_1348995 692682835512054784558591 := by
  unfold tailWord_1348995
  simp only [CollatzResearch.WordTrace]
  refine ⟨49201889747828979848824439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32801259831885986565882959 49201889747828979848824439)
  ·
    refine ⟨73802834621743469773236659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49201889747828979848824439 73802834621743469773236659)
    ·
      refine ⟨110704251932615204659854989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73802834621743469773236659 110704251932615204659854989)
      ·
        refine ⟨41514094474730701747445621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110704251932615204659854989 41514094474730701747445621)
        ·
          refine ⟨3891946357006003288823027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41514094474730701747445621 3891946357006003288823027)
          ·
            refine ⟨5837919535509004933234541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3891946357006003288823027 5837919535509004933234541)
            ·
              refine ⟨2189219825815876849962953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5837919535509004933234541 2189219825815876849962953)
              ·
                refine ⟨1641914869361907637472215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2189219825815876849962953 1641914869361907637472215)
                ·
                  refine ⟨2462872304042861456208323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1641914869361907637472215 2462872304042861456208323)
                  ·
                    refine ⟨3694308456064292184312485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2462872304042861456208323 3694308456064292184312485)
                    ·
                      refine ⟨692682835512054784558591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3694308456064292184312485 692682835512054784558591)
                      ·
                        rfl

theorem cell23_1348995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2, 1, 1, 4].length) (baseStart_1348995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1348995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1348995 prefixEnd_1348995 := by exact prefixLift 1348995
  have htrace : WordTrace (prefixWord ++ tailWord_1348995) baseStart_1348995 baseEnd_1348995 := by
    simpa [prefixWord, tailWord_1348995, baseEnd_1348995] using wordTrace_append hprefix tailTrace_1348995
  have hstable : (prefixWord ++ tailWord_1348995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1348995).length < 2 ^ (prefixWord ++ tailWord_1348995).sum := by decide
  have hdescent : baseEnd_1348995 < baseStart_1348995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1348995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349028 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 5, 3, 3]
def baseStart_1349028 : Nat := 118140960795 + 1349028 * 2 ^ 59
def prefixEnd_1349028 : Nat := 4983230072969 + 3 ^ 40 * 1349028 * 2
def baseEnd_1349028 : Nat := 692699780373653155445939

theorem tailTrace_1349028 : CollatzResearch.WordTrace tailWord_1349028 prefixEnd_1349028 692699780373653155445939 := by
  unfold tailWord_1349028
  simp only [CollatzResearch.WordTrace]
  refine ⟨24601546678354713242387869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32802062237806284323183825 24601546678354713242387869)
  ·
    refine ⟨9225580004383017465895451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24601546678354713242387869 9225580004383017465895451)
    ·
      refine ⟨13838370006574526198843177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9225580004383017465895451 13838370006574526198843177)
      ·
        refine ⟨10378777504930894649132383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13838370006574526198843177 10378777504930894649132383)
        ·
          refine ⟨15568166257396341973698575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10378777504930894649132383 15568166257396341973698575)
          ·
            refine ⟨23352249386094512960547863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15568166257396341973698575 23352249386094512960547863)
            ·
              refine ⟨35028374079141769440821795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23352249386094512960547863 35028374079141769440821795)
              ·
                refine ⟨52542561118712654161232693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35028374079141769440821795 52542561118712654161232693)
                ·
                  refine ⟨4925865104879311327615565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 52542561118712654161232693 4925865104879311327615565)
                  ·
                    refine ⟨1847199414329741747855837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4925865104879311327615565 1847199414329741747855837)
                    ·
                      refine ⟨692699780373653155445939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1847199414329741747855837 692699780373653155445939)
                      ·
                        rfl

theorem cell23_1349028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 5, 3, 3].length) (baseStart_1349028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349028 prefixEnd_1349028 := by exact prefixLift 1349028
  have htrace : WordTrace (prefixWord ++ tailWord_1349028) baseStart_1349028 baseEnd_1349028 := by
    simpa [prefixWord, tailWord_1349028, baseEnd_1349028] using wordTrace_append hprefix tailTrace_1349028
  have hstable : (prefixWord ++ tailWord_1349028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349028).length < 2 ^ (prefixWord ++ tailWord_1349028).sum := by decide
  have hdescent : baseEnd_1349028 < baseStart_1349028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349045 : List Nat := [1, 3, 3, 2, 2, 1, 1, 3, 1, 3, 3]
def baseStart_1349045 : Nat := 118140960795 + 1349045 * 2 ^ 59
def prefixEnd_1349045 : Nat := 4983230072969 + 3 ^ 40 * 1349045 * 2
def baseEnd_1349045 : Nat := 692708509544779588933361

theorem tailTrace_1349045 : CollatzResearch.WordTrace tailWord_1349045 prefixEnd_1349045 692708509544779588933361 := by
  unfold tailWord_1349045
  simp only [CollatzResearch.WordTrace]
  refine ⟨49203713397647838388144589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32802475598431892258763059 49203713397647838388144589)
  ·
    refine ⟨18451392524117939395554221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49203713397647838388144589 18451392524117939395554221)
    ·
      refine ⟨6919272196544227273332833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18451392524117939395554221 6919272196544227273332833)
      ·
        refine ⟨5189454147408170454999625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6919272196544227273332833 5189454147408170454999625)
        ·
          refine ⟨3892090610556127841249719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5189454147408170454999625 3892090610556127841249719)
          ·
            refine ⟨5838135915834191761874579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3892090610556127841249719 5838135915834191761874579)
            ·
              refine ⟨8757203873751287642811869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5838135915834191761874579 8757203873751287642811869)
              ·
                refine ⟨3283951452656732866054451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8757203873751287642811869 3283951452656732866054451)
                ·
                  refine ⟨4925927178985099299081677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3283951452656732866054451 4925927178985099299081677)
                  ·
                    refine ⟨1847222692119412237155629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4925927178985099299081677 1847222692119412237155629)
                    ·
                      refine ⟨692708509544779588933361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1847222692119412237155629 692708509544779588933361)
                      ·
                        rfl

theorem cell23_1349045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_1349045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349045 prefixEnd_1349045 := by exact prefixLift 1349045
  have htrace : WordTrace (prefixWord ++ tailWord_1349045) baseStart_1349045 baseEnd_1349045 := by
    simpa [prefixWord, tailWord_1349045, baseEnd_1349045] using wordTrace_append hprefix tailTrace_1349045
  have hstable : (prefixWord ++ tailWord_1349045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349045).length < 2 ^ (prefixWord ++ tailWord_1349045).sum := by decide
  have hdescent : baseEnd_1349045 < baseStart_1349045 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349088 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 3]
def baseStart_1349088 : Nat := 118140960795 + 1349088 * 2 ^ 59
def prefixEnd_1349088 : Nat := 4983230072969 + 3 ^ 40 * 1349088 * 2
def baseEnd_1349088 : Nat := 692730589212922920695663

theorem tailTrace_1349088 : CollatzResearch.WordTrace tailWord_1349088 prefixEnd_1349088 692730589212922920695663 := by
  unfold tailWord_1349088
  simp only [CollatzResearch.WordTrace]
  refine ⟨24602640868246028365979959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32803521157661371154639945 24602640868246028365979959)
  ·
    refine ⟨36903961302369042548969939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24602640868246028365979959 36903961302369042548969939)
    ·
      refine ⟨55355941953553563823454909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36903961302369042548969939 55355941953553563823454909)
      ·
        refine ⟨20758478232582586433795591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55355941953553563823454909 20758478232582586433795591)
        ·
          refine ⟨31137717348873879650693387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20758478232582586433795591 31137717348873879650693387)
          ·
            refine ⟨46706576023310819476040081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31137717348873879650693387 46706576023310819476040081)
            ·
              refine ⟨35029932017483114607030061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46706576023310819476040081 35029932017483114607030061)
              ·
                refine ⟨13136224506556167977636273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35029932017483114607030061 13136224506556167977636273)
                ·
                  refine ⟨9852168379917125983227205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13136224506556167977636273 9852168379917125983227205)
                  ·
                    refine ⟨1847281571234461121855101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9852168379917125983227205 1847281571234461121855101)
                    ·
                      refine ⟨692730589212922920695663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1847281571234461121855101 692730589212922920695663)
                      ·
                        rfl

theorem cell23_1349088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 2, 4, 3].length) (baseStart_1349088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349088 prefixEnd_1349088 := by exact prefixLift 1349088
  have htrace : WordTrace (prefixWord ++ tailWord_1349088) baseStart_1349088 baseEnd_1349088 := by
    simpa [prefixWord, tailWord_1349088, baseEnd_1349088] using wordTrace_append hprefix tailTrace_1349088
  have hstable : (prefixWord ++ tailWord_1349088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349088).length < 2 ^ (prefixWord ++ tailWord_1349088).sum := by decide
  have hdescent : baseEnd_1349088 < baseStart_1349088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349122 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 2, 1, 5]
def baseStart_1349122 : Nat := 118140960795 + 1349122 * 2 ^ 59
def prefixEnd_1349122 : Nat := 4983230072969 + 3 ^ 40 * 1349122 * 2
def baseEnd_1349122 : Nat := 692748047555175787670507

theorem tailTrace_1349122 : CollatzResearch.WordTrace tailWord_1349122 prefixEnd_1349122 692748047555175787670507 := by
  unfold tailWord_1349122
  simp only [CollatzResearch.WordTrace]
  refine ⟨12301630454592220134674405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32804347878912587025798413 12301630454592220134674405)
  ·
    refine ⟨2306555710236041275251451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12301630454592220134674405 2306555710236041275251451)
    ·
      refine ⟨3459833565354061912877177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2306555710236041275251451 3459833565354061912877177)
      ·
        refine ⟨2594875174015546434657883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3459833565354061912877177 2594875174015546434657883)
        ·
          refine ⟨3892312761023319651986825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2594875174015546434657883 3892312761023319651986825)
          ·
            refine ⟨2919234570767489738990119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3892312761023319651986825 2919234570767489738990119)
            ·
              refine ⟨4378851856151234608485179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2919234570767489738990119 4378851856151234608485179)
              ·
                refine ⟨6568277784226851912727769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4378851856151234608485179 6568277784226851912727769)
                ·
                  refine ⟨4926208338170138934545827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6568277784226851912727769 4926208338170138934545827)
                  ·
                    refine ⟨7389312507255208401818741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4926208338170138934545827 7389312507255208401818741)
                    ·
                      refine ⟨692748047555175787670507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7389312507255208401818741 692748047555175787670507)
                      ·
                        rfl

theorem cell23_1349122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 2, 1, 5].length) (baseStart_1349122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349122 prefixEnd_1349122 := by exact prefixLift 1349122
  have htrace : WordTrace (prefixWord ++ tailWord_1349122) baseStart_1349122 baseEnd_1349122 := by
    simpa [prefixWord, tailWord_1349122, baseEnd_1349122] using wordTrace_append hprefix tailTrace_1349122
  have hstable : (prefixWord ++ tailWord_1349122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349122).length < 2 ^ (prefixWord ++ tailWord_1349122).sum := by decide
  have hdescent : baseEnd_1349122 < baseStart_1349122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349175 : List Nat := [1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 4]
def baseStart_1349175 : Nat := 118140960795 + 1349175 * 2 ^ 59
def prefixEnd_1349175 : Nat := 4983230072969 + 3 ^ 40 * 1349175 * 2
def baseEnd_1349175 : Nat := 692775262029864080307763

theorem tailTrace_1349175 : CollatzResearch.WordTrace tailWord_1349175 prefixEnd_1349175 692775262029864080307763 := by
  unfold tailWord_1349175
  simp only [CollatzResearch.WordTrace]
  refine ⟨49208454887176870590376979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32805636591451247060251319 49208454887176870590376979)
  ·
    refine ⟨73812682330765305885565469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49208454887176870590376979 73812682330765305885565469)
    ·
      refine ⟨27679755874036989707087051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73812682330765305885565469 27679755874036989707087051)
      ·
        refine ⟨41519633811055484560630577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27679755874036989707087051 41519633811055484560630577)
        ·
          refine ⟨31139725358291613420472933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41519633811055484560630577 31139725358291613420472933)
          ·
            refine ⟨5838698504679677516338675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31139725358291613420472933 5838698504679677516338675)
            ·
              refine ⟨8758047757019516274508013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5838698504679677516338675 8758047757019516274508013)
              ·
                refine ⟨3284267908882318602940505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8758047757019516274508013 3284267908882318602940505)
                ·
                  refine ⟨2463200931661738952205379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3284267908882318602940505 2463200931661738952205379)
                  ·
                    refine ⟨3694801397492608428308069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2463200931661738952205379 3694801397492608428308069)
                    ·
                      refine ⟨692775262029864080307763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3694801397492608428308069 692775262029864080307763)
                      ·
                        rfl

theorem cell23_1349175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 4].length) (baseStart_1349175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349175 prefixEnd_1349175 := by exact prefixLift 1349175
  have htrace : WordTrace (prefixWord ++ tailWord_1349175) baseStart_1349175 baseEnd_1349175 := by
    simpa [prefixWord, tailWord_1349175, baseEnd_1349175] using wordTrace_append hprefix tailTrace_1349175
  have hstable : (prefixWord ++ tailWord_1349175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349175).length < 2 ^ (prefixWord ++ tailWord_1349175).sum := by decide
  have hdescent : baseEnd_1349175 < baseStart_1349175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349259 : List Nat := [1, 1, 1, 1, 4, 1, 3, 6, 1, 1, 3]
def baseStart_1349259 : Nat := 118140960795 + 1349259 * 2 ^ 59
def prefixEnd_1349259 : Nat := 4983230072969 + 3 ^ 40 * 1349259 * 2
def baseEnd_1349259 : Nat := 692818394404841751657377

theorem tailTrace_1349259 : CollatzResearch.WordTrace tailWord_1349259 prefixEnd_1349259 692818394404841751657377 := by
  unfold tailWord_1349259
  simp only [CollatzResearch.WordTrace]
  refine ⟨49211518618872552936434831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32807679079248368624289887 49211518618872552936434831)
  ·
    refine ⟨73817277928308829404652247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49211518618872552936434831 73817277928308829404652247)
    ·
      refine ⟨110725916892463244106978371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73817277928308829404652247 110725916892463244106978371)
      ·
        refine ⟨166088875338694866160467557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110725916892463244106978371 166088875338694866160467557)
        ·
          refine ⟨31141664126005287405087667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 166088875338694866160467557 31141664126005287405087667)
          ·
            refine ⟨46712496189007931107631501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31141664126005287405087667 46712496189007931107631501)
            ·
              refine ⟨17517186070877974165361813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46712496189007931107631501 17517186070877974165361813)
              ·
                refine ⟨821118097072405039001335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17517186070877974165361813 821118097072405039001335)
                ·
                  refine ⟨1231677145608607558502003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 821118097072405039001335 1231677145608607558502003)
                  ·
                    refine ⟨1847515718412911337753005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1231677145608607558502003 1847515718412911337753005)
                    ·
                      refine ⟨692818394404841751657377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1847515718412911337753005 692818394404841751657377)
                      ·
                        rfl

theorem cell23_1349259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 6, 1, 1, 3].length) (baseStart_1349259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349259 prefixEnd_1349259 := by exact prefixLift 1349259
  have htrace : WordTrace (prefixWord ++ tailWord_1349259) baseStart_1349259 baseEnd_1349259 := by
    simpa [prefixWord, tailWord_1349259, baseEnd_1349259] using wordTrace_append hprefix tailTrace_1349259
  have hstable : (prefixWord ++ tailWord_1349259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349259).length < 2 ^ (prefixWord ++ tailWord_1349259).sum := by decide
  have hdescent : baseEnd_1349259 < baseStart_1349259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349265 : List Nat := [1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 4]
def baseStart_1349265 : Nat := 118140960795 + 1349265 * 2 ^ 59
def prefixEnd_1349265 : Nat := 4983230072969 + 3 ^ 40 * 1349265 * 2
def baseEnd_1349265 : Nat := 692821475288768728182349

theorem tailTrace_1349265 : CollatzResearch.WordTrace tailWord_1349265 prefixEnd_1349265 692821475288768728182349 := by
  unfold tailWord_1349265
  simp only [CollatzResearch.WordTrace]
  refine ⟨49211737456850815961153249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32807824971233877307435499 49211737456850815961153249)
  ·
    refine ⟨36908803092638111970864937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49211737456850815961153249 36908803092638111970864937)
    ·
      refine ⟨27681602319478583978148703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36908803092638111970864937 27681602319478583978148703)
      ·
        refine ⟨41522403479217875967223055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27681602319478583978148703 41522403479217875967223055)
        ·
          refine ⟨62283605218826813950834583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41522403479217875967223055 62283605218826813950834583)
          ·
            refine ⟨93425407828240220926251875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62283605218826813950834583 93425407828240220926251875)
            ·
              refine ⟨140138111742360331389377813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93425407828240220926251875 140138111742360331389377813)
              ·
                refine ⟨6568973987923140533877085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 140138111742360331389377813 6568973987923140533877085)
                ·
                  refine ⟨2463365245471177700203907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6568973987923140533877085 2463365245471177700203907)
                  ·
                    refine ⟨3695047868206766550305861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2463365245471177700203907 3695047868206766550305861)
                    ·
                      refine ⟨692821475288768728182349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3695047868206766550305861 692821475288768728182349)
                      ·
                        rfl

theorem cell23_1349265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 4].length) (baseStart_1349265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349265 prefixEnd_1349265 := by exact prefixLift 1349265
  have htrace : WordTrace (prefixWord ++ tailWord_1349265) baseStart_1349265 baseEnd_1349265 := by
    simpa [prefixWord, tailWord_1349265, baseEnd_1349265] using wordTrace_append hprefix tailTrace_1349265
  have hstable : (prefixWord ++ tailWord_1349265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349265).length < 2 ^ (prefixWord ++ tailWord_1349265).sum := by decide
  have hdescent : baseEnd_1349265 < baseStart_1349265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349295 : List Nat := [1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 4]
def baseStart_1349295 : Nat := 118140960795 + 1349295 * 2 ^ 59
def prefixEnd_1349295 : Nat := 4983230072969 + 3 ^ 40 * 1349295 * 2
def baseEnd_1349295 : Nat := 692836879708403610807211

theorem tailTrace_1349295 : CollatzResearch.WordTrace tailWord_1349295 prefixEnd_1349295 692836879708403610807211 := by
  unfold tailWord_1349295
  simp only [CollatzResearch.WordTrace]
  refine ⟨49212831646742131084745339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32808554431161420723163559 49212831646742131084745339)
  ·
    refine ⟨73819247470113196627118009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49212831646742131084745339 73819247470113196627118009)
    ·
      refine ⟨55364435602584897470338507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73819247470113196627118009 55364435602584897470338507)
      ·
        refine ⟨83046653403877346205507761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55364435602584897470338507 83046653403877346205507761)
        ·
          refine ⟨62284990052908009654130821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83046653403877346205507761 62284990052908009654130821)
          ·
            refine ⟨11678435634920251810149529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62284990052908009654130821 11678435634920251810149529)
            ·
              refine ⟨8758826726190188857612147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11678435634920251810149529 8758826726190188857612147)
              ·
                refine ⟨13138240089285283286418221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8758826726190188857612147 13138240089285283286418221)
                ·
                  refine ⟨4926840033481981232406833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13138240089285283286418221 4926840033481981232406833)
                  ·
                    refine ⟨3695130025111485924305125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4926840033481981232406833 3695130025111485924305125)
                    ·
                      refine ⟨692836879708403610807211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3695130025111485924305125 692836879708403610807211)
                      ·
                        rfl

theorem cell23_1349295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 4].length) (baseStart_1349295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349295 prefixEnd_1349295 := by exact prefixLift 1349295
  have htrace : WordTrace (prefixWord ++ tailWord_1349295) baseStart_1349295 baseEnd_1349295 := by
    simpa [prefixWord, tailWord_1349295, baseEnd_1349295] using wordTrace_append hprefix tailTrace_1349295
  have hstable : (prefixWord ++ tailWord_1349295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349295).length < 2 ^ (prefixWord ++ tailWord_1349295).sum := by decide
  have hdescent : baseEnd_1349295 < baseStart_1349295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349322 : List Nat := [3, 1, 2, 1, 5, 1, 2, 8]
def baseStart_1349322 : Nat := 118140960795 + 1349322 * 2 ^ 59
def prefixEnd_1349322 : Nat := 4983230072969 + 3 ^ 40 * 1349322 * 2
def baseEnd_1349322 : Nat := 25661138655039815006281

theorem tailTrace_1349322 : CollatzResearch.WordTrace tailWord_1349322 prefixEnd_1349322 25661138655039815006281 := by
  unfold tailWord_1349322
  simp only [CollatzResearch.WordTrace]
  refine ⟨12303454104411078673994555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32809210945096209797318813 12303454104411078673994555)
  ·
    refine ⟨18455181156616618010991833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12303454104411078673994555 18455181156616618010991833)
    ·
      refine ⟨13841385867462463508243875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18455181156616618010991833 13841385867462463508243875)
      ·
        refine ⟨20762078801193695262365813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13841385867462463508243875 20762078801193695262365813)
        ·
          refine ⟨1946444887611908930846795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20762078801193695262365813 1946444887611908930846795)
          ·
            refine ⟨2919667331417863396270193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1946444887611908930846795 2919667331417863396270193)
            ·
              refine ⟨2189750498563397547202645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2919667331417863396270193 2189750498563397547202645)
              ·
                refine ⟨25661138655039815006281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2189750498563397547202645 25661138655039815006281)
                ·
                  rfl

theorem cell23_1349322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 8].length) (baseStart_1349322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349322 prefixEnd_1349322 := by exact prefixLift 1349322
  have htrace : WordTrace (prefixWord ++ tailWord_1349322) baseStart_1349322 baseEnd_1349322 := by
    simpa [prefixWord, tailWord_1349322, baseEnd_1349322] using wordTrace_append hprefix tailTrace_1349322
  have hstable : (prefixWord ++ tailWord_1349322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349322).length < 2 ^ (prefixWord ++ tailWord_1349322).sum := by decide
  have hdescent : baseEnd_1349322 < baseStart_1349322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349366 : List Nat := [5, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3]
def baseStart_1349366 : Nat := 118140960795 + 1349366 * 2 ^ 59
def prefixEnd_1349366 : Nat := 4983230072969 + 3 ^ 40 * 1349366 * 2
def baseEnd_1349366 : Nat := 692873336834872833019385

theorem tailTrace_1349366 : CollatzResearch.WordTrace tailWord_1349366 prefixEnd_1349366 692873336834872833019385 := by
  unfold tailWord_1349366
  simp only [CollatzResearch.WordTrace]
  refine ⟨3075963826842806888161247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32810280819656606807053301 3075963826842806888161247)
  ·
    refine ⟨4613945740264210332241871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3075963826842806888161247 4613945740264210332241871)
    ·
      refine ⟨6920918610396315498362807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4613945740264210332241871 6920918610396315498362807)
      ·
        refine ⟨10381377915594473247544211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6920918610396315498362807 10381377915594473247544211)
        ·
          refine ⟨15572066873391709871316317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10381377915594473247544211 15572066873391709871316317)
          ·
            refine ⟨5839525077521891201743619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15572066873391709871316317 5839525077521891201743619)
            ·
              refine ⟨8759287616282836802615429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5839525077521891201743619 8759287616282836802615429)
              ·
                refine ⟨1642366428053031900490393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8759287616282836802615429 1642366428053031900490393)
                ·
                  refine ⟨1231774821039773925367795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1642366428053031900490393 1231774821039773925367795)
                  ·
                    refine ⟨1847662231559660888051693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1231774821039773925367795 1847662231559660888051693)
                    ·
                      refine ⟨692873336834872833019385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1847662231559660888051693 692873336834872833019385)
                      ·
                        rfl

theorem cell23_1349366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 4, 2, 1, 3].length) (baseStart_1349366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349366 prefixEnd_1349366 := by exact prefixLift 1349366
  have htrace : WordTrace (prefixWord ++ tailWord_1349366) baseStart_1349366 baseEnd_1349366 := by
    simpa [prefixWord, tailWord_1349366, baseEnd_1349366] using wordTrace_append hprefix tailTrace_1349366
  have hstable : (prefixWord ++ tailWord_1349366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349366).length < 2 ^ (prefixWord ++ tailWord_1349366).sum := by decide
  have hdescent : baseEnd_1349366 < baseStart_1349366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349375 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 5]
def baseStart_1349375 : Nat := 118140960795 + 1349375 * 2 ^ 59
def prefixEnd_1349375 : Nat := 4983230072969 + 3 ^ 40 * 1349375 * 2
def baseEnd_1349375 : Nat := 692877958160763297806843

theorem tailTrace_1349375 : CollatzResearch.WordTrace tailWord_1349375 prefixEnd_1349375 692877958160763297806843 := by
  unfold tailWord_1349375
  simp only [CollatzResearch.WordTrace]
  refine ⟨49215749486452304747657579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32810499657634869831771719 49215749486452304747657579)
  ·
    refine ⟨73823624229678457121486369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49215749486452304747657579 73823624229678457121486369)
    ·
      refine ⟨55367718172258842841114777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73823624229678457121486369 55367718172258842841114777)
      ·
        refine ⟨41525788629194132130836083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55367718172258842841114777 41525788629194132130836083)
        ·
          refine ⟨62288682943791198196254125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41525788629194132130836083 62288682943791198196254125)
          ·
            refine ⟨23358256103921699323595297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62288682943791198196254125 23358256103921699323595297)
            ·
              refine ⟨17518692077941274492696473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23358256103921699323595297 17518692077941274492696473)
              ·
                refine ⟨13139019058455955869522355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17518692077941274492696473 13139019058455955869522355)
                ·
                  refine ⟨19708528587683933804283533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13139019058455955869522355 19708528587683933804283533)
                  ·
                    refine ⟨7390698220381475176606325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19708528587683933804283533 7390698220381475176606325)
                    ·
                      refine ⟨692877958160763297806843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7390698220381475176606325 692877958160763297806843)
                      ·
                        rfl

theorem cell23_1349375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 5].length) (baseStart_1349375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349375 prefixEnd_1349375 := by exact prefixLift 1349375
  have htrace : WordTrace (prefixWord ++ tailWord_1349375) baseStart_1349375 baseEnd_1349375 := by
    simpa [prefixWord, tailWord_1349375, baseEnd_1349375] using wordTrace_append hprefix tailTrace_1349375
  have hstable : (prefixWord ++ tailWord_1349375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349375).length < 2 ^ (prefixWord ++ tailWord_1349375).sum := by decide
  have hdescent : baseEnd_1349375 < baseStart_1349375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349429 : List Nat := [1, 3, 3, 1, 4, 1, 2, 1, 7]
def baseStart_1349429 : Nat := 118140960795 + 1349429 * 2 ^ 59
def prefixEnd_1349429 : Nat := 4983230072969 + 3 ^ 40 * 1349429 * 2
def baseEnd_1349429 : Nat := 76989520679567342947955

theorem tailTrace_1349429 : CollatzResearch.WordTrace tailWord_1349429 prefixEnd_1349429 76989520679567342947955 := by
  unfold tailWord_1349429
  simp only [CollatzResearch.WordTrace]
  refine ⟨49217719028256671970123341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32811812685504447980082227 49217719028256671970123341)
  ·
    refine ⟨18456644635596251988796253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49217719028256671970123341 18456644635596251988796253)
    ·
      refine ⟨6921241738348594495798595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18456644635596251988796253 6921241738348594495798595)
      ·
        refine ⟨10381862607522891743697893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6921241738348594495798595 10381862607522891743697893)
        ·
          refine ⟨1946599238910542201943355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10381862607522891743697893 1946599238910542201943355)
          ·
            refine ⟨2919898858365813302915033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1946599238910542201943355 2919898858365813302915033)
            ·
              refine ⟨2189924143774359977186275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2919898858365813302915033 2189924143774359977186275)
              ·
                refine ⟨3284886215661539965779413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2189924143774359977186275 3284886215661539965779413)
                ·
                  refine ⟨76989520679567342947955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3284886215661539965779413 76989520679567342947955)
                  ·
                    rfl

theorem cell23_1349429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 7].length) (baseStart_1349429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349429 prefixEnd_1349429 := by exact prefixLift 1349429
  have htrace : WordTrace (prefixWord ++ tailWord_1349429) baseStart_1349429 baseEnd_1349429 := by
    simpa [prefixWord, tailWord_1349429, baseEnd_1349429] using wordTrace_append hprefix tailTrace_1349429
  have hstable : (prefixWord ++ tailWord_1349429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349429).length < 2 ^ (prefixWord ++ tailWord_1349429).sum := by decide
  have hdescent : baseEnd_1349429 < baseStart_1349429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349446 : List Nat := [6, 1, 1, 2, 1, 1, 2, 2, 7]
def baseStart_1349446 : Nat := 118140960795 + 1349446 * 2 ^ 59
def prefixEnd_1349446 : Nat := 4983230072969 + 3 ^ 40 * 1349446 * 2
def baseEnd_1349446 : Nat := 76990490587470280002113

theorem tailTrace_1349446 : CollatzResearch.WordTrace tailWord_1349446 prefixEnd_1349446 76990490587470280002113 := by
  unfold tailWord_1349446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1538073095912346371046631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32812226046130055915661461 1538073095912346371046631)
  ·
    refine ⟨2307109643868519556569947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1538073095912346371046631 2307109643868519556569947)
    ·
      refine ⟨3460664465802779334854921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2307109643868519556569947 3460664465802779334854921)
      ·
        refine ⟨2595498349352084501141191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3460664465802779334854921 2595498349352084501141191)
        ·
          refine ⟨3893247524028126751711787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2595498349352084501141191 3893247524028126751711787)
          ·
            refine ⟨5839871286042190127567681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3893247524028126751711787 5839871286042190127567681)
            ·
              refine ⟨4379903464531642595675761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5839871286042190127567681 4379903464531642595675761)
              ·
                refine ⟨3284927598398731946756821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4379903464531642595675761 3284927598398731946756821)
                ·
                  refine ⟨76990490587470280002113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3284927598398731946756821 76990490587470280002113)
                  ·
                    rfl

theorem cell23_1349446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_1349446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349446 prefixEnd_1349446 := by exact prefixLift 1349446
  have htrace : WordTrace (prefixWord ++ tailWord_1349446) baseStart_1349446 baseEnd_1349446 := by
    simpa [prefixWord, tailWord_1349446, baseEnd_1349446] using wordTrace_append hprefix tailTrace_1349446
  have hstable : (prefixWord ++ tailWord_1349446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349446).length < 2 ^ (prefixWord ++ tailWord_1349446).sum := by decide
  have hdescent : baseEnd_1349446 < baseStart_1349446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349463 : List Nat := [1, 1, 3, 2, 6, 1, 1, 3, 5]
def baseStart_1349463 : Nat := 118140960795 + 1349463 * 2 ^ 59
def prefixEnd_1349463 : Nat := 4983230072969 + 3 ^ 40 * 1349463 * 2
def baseEnd_1349463 : Nat := 76991460495373217056271

theorem tailTrace_1349463 : CollatzResearch.WordTrace tailWord_1349463 prefixEnd_1349463 76991460495373217056271 := by
  unfold tailWord_1349463
  simp only [CollatzResearch.WordTrace]
  refine ⟨49218959110133495776861043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32812639406755663851240695 49218959110133495776861043)
  ·
    refine ⟨73828438665200243665291565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49218959110133495776861043 73828438665200243665291565)
    ·
      refine ⟨27685664499450091374484337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73828438665200243665291565 27685664499450091374484337)
      ·
        refine ⟨20764248374587568530863253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27685664499450091374484337 20764248374587568530863253)
        ·
          refine ⟨973324142558792274884215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20764248374587568530863253 973324142558792274884215)
          ·
            refine ⟨1459986213838188412326323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 973324142558792274884215 1459986213838188412326323)
            ·
              refine ⟨2189979320757282618489485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1459986213838188412326323 2189979320757282618489485)
              ·
                refine ⟨821242245283980981933557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2189979320757282618489485 821242245283980981933557)
                ·
                  refine ⟨76991460495373217056271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 821242245283980981933557 76991460495373217056271)
                  ·
                    rfl

theorem cell23_1349463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 3, 5].length) (baseStart_1349463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349463 prefixEnd_1349463 := by exact prefixLift 1349463
  have htrace : WordTrace (prefixWord ++ tailWord_1349463) baseStart_1349463 baseEnd_1349463 := by
    simpa [prefixWord, tailWord_1349463, baseEnd_1349463] using wordTrace_append hprefix tailTrace_1349463
  have hstable : (prefixWord ++ tailWord_1349463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349463).length < 2 ^ (prefixWord ++ tailWord_1349463).sum := by decide
  have hdescent : baseEnd_1349463 < baseStart_1349463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349479 : List Nat := [1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_1349479 : Nat := 118140960795 + 1349479 * 2 ^ 59
def prefixEnd_1349479 : Nat := 4983230072969 + 3 ^ 40 * 1349479 * 2
def baseEnd_1349479 : Nat := 692931360148830890906365

theorem tailTrace_1349479 : CollatzResearch.WordTrace tailWord_1349479 prefixEnd_1349479 692931360148830890906365 := by
  unfold tailWord_1349479
  simp only [CollatzResearch.WordTrace]
  refine ⟨49219542678075530509443491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32813028452050353672962327 49219542678075530509443491)
  ·
    refine ⟨73829314017113295764165237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49219542678075530509443491 73829314017113295764165237)
    ·
      refine ⟨6921498189104371477890491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73829314017113295764165237 6921498189104371477890491)
      ·
        refine ⟨10382247283656557216835737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6921498189104371477890491 10382247283656557216835737)
        ·
          refine ⟨7786685462742417912626803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10382247283656557216835737 7786685462742417912626803)
          ·
            refine ⟨11680028194113626868940205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7786685462742417912626803 11680028194113626868940205)
            ·
              refine ⟨4380010572792610075852577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11680028194113626868940205 4380010572792610075852577)
              ·
                refine ⟨3285007929594457556889433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4380010572792610075852577 3285007929594457556889433)
                ·
                  refine ⟨2463755947195843167667075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3285007929594457556889433 2463755947195843167667075)
                  ·
                    refine ⟨3695633920793764751500613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2463755947195843167667075 3695633920793764751500613)
                    ·
                      refine ⟨692931360148830890906365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3695633920793764751500613 692931360148830890906365)
                      ·
                        rfl

theorem cell23_1349479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_1349479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349479 prefixEnd_1349479 := by exact prefixLift 1349479
  have htrace : WordTrace (prefixWord ++ tailWord_1349479) baseStart_1349479 baseEnd_1349479 := by
    simpa [prefixWord, tailWord_1349479, baseEnd_1349479] using wordTrace_append hprefix tailTrace_1349479
  have hstable : (prefixWord ++ tailWord_1349479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349479).length < 2 ^ (prefixWord ++ tailWord_1349479).sum := by decide
  have hdescent : baseEnd_1349479 < baseStart_1349479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349539 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 3, 5, 2]
def baseStart_1349539 : Nat := 118140960795 + 1349539 * 2 ^ 59
def prefixEnd_1349539 : Nat := 4983230072969 + 3 ^ 40 * 1349539 * 2
def baseEnd_1349539 : Nat := 692962168988100656156089

theorem tailTrace_1349539 : CollatzResearch.WordTrace tailWord_1349539 prefixEnd_1349539 692962168988100656156089 := by
  unfold tailWord_1349539
  simp only [CollatzResearch.WordTrace]
  refine ⟨49221731057858160756627671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32814487371905440504418447 49221731057858160756627671)
  ·
    refine ⟨73832596586787241134941507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49221731057858160756627671 73832596586787241134941507)
    ·
      refine ⟨110748894880180861702412261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73832596586787241134941507 110748894880180861702412261)
      ·
        refine ⟨20765417790033911569202299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110748894880180861702412261 20765417790033911569202299)
        ·
          refine ⟨31148126685050867353803449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20765417790033911569202299 31148126685050867353803449)
          ·
            refine ⟨23361095013788150515352587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31148126685050867353803449 23361095013788150515352587)
            ·
              refine ⟨35041642520682225773028881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23361095013788150515352587 35041642520682225773028881)
              ·
                refine ⟨26281231890511669329771661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35041642520682225773028881 26281231890511669329771661)
                ·
                  refine ⟨9855461958941875998664373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26281231890511669329771661 9855461958941875998664373)
                  ·
                    refine ⟨923949558650800874874785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9855461958941875998664373 923949558650800874874785)
                    ·
                      refine ⟨692962168988100656156089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 923949558650800874874785 692962168988100656156089)
                      ·
                        rfl

theorem cell23_1349539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 5, 2].length) (baseStart_1349539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349539 prefixEnd_1349539 := by exact prefixLift 1349539
  have htrace : WordTrace (prefixWord ++ tailWord_1349539) baseStart_1349539 baseEnd_1349539 := by
    simpa [prefixWord, tailWord_1349539, baseEnd_1349539] using wordTrace_append hprefix tailTrace_1349539
  have hstable : (prefixWord ++ tailWord_1349539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349539).length < 2 ^ (prefixWord ++ tailWord_1349539).sum := by decide
  have hdescent : baseEnd_1349539 < baseStart_1349539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349540 : List Nat := [2, 3, 1, 2, 1, 5, 2, 2, 1, 4]
def baseStart_1349540 : Nat := 118140960795 + 1349540 * 2 ^ 59
def prefixEnd_1349540 : Nat := 4983230072969 + 3 ^ 40 * 1349540 * 2
def baseEnd_1349540 : Nat := 230987560822918384081195

theorem tailTrace_1349540 : CollatzResearch.WordTrace tailWord_1349540 prefixEnd_1349540 230987560822918384081195 := by
  unfold tailWord_1349540
  simp only [CollatzResearch.WordTrace]
  refine ⟨24610883765427268963707037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32814511687236358618276049 24610883765427268963707037)
  ·
    refine ⟨9229081412035225861390139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24610883765427268963707037 9229081412035225861390139)
    ·
      refine ⟨13843622118052838792085209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9229081412035225861390139 13843622118052838792085209)
      ·
        refine ⟨10382716588539629094063907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13843622118052838792085209 10382716588539629094063907)
        ·
          refine ⟨15574074882809443641095861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10382716588539629094063907 15574074882809443641095861)
          ·
            refine ⟨1460069520263385341352737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15574074882809443641095861 1460069520263385341352737)
            ·
              refine ⟨1095052140197539006014553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1460069520263385341352737 1095052140197539006014553)
              ·
                refine ⟨821289105148154254510915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1095052140197539006014553 821289105148154254510915)
                ·
                  refine ⟨1231933657722231381766373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 821289105148154254510915 1231933657722231381766373)
                  ·
                    refine ⟨230987560822918384081195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1231933657722231381766373 230987560822918384081195)
                    ·
                      rfl

theorem cell23_1349540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 2, 2, 1, 4].length) (baseStart_1349540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349540 prefixEnd_1349540 := by exact prefixLift 1349540
  have htrace : WordTrace (prefixWord ++ tailWord_1349540) baseStart_1349540 baseEnd_1349540 := by
    simpa [prefixWord, tailWord_1349540, baseEnd_1349540] using wordTrace_append hprefix tailTrace_1349540
  have hstable : (prefixWord ++ tailWord_1349540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349540).length < 2 ^ (prefixWord ++ tailWord_1349540).sum := by decide
  have hdescent : baseEnd_1349540 < baseStart_1349540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349579 : List Nat := [1, 1, 1, 1, 3, 4, 2, 2, 4, 4]
def baseStart_1349579 : Nat := 118140960795 + 1349579 * 2 ^ 59
def prefixEnd_1349579 : Nat := 4983230072969 + 3 ^ 40 * 1349579 * 2
def baseEnd_1349579 : Nat := 230994236071426833218635

theorem tailTrace_1349579 : CollatzResearch.WordTrace tailWord_1349579 prefixEnd_1349579 230994236071426833218635 := by
  unfold tailWord_1349579
  simp only [CollatzResearch.WordTrace]
  refine ⟨49223189977713247588083791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32815459985142165058722527 49223189977713247588083791)
  ·
    refine ⟨73834784966569871382125687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49223189977713247588083791 73834784966569871382125687)
    ·
      refine ⟨110752177449854807073188531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73834784966569871382125687 110752177449854807073188531)
      ·
        refine ⟨166128266174782210609782797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110752177449854807073188531 166128266174782210609782797)
        ·
          refine ⟨62298099815543328978668549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166128266174782210609782797 62298099815543328978668549)
          ·
            refine ⟨11680893715414374183500353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62298099815543328978668549 11680893715414374183500353)
            ·
              refine ⟨8760670286560780637625265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11680893715414374183500353 8760670286560780637625265)
              ·
                refine ⟨6570502714920585478218949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8760670286560780637625265 6570502714920585478218949)
                ·
                  refine ⟨1231969259047609777166053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6570502714920585478218949 1231969259047609777166053)
                  ·
                    refine ⟨230994236071426833218635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1231969259047609777166053 230994236071426833218635)
                    ·
                      rfl

theorem cell23_1349579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 4, 4].length) (baseStart_1349579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349579 prefixEnd_1349579 := by exact prefixLift 1349579
  have htrace : WordTrace (prefixWord ++ tailWord_1349579) baseStart_1349579 baseEnd_1349579 := by
    simpa [prefixWord, tailWord_1349579, baseEnd_1349579] using wordTrace_append hprefix tailTrace_1349579
  have hstable : (prefixWord ++ tailWord_1349579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349579).length < 2 ^ (prefixWord ++ tailWord_1349579).sum := by decide
  have hdescent : baseEnd_1349579 < baseStart_1349579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349580 : List Nat := [2, 2, 1, 4, 1, 3, 2, 3, 1, 1, 3]
def baseStart_1349580 : Nat := 118140960795 + 1349580 * 2 ^ 59
def prefixEnd_1349580 : Nat := 4983230072969 + 3 ^ 40 * 1349580 * 2
def baseEnd_1349580 : Nat := 692983221694934995743401

theorem tailTrace_1349580 : CollatzResearch.WordTrace tailWord_1349580 prefixEnd_1349580 692983221694934995743401 := by
  unfold tailWord_1349580
  simp only [CollatzResearch.WordTrace]
  refine ⟨24611613225354812379435097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32815484300473083172580129 24611613225354812379435097)
  ·
    refine ⟨18458709919016109284576323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24611613225354812379435097 18458709919016109284576323)
    ·
      refine ⟨27688064878524163926864485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18458709919016109284576323 27688064878524163926864485)
      ·
        refine ⟨5191512164723280736287091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27688064878524163926864485 5191512164723280736287091)
        ·
          refine ⟨7787268247084921104430637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5191512164723280736287091 7787268247084921104430637)
          ·
            refine ⟨2920225592656845414161489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7787268247084921104430637 2920225592656845414161489)
            ·
              refine ⟨2190169194492634060621117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2920225592656845414161489 2190169194492634060621117)
              ·
                refine ⟨821313447934737772732919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2190169194492634060621117 821313447934737772732919)
                ·
                  refine ⟨1231970171902106659099379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 821313447934737772732919 1231970171902106659099379)
                  ·
                    refine ⟨1847955257853159988649069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1231970171902106659099379 1847955257853159988649069)
                    ·
                      refine ⟨692983221694934995743401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1847955257853159988649069 692983221694934995743401)
                      ·
                        rfl

theorem cell23_1349580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 2, 3, 1, 1, 3].length) (baseStart_1349580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349580 prefixEnd_1349580 := by exact prefixLift 1349580
  have htrace : WordTrace (prefixWord ++ tailWord_1349580) baseStart_1349580 baseEnd_1349580 := by
    simpa [prefixWord, tailWord_1349580, baseEnd_1349580] using wordTrace_append hprefix tailTrace_1349580
  have hstable : (prefixWord ++ tailWord_1349580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349580).length < 2 ^ (prefixWord ++ tailWord_1349580).sum := by decide
  have hdescent : baseEnd_1349580 < baseStart_1349580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349592 : List Nat := [2, 1, 2, 2, 2, 2, 12]
def baseStart_1349592 : Nat := 118140960795 + 1349592 * 2 ^ 59
def prefixEnd_1349592 : Nat := 4983230072969 + 3 ^ 40 * 1349592 * 2
def baseEnd_1349592 : Nat := 8555424487194925293745

theorem tailTrace_1349592 : CollatzResearch.WordTrace tailWord_1349592 prefixEnd_1349592 8555424487194925293745 := by
  unfold tailWord_1349592
  simp only [CollatzResearch.WordTrace]
  refine ⟨24611832063333075404153515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32815776084444100538871353 24611832063333075404153515)
  ·
    refine ⟨36917748094999613106230273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24611832063333075404153515 36917748094999613106230273)
    ·
      refine ⟨27688311071249709829672705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36917748094999613106230273 27688311071249709829672705)
      ·
        refine ⟨20766233303437282372254529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27688311071249709829672705 20766233303437282372254529)
        ·
          refine ⟨15574674977577961779190897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20766233303437282372254529 15574674977577961779190897)
          ·
            refine ⟨11681006233183471334393173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15574674977577961779190897 11681006233183471334393173)
            ·
              refine ⟨8555424487194925293745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 11681006233183471334393173 8555424487194925293745)
              ·
                rfl

theorem cell23_1349592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 12].length) (baseStart_1349592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349592 prefixEnd_1349592 := by exact prefixLift 1349592
  have htrace : WordTrace (prefixWord ++ tailWord_1349592) baseStart_1349592 baseEnd_1349592 := by
    simpa [prefixWord, tailWord_1349592, baseEnd_1349592] using wordTrace_append hprefix tailTrace_1349592
  have hstable : (prefixWord ++ tailWord_1349592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349592).length < 2 ^ (prefixWord ++ tailWord_1349592).sum := by decide
  have hdescent : baseEnd_1349592 < baseStart_1349592 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349603 : List Nat := [1, 1, 1, 6, 1, 2, 1, 3, 3, 2, 2]
def baseStart_1349603 : Nat := 118140960795 + 1349603 * 2 ^ 59
def prefixEnd_1349603 : Nat := 4983230072969 + 3 ^ 40 * 1349603 * 2
def baseEnd_1349603 : Nat := 692995031749988405755795

theorem tailTrace_1349603 : CollatzResearch.WordTrace tailWord_1349603 prefixEnd_1349603 692995031749988405755795 := by
  unfold tailWord_1349603
  simp only [CollatzResearch.WordTrace]
  refine ⟨49224065329626299686957463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32816043553084199791304975 49224065329626299686957463)
  ·
    refine ⟨73836097994439449530436195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49224065329626299686957463 73836097994439449530436195)
    ·
      refine ⟨110754146991659174295654293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73836097994439449530436195 110754146991659174295654293)
      ·
        refine ⟨5191600640234023795108795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 110754146991659174295654293 5191600640234023795108795)
        ·
          refine ⟨7787400960351035692663193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5191600640234023795108795 7787400960351035692663193)
          ·
            refine ⟨5840550720263276769497395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7787400960351035692663193 5840550720263276769497395)
            ·
              refine ⟨8760826080394915154246093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5840550720263276769497395 8760826080394915154246093)
              ·
                refine ⟨3285309780148093182842285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8760826080394915154246093 3285309780148093182842285)
                ·
                  refine ⟨1231991167555534943565857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3285309780148093182842285 1231991167555534943565857)
                  ·
                    refine ⟨923993375666651207674393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1231991167555534943565857 923993375666651207674393)
                    ·
                      refine ⟨692995031749988405755795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 923993375666651207674393 692995031749988405755795)
                      ·
                        rfl

theorem cell23_1349603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_1349603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349603 prefixEnd_1349603 := by exact prefixLift 1349603
  have htrace : WordTrace (prefixWord ++ tailWord_1349603) baseStart_1349603 baseEnd_1349603 := by
    simpa [prefixWord, tailWord_1349603, baseEnd_1349603] using wordTrace_append hprefix tailTrace_1349603
  have hstable : (prefixWord ++ tailWord_1349603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349603).length < 2 ^ (prefixWord ++ tailWord_1349603).sum := by decide
  have hdescent : baseEnd_1349603 < baseStart_1349603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349637 : List Nat := [1, 3, 1, 1, 2, 6, 1, 3, 1, 2, 2]
def baseStart_1349637 : Nat := 118140960795 + 1349637 * 2 ^ 59
def prefixEnd_1349637 : Nat := 4983230072969 + 3 ^ 40 * 1349637 * 2
def baseEnd_1349637 : Nat := 693012490092241272730639

theorem tailTrace_1349637 : CollatzResearch.WordTrace tailWord_1349637 prefixEnd_1349637 693012490092241272730639 := by
  unfold tailWord_1349637
  simp only [CollatzResearch.WordTrace]
  refine ⟨49225305411503123493695165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32816870274335415662463443 49225305411503123493695165)
  ·
    refine ⟨18459489529313671310135687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49225305411503123493695165 18459489529313671310135687)
    ·
      refine ⟨27689234293970506965203531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18459489529313671310135687 27689234293970506965203531)
      ·
        refine ⟨41533851440955760447805297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27689234293970506965203531 41533851440955760447805297)
        ·
          refine ⟨31150388580716820335853973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41533851440955760447805297 31150388580716820335853973)
          ·
            refine ⟨1460174464721100953243155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31150388580716820335853973 1460174464721100953243155)
            ·
              refine ⟨2190261697081651429864733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1460174464721100953243155 2190261697081651429864733)
              ·
                refine ⟨821348136405619286199275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2190261697081651429864733 821348136405619286199275)
                ·
                  refine ⟨1232022204608428929298913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 821348136405619286199275 1232022204608428929298913)
                  ·
                    refine ⟨924016653456321696974185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1232022204608428929298913 924016653456321696974185)
                    ·
                      refine ⟨693012490092241272730639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 924016653456321696974185 693012490092241272730639)
                      ·
                        rfl

theorem cell23_1349637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 6, 1, 3, 1, 2, 2].length) (baseStart_1349637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349637 prefixEnd_1349637 := by exact prefixLift 1349637
  have htrace : WordTrace (prefixWord ++ tailWord_1349637) baseStart_1349637 baseEnd_1349637 := by
    simpa [prefixWord, tailWord_1349637, baseEnd_1349637] using wordTrace_append hprefix tailTrace_1349637
  have hstable : (prefixWord ++ tailWord_1349637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349637).length < 2 ^ (prefixWord ++ tailWord_1349637).sum := by decide
  have hdescent : baseEnd_1349637 < baseStart_1349637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349679 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 3]
def baseStart_1349679 : Nat := 118140960795 + 1349679 * 2 ^ 59
def prefixEnd_1349679 : Nat := 4983230072969 + 3 ^ 40 * 1349679 * 2
def baseEnd_1349679 : Nat := 693034056279730108405445

theorem tailTrace_1349679 : CollatzResearch.WordTrace tailWord_1349679 prefixEnd_1349679 693034056279730108405445 := by
  unfold tailWord_1349679
  simp only [CollatzResearch.WordTrace]
  refine ⟨49226837277350964666724091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32817891518233976444482727 49226837277350964666724091)
  ·
    refine ⟨73840255916026447000086137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49226837277350964666724091 73840255916026447000086137)
    ·
      refine ⟨55380191937019835250064603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73840255916026447000086137 55380191937019835250064603)
      ·
        refine ⟨83070287905529752875096905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55380191937019835250064603 83070287905529752875096905)
        ·
          refine ⟨62302715929147314656322679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83070287905529752875096905 62302715929147314656322679)
          ·
            refine ⟨93454073893720971984484019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62302715929147314656322679 93454073893720971984484019)
            ·
              refine ⟨140181110840581457976726029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93454073893720971984484019 140181110840581457976726029)
              ·
                refine ⟨52567916565218046741272261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140181110840581457976726029 52567916565218046741272261)
                ·
                  refine ⟨9856484355978383763988549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52567916565218046741272261 9856484355978383763988549)
                  ·
                    refine ⟨1848090816745946955747853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9856484355978383763988549 1848090816745946955747853)
                    ·
                      refine ⟨693034056279730108405445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1848090816745946955747853 693034056279730108405445)
                      ·
                        rfl

theorem cell23_1349679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 4, 4, 3].length) (baseStart_1349679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349679 prefixEnd_1349679 := by exact prefixLift 1349679
  have htrace : WordTrace (prefixWord ++ tailWord_1349679) baseStart_1349679 baseEnd_1349679 := by
    simpa [prefixWord, tailWord_1349679, baseEnd_1349679] using wordTrace_append hprefix tailTrace_1349679
  have hstable : (prefixWord ++ tailWord_1349679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349679).length < 2 ^ (prefixWord ++ tailWord_1349679).sum := by decide
  have hdescent : baseEnd_1349679 < baseStart_1349679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349680 : List Nat := [2, 1, 1, 1, 2, 7, 1, 2, 1, 3, 2]
def baseStart_1349680 : Nat := 118140960795 + 1349680 * 2 ^ 59
def prefixEnd_1349680 : Nat := 4983230072969 + 3 ^ 40 * 1349680 * 2
def baseEnd_1349680 : Nat := 693034569760384604492941

theorem tailTrace_1349680 : CollatzResearch.WordTrace tailWord_1349680 prefixEnd_1349680 693034569760384604492941 := by
  unfold tailWord_1349680
  simp only [CollatzResearch.WordTrace]
  refine ⟨24613436875173670918755247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32817915833564894558340329 24613436875173670918755247)
  ·
    refine ⟨36920155312760506378132871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24613436875173670918755247 36920155312760506378132871)
    ·
      refine ⟨55380232969140759567199307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36920155312760506378132871 55380232969140759567199307)
      ·
        refine ⟨83070349453711139350798961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55380232969140759567199307 83070349453711139350798961)
        ·
          refine ⟨62302762090283354513099221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83070349453711139350798961 62302762090283354513099221)
          ·
            refine ⟨1460220986491016121400763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 62302762090283354513099221 1460220986491016121400763)
            ·
              refine ⟨2190331479736524182101145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1460220986491016121400763 2190331479736524182101145)
              ·
                refine ⟨1642748609802393136575859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2190331479736524182101145 1642748609802393136575859)
                ·
                  refine ⟨2464122914703589704863789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1642748609802393136575859 2464122914703589704863789)
                  ·
                    refine ⟨924046093013846139323921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2464122914703589704863789 924046093013846139323921)
                    ·
                      refine ⟨693034569760384604492941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 924046093013846139323921 693034569760384604492941)
                      ·
                        rfl

theorem cell23_1349680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 1, 3, 2].length) (baseStart_1349680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349680 prefixEnd_1349680 := by exact prefixLift 1349680
  have htrace : WordTrace (prefixWord ++ tailWord_1349680) baseStart_1349680 baseEnd_1349680 := by
    simpa [prefixWord, tailWord_1349680, baseEnd_1349680] using wordTrace_append hprefix tailTrace_1349680
  have hstable : (prefixWord ++ tailWord_1349680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349680).length < 2 ^ (prefixWord ++ tailWord_1349680).sum := by decide
  have hdescent : baseEnd_1349680 < baseStart_1349680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349693 : List Nat := [1, 4, 1, 3, 1, 1, 3, 2, 1, 4, 2]
def baseStart_1349693 : Nat := 118140960795 + 1349693 * 2 ^ 59
def prefixEnd_1349693 : Nat := 4983230072969 + 3 ^ 40 * 1349693 * 2
def baseEnd_1349693 : Nat := 693041245008893053630381

theorem tailTrace_1349693 : CollatzResearch.WordTrace tailWord_1349693 prefixEnd_1349693 693041245008893053630381 := by
  unfold tailWord_1349693
  simp only [CollatzResearch.WordTrace]
  refine ⟨49227347899300245057733733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32818231932866830038489155 49227347899300245057733733)
  ·
    refine ⟨9230127731118795948325075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49227347899300245057733733 9230127731118795948325075)
    ·
      refine ⟨13845191596678193922487613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9230127731118795948325075 13845191596678193922487613)
      ·
        refine ⟨5191946848754322720932855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13845191596678193922487613 5191946848754322720932855)
        ·
          refine ⟨7787920273131484081399283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5191946848754322720932855 7787920273131484081399283)
          ·
            refine ⟨11681880409697226122098925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7787920273131484081399283 11681880409697226122098925)
            ·
              refine ⟨4380705153636459795787097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11681880409697226122098925 4380705153636459795787097)
              ·
                refine ⟨3285528865227344846840323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4380705153636459795787097 3285528865227344846840323)
                ·
                  refine ⟨4928293297841017270260485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3285528865227344846840323 4928293297841017270260485)
                  ·
                    refine ⟨924054993345190738173841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4928293297841017270260485 924054993345190738173841)
                    ·
                      refine ⟨693041245008893053630381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 924054993345190738173841 693041245008893053630381)
                      ·
                        rfl

theorem cell23_1349693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 4, 2].length) (baseStart_1349693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349693 prefixEnd_1349693 := by exact prefixLift 1349693
  have htrace : WordTrace (prefixWord ++ tailWord_1349693) baseStart_1349693 baseEnd_1349693 := by
    simpa [prefixWord, tailWord_1349693, baseEnd_1349693] using wordTrace_append hprefix tailTrace_1349693
  have hstable : (prefixWord ++ tailWord_1349693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349693).length < 2 ^ (prefixWord ++ tailWord_1349693).sum := by decide
  have hdescent : baseEnd_1349693 < baseStart_1349693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349697 : List Nat := [1, 2, 5, 1, 2, 2, 3, 1, 1, 3, 2]
def baseStart_1349697 : Nat := 118140960795 + 1349697 * 2 ^ 59
def prefixEnd_1349697 : Nat := 4983230072969 + 3 ^ 40 * 1349697 * 2
def baseEnd_1349697 : Nat := 693043298931511037980363

theorem tailTrace_1349697 : CollatzResearch.WordTrace tailWord_1349697 prefixEnd_1349697 693043298931511037980363 := by
  unfold tailWord_1349697
  simp only [CollatzResearch.WordTrace]
  refine ⟨49227493791285753740879345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32818329194190502493919563 49227493791285753740879345)
  ·
    refine ⟨36920620343464315305659509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49227493791285753740879345 36920620343464315305659509)
    ·
      refine ⟨3461308157199779559905579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36920620343464315305659509 3461308157199779559905579)
      ·
        refine ⟨5191962235799669339858369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3461308157199779559905579 5191962235799669339858369)
        ·
          refine ⟨3893971676849752004893777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5191962235799669339858369 3893971676849752004893777)
          ·
            refine ⟨2920478757637314003670333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3893971676849752004893777 2920478757637314003670333)
            ·
              refine ⟨1095179534113992751376375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2920478757637314003670333 1095179534113992751376375)
              ·
                refine ⟨1642769301170989127064563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1095179534113992751376375 1642769301170989127064563)
                ·
                  refine ⟨2464153951756483690596845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1642769301170989127064563 2464153951756483690596845)
                  ·
                    refine ⟨924057731908681383973817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2464153951756483690596845 924057731908681383973817)
                    ·
                      refine ⟨693043298931511037980363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 924057731908681383973817 693043298931511037980363)
                      ·
                        rfl

theorem cell23_1349697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 1, 3, 2].length) (baseStart_1349697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349697 prefixEnd_1349697 := by exact prefixLift 1349697
  have htrace : WordTrace (prefixWord ++ tailWord_1349697) baseStart_1349697 baseEnd_1349697 := by
    simpa [prefixWord, tailWord_1349697, baseEnd_1349697] using wordTrace_append hprefix tailTrace_1349697
  have hstable : (prefixWord ++ tailWord_1349697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349697).length < 2 ^ (prefixWord ++ tailWord_1349697).sum := by decide
  have hdescent : baseEnd_1349697 < baseStart_1349697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349710 : List Nat := [4, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2]
def baseStart_1349710 : Nat := 118140960795 + 1349710 * 2 ^ 59
def prefixEnd_1349710 : Nat := 4983230072969 + 3 ^ 40 * 1349710 * 2
def baseEnd_1349710 : Nat := 693049974180019487117803

theorem tailTrace_1349710 : CollatzResearch.WordTrace tailWord_1349710 prefixEnd_1349710 693049974180019487117803 := by
  unfold tailWord_1349710
  simp only [CollatzResearch.WordTrace]
  refine ⟨6153495992529832120137823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32818645293492437974068389 6153495992529832120137823)
  ·
    refine ⟨9230243988794748180206735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6153495992529832120137823 9230243988794748180206735)
    ·
      refine ⟨13845365983192122270310103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9230243988794748180206735 13845365983192122270310103)
      ·
        refine ⟨20768048974788183405465155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13845365983192122270310103 20768048974788183405465155)
        ·
          refine ⟨31152073462182275108197733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20768048974788183405465155 31152073462182275108197733)
          ·
            refine ⟨5841013774159176582787075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31152073462182275108197733 5841013774159176582787075)
            ·
              refine ⟨8761520661238764874180613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5841013774159176582787075 8761520661238764874180613)
              ·
                refine ⟨1642785123982268413908865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8761520661238764874180613 1642785123982268413908865)
                ·
                  refine ⟨1232088842986701310431649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1642785123982268413908865 1232088842986701310431649)
                  ·
                    refine ⟨924066632240025982823737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1232088842986701310431649 924066632240025982823737)
                    ·
                      refine ⟨693049974180019487117803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 924066632240025982823737 693049974180019487117803)
                      ·
                        rfl

theorem cell23_1349710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 4, 2, 2, 2].length) (baseStart_1349710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349710 prefixEnd_1349710 := by exact prefixLift 1349710
  have htrace : WordTrace (prefixWord ++ tailWord_1349710) baseStart_1349710 baseEnd_1349710 := by
    simpa [prefixWord, tailWord_1349710, baseEnd_1349710] using wordTrace_append hprefix tailTrace_1349710
  have hstable : (prefixWord ++ tailWord_1349710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349710).length < 2 ^ (prefixWord ++ tailWord_1349710).sum := by decide
  have hdescent : baseEnd_1349710 < baseStart_1349710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349729 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 1, 7]
def baseStart_1349729 : Nat := 118140960795 + 1349729 * 2 ^ 59
def prefixEnd_1349729 : Nat := 4983230072969 + 3 ^ 40 * 1349729 * 2
def baseEnd_1349729 : Nat := 231019910104151637593405

theorem tailTrace_1349729 : CollatzResearch.WordTrace tailWord_1349729 prefixEnd_1349729 231019910104151637593405 := by
  unfold tailWord_1349729
  simp only [CollatzResearch.WordTrace]
  refine ⟨49228660927169823206044241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32819107284779882137362827 49228660927169823206044241)
  ·
    refine ⟨36921495695377367404533181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49228660927169823206044241 36921495695377367404533181)
    ·
      refine ⟨13845560885766512776699943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36921495695377367404533181 13845560885766512776699943)
      ·
        refine ⟨20768341328649769165049915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13845560885766512776699943 20768341328649769165049915)
        ·
          refine ⟨31152511992974653747574873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20768341328649769165049915 31152511992974653747574873)
          ·
            refine ⟨23364383994730990310681155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31152511992974653747574873 23364383994730990310681155)
            ·
              refine ⟨35046575992096485466021733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23364383994730990310681155 35046575992096485466021733)
              ·
                refine ⟨6571232998518091024879075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35046575992096485466021733 6571232998518091024879075)
                ·
                  refine ⟨9856849497777136537318613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6571232998518091024879075 9856849497777136537318613)
                  ·
                    refine ⟨231019910104151637593405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9856849497777136537318613 231019910104151637593405)
                    ·
                      rfl

theorem cell23_1349729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_1349729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349729 prefixEnd_1349729 := by exact prefixLift 1349729
  have htrace : WordTrace (prefixWord ++ tailWord_1349729) baseStart_1349729 baseEnd_1349729 := by
    simpa [prefixWord, tailWord_1349729, baseEnd_1349729] using wordTrace_append hprefix tailTrace_1349729
  have hstable : (prefixWord ++ tailWord_1349729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349729).length < 2 ^ (prefixWord ++ tailWord_1349729).sum := by decide
  have hdescent : baseEnd_1349729 < baseStart_1349729 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349746 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 1, 7]
def baseStart_1349746 : Nat := 118140960795 + 1349746 * 2 ^ 59
def prefixEnd_1349746 : Nat := 4983230072969 + 3 ^ 40 * 1349746 * 2
def baseEnd_1349746 : Nat := 231022819827860448755879

theorem tailTrace_1349746 : CollatzResearch.WordTrace tailWord_1349746 prefixEnd_1349746 231022819827860448755879 := by
  unfold tailWord_1349746
  simp only [CollatzResearch.WordTrace]
  refine ⟨12307320242027058777353273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32819520645405490072942061 12307320242027058777353273)
  ·
    refine ⟨9230490181520294083014955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12307320242027058777353273 9230490181520294083014955)
    ·
      refine ⟨13845735272280441124522433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9230490181520294083014955 13845735272280441124522433)
      ·
        refine ⟨10384301454210330843391825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13845735272280441124522433 10384301454210330843391825)
        ·
          refine ⟨7788226090657748132543869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10384301454210330843391825 7788226090657748132543869)
          ·
            refine ⟨2920584783996655549703951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7788226090657748132543869 2920584783996655549703951)
            ·
              refine ⟨4380877175994983324555927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2920584783996655549703951 4380877175994983324555927)
              ·
                refine ⟨6571315763992474986833891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4380877175994983324555927 6571315763992474986833891)
                ·
                  refine ⟨9856973645988712480250837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6571315763992474986833891 9856973645988712480250837)
                  ·
                    refine ⟨231022819827860448755879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9856973645988712480250837 231022819827860448755879)
                    ·
                      rfl

theorem cell23_1349746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_1349746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349746 prefixEnd_1349746 := by exact prefixLift 1349746
  have htrace : WordTrace (prefixWord ++ tailWord_1349746) baseStart_1349746 baseEnd_1349746 := by
    simpa [prefixWord, tailWord_1349746, baseEnd_1349746] using wordTrace_append hprefix tailTrace_1349746
  have hstable : (prefixWord ++ tailWord_1349746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349746).length < 2 ^ (prefixWord ++ tailWord_1349746).sum := by decide
  have hdescent : baseEnd_1349746 < baseStart_1349746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349750 : List Nat := [5, 1, 1, 2, 1, 3, 2, 3, 5]
def baseStart_1349750 : Nat := 118140960795 + 1349750 * 2 ^ 59
def prefixEnd_1349750 : Nat := 4983230072969 + 3 ^ 40 * 1349750 * 2
def baseEnd_1349750 : Nat := 77007834822911036735291

theorem tailTrace_1349750 : CollatzResearch.WordTrace tailWord_1349750 prefixEnd_1349750 77007834822911036735291 := by
  unfold tailWord_1349750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3076839178755858987034919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32819617906729162528372469 3076839178755858987034919)
  ·
    refine ⟨4615258768133788480552379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3076839178755858987034919 4615258768133788480552379)
    ·
      refine ⟨6922888152200682720828569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4615258768133788480552379 6922888152200682720828569)
      ·
        refine ⟨5192166114150512040621427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6922888152200682720828569 5192166114150512040621427)
        ·
          refine ⟨7788249171225768060932141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5192166114150512040621427 7788249171225768060932141)
          ·
            refine ⟨2920593439209663022849553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7788249171225768060932141 2920593439209663022849553)
            ·
              refine ⟨2190445079407247267137165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2920593439209663022849553 2190445079407247267137165)
              ·
                refine ⟨821416904777717725176437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2190445079407247267137165 821416904777717725176437)
                ·
                  refine ⟨77007834822911036735291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 821416904777717725176437 77007834822911036735291)
                  ·
                    rfl

theorem cell23_1349750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_1349750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349750 prefixEnd_1349750 := by exact prefixLift 1349750
  have htrace : WordTrace (prefixWord ++ tailWord_1349750) baseStart_1349750 baseEnd_1349750 := by
    simpa [prefixWord, tailWord_1349750, baseEnd_1349750] using wordTrace_append hprefix tailTrace_1349750
  have hstable : (prefixWord ++ tailWord_1349750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349750).length < 2 ^ (prefixWord ++ tailWord_1349750).sum := by decide
  have hdescent : baseEnd_1349750 < baseStart_1349750 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349779 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 6]
def baseStart_1349779 : Nat := 118140960795 + 1349779 * 2 ^ 59
def prefixEnd_1349779 : Nat := 4983230072969 + 3 ^ 40 * 1349779 * 2
def baseEnd_1349779 : Nat := 693085404345179717154985

theorem tailTrace_1349779 : CollatzResearch.WordTrace tailWord_1349779 prefixEnd_1349779 693085404345179717154985 := by
  unfold tailWord_1349779
  simp only [CollatzResearch.WordTrace]
  refine ⟨49230484576988681745364391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32820323051325787830242927 49230484576988681745364391)
  ·
    refine ⟨73845726865483022618046587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49230484576988681745364391 73845726865483022618046587)
    ·
      refine ⟨110768590298224533927069881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73845726865483022618046587 110768590298224533927069881)
      ·
        refine ⟨83076442723668400445302411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110768590298224533927069881 83076442723668400445302411)
        ·
          refine ⟨124614664085502600667953617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83076442723668400445302411 124614664085502600667953617)
          ·
            refine ⟨93460998064126950500965213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124614664085502600667953617 93460998064126950500965213)
            ·
              refine ⟨35047874274047606437861955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93460998064126950500965213 35047874274047606437861955)
              ·
                refine ⟨52571811411071409656792933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35047874274047606437861955 52571811411071409656792933)
                ·
                  refine ⟨9857214639575889310648675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52571811411071409656792933 9857214639575889310648675)
                  ·
                    refine ⟨14785821959363833965973013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9857214639575889310648675 14785821959363833965973013)
                    ·
                      refine ⟨693085404345179717154985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14785821959363833965973013 693085404345179717154985)
                      ·
                        rfl

theorem cell23_1349779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_1349779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349779 prefixEnd_1349779 := by exact prefixLift 1349779
  have htrace : WordTrace (prefixWord ++ tailWord_1349779) baseStart_1349779 baseEnd_1349779 := by
    simpa [prefixWord, tailWord_1349779, baseEnd_1349779] using wordTrace_append hprefix tailTrace_1349779
  have hstable : (prefixWord ++ tailWord_1349779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349779).length < 2 ^ (prefixWord ++ tailWord_1349779).sum := by decide
  have hdescent : baseEnd_1349779 < baseStart_1349779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349793 : List Nat := [1, 2, 3, 3, 1, 2, 2, 2, 3, 4]
def baseStart_1349793 : Nat := 118140960795 + 1349793 * 2 ^ 59
def prefixEnd_1349793 : Nat := 4983230072969 + 3 ^ 40 * 1349793 * 2
def baseEnd_1349793 : Nat := 231030864358114220793307

theorem tailTrace_1349793 : CollatzResearch.WordTrace tailWord_1349793 prefixEnd_1349793 231030864358114220793307 := by
  unfold tailWord_1349793
  simp only [CollatzResearch.WordTrace]
  refine ⟨49230995198937962136374033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32820663465958641424249355 49230995198937962136374033)
  ·
    refine ⟨36923246399203471602280525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49230995198937962136374033 36923246399203471602280525)
    ·
      refine ⟨13846217399701301850855197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36923246399203471602280525 13846217399701301850855197)
      ·
        refine ⟨5192331524887988194070699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13846217399701301850855197 5192331524887988194070699)
        ·
          refine ⟨7788497287331982291106049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5192331524887988194070699 7788497287331982291106049)
          ·
            refine ⟨5841372965498986718329537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7788497287331982291106049 5841372965498986718329537)
            ·
              refine ⟨4381029724124240038747153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5841372965498986718329537 4381029724124240038747153)
              ·
                refine ⟨3285772293093180029060365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4381029724124240038747153 3285772293093180029060365)
                ·
                  refine ⟨1232164609909942510897637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3285772293093180029060365 1232164609909942510897637)
                  ·
                    refine ⟨231030864358114220793307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1232164609909942510897637 231030864358114220793307)
                    ·
                      rfl

theorem cell23_1349793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_1349793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349793 prefixEnd_1349793 := by exact prefixLift 1349793
  have htrace : WordTrace (prefixWord ++ tailWord_1349793) baseStart_1349793 baseEnd_1349793 := by
    simpa [prefixWord, tailWord_1349793, baseEnd_1349793] using wordTrace_append hprefix tailTrace_1349793
  have hstable : (prefixWord ++ tailWord_1349793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349793).length < 2 ^ (prefixWord ++ tailWord_1349793).sum := by decide
  have hdescent : baseEnd_1349793 < baseStart_1349793 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349820 : List Nat := [2, 2, 2, 3, 3, 1, 1, 2, 2, 2, 3]
def baseStart_1349820 : Nat := 118140960795 + 1349820 * 2 ^ 59
def prefixEnd_1349820 : Nat := 4983230072969 + 3 ^ 40 * 1349820 * 2
def baseEnd_1349820 : Nat := 693106457052014056742297

theorem tailTrace_1349820 : CollatzResearch.WordTrace tailWord_1349820 prefixEnd_1349820 693106457052014056742297 := by
  unfold tailWord_1349820
  simp only [CollatzResearch.WordTrace]
  refine ⟨24615989984920072873803457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32821319979893430498404609 24615989984920072873803457)
  ·
    refine ⟨18461992488690054655352593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24615989984920072873803457 18461992488690054655352593)
    ·
      refine ⟨13846494366517540991514445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18461992488690054655352593 13846494366517540991514445)
      ·
        refine ⟨5192435387444077871817917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13846494366517540991514445 5192435387444077871817917)
        ·
          refine ⟨1947163270291529201931719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5192435387444077871817917 1947163270291529201931719)
          ·
            refine ⟨2920744905437293802897579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1947163270291529201931719 2920744905437293802897579)
            ·
              refine ⟨4381117358155940704346369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2920744905437293802897579 4381117358155940704346369)
              ·
                refine ⟨3285838018616955528259777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4381117358155940704346369 3285838018616955528259777)
                ·
                  refine ⟨2464378513962716646194833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3285838018616955528259777 2464378513962716646194833)
                  ·
                    refine ⟨1848283885472037484646125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2464378513962716646194833 1848283885472037484646125)
                    ·
                      refine ⟨693106457052014056742297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1848283885472037484646125 693106457052014056742297)
                      ·
                        rfl

theorem cell23_1349820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 2, 2, 3].length) (baseStart_1349820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349820 prefixEnd_1349820 := by exact prefixLift 1349820
  have htrace : WordTrace (prefixWord ++ tailWord_1349820) baseStart_1349820 baseEnd_1349820 := by
    simpa [prefixWord, tailWord_1349820, baseEnd_1349820] using wordTrace_append hprefix tailTrace_1349820
  have hstable : (prefixWord ++ tailWord_1349820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349820).length < 2 ^ (prefixWord ++ tailWord_1349820).sum := by decide
  have hdescent : baseEnd_1349820 < baseStart_1349820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349833 : List Nat := [1, 2, 1, 1, 2, 1, 1, 7, 3, 1, 3]
def baseStart_1349833 : Nat := 118140960795 + 1349833 * 2 ^ 59
def prefixEnd_1349833 : Nat := 4983230072969 + 3 ^ 40 * 1349833 * 2
def baseEnd_1349833 : Nat := 693113132300522505879737

theorem tailTrace_1349833 : CollatzResearch.WordTrace tailWord_1349833 prefixEnd_1349833 693113132300522505879737 := by
  unfold tailWord_1349833
  simp only [CollatzResearch.WordTrace]
  refine ⟨49232454118793048967830153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32821636079195365978553435 49232454118793048967830153)
  ·
    refine ⟨36924340589094786725872615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49232454118793048967830153 36924340589094786725872615)
    ·
      refine ⟨55386510883642180088808923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36924340589094786725872615 55386510883642180088808923)
      ·
        refine ⟨83079766325463270133213385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55386510883642180088808923 83079766325463270133213385)
        ·
          refine ⟨62309824744097452599910039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83079766325463270133213385 62309824744097452599910039)
          ·
            refine ⟨93464737116146178899865059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62309824744097452599910039 93464737116146178899865059)
            ·
              refine ⟨140197105674219268349797589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93464737116146178899865059 140197105674219268349797589)
              ·
                refine ⟨3285869664239514101948381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 140197105674219268349797589 3285869664239514101948381)
                ·
                  refine ⟨1232201124089817788230643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3285869664239514101948381 1232201124089817788230643)
                  ·
                    refine ⟨1848301686134726682345965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1232201124089817788230643 1848301686134726682345965)
                    ·
                      refine ⟨693113132300522505879737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1848301686134726682345965 693113132300522505879737)
                      ·
                        rfl

theorem cell23_1349833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 1, 3].length) (baseStart_1349833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349833 prefixEnd_1349833 := by exact prefixLift 1349833
  have htrace : WordTrace (prefixWord ++ tailWord_1349833) baseStart_1349833 baseEnd_1349833 := by
    simpa [prefixWord, tailWord_1349833, baseEnd_1349833] using wordTrace_append hprefix tailTrace_1349833
  have hstable : (prefixWord ++ tailWord_1349833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349833).length < 2 ^ (prefixWord ++ tailWord_1349833).sum := by decide
  have hdescent : baseEnd_1349833 < baseStart_1349833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349873 : List Nat := [1, 2, 2, 2, 2, 1, 2, 5, 1, 1, 4]
def baseStart_1349873 : Nat := 118140960795 + 1349873 * 2 ^ 59
def prefixEnd_1349873 : Nat := 4983230072969 + 3 ^ 40 * 1349873 * 2
def baseEnd_1349873 : Nat := 693133671526702349379553

theorem tailTrace_1349873 : CollatzResearch.WordTrace tailWord_1349873 prefixEnd_1349873 693133671526702349379553 := by
  unfold tailWord_1349873
  simp only [CollatzResearch.WordTrace]
  refine ⟨49233913038648135799286273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32822608692432090532857515 49233913038648135799286273)
  ·
    refine ⟨36925434778986101849464705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49233913038648135799286273 36925434778986101849464705)
    ·
      refine ⟨27694076084239576387098529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36925434778986101849464705 27694076084239576387098529)
      ·
        refine ⟨20770557063179682290323897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27694076084239576387098529 20770557063179682290323897)
        ·
          refine ⟨15577917797384761717742923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20770557063179682290323897 15577917797384761717742923)
          ·
            refine ⟨23366876696077142576614385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15577917797384761717742923 23366876696077142576614385)
            ·
              refine ⟨17525157522057856932460789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23366876696077142576614385 17525157522057856932460789)
              ·
                refine ⟨1642983517692924087418199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17525157522057856932460789 1642983517692924087418199)
                ·
                  refine ⟨2464475276539386131127299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1642983517692924087418199 2464475276539386131127299)
                  ·
                    refine ⟨3696712914809079196690949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2464475276539386131127299 3696712914809079196690949)
                    ·
                      refine ⟨693133671526702349379553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3696712914809079196690949 693133671526702349379553)
                      ·
                        rfl

theorem cell23_1349873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 1, 4].length) (baseStart_1349873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349873 prefixEnd_1349873 := by exact prefixLift 1349873
  have htrace : WordTrace (prefixWord ++ tailWord_1349873) baseStart_1349873 baseEnd_1349873 := by
    simpa [prefixWord, tailWord_1349873, baseEnd_1349873] using wordTrace_append hprefix tailTrace_1349873
  have hstable : (prefixWord ++ tailWord_1349873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349873).length < 2 ^ (prefixWord ++ tailWord_1349873).sum := by decide
  have hdescent : baseEnd_1349873 < baseStart_1349873 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349884 : List Nat := [2, 2, 2, 1, 4, 1, 4, 2, 1, 1, 3]
def baseStart_1349884 : Nat := 118140960795 + 1349884 * 2 ^ 59
def prefixEnd_1349884 : Nat := 4983230072969 + 3 ^ 40 * 1349884 * 2
def baseEnd_1349884 : Nat := 693139319813901806342003

theorem tailTrace_1349884 : CollatzResearch.WordTrace tailWord_1349884 prefixEnd_1349884 693139319813901806342003 := by
  unfold tailWord_1349884
  simp only [CollatzResearch.WordTrace]
  refine ⟨24617157120804142338968353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32822876161072189785291137 24617157120804142338968353)
  ·
    refine ⟨18462867840603106754226265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24617157120804142338968353 18462867840603106754226265)
    ·
      refine ⟨13847150880452330065669699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18462867840603106754226265 13847150880452330065669699)
      ·
        refine ⟨20770726320678495098504549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13847150880452330065669699 20770726320678495098504549)
        ·
          refine ⟨3894511185127217830969603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20770726320678495098504549 3894511185127217830969603)
          ·
            refine ⟨5841766777690826746454405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3894511185127217830969603 5841766777690826746454405)
            ·
              refine ⟨1095331270817030014960201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5841766777690826746454405 1095331270817030014960201)
              ·
                refine ⟨821498453112772511220151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1095331270817030014960201 821498453112772511220151)
                ·
                  refine ⟨1232247679669158766830227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 821498453112772511220151 1232247679669158766830227)
                  ·
                    refine ⟨1848371519503738150245341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1232247679669158766830227 1848371519503738150245341)
                    ·
                      refine ⟨693139319813901806342003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1848371519503738150245341 693139319813901806342003)
                      ·
                        rfl

theorem cell23_1349884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 1, 1, 3].length) (baseStart_1349884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349884 prefixEnd_1349884 := by exact prefixLift 1349884
  have htrace : WordTrace (prefixWord ++ tailWord_1349884) baseStart_1349884 baseEnd_1349884 := by
    simpa [prefixWord, tailWord_1349884, baseEnd_1349884] using wordTrace_append hprefix tailTrace_1349884
  have hstable : (prefixWord ++ tailWord_1349884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349884).length < 2 ^ (prefixWord ++ tailWord_1349884).sum := by decide
  have hdescent : baseEnd_1349884 < baseStart_1349884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349890 : List Nat := [3, 4, 1, 1, 2, 1, 1, 2, 3, 1, 4]
def baseStart_1349890 : Nat := 118140960795 + 1349890 * 2 ^ 59
def prefixEnd_1349890 : Nat := 4983230072969 + 3 ^ 40 * 1349890 * 2
def baseEnd_1349890 : Nat := 693142400697828782866975

theorem tailTrace_1349890 : CollatzResearch.WordTrace tailWord_1349890 prefixEnd_1349890 693142400697828782866975 := by
  unfold tailWord_1349890
  simp only [CollatzResearch.WordTrace]
  refine ⟨12308633269896636925663781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32823022053057698468436749 12308633269896636925663781)
  ·
    refine ⟨2307868738105619423561959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12308633269896636925663781 2307868738105619423561959)
    ·
      refine ⟨3461803107158429135342939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2307868738105619423561959 3461803107158429135342939)
      ·
        refine ⟨5192704660737643703014409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3461803107158429135342939 5192704660737643703014409)
        ·
          refine ⟨3894528495553232777260807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5192704660737643703014409 3894528495553232777260807)
          ·
            refine ⟨5841792743329849165891211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3894528495553232777260807 5841792743329849165891211)
            ·
              refine ⟨8762689114994773748836817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5841792743329849165891211 8762689114994773748836817)
              ·
                refine ⟨6572016836246080311627613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8762689114994773748836817 6572016836246080311627613)
                ·
                  refine ⟨2464506313592280116860355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6572016836246080311627613 2464506313592280116860355)
                  ·
                    refine ⟨3696759470388420175290533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2464506313592280116860355 3696759470388420175290533)
                    ·
                      refine ⟨693142400697828782866975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3696759470388420175290533 693142400697828782866975)
                      ·
                        rfl

theorem cell23_1349890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 2, 3, 1, 4].length) (baseStart_1349890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349890 prefixEnd_1349890 := by exact prefixLift 1349890
  have htrace : WordTrace (prefixWord ++ tailWord_1349890) baseStart_1349890 baseEnd_1349890 := by
    simpa [prefixWord, tailWord_1349890, baseEnd_1349890] using wordTrace_append hprefix tailTrace_1349890
  have hstable : (prefixWord ++ tailWord_1349890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349890).length < 2 ^ (prefixWord ++ tailWord_1349890).sum := by decide
  have hdescent : baseEnd_1349890 < baseStart_1349890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349923 : List Nat := [1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 3]
def baseStart_1349923 : Nat := 118140960795 + 1349923 * 2 ^ 59
def prefixEnd_1349923 : Nat := 4983230072969 + 3 ^ 40 * 1349923 * 2
def baseEnd_1349923 : Nat := 693159345559427153754323

theorem tailTrace_1349923 : CollatzResearch.WordTrace tailWord_1349923 prefixEnd_1349923 693159345559427153754323 := by
  unfold tailWord_1349923
  simp only [CollatzResearch.WordTrace]
  refine ⟨49235736688466994338606423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32823824458977996225737615 49235736688466994338606423)
  ·
    refine ⟨73853605032700491507909635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49235736688466994338606423 73853605032700491507909635)
    ·
      refine ⟨110780407549050737261864453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73853605032700491507909635 110780407549050737261864453)
      ·
        refine ⟨20771326415447013236599585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 110780407549050737261864453 20771326415447013236599585)
        ·
          refine ⟨15578494811585259927449689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20771326415447013236599585 15578494811585259927449689)
          ·
            refine ⟨11683871108688944945587267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15578494811585259927449689 11683871108688944945587267)
            ·
              refine ⟨17525806663033417418380901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11683871108688944945587267 17525806663033417418380901)
              ·
                refine ⟨3286088749318765765946419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17525806663033417418380901 3286088749318765765946419)
                ·
                  refine ⟨4929133123978148648919629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3286088749318765765946419 4929133123978148648919629)
                  ·
                    refine ⟨1848424921491805743344861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4929133123978148648919629 1848424921491805743344861)
                    ·
                      refine ⟨693159345559427153754323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1848424921491805743344861 693159345559427153754323)
                      ·
                        rfl

theorem cell23_1349923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 3, 3].length) (baseStart_1349923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349923 prefixEnd_1349923 := by exact prefixLift 1349923
  have htrace : WordTrace (prefixWord ++ tailWord_1349923) baseStart_1349923 baseEnd_1349923 := by
    simpa [prefixWord, tailWord_1349923, baseEnd_1349923] using wordTrace_append hprefix tailTrace_1349923
  have hstable : (prefixWord ++ tailWord_1349923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349923).length < 2 ^ (prefixWord ++ tailWord_1349923).sum := by decide
  have hdescent : baseEnd_1349923 < baseStart_1349923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349924 : List Nat := [2, 3, 1, 3, 1, 2, 1, 5, 1, 2, 2]
def baseStart_1349924 : Nat := 118140960795 + 1349924 * 2 ^ 59
def prefixEnd_1349924 : Nat := 4983230072969 + 3 ^ 40 * 1349924 * 2
def baseEnd_1349924 : Nat := 693159859040081649841819

theorem tailTrace_1349924 : CollatzResearch.WordTrace tailWord_1349924 prefixEnd_1349924 693159859040081649841819 := by
  unfold tailWord_1349924
  simp only [CollatzResearch.WordTrace]
  refine ⟨24617886580731685754696413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32823848774308914339595217 24617886580731685754696413)
  ·
    refine ⟨9231707467774382158011155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24617886580731685754696413 9231707467774382158011155)
    ·
      refine ⟨13847561201661573237016733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9231707467774382158011155 13847561201661573237016733)
      ·
        refine ⟨5192835450623089963881275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13847561201661573237016733 5192835450623089963881275)
        ·
          refine ⟨7789253175934634945821913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5192835450623089963881275 7789253175934634945821913)
          ·
            refine ⟨5841939881950976209366435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7789253175934634945821913 5841939881950976209366435)
            ·
              refine ⟨8762909822926464314049653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5841939881950976209366435 8762909822926464314049653)
              ·
                refine ⟨821522795899356029442155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8762909822926464314049653 821522795899356029442155)
                ·
                  refine ⟨1232284193849034044163233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 821522795899356029442155 1232284193849034044163233)
                  ·
                    refine ⟨924213145386775533122425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1232284193849034044163233 924213145386775533122425)
                    ·
                      refine ⟨693159859040081649841819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 924213145386775533122425 693159859040081649841819)
                      ·
                        rfl

theorem cell23_1349924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 5, 1, 2, 2].length) (baseStart_1349924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349924 prefixEnd_1349924 := by exact prefixLift 1349924
  have htrace : WordTrace (prefixWord ++ tailWord_1349924) baseStart_1349924 baseEnd_1349924 := by
    simpa [prefixWord, tailWord_1349924, baseEnd_1349924] using wordTrace_append hprefix tailTrace_1349924
  have hstable : (prefixWord ++ tailWord_1349924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349924).length < 2 ^ (prefixWord ++ tailWord_1349924).sum := by decide
  have hdescent : baseEnd_1349924 < baseStart_1349924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349936 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 5]
def baseStart_1349936 : Nat := 118140960795 + 1349936 * 2 ^ 59
def prefixEnd_1349936 : Nat := 4983230072969 + 3 ^ 40 * 1349936 * 2
def baseEnd_1349936 : Nat := 693166020807935602891763

theorem tailTrace_1349936 : CollatzResearch.WordTrace tailWord_1349936 prefixEnd_1349936 693166020807935602891763 := by
  unfold tailWord_1349936
  simp only [CollatzResearch.WordTrace]
  refine ⟨24618105418709948779414831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32824140558279931705886441 24618105418709948779414831)
  ·
    refine ⟨36927158128064923169122247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24618105418709948779414831 36927158128064923169122247)
    ·
      refine ⟨55390737192097384753683371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36927158128064923169122247 55390737192097384753683371)
      ·
        refine ⟨83086105788146077130525057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55390737192097384753683371 83086105788146077130525057)
        ·
          refine ⟨62314579341109557847893793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83086105788146077130525057 62314579341109557847893793)
          ·
            refine ⟨46735934505832168385920345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62314579341109557847893793 46735934505832168385920345)
            ·
              refine ⟨35051950879374126289440259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46735934505832168385920345 35051950879374126289440259)
              ·
                refine ⟨52577926319061189434160389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35051950879374126289440259 52577926319061189434160389)
                ·
                  refine ⟨9858361184823973018905073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52577926319061189434160389 9858361184823973018905073)
                  ·
                    refine ⟨7393770888617979764178805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9858361184823973018905073 7393770888617979764178805)
                    ·
                      refine ⟨693166020807935602891763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7393770888617979764178805 693166020807935602891763)
                      ·
                        rfl

theorem cell23_1349936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_1349936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349936 prefixEnd_1349936 := by exact prefixLift 1349936
  have htrace : WordTrace (prefixWord ++ tailWord_1349936) baseStart_1349936 baseEnd_1349936 := by
    simpa [prefixWord, tailWord_1349936, baseEnd_1349936] using wordTrace_append hprefix tailTrace_1349936
  have hstable : (prefixWord ++ tailWord_1349936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349936).length < 2 ^ (prefixWord ++ tailWord_1349936).sum := by decide
  have hdescent : baseEnd_1349936 < baseStart_1349936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1349997 : List Nat := [1, 5, 1, 1, 1, 2, 1, 3, 4, 2, 2]
def baseStart_1349997 : Nat := 118140960795 + 1349997 * 2 ^ 59
def prefixEnd_1349997 : Nat := 4983230072969 + 3 ^ 40 * 1349997 * 2
def baseEnd_1349997 : Nat := 693197343127859864228983

theorem tailTrace_1349997 : CollatzResearch.WordTrace tailWord_1349997 prefixEnd_1349997 693197343127859864228983 := by
  unfold tailWord_1349997
  simp only [CollatzResearch.WordTrace]
  refine ⟨49238435690198904976800245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32825623793465936651200163 49238435690198904976800245)
  ·
    refine ⟨4616103345956147341575023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49238435690198904976800245 4616103345956147341575023)
    ·
      refine ⟨6924155018934221012362535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4616103345956147341575023 6924155018934221012362535)
      ·
        refine ⟨10386232528401331518543803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6924155018934221012362535 10386232528401331518543803)
        ·
          refine ⟨15579348792601997277815705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10386232528401331518543803 15579348792601997277815705)
          ·
            refine ⟨11684511594451497958361779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15579348792601997277815705 11684511594451497958361779)
            ·
              refine ⟨17526767391677246937542669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11684511594451497958361779 17526767391677246937542669)
              ·
                refine ⟨6572537771878967601578501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17526767391677246937542669 6572537771878967601578501)
                ·
                  refine ⟨1232350832227306425295969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6572537771878967601578501 1232350832227306425295969)
                  ·
                    refine ⟨924263124170479818971977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1232350832227306425295969 924263124170479818971977)
                    ·
                      refine ⟨693197343127859864228983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 924263124170479818971977 693197343127859864228983)
                      ·
                        rfl

theorem cell23_1349997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 3, 4, 2, 2].length) (baseStart_1349997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1349997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1349997 prefixEnd_1349997 := by exact prefixLift 1349997
  have htrace : WordTrace (prefixWord ++ tailWord_1349997) baseStart_1349997 baseEnd_1349997 := by
    simpa [prefixWord, tailWord_1349997, baseEnd_1349997] using wordTrace_append hprefix tailTrace_1349997
  have hstable : (prefixWord ++ tailWord_1349997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1349997).length < 2 ^ (prefixWord ++ tailWord_1349997).sum := by decide
  have hdescent : baseEnd_1349997 < baseStart_1349997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1349997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350018 : List Nat := [3, 4, 2, 1, 2, 2, 1, 2, 1, 3, 2]
def baseStart_1350018 : Nat := 118140960795 + 1350018 * 2 ^ 59
def prefixEnd_1350018 : Nat := 4983230072969 + 3 ^ 40 * 1350018 * 2
def baseEnd_1350018 : Nat := 693208126221604282066387

theorem tailTrace_1350018 : CollatzResearch.WordTrace tailWord_1350018 prefixEnd_1350018 693208126221604282066387 := by
  unfold tailWord_1350018
  simp only [CollatzResearch.WordTrace]
  refine ⟨12309800405780706390828677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32826134415415217042209805 12309800405780706390828677)
  ·
    refine ⟨2308087576083882448280377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12309800405780706390828677 2308087576083882448280377)
    ·
      refine ⟨1731065682062911836210283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2308087576083882448280377 1731065682062911836210283)
      ·
        refine ⟨2596598523094367754315425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1731065682062911836210283 2596598523094367754315425)
        ·
          refine ⟨1947448892320775815736569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2596598523094367754315425 1947448892320775815736569)
          ·
            refine ⟨1460586669240581861802427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1947448892320775815736569 1460586669240581861802427)
            ·
              refine ⟨2190880003860872792703641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1460586669240581861802427 2190880003860872792703641)
              ·
                refine ⟨1643160002895654594527731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2190880003860872792703641 1643160002895654594527731)
                ·
                  refine ⟨2464740004343481891791597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1643160002895654594527731 2464740004343481891791597)
                  ·
                    refine ⟨924277501628805709421849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2464740004343481891791597 924277501628805709421849)
                    ·
                      refine ⟨693208126221604282066387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 924277501628805709421849 693208126221604282066387)
                      ·
                        rfl

theorem cell23_1350018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 1, 3, 2].length) (baseStart_1350018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350018 prefixEnd_1350018 := by exact prefixLift 1350018
  have htrace : WordTrace (prefixWord ++ tailWord_1350018) baseStart_1350018 baseEnd_1350018 := by
    simpa [prefixWord, tailWord_1350018, baseEnd_1350018] using wordTrace_append hprefix tailTrace_1350018
  have hstable : (prefixWord ++ tailWord_1350018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350018).length < 2 ^ (prefixWord ++ tailWord_1350018).sum := by decide
  have hdescent : baseEnd_1350018 < baseStart_1350018 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350050 : List Nat := [3, 3, 1, 2, 1, 1, 1, 4, 2, 5]
def baseStart_1350050 : Nat := 118140960795 + 1350050 * 2 ^ 59
def prefixEnd_1350050 : Nat := 4983230072969 + 3 ^ 40 * 1350050 * 2
def baseEnd_1350050 : Nat := 231074852534182718955413

theorem tailTrace_1350050 : CollatzResearch.WordTrace tailWord_1350050 prefixEnd_1350050 231074852534182718955413 := by
  unfold tailWord_1350050
  simp only [CollatzResearch.WordTrace]
  refine ⟨12310092189751723757119901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32826912506004596685653069 12310092189751723757119901)
  ·
    refine ⟨4616284571156896408919963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12310092189751723757119901 4616284571156896408919963)
    ·
      refine ⟨6924426856735344613379945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4616284571156896408919963 6924426856735344613379945)
      ·
        refine ⟨5193320142551508460034959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6924426856735344613379945 5193320142551508460034959)
        ·
          refine ⟨7789980213827262690052439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5193320142551508460034959 7789980213827262690052439)
          ·
            refine ⟨11684970320740894035078659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7789980213827262690052439 11684970320740894035078659)
            ·
              refine ⟨17527455481111341052617989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11684970320740894035078659 17527455481111341052617989)
              ·
                refine ⟨3286397902708376447365873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17527455481111341052617989 3286397902708376447365873)
                ·
                  refine ⟨2464798427031282335524405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3286397902708376447365873 2464798427031282335524405)
                  ·
                    refine ⟨231074852534182718955413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2464798427031282335524405 231074852534182718955413)
                    ·
                      rfl

theorem cell23_1350050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_1350050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350050 prefixEnd_1350050 := by exact prefixLift 1350050
  have htrace : WordTrace (prefixWord ++ tailWord_1350050) baseStart_1350050 baseEnd_1350050 := by
    simpa [prefixWord, tailWord_1350050, baseEnd_1350050] using wordTrace_append hprefix tailTrace_1350050
  have hstable : (prefixWord ++ tailWord_1350050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350050).length < 2 ^ (prefixWord ++ tailWord_1350050).sum := by decide
  have hdescent : baseEnd_1350050 < baseStart_1350050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350084 : List Nat := [2, 3, 3, 2, 2, 2, 1, 1, 2, 5]
def baseStart_1350084 : Nat := 118140960795 + 1350084 * 2 ^ 59
def prefixEnd_1350084 : Nat := 4983230072969 + 3 ^ 40 * 1350084 * 2
def baseEnd_1350084 : Nat := 231080671981600341280361

theorem tailTrace_1350084 : CollatzResearch.WordTrace tailWord_1350084 prefixEnd_1350084 231080671981600341280361 := by
  unfold tailWord_1350084
  simp only [CollatzResearch.WordTrace]
  refine ⟨24620804420441859417608653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32827739227255812556811537 24620804420441859417608653)
  ·
    refine ⟨9232801657665697281603245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24620804420441859417608653 9232801657665697281603245)
    ·
      refine ⟨3462300621624636480601217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9232801657665697281603245 3462300621624636480601217)
      ·
        refine ⟨2596725466218477360450913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3462300621624636480601217 2596725466218477360450913)
        ·
          refine ⟨1947544099663858020338185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2596725466218477360450913 1947544099663858020338185)
          ·
            refine ⟨1460658074747893515253639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1947544099663858020338185 1460658074747893515253639)
            ·
              refine ⟨2190987112121840272880459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1460658074747893515253639 2190987112121840272880459)
              ·
                refine ⟨3286480668182760409320689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190987112121840272880459 3286480668182760409320689)
                ·
                  refine ⟨2464860501137070306990517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3286480668182760409320689 2464860501137070306990517)
                  ·
                    refine ⟨231080671981600341280361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2464860501137070306990517 231080671981600341280361)
                    ·
                      rfl

theorem cell23_1350084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 2, 5].length) (baseStart_1350084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350084 prefixEnd_1350084 := by exact prefixLift 1350084
  have htrace : WordTrace (prefixWord ++ tailWord_1350084) baseStart_1350084 baseEnd_1350084 := by
    simpa [prefixWord, tailWord_1350084, baseEnd_1350084] using wordTrace_append hprefix tailTrace_1350084
  have hstable : (prefixWord ++ tailWord_1350084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350084).length < 2 ^ (prefixWord ++ tailWord_1350084).sum := by decide
  have hdescent : baseEnd_1350084 < baseStart_1350084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350087 : List Nat := [1, 1, 4, 1, 1, 6, 1, 1, 2, 1, 4]
def baseStart_1350087 : Nat := 118140960795 + 1350087 * 2 ^ 59
def prefixEnd_1350087 : Nat := 4983230072969 + 3 ^ 40 * 1350087 * 2
def baseEnd_1350087 : Nat := 693243556386764512103569

theorem tailTrace_1350087 : CollatzResearch.WordTrace tailWord_1350087 prefixEnd_1350087 693243556386764512103569 := by
  unfold tailWord_1350087
  simp only [CollatzResearch.WordTrace]
  refine ⟨49241718259872850347576515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32827812173248566898384343 49241718259872850347576515)
  ·
    refine ⟨73862577389809275521364773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49241718259872850347576515 73862577389809275521364773)
    ·
      refine ⟨13849233260589239160255895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 73862577389809275521364773 13849233260589239160255895)
      ·
        refine ⟨20773849890883858740383843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13849233260589239160255895 20773849890883858740383843)
        ·
          refine ⟨31160774836325788110575765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20773849890883858740383843 31160774836325788110575765)
          ·
            refine ⟨1460661320452771317683239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31160774836325788110575765 1460661320452771317683239)
            ·
              refine ⟨2190991980679156976524859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1460661320452771317683239 2190991980679156976524859)
              ·
                refine ⟨3286487971018735464787289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2190991980679156976524859 3286487971018735464787289)
                ·
                  refine ⟨2464865978264051598590467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3286487971018735464787289 2464865978264051598590467)
                  ·
                    refine ⟨3697298967396077397885701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2464865978264051598590467 3697298967396077397885701)
                    ·
                      refine ⟨693243556386764512103569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3697298967396077397885701 693243556386764512103569)
                      ·
                        rfl

theorem cell23_1350087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 1, 4].length) (baseStart_1350087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350087 prefixEnd_1350087 := by exact prefixLift 1350087
  have htrace : WordTrace (prefixWord ++ tailWord_1350087) baseStart_1350087 baseEnd_1350087 := by
    simpa [prefixWord, tailWord_1350087, baseEnd_1350087] using wordTrace_append hprefix tailTrace_1350087
  have hstable : (prefixWord ++ tailWord_1350087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350087).length < 2 ^ (prefixWord ++ tailWord_1350087).sum := by decide
  have hdescent : baseEnd_1350087 < baseStart_1350087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350090 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 1, 4, 3]
def baseStart_1350090 : Nat := 118140960795 + 1350090 * 2 ^ 59
def prefixEnd_1350090 : Nat := 4983230072969 + 3 ^ 40 * 1350090 * 2
def baseEnd_1350090 : Nat := 693245096828728000366055

theorem tailTrace_1350090 : CollatzResearch.WordTrace tailWord_1350090 prefixEnd_1350090 693245096828728000366055 := by
  unfold tailWord_1350090
  simp only [CollatzResearch.WordTrace]
  refine ⟨12310456919715495464983931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32827885119241321239957149 12310456919715495464983931)
  ·
    refine ⟨18465685379573243197475897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12310456919715495464983931 18465685379573243197475897)
    ·
      refine ⟨13849264034679932398106923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18465685379573243197475897 13849264034679932398106923)
      ·
        refine ⟨20773896052019898597160385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13849264034679932398106923 20773896052019898597160385)
        ·
          refine ⟨15580422039014923947870289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20773896052019898597160385 15580422039014923947870289)
          ·
            refine ⟨11685316529261192960902717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15580422039014923947870289 11685316529261192960902717)
            ·
              refine ⟨4381993698472947360338519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11685316529261192960902717 4381993698472947360338519)
              ·
                refine ⟨6572990547709421040507779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4381993698472947360338519 6572990547709421040507779)
                ·
                  refine ⟨9859485821564131560761669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6572990547709421040507779 9859485821564131560761669)
                  ·
                    refine ⟨1848653591543274667642813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9859485821564131560761669 1848653591543274667642813)
                    ·
                      refine ⟨693245096828728000366055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1848653591543274667642813 693245096828728000366055)
                      ·
                        rfl

theorem cell23_1350090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 1, 4, 3].length) (baseStart_1350090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350090 prefixEnd_1350090 := by exact prefixLift 1350090
  have htrace : WordTrace (prefixWord ++ tailWord_1350090) baseStart_1350090 baseEnd_1350090 := by
    simpa [prefixWord, tailWord_1350090, baseEnd_1350090] using wordTrace_append hprefix tailTrace_1350090
  have hstable : (prefixWord ++ tailWord_1350090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350090).length < 2 ^ (prefixWord ++ tailWord_1350090).sum := by decide
  have hdescent : baseEnd_1350090 < baseStart_1350090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350100 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 2, 1, 6]
def baseStart_1350100 : Nat := 118140960795 + 1350100 * 2 ^ 59
def prefixEnd_1350100 : Nat := 4983230072969 + 3 ^ 40 * 1350100 * 2
def baseEnd_1350100 : Nat := 693250231635272961241009

theorem tailTrace_1350100 : CollatzResearch.WordTrace tailWord_1350100 prefixEnd_1350100 693250231635272961241009 := by
  unfold tailWord_1350100
  simp only [CollatzResearch.WordTrace]
  refine ⟨24621096204412876783899877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32828128272550502378533169 24621096204412876783899877)
  ·
    refine ⟨4616455538327414396981227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24621096204412876783899877 4616455538327414396981227)
    ·
      refine ⟨6924683307491121595471841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4616455538327414396981227 6924683307491121595471841)
      ·
        refine ⟨5193512480618341196603881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6924683307491121595471841 5193512480618341196603881)
        ·
          refine ⟨3895134360463755897452911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5193512480618341196603881 3895134360463755897452911)
          ·
            refine ⟨5842701540695633846179367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3895134360463755897452911 5842701540695633846179367)
            ·
              refine ⟨8764052311043450769269051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5842701540695633846179367 8764052311043450769269051)
              ·
                refine ⟨13146078466565176153903577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8764052311043450769269051 13146078466565176153903577)
                ·
                  refine ⟨9859558849923882115427683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13146078466565176153903577 9859558849923882115427683)
                  ·
                    refine ⟨14789338274885823173141525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9859558849923882115427683 14789338274885823173141525)
                    ·
                      refine ⟨693250231635272961241009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14789338274885823173141525 693250231635272961241009)
                      ·
                        rfl

theorem cell23_1350100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_1350100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350100 prefixEnd_1350100 := by exact prefixLift 1350100
  have htrace : WordTrace (prefixWord ++ tailWord_1350100) baseStart_1350100 baseEnd_1350100 := by
    simpa [prefixWord, tailWord_1350100, baseEnd_1350100] using wordTrace_append hprefix tailTrace_1350100
  have hstable : (prefixWord ++ tailWord_1350100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350100).length < 2 ^ (prefixWord ++ tailWord_1350100).sum := by decide
  have hdescent : baseEnd_1350100 < baseStart_1350100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350113 : List Nat := [1, 2, 3, 1, 2, 2, 1, 1, 1, 1, 8]
def baseStart_1350113 : Nat := 118140960795 + 1350113 * 2 ^ 59
def prefixEnd_1350113 : Nat := 4983230072969 + 3 ^ 40 * 1350113 * 2
def baseEnd_1350113 : Nat := 693256906883781410378449

theorem tailTrace_1350113 : CollatzResearch.WordTrace tailWord_1350113 prefixEnd_1350113 693256906883781410378449 := by
  unfold tailWord_1350113
  simp only [CollatzResearch.WordTrace]
  refine ⟨49242666557778656788022993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32828444371852437858681995 49242666557778656788022993)
  ·
    refine ⟨36931999918333992591017245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49242666557778656788022993 36931999918333992591017245)
    ·
      refine ⟨13849499969375247221631467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36931999918333992591017245 13849499969375247221631467)
      ·
        refine ⟨20774249954062870832447201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13849499969375247221631467 20774249954062870832447201)
        ·
          refine ⟨15580687465547153124335401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20774249954062870832447201 15580687465547153124335401)
          ·
            refine ⟨11685515599160364843251551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15580687465547153124335401 11685515599160364843251551)
            ·
              refine ⟨17528273398740547264877327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11685515599160364843251551 17528273398740547264877327)
              ·
                refine ⟨26292410098110820897315991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17528273398740547264877327 26292410098110820897315991)
                ·
                  refine ⟨39438615147166231345973987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26292410098110820897315991 39438615147166231345973987)
                  ·
                    refine ⟨59157922720749347018960981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39438615147166231345973987 59157922720749347018960981)
                    ·
                      refine ⟨693256906883781410378449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 59157922720749347018960981 693256906883781410378449)
                      ·
                        rfl

theorem cell23_1350113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 1, 8].length) (baseStart_1350113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350113 prefixEnd_1350113 := by exact prefixLift 1350113
  have htrace : WordTrace (prefixWord ++ tailWord_1350113) baseStart_1350113 baseEnd_1350113 := by
    simpa [prefixWord, tailWord_1350113, baseEnd_1350113] using wordTrace_append hprefix tailTrace_1350113
  have hstable : (prefixWord ++ tailWord_1350113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350113).length < 2 ^ (prefixWord ++ tailWord_1350113).sum := by decide
  have hdescent : baseEnd_1350113 < baseStart_1350113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350137 : List Nat := [1, 2, 1, 3, 1, 2, 4, 2, 3, 1, 3]
def baseStart_1350137 : Nat := 118140960795 + 1350137 * 2 ^ 59
def prefixEnd_1350137 : Nat := 4983230072969 + 3 ^ 40 * 1350137 * 2
def baseEnd_1350137 : Nat := 693269230419489316478339

theorem tailTrace_1350137 : CollatzResearch.WordTrace tailWord_1350137 prefixEnd_1350137 693269230419489316478339 := by
  unfold tailWord_1350137
  simp only [CollatzResearch.WordTrace]
  refine ⟨49243541909691708886896665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32829027939794472591264443 49243541909691708886896665)
  ·
    refine ⟨36932656432268781665172499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49243541909691708886896665 36932656432268781665172499)
    ·
      refine ⟨55398984648403172497758749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36932656432268781665172499 55398984648403172497758749)
      ·
        refine ⟨20774619243151189686659531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55398984648403172497758749 20774619243151189686659531)
        ·
          refine ⟨31161928864726784529989297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20774619243151189686659531 31161928864726784529989297)
          ·
            refine ⟨23371446648545088397491973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31161928864726784529989297 23371446648545088397491973)
            ·
              refine ⟨4382146246602204074529745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23371446648545088397491973 4382146246602204074529745)
              ·
                refine ⟨3286609684951653055897309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4382146246602204074529745 3286609684951653055897309)
                ·
                  refine ⟨1232478631856869895961491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3286609684951653055897309 1232478631856869895961491)
                  ·
                    refine ⟨1848717947785304843942237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1232478631856869895961491 1848717947785304843942237)
                    ·
                      refine ⟨693269230419489316478339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1848717947785304843942237 693269230419489316478339)
                      ·
                        rfl

theorem cell23_1350137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 1, 3].length) (baseStart_1350137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350137 prefixEnd_1350137 := by exact prefixLift 1350137
  have htrace : WordTrace (prefixWord ++ tailWord_1350137) baseStart_1350137 baseEnd_1350137 := by
    simpa [prefixWord, tailWord_1350137, baseEnd_1350137] using wordTrace_append hprefix tailTrace_1350137
  have hstable : (prefixWord ++ tailWord_1350137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350137).length < 2 ^ (prefixWord ++ tailWord_1350137).sum := by decide
  have hdescent : baseEnd_1350137 < baseStart_1350137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350147 : List Nat := [1, 1, 1, 3, 2, 1, 4, 3, 2, 3, 2]
def baseStart_1350147 : Nat := 118140960795 + 1350147 * 2 ^ 59
def prefixEnd_1350147 : Nat := 4983230072969 + 3 ^ 40 * 1350147 * 2
def baseEnd_1350147 : Nat := 693274365226034277353293

theorem tailTrace_1350147 : CollatzResearch.WordTrace tailWord_1350147 prefixEnd_1350147 693274365226034277353293 := by
  unfold tailWord_1350147
  simp only [CollatzResearch.WordTrace]
  refine ⟨49243906639655480594760695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32829271093103653729840463 49243906639655480594760695)
  ·
    refine ⟨73865859959483220892141043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49243906639655480594760695 73865859959483220892141043)
    ·
      refine ⟨110798789939224831338211565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73865859959483220892141043 110798789939224831338211565)
      ·
        refine ⟨41549546227209311751829337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110798789939224831338211565 41549546227209311751829337)
        ·
          refine ⟨31162159670406983813872003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41549546227209311751829337 31162159670406983813872003)
          ·
            refine ⟨46743239505610475720808005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31162159670406983813872003 46743239505610475720808005)
            ·
              refine ⟨8764357407301964197651501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46743239505610475720808005 8764357407301964197651501)
              ·
                refine ⟨3286634027738236574119313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8764357407301964197651501 3286634027738236574119313)
                ·
                  refine ⟨2464975520803677430589485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3286634027738236574119313 2464975520803677430589485)
                  ·
                    refine ⟨924365820301379036471057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2464975520803677430589485 924365820301379036471057)
                    ·
                      refine ⟨693274365226034277353293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 924365820301379036471057 693274365226034277353293)
                      ·
                        rfl

theorem cell23_1350147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 3, 2].length) (baseStart_1350147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350147 prefixEnd_1350147 := by exact prefixLift 1350147
  have htrace : WordTrace (prefixWord ++ tailWord_1350147) baseStart_1350147 baseEnd_1350147 := by
    simpa [prefixWord, tailWord_1350147, baseEnd_1350147] using wordTrace_append hprefix tailTrace_1350147
  have hstable : (prefixWord ++ tailWord_1350147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350147).length < 2 ^ (prefixWord ++ tailWord_1350147).sum := by decide
  have hdescent : baseEnd_1350147 < baseStart_1350147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350194 : List Nat := [3, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2]
def baseStart_1350194 : Nat := 118140960795 + 1350194 * 2 ^ 59
def prefixEnd_1350194 : Nat := 4983230072969 + 3 ^ 40 * 1350194 * 2
def baseEnd_1350194 : Nat := 693298498816795593465577

theorem tailTrace_1350194 : CollatzResearch.WordTrace tailWord_1350194 prefixEnd_1350194 693298498816795593465577 := by
  unfold tailWord_1350194
  simp only [CollatzResearch.WordTrace]
  refine ⟨12311405217621301905430409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32830413913656805081147757 12311405217621301905430409)
  ·
    refine ⟨9233553913215976429072807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12311405217621301905430409 9233553913215976429072807)
    ·
      refine ⟨13850330869823964643609211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9233553913215976429072807 13850330869823964643609211)
      ·
        refine ⟨20775496304735946965413817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13850330869823964643609211 20775496304735946965413817)
        ·
          refine ⟨15581622228551960224060363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20775496304735946965413817 15581622228551960224060363)
          ·
            refine ⟨23372433342827940336090545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15581622228551960224060363 23372433342827940336090545)
            ·
              refine ⟨17529325007120955252067909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23372433342827940336090545 17529325007120955252067909)
              ·
                refine ⟨3286748438835179109762733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17529325007120955252067909 3286748438835179109762733)
                ·
                  refine ⟨1232530664563192166161025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3286748438835179109762733 1232530664563192166161025)
                  ·
                    refine ⟨924397998422394124620769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1232530664563192166161025 924397998422394124620769)
                    ·
                      refine ⟨693298498816795593465577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 924397998422394124620769 693298498816795593465577)
                      ·
                        rfl

theorem cell23_1350194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2].length) (baseStart_1350194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350194 prefixEnd_1350194 := by exact prefixLift 1350194
  have htrace : WordTrace (prefixWord ++ tailWord_1350194) baseStart_1350194 baseEnd_1350194 := by
    simpa [prefixWord, tailWord_1350194, baseEnd_1350194] using wordTrace_append hprefix tailTrace_1350194
  have hstable : (prefixWord ++ tailWord_1350194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350194).length < 2 ^ (prefixWord ++ tailWord_1350194).sum := by decide
  have hdescent : baseEnd_1350194 < baseStart_1350194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350197 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 3, 2, 3]
def baseStart_1350197 : Nat := 118140960795 + 1350197 * 2 ^ 59
def prefixEnd_1350197 : Nat := 4983230072969 + 3 ^ 40 * 1350197 * 2
def baseEnd_1350197 : Nat := 693300039258759081728063

theorem tailTrace_1350197 : CollatzResearch.WordTrace tailWord_1350197 prefixEnd_1350197 693300039258759081728063 := by
  unfold tailWord_1350197
  simp only [CollatzResearch.WordTrace]
  refine ⟨49245730289474339134080845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32830486859649559422720563 49245730289474339134080845)
  ·
    refine ⟨18467148858552877175280317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49245730289474339134080845 18467148858552877175280317)
    ·
      refine ⟨6925180821957328940730119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18467148858552877175280317 6925180821957328940730119)
      ·
        refine ⟨10387771232935993411095179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6925180821957328940730119 10387771232935993411095179)
        ·
          refine ⟨15581656849403990116642769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10387771232935993411095179 15581656849403990116642769)
          ·
            refine ⟨11686242637052992587482077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15581656849403990116642769 11686242637052992587482077)
            ·
              refine ⟨4382340988894872220305779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11686242637052992587482077 4382340988894872220305779)
              ·
                refine ⟨6573511483342308330458669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4382340988894872220305779 6573511483342308330458669)
                ·
                  refine ⟨2465066806253365623922001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6573511483342308330458669 2465066806253365623922001)
                  ·
                    refine ⟨1848800104690024217941501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2465066806253365623922001 1848800104690024217941501)
                    ·
                      refine ⟨693300039258759081728063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1848800104690024217941501 693300039258759081728063)
                      ·
                        rfl

theorem cell23_1350197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_1350197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350197 prefixEnd_1350197 := by exact prefixLift 1350197
  have htrace : WordTrace (prefixWord ++ tailWord_1350197) baseStart_1350197 baseEnd_1350197 := by
    simpa [prefixWord, tailWord_1350197, baseEnd_1350197] using wordTrace_append hprefix tailTrace_1350197
  have hstable : (prefixWord ++ tailWord_1350197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350197).length < 2 ^ (prefixWord ++ tailWord_1350197).sum := by decide
  have hdescent : baseEnd_1350197 < baseStart_1350197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350221 : List Nat := [1, 6, 1, 1, 2, 2, 2, 2, 2, 4]
def baseStart_1350221 : Nat := 118140960795 + 1350221 * 2 ^ 59
def prefixEnd_1350221 : Nat := 4983230072969 + 3 ^ 40 * 1350221 * 2
def baseEnd_1350221 : Nat := 231104120931488995942651

theorem tailTrace_1350221 : CollatzResearch.WordTrace tailWord_1350221 prefixEnd_1350221 231104120931488995942651 := by
  unfold tailWord_1350221
  simp only [CollatzResearch.WordTrace]
  refine ⟨49246605641387391232954517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32831070427591594155303011 49246605641387391232954517)
  ·
    refine ⟨2308434639440033964044743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49246605641387391232954517 2308434639440033964044743)
    ·
      refine ⟨3462651959160050946067115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2308434639440033964044743 3462651959160050946067115)
      ·
        refine ⟨5193977938740076419100673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3462651959160050946067115 5193977938740076419100673)
        ·
          refine ⟨3895483454055057314325505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5193977938740076419100673 3895483454055057314325505)
          ·
            refine ⟨2921612590541292985744129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3895483454055057314325505 2921612590541292985744129)
            ·
              refine ⟨2191209442905969739308097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2921612590541292985744129 2191209442905969739308097)
              ·
                refine ⟨1643407082179477304481073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2191209442905969739308097 1643407082179477304481073)
                ·
                  refine ⟨1232555311634607978360805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1643407082179477304481073 1232555311634607978360805)
                  ·
                    refine ⟨231104120931488995942651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1232555311634607978360805 231104120931488995942651)
                    ·
                      rfl

theorem cell23_1350221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_1350221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350221 prefixEnd_1350221 := by exact prefixLift 1350221
  have htrace : WordTrace (prefixWord ++ tailWord_1350221) baseStart_1350221 baseEnd_1350221 := by
    simpa [prefixWord, tailWord_1350221, baseEnd_1350221] using wordTrace_append hprefix tailTrace_1350221
  have hstable : (prefixWord ++ tailWord_1350221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350221).length < 2 ^ (prefixWord ++ tailWord_1350221).sum := by decide
  have hdescent : baseEnd_1350221 < baseStart_1350221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350228 : List Nat := [2, 4, 1, 1, 1, 4, 1, 4, 1, 2, 2]
def baseStart_1350228 : Nat := 118140960795 + 1350228 * 2 ^ 59
def prefixEnd_1350228 : Nat := 4983230072969 + 3 ^ 40 * 1350228 * 2
def baseEnd_1350228 : Nat := 693315957159048460440421

theorem tailTrace_1350228 : CollatzResearch.WordTrace tailWord_1350228 prefixEnd_1350228 693315957159048460440421 := by
  unfold tailWord_1350228
  simp only [CollatzResearch.WordTrace]
  refine ⟨24623430476181015714229669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32831240634908020952306225 24623430476181015714229669)
  ·
    refine ⟨4616893214283940446418063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24623430476181015714229669 4616893214283940446418063)
    ·
      refine ⟨6925339821425910669627095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4616893214283940446418063 6925339821425910669627095)
      ·
        refine ⟨10388009732138866004440643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6925339821425910669627095 10388009732138866004440643)
        ·
          refine ⟨15582014598208299006660965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10388009732138866004440643 15582014598208299006660965)
          ·
            refine ⟨2921627737164056063748931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15582014598208299006660965 2921627737164056063748931)
            ·
              refine ⟨4382441605746084095623397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2921627737164056063748931 4382441605746084095623397)
              ·
                refine ⟨821707801077390767929387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4382441605746084095623397 821707801077390767929387)
                ·
                  refine ⟨1232561701616086151894081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 821707801077390767929387 1232561701616086151894081)
                  ·
                    refine ⟨924421276212064613920561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1232561701616086151894081 924421276212064613920561)
                    ·
                      refine ⟨693315957159048460440421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 924421276212064613920561 693315957159048460440421)
                      ·
                        rfl

theorem cell23_1350228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 4, 1, 2, 2].length) (baseStart_1350228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350228 prefixEnd_1350228 := by exact prefixLift 1350228
  have htrace : WordTrace (prefixWord ++ tailWord_1350228) baseStart_1350228 baseEnd_1350228 := by
    simpa [prefixWord, tailWord_1350228, baseEnd_1350228] using wordTrace_append hprefix tailTrace_1350228
  have hstable : (prefixWord ++ tailWord_1350228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350228).length < 2 ^ (prefixWord ++ tailWord_1350228).sum := by decide
  have hdescent : baseEnd_1350228 < baseStart_1350228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350238 : List Nat := [4, 4, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_1350238 : Nat := 118140960795 + 1350238 * 2 ^ 59
def prefixEnd_1350238 : Nat := 4983230072969 + 3 ^ 40 * 1350238 * 2
def baseEnd_1350238 : Nat := 231107030655197807105125

theorem tailTrace_1350238 : CollatzResearch.WordTrace tailWord_1350238 prefixEnd_1350238 231107030655197807105125 := by
  unfold tailWord_1350238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6155903210290725392040421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32831483788217202090882245 6155903210290725392040421)
  ·
    refine ⟨1154231851929511011007579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6155903210290725392040421 1154231851929511011007579)
    ·
      refine ⟨1731347777894266516511369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1154231851929511011007579 1731347777894266516511369)
      ·
        refine ⟨1298510833420699887383527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1731347777894266516511369 1298510833420699887383527)
        ·
          refine ⟨1947766250131049831075291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1298510833420699887383527 1947766250131049831075291)
          ·
            refine ⟨2921649375196574746612937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1947766250131049831075291 2921649375196574746612937)
            ·
              refine ⟨2191237031397431059959703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2921649375196574746612937 2191237031397431059959703)
              ·
                refine ⟨3286855547096146589939555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2191237031397431059959703 3286855547096146589939555)
                ·
                  refine ⟨4930283320644219884909333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3286855547096146589939555 4930283320644219884909333)
                  ·
                    refine ⟨231107030655197807105125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4930283320644219884909333 231107030655197807105125)
                    ·
                      rfl

theorem cell23_1350238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_1350238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350238 prefixEnd_1350238 := by exact prefixLift 1350238
  have htrace : WordTrace (prefixWord ++ tailWord_1350238) baseStart_1350238 baseEnd_1350238 := by
    simpa [prefixWord, tailWord_1350238, baseEnd_1350238] using wordTrace_append hprefix tailTrace_1350238
  have hstable : (prefixWord ++ tailWord_1350238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350238).length < 2 ^ (prefixWord ++ tailWord_1350238).sum := by decide
  have hdescent : baseEnd_1350238 < baseStart_1350238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350244 : List Nat := [2, 3, 1, 1, 2, 2, 1, 5, 2, 1, 3]
def baseStart_1350244 : Nat := 118140960795 + 1350244 * 2 ^ 59
def prefixEnd_1350244 : Nat := 4983230072969 + 3 ^ 40 * 1350244 * 2
def baseEnd_1350244 : Nat := 693324172849520397840347

theorem tailTrace_1350244 : CollatzResearch.WordTrace tailWord_1350244 prefixEnd_1350244 693324172849520397840347 := by
  unfold tailWord_1350244
  simp only [CollatzResearch.WordTrace]
  refine ⟨24623722260152033080520893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32831629680202710774027857 24623722260152033080520893)
  ·
    refine ⟨9233895847557012405195335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24623722260152033080520893 9233895847557012405195335)
    ·
      refine ⟨13850843771335518607793003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9233895847557012405195335 13850843771335518607793003)
      ·
        refine ⟨20776265657003277911689505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13850843771335518607793003 20776265657003277911689505)
        ·
          refine ⟨15582199242752458433767129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20776265657003277911689505 15582199242752458433767129)
          ·
            refine ⟨11686649432064343825325347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15582199242752458433767129 11686649432064343825325347)
            ·
              refine ⟨17529974148096515737988021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11686649432064343825325347 17529974148096515737988021)
              ·
                refine ⟨1643435076384048350436377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17529974148096515737988021 1643435076384048350436377)
                ·
                  refine ⟨1232576307288036262827283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1643435076384048350436377 1232576307288036262827283)
                  ·
                    refine ⟨1848864460932054394240925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1232576307288036262827283 1848864460932054394240925)
                    ·
                      refine ⟨693324172849520397840347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1848864460932054394240925 693324172849520397840347)
                      ·
                        rfl

theorem cell23_1350244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 2, 1, 3].length) (baseStart_1350244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350244 prefixEnd_1350244 := by exact prefixLift 1350244
  have htrace : WordTrace (prefixWord ++ tailWord_1350244) baseStart_1350244 baseEnd_1350244 := by
    simpa [prefixWord, tailWord_1350244, baseEnd_1350244] using wordTrace_append hprefix tailTrace_1350244
  have hstable : (prefixWord ++ tailWord_1350244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350244).length < 2 ^ (prefixWord ++ tailWord_1350244).sum := by decide
  have hdescent : baseEnd_1350244 < baseStart_1350244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350267 : List Nat := [1, 1, 1, 1, 1, 4, 2, 3, 3, 4, 2]
def baseStart_1350267 : Nat := 118140960795 + 1350267 * 2 ^ 59
def prefixEnd_1350267 : Nat := 4983230072969 + 3 ^ 40 * 1350267 * 2
def baseEnd_1350267 : Nat := 693335982904573807852741

theorem tailTrace_1350267 : CollatzResearch.WordTrace tailWord_1350267 prefixEnd_1350267 693335982904573807852741 := by
  unfold tailWord_1350267
  simp only [CollatzResearch.WordTrace]
  refine ⟨49248283399220741089129055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32832188932813827392752703 49248283399220741089129055)
  ·
    refine ⟨73872425098831111633693583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49248283399220741089129055 73872425098831111633693583)
    ·
      refine ⟨110808637648246667450540375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73872425098831111633693583 110808637648246667450540375)
      ·
        refine ⟨166212956472370001175810563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110808637648246667450540375 166212956472370001175810563)
        ·
          refine ⟨249319434708555001763715845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166212956472370001175810563 249319434708555001763715845)
          ·
            refine ⟨46747394007854062830696721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 249319434708555001763715845 46747394007854062830696721)
            ·
              refine ⟨35060545505890547123022541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46747394007854062830696721 35060545505890547123022541)
              ·
                refine ⟨13147704564708955171133453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35060545505890547123022541 13147704564708955171133453)
                ·
                  refine ⟨4930389211765858189175045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13147704564708955171133453 4930389211765858189175045)
                  ·
                    refine ⟨924447977206098410470321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4930389211765858189175045 924447977206098410470321)
                    ·
                      refine ⟨693335982904573807852741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 924447977206098410470321 693335982904573807852741)
                      ·
                        rfl

theorem cell23_1350267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 4, 2].length) (baseStart_1350267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350267 prefixEnd_1350267 := by exact prefixLift 1350267
  have htrace : WordTrace (prefixWord ++ tailWord_1350267) baseStart_1350267 baseEnd_1350267 := by
    simpa [prefixWord, tailWord_1350267, baseEnd_1350267] using wordTrace_append hprefix tailTrace_1350267
  have hstable : (prefixWord ++ tailWord_1350267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350267).length < 2 ^ (prefixWord ++ tailWord_1350267).sum := by decide
  have hdescent : baseEnd_1350267 < baseStart_1350267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350301 : List Nat := [1, 4, 2, 1, 1, 1, 2, 5, 2, 2, 2]
def baseStart_1350301 : Nat := 118140960795 + 1350301 * 2 ^ 59
def prefixEnd_1350301 : Nat := 4983230072969 + 3 ^ 40 * 1350301 * 2
def baseEnd_1350301 : Nat := 693353441246826674827585

theorem tailTrace_1350301 : CollatzResearch.WordTrace tailWord_1350301 prefixEnd_1350301 693353441246826674827585 := by
  unfold tailWord_1350301
  simp only [CollatzResearch.WordTrace]
  refine ⟨49249523481097564895866757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32833015654065043263911171 49249523481097564895866757)
  ·
    refine ⟨9234285652705793417975017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49249523481097564895866757 9234285652705793417975017)
    ·
      refine ⟨6925714239529345063481263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9234285652705793417975017 6925714239529345063481263)
      ·
        refine ⟨10388571359294017595221895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6925714239529345063481263 10388571359294017595221895)
        ·
          refine ⟨15582857038941026392832843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10388571359294017595221895 15582857038941026392832843)
          ·
            refine ⟨23374285558411539589249265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15582857038941026392832843 23374285558411539589249265)
            ·
              refine ⟨17530714168808654691936949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23374285558411539589249265 17530714168808654691936949)
              ·
                refine ⟨1643504453325811377369089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17530714168808654691936949 1643504453325811377369089)
                ·
                  refine ⟨1232628339994358533026817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1643504453325811377369089 1232628339994358533026817)
                  ·
                    refine ⟨924471254995768899770113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1232628339994358533026817 924471254995768899770113)
                    ·
                      refine ⟨693353441246826674827585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 924471254995768899770113 693353441246826674827585)
                      ·
                        rfl

theorem cell23_1350301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 5, 2, 2, 2].length) (baseStart_1350301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350301 prefixEnd_1350301 := by exact prefixLift 1350301
  have htrace : WordTrace (prefixWord ++ tailWord_1350301) baseStart_1350301 baseEnd_1350301 := by
    simpa [prefixWord, tailWord_1350301, baseEnd_1350301] using wordTrace_append hprefix tailTrace_1350301
  have hstable : (prefixWord ++ tailWord_1350301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350301).length < 2 ^ (prefixWord ++ tailWord_1350301).sum := by decide
  have hdescent : baseEnd_1350301 < baseStart_1350301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350318 : List Nat := [4, 1, 4, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_1350318 : Nat := 118140960795 + 1350318 * 2 ^ 59
def prefixEnd_1350318 : Nat := 4983230072969 + 3 ^ 40 * 1350318 * 2
def baseEnd_1350318 : Nat := 693362170417953108315007

theorem tailTrace_1350318 : CollatzResearch.WordTrace tailWord_1350318 prefixEnd_1350318 693362170417953108315007 := by
  unfold tailWord_1350318
  simp only [CollatzResearch.WordTrace]
  refine ⟨6156267940254497099904451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32833429014690651199490405 6156267940254497099904451)
  ·
    refine ⟨9234401910381745649856677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6156267940254497099904451 9234401910381745649856677)
    ·
      refine ⟨1731450358196577309348127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9234401910381745649856677 1731450358196577309348127)
      ·
        refine ⟨2597175537294865964022191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1731450358196577309348127 2597175537294865964022191)
        ·
          refine ⟨3895763305942298946033287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2597175537294865964022191 3895763305942298946033287)
          ·
            refine ⟨5843644958913448419049931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3895763305942298946033287 5843644958913448419049931)
            ·
              refine ⟨8765467438370172628574897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5843644958913448419049931 8765467438370172628574897)
              ·
                refine ⟨6574100578777629471431173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8765467438370172628574897 6574100578777629471431173)
                ·
                  refine ⟨1232643858520805525893345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6574100578777629471431173 1232643858520805525893345)
                  ·
                    refine ⟨924482893890604144420009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1232643858520805525893345 924482893890604144420009)
                    ·
                      refine ⟨693362170417953108315007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 924482893890604144420009 693362170417953108315007)
                      ·
                        rfl

theorem cell23_1350318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_1350318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350318 prefixEnd_1350318 := by exact prefixLift 1350318
  have htrace : WordTrace (prefixWord ++ tailWord_1350318) baseStart_1350318 baseEnd_1350318 := by
    simpa [prefixWord, tailWord_1350318, baseEnd_1350318] using wordTrace_append hprefix tailTrace_1350318
  have hstable : (prefixWord ++ tailWord_1350318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350318).length < 2 ^ (prefixWord ++ tailWord_1350318).sum := by decide
  have hdescent : baseEnd_1350318 < baseStart_1350318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350377 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 1, 4, 3]
def baseStart_1350377 : Nat := 118140960795 + 1350377 * 2 ^ 59
def prefixEnd_1350377 : Nat := 4983230072969 + 3 ^ 40 * 1350377 * 2
def baseEnd_1350377 : Nat := 693392465776568377477235

theorem tailTrace_1350377 : CollatzResearch.WordTrace tailWord_1350377 prefixEnd_1350377 693392465776568377477235 := by
  unfold tailWord_1350377
  simp only [CollatzResearch.WordTrace]
  refine ⟨49252295428822229875633385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32834863619214819917088923 49252295428822229875633385)
  ·
    refine ⟨36939221571616672406725039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49252295428822229875633385 36939221571616672406725039)
    ·
      refine ⟨55408832357425008610087559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36939221571616672406725039 55408832357425008610087559)
      ·
        refine ⟨83113248536137512915131339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55408832357425008610087559 83113248536137512915131339)
        ·
          refine ⟨124669872804206269372697009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83113248536137512915131339 124669872804206269372697009)
          ·
            refine ⟨93502404603154702029522757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124669872804206269372697009 93502404603154702029522757)
            ·
              refine ⟨17531700863091506630535517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93502404603154702029522757 17531700863091506630535517)
              ·
                refine ⟨6574387823659314986450819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17531700863091506630535517 6574387823659314986450819)
                ·
                  refine ⟨9861581735488972479676229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6574387823659314986450819 9861581735488972479676229)
                  ·
                    refine ⟨1849046575404182339939293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9861581735488972479676229 1849046575404182339939293)
                    ·
                      refine ⟨693392465776568377477235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1849046575404182339939293 693392465776568377477235)
                      ·
                        rfl

theorem cell23_1350377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 4, 3].length) (baseStart_1350377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350377 prefixEnd_1350377 := by exact prefixLift 1350377
  have htrace : WordTrace (prefixWord ++ tailWord_1350377) baseStart_1350377 baseEnd_1350377 := by
    simpa [prefixWord, tailWord_1350377, baseEnd_1350377] using wordTrace_append hprefix tailTrace_1350377
  have hstable : (prefixWord ++ tailWord_1350377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350377).length < 2 ^ (prefixWord ++ tailWord_1350377).sum := by decide
  have hdescent : baseEnd_1350377 < baseStart_1350377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350394 : List Nat := [3, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3]
def baseStart_1350394 : Nat := 118140960795 + 1350394 * 2 ^ 59
def prefixEnd_1350394 : Nat := 4983230072969 + 3 ^ 40 * 1350394 * 2
def baseEnd_1350394 : Nat := 693401194947694810964657

theorem tailTrace_1350394 : CollatzResearch.WordTrace tailWord_1350394 prefixEnd_1350394 693401194947694810964657 := by
  unfold tailWord_1350394
  simp only [CollatzResearch.WordTrace]
  refine ⟨12313228867440160444750559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32835276979840427852668157 12313228867440160444750559)
  ·
    refine ⟨18469843301160240667125839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12313228867440160444750559 18469843301160240667125839)
    ·
      refine ⟨27704764951740361000688759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18469843301160240667125839 27704764951740361000688759)
      ·
        refine ⟨41557147427610541501033139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27704764951740361000688759 41557147427610541501033139)
        ·
          refine ⟨62335721141415812251549709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41557147427610541501033139 62335721141415812251549709)
          ·
            refine ⟨23375895428030929594331141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62335721141415812251549709 23375895428030929594331141)
            ·
              refine ⟨4382980392755799298937089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23375895428030929594331141 4382980392755799298937089)
              ·
                refine ⟨3287235294566849474202817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4382980392755799298937089 3287235294566849474202817)
                ·
                  refine ⟨2465426470925137105652113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3287235294566849474202817 2465426470925137105652113)
                  ·
                    refine ⟨1849069853193852829239085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2465426470925137105652113 1849069853193852829239085)
                    ·
                      refine ⟨693401194947694810964657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1849069853193852829239085 693401194947694810964657)
                      ·
                        rfl

theorem cell23_1350394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 2, 2, 3].length) (baseStart_1350394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350394 prefixEnd_1350394 := by exact prefixLift 1350394
  have htrace : WordTrace (prefixWord ++ tailWord_1350394) baseStart_1350394 baseEnd_1350394 := by
    simpa [prefixWord, tailWord_1350394, baseEnd_1350394] using wordTrace_append hprefix tailTrace_1350394
  have hstable : (prefixWord ++ tailWord_1350394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350394).length < 2 ^ (prefixWord ++ tailWord_1350394).sum := by decide
  have hdescent : baseEnd_1350394 < baseStart_1350394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350418 : List Nat := [3, 2, 4, 1, 2, 1, 1, 2, 3, 4]
def baseStart_1350418 : Nat := 118140960795 + 1350418 * 2 ^ 59
def prefixEnd_1350418 : Nat := 4983230072969 + 3 ^ 40 * 1350418 * 2
def baseEnd_1350418 : Nat := 231137839494467572354849

theorem tailTrace_1350418 : CollatzResearch.WordTrace tailWord_1350418 prefixEnd_1350418 231137839494467572354849 := by
  unfold tailWord_1350418
  simp only [CollatzResearch.WordTrace]
  refine ⟨12313447705418423469468977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32835860547782462585250605 12313447705418423469468977)
  ·
    refine ⟨9235085779063817602101733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12313447705418423469468977 9235085779063817602101733)
    ·
      refine ⟨1731578583574465800394075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9235085779063817602101733 1731578583574465800394075)
      ·
        refine ⟨2597367875361698700591113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1731578583574465800394075 2597367875361698700591113)
        ·
          refine ⟨1948025906521274025443335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2597367875361698700591113 1948025906521274025443335)
          ·
            refine ⟨2922038859781911038165003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1948025906521274025443335 2922038859781911038165003)
            ·
              refine ⟨4383058289672866557247505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2922038859781911038165003 4383058289672866557247505)
              ·
                refine ⟨3287293717254649917935629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4383058289672866557247505 3287293717254649917935629)
                ·
                  refine ⟨1232735143970493719225861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3287293717254649917935629 1232735143970493719225861)
                  ·
                    refine ⟨231137839494467572354849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1232735143970493719225861 231137839494467572354849)
                    ·
                      rfl

theorem cell23_1350418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_1350418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350418 prefixEnd_1350418 := by exact prefixLift 1350418
  have htrace : WordTrace (prefixWord ++ tailWord_1350418) baseStart_1350418 baseEnd_1350418 := by
    simpa [prefixWord, tailWord_1350418, baseEnd_1350418] using wordTrace_append hprefix tailTrace_1350418
  have hstable : (prefixWord ++ tailWord_1350418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350418).length < 2 ^ (prefixWord ++ tailWord_1350418).sum := by decide
  have hdescent : baseEnd_1350418 < baseStart_1350418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350444 : List Nat := [2, 2, 1, 1, 1, 4, 3, 3, 1, 5]
def baseStart_1350444 : Nat := 118140960795 + 1350444 * 2 ^ 59
def prefixEnd_1350444 : Nat := 4983230072969 + 3 ^ 40 * 1350444 * 2
def baseEnd_1350444 : Nat := 231142289660139871779809

theorem tailTrace_1350444 : CollatzResearch.WordTrace tailWord_1350444 prefixEnd_1350444 231142289660139871779809 := by
  unfold tailWord_1350444
  simp only [CollatzResearch.WordTrace]
  refine ⟨24627369559789750159161193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32836492746386333545548257 24627369559789750159161193)
  ·
    refine ⟨18470527169842312619370895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24627369559789750159161193 18470527169842312619370895)
    ·
      refine ⟨27705790754763468929056343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18470527169842312619370895 27705790754763468929056343)
      ·
        refine ⟨41558686132145203393584515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27705790754763468929056343 41558686132145203393584515)
        ·
          refine ⟨62338029198217805090376773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41558686132145203393584515 62338029198217805090376773)
          ·
            refine ⟨11688380474665838454445645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62338029198217805090376773 11688380474665838454445645)
            ·
              refine ⟨4383142677999689420417117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11688380474665838454445645 4383142677999689420417117)
              ·
                refine ⟨1643678504249883532656419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4383142677999689420417117 1643678504249883532656419)
                ·
                  refine ⟨2465517756374825298984629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1643678504249883532656419 2465517756374825298984629)
                  ·
                    refine ⟨231142289660139871779809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2465517756374825298984629 231142289660139871779809)
                    ·
                      rfl

theorem cell23_1350444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 5].length) (baseStart_1350444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350444 prefixEnd_1350444 := by exact prefixLift 1350444
  have htrace : WordTrace (prefixWord ++ tailWord_1350444) baseStart_1350444 baseEnd_1350444 := by
    simpa [prefixWord, tailWord_1350444, baseEnd_1350444] using wordTrace_append hprefix tailTrace_1350444
  have hstable : (prefixWord ++ tailWord_1350444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350444).length < 2 ^ (prefixWord ++ tailWord_1350444).sum := by decide
  have hdescent : baseEnd_1350444 < baseStart_1350444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350458 : List Nat := [3, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3]
def baseStart_1350458 : Nat := 118140960795 + 1350458 * 2 ^ 59
def prefixEnd_1350458 : Nat := 4983230072969 + 3 ^ 40 * 1350458 * 2
def baseEnd_1350458 : Nat := 693434057709582560564363

theorem tailTrace_1350458 : CollatzResearch.WordTrace tailWord_1350458 prefixEnd_1350458 693434057709582560564363 := by
  unfold tailWord_1350458
  simp only [CollatzResearch.WordTrace]
  refine ⟨12313812435382195177333007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32836833161019187139554685 12313812435382195177333007)
  ·
    refine ⟨18470718653073292765999511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12313812435382195177333007 18470718653073292765999511)
    ·
      refine ⟨27706077979609939148999267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18470718653073292765999511 27706077979609939148999267)
      ·
        refine ⟨41559116969414908723498901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27706077979609939148999267 41559116969414908723498901)
        ·
          refine ⟨1948083607941323846414011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 41559116969414908723498901 1948083607941323846414011)
          ·
            refine ⟨2922125411911985769621017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1948083607941323846414011 2922125411911985769621017)
            ·
              refine ⟨2191594058933989327215763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2922125411911985769621017 2191594058933989327215763)
              ·
                refine ⟨3287391088400983990823645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2191594058933989327215763 3287391088400983990823645)
                ·
                  refine ⟨1232771658150368996558867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3287391088400983990823645 1232771658150368996558867)
                  ·
                    refine ⟨1849157487225553494838301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1232771658150368996558867 1849157487225553494838301)
                    ·
                      refine ⟨693434057709582560564363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1849157487225553494838301 693434057709582560564363)
                      ·
                        rfl

theorem cell23_1350458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 3, 1, 3].length) (baseStart_1350458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350458 prefixEnd_1350458 := by exact prefixLift 1350458
  have htrace : WordTrace (prefixWord ++ tailWord_1350458) baseStart_1350458 baseEnd_1350458 := by
    simpa [prefixWord, tailWord_1350458, baseEnd_1350458] using wordTrace_append hprefix tailTrace_1350458
  have hstable : (prefixWord ++ tailWord_1350458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350458).length < 2 ^ (prefixWord ++ tailWord_1350458).sum := by decide
  have hdescent : baseEnd_1350458 < baseStart_1350458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350492 : List Nat := [2, 2, 4, 2, 1, 3, 1, 3, 1, 1, 3]
def baseStart_1350492 : Nat := 118140960795 + 1350492 * 2 ^ 59
def prefixEnd_1350492 : Nat := 4983230072969 + 3 ^ 40 * 1350492 * 2
def baseEnd_1350492 : Nat := 693451516051835427539207

theorem tailTrace_1350492 : CollatzResearch.WordTrace tailWord_1350492 prefixEnd_1350492 693451516051835427539207 := by
  unfold tailWord_1350492
  simp only [CollatzResearch.WordTrace]
  refine ⟨24628244911702802258034865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32837659882270403010713153 24628244911702802258034865)
  ·
    refine ⟨18471183683777101693526149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24628244911702802258034865 18471183683777101693526149)
    ·
      refine ⟨3463346940708206567536153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18471183683777101693526149 3463346940708206567536153)
      ·
        refine ⟨2597510205531154925652115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3463346940708206567536153 2597510205531154925652115)
        ·
          refine ⟨3896265308296732388478173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2597510205531154925652115 3896265308296732388478173)
          ·
            refine ⟨1461099490611274645679315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3896265308296732388478173 1461099490611274645679315)
            ·
              refine ⟨2191649235916911968518973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1461099490611274645679315 2191649235916911968518973)
              ·
                refine ⟨821868463468841988194615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2191649235916911968518973 821868463468841988194615)
                ·
                  refine ⟨1232802695203262982291923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 821868463468841988194615 1232802695203262982291923)
                  ·
                    refine ⟨1849204042804894473437885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1232802695203262982291923 1849204042804894473437885)
                    ·
                      refine ⟨693451516051835427539207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1849204042804894473437885 693451516051835427539207)
                      ·
                        rfl

theorem cell23_1350492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_1350492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350492 prefixEnd_1350492 := by exact prefixLift 1350492
  have htrace : WordTrace (prefixWord ++ tailWord_1350492) baseStart_1350492 baseEnd_1350492 := by
    simpa [prefixWord, tailWord_1350492, baseEnd_1350492] using wordTrace_append hprefix tailTrace_1350492
  have hstable : (prefixWord ++ tailWord_1350492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350492).length < 2 ^ (prefixWord ++ tailWord_1350492).sum := by decide
  have hdescent : baseEnd_1350492 < baseStart_1350492 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350501 : List Nat := [1, 3, 1, 3, 1, 1, 4, 3, 1, 2, 3]
def baseStart_1350501 : Nat := 118140960795 + 1350501 * 2 ^ 59
def prefixEnd_1350501 : Nat := 4983230072969 + 3 ^ 40 * 1350501 * 2
def baseEnd_1350501 : Nat := 693456137377725892326665

theorem tailTrace_1350501 : CollatzResearch.WordTrace tailWord_1350501 prefixEnd_1350501 693456137377725892326665 := by
  unfold tailWord_1350501
  simp only [CollatzResearch.WordTrace]
  refine ⟨49256818080372999053147357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32837878720248666035431571 49256818080372999053147357)
  ·
    refine ⟨18471306780139874644930259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49256818080372999053147357 18471306780139874644930259)
    ·
      refine ⟨27706960170209811967395389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18471306780139874644930259 27706960170209811967395389)
      ·
        refine ⟨10390110063828679487773271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27706960170209811967395389 10390110063828679487773271)
        ·
          refine ⟨15585165095743019231659907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10390110063828679487773271 15585165095743019231659907)
          ·
            refine ⟨23377747643614528847489861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15585165095743019231659907 23377747643614528847489861)
            ·
              refine ⟨4383327683177724158904349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23377747643614528847489861 4383327683177724158904349)
              ·
                refine ⟨1643747881191646559589131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4383327683177724158904349 1643747881191646559589131)
                ·
                  refine ⟨2465621821787469839383697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1643747881191646559589131 2465621821787469839383697)
                  ·
                    refine ⟨1849216366340602379537773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2465621821787469839383697 1849216366340602379537773)
                    ·
                      refine ⟨693456137377725892326665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1849216366340602379537773 693456137377725892326665)
                      ·
                        rfl

theorem cell23_1350501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 2, 3].length) (baseStart_1350501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350501 prefixEnd_1350501 := by exact prefixLift 1350501
  have htrace : WordTrace (prefixWord ++ tailWord_1350501) baseStart_1350501 baseEnd_1350501 := by
    simpa [prefixWord, tailWord_1350501, baseEnd_1350501] using wordTrace_append hprefix tailTrace_1350501
  have hstable : (prefixWord ++ tailWord_1350501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350501).length < 2 ^ (prefixWord ++ tailWord_1350501).sum := by decide
  have hdescent : baseEnd_1350501 < baseStart_1350501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350504 : List Nat := [2, 1, 4, 2, 1, 4, 9]
def baseStart_1350504 : Nat := 118140960795 + 1350504 * 2 ^ 59
def prefixEnd_1350504 : Nat := 4983230072969 + 3 ^ 40 * 1350504 * 2
def baseEnd_1350504 : Nat := 8561205899008510871471

theorem tailTrace_1350504 : CollatzResearch.WordTrace tailWord_1350504 prefixEnd_1350504 8561205899008510871471 := by
  unfold tailWord_1350504
  simp only [CollatzResearch.WordTrace]
  refine ⟨24628463749681065282753283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32837951666241420377004377 24628463749681065282753283)
  ·
    refine ⟨36942695624521597924129925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24628463749681065282753283 36942695624521597924129925)
    ·
      refine ⟨6926755429597799610774361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36942695624521597924129925 6926755429597799610774361)
      ·
        refine ⟨5195066572198349708080771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6926755429597799610774361 5195066572198349708080771)
        ·
          refine ⟨7792599858297524562121157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5195066572198349708080771 7792599858297524562121157)
          ·
            refine ⟨1461112473430785855397717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7792599858297524562121157 1461112473430785855397717)
            ·
              refine ⟨8561205899008510871471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1461112473430785855397717 8561205899008510871471)
              ·
                rfl

theorem cell23_1350504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 9].length) (baseStart_1350504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350504 prefixEnd_1350504 := by exact prefixLift 1350504
  have htrace : WordTrace (prefixWord ++ tailWord_1350504) baseStart_1350504 baseEnd_1350504 := by
    simpa [prefixWord, tailWord_1350504, baseEnd_1350504] using wordTrace_append hprefix tailTrace_1350504
  have hstable : (prefixWord ++ tailWord_1350504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350504).length < 2 ^ (prefixWord ++ tailWord_1350504).sum := by decide
  have hdescent : baseEnd_1350504 < baseStart_1350504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350547 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 3, 8]
def baseStart_1350547 : Nat := 118140960795 + 1350547 * 2 ^ 59
def prefixEnd_1350547 : Nat := 4983230072969 + 3 ^ 40 * 1350547 * 2
def baseEnd_1350547 : Nat := 231159919162610904117151

theorem tailTrace_1350547 : CollatzResearch.WordTrace tailWord_1350547 prefixEnd_1350547 231159919162610904117151 := by
  unfold tailWord_1350547
  simp only [CollatzResearch.WordTrace]
  refine ⟨49258495838206348909321895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32838997225470899272881263 49258495838206348909321895)
  ·
    refine ⟨73887743757309523363982843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49258495838206348909321895 73887743757309523363982843)
    ·
      refine ⟨110831615635964285045974265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73887743757309523363982843 110831615635964285045974265)
      ·
        refine ⟨83123711726973213784480699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110831615635964285045974265 83123711726973213784480699)
        ·
          refine ⟨124685567590459820676721049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83123711726973213784480699 124685567590459820676721049)
          ·
            refine ⟨93514175692844865507540787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124685567590459820676721049 93514175692844865507540787)
            ·
              refine ⟨140271263539267298261311181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93514175692844865507540787 140271263539267298261311181)
              ·
                refine ⟨52601723827225236847991693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140271263539267298261311181 52601723827225236847991693)
                ·
                  refine ⟨19725646435209463817996885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52601723827225236847991693 19725646435209463817996885)
                  ·
                    refine ⟨231159919162610904117151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19725646435209463817996885 231159919162610904117151)
                    ·
                      rfl

theorem cell23_1350547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 8].length) (baseStart_1350547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350547 prefixEnd_1350547 := by exact prefixLift 1350547
  have htrace : WordTrace (prefixWord ++ tailWord_1350547) baseStart_1350547 baseEnd_1350547 := by
    simpa [prefixWord, tailWord_1350547, baseEnd_1350547] using wordTrace_append hprefix tailTrace_1350547
  have hstable : (prefixWord ++ tailWord_1350547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350547).length < 2 ^ (prefixWord ++ tailWord_1350547).sum := by decide
  have hdescent : baseEnd_1350547 < baseStart_1350547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350564 : List Nat := [2, 3, 1, 2, 1, 2, 2, 2, 2, 6]
def baseStart_1350564 : Nat := 118140960795 + 1350564 * 2 ^ 59
def prefixEnd_1350564 : Nat := 4983230072969 + 3 ^ 40 * 1350564 * 2
def baseEnd_1350564 : Nat := 231162828886319715279625

theorem tailTrace_1350564 : CollatzResearch.WordTrace tailWord_1350564 prefixEnd_1350564 231162828886319715279625 := by
  unfold tailWord_1350564
  simp only [CollatzResearch.WordTrace]
  refine ⟨24629557939572380406345373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32839410586096507208460497 24629557939572380406345373)
  ·
    refine ⟨9236084227339642652379515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24629557939572380406345373 9236084227339642652379515)
    ·
      refine ⟨13854126341009463978569273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9236084227339642652379515 13854126341009463978569273)
      ·
        refine ⟨10390594755757097983926955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13854126341009463978569273 10390594755757097983926955)
        ·
          refine ⟨15585892133635646975890433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10390594755757097983926955 15585892133635646975890433)
          ·
            refine ⟨11689419100226735231917825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15585892133635646975890433 11689419100226735231917825)
            ·
              refine ⟨8767064325170051423938369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11689419100226735231917825 8767064325170051423938369)
              ·
                refine ⟨6575298243877538567953777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8767064325170051423938369 6575298243877538567953777)
                ·
                  refine ⟨4931473682908153925965333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6575298243877538567953777 4931473682908153925965333)
                  ·
                    refine ⟨231162828886319715279625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4931473682908153925965333 231162828886319715279625)
                    ·
                      rfl

theorem cell23_1350564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 2, 2, 6].length) (baseStart_1350564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350564 prefixEnd_1350564 := by exact prefixLift 1350564
  have htrace : WordTrace (prefixWord ++ tailWord_1350564) baseStart_1350564 baseEnd_1350564 := by
    simpa [prefixWord, tailWord_1350564, baseEnd_1350564] using wordTrace_append hprefix tailTrace_1350564
  have hstable : (prefixWord ++ tailWord_1350564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350564).length < 2 ^ (prefixWord ++ tailWord_1350564).sum := by decide
  have hdescent : baseEnd_1350564 < baseStart_1350564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350584 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 1, 4, 4]
def baseStart_1350584 : Nat := 118140960795 + 1350584 * 2 ^ 59
def prefixEnd_1350584 : Nat := 4983230072969 + 3 ^ 40 * 1350584 * 2
def baseEnd_1350584 : Nat := 693498756272049067588783

theorem tailTrace_1350584 : CollatzResearch.WordTrace tailWord_1350584 prefixEnd_1350584 693498756272049067588783 := by
  unfold tailWord_1350584
  simp only [CollatzResearch.WordTrace]
  refine ⟨24629922669536152114209403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32839896892714869485612537 24629922669536152114209403)
  ·
    refine ⟨36944884004304228171314105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24629922669536152114209403 36944884004304228171314105)
    ·
      refine ⟨27708663003228171128485579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36944884004304228171314105 27708663003228171128485579)
      ·
        refine ⟨41562994504842256692728369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27708663003228171128485579 41562994504842256692728369)
        ·
          refine ⟨31172245878631692519546277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41562994504842256692728369 31172245878631692519546277)
          ·
            refine ⟨5844796102243442347414927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31172245878631692519546277 5844796102243442347414927)
            ·
              refine ⟨8767194153365163521122391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5844796102243442347414927 8767194153365163521122391)
              ·
                refine ⟨13150791230047745281683587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8767194153365163521122391 13150791230047745281683587)
                ·
                  refine ⟨19726186845071617922525381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13150791230047745281683587 19726186845071617922525381)
                  ·
                    refine ⟨3698660033450928360473509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19726186845071617922525381 3698660033450928360473509)
                    ·
                      refine ⟨693498756272049067588783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3698660033450928360473509 693498756272049067588783)
                      ·
                        rfl

theorem cell23_1350584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 1, 4, 4].length) (baseStart_1350584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350584 prefixEnd_1350584 := by exact prefixLift 1350584
  have htrace : WordTrace (prefixWord ++ tailWord_1350584) baseStart_1350584 baseEnd_1350584 := by
    simpa [prefixWord, tailWord_1350584, baseEnd_1350584] using wordTrace_append hprefix tailTrace_1350584
  have hstable : (prefixWord ++ tailWord_1350584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350584).length < 2 ^ (prefixWord ++ tailWord_1350584).sum := by decide
  have hdescent : baseEnd_1350584 < baseStart_1350584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350661 : List Nat := [1, 3, 1, 1, 2, 3, 2, 3, 2, 1, 4]
def baseStart_1350661 : Nat := 118140960795 + 1350661 * 2 ^ 59
def prefixEnd_1350661 : Nat := 4983230072969 + 3 ^ 40 * 1350661 * 2
def baseEnd_1350661 : Nat := 693538294282445266325929

theorem tailTrace_1350661 : CollatzResearch.WordTrace tailWord_1350661 prefixEnd_1350661 693538294282445266325929 := by
  unfold tailWord_1350661
  simp only [CollatzResearch.WordTrace]
  refine ⟨49262653759793346378971837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32841769173195564252647891 49262653759793346378971837)
  ·
    refine ⟨18473495159922504892114439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49262653759793346378971837 18473495159922504892114439)
    ·
      refine ⟨27710242739883757338171659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18473495159922504892114439 27710242739883757338171659)
      ·
        refine ⟨41565364109825636007257489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27710242739883757338171659 41565364109825636007257489)
        ·
          refine ⟨31174023082369227005443117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41565364109825636007257489 31174023082369227005443117)
          ·
            refine ⟨11690258655888460127041169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31174023082369227005443117 11690258655888460127041169)
            ·
              refine ⟨8767693991916345095280877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11690258655888460127041169 8767693991916345095280877)
              ·
                refine ⟨3287885246968629410730329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8767693991916345095280877 3287885246968629410730329)
                ·
                  refine ⟨2465913935226472058047747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3287885246968629410730329 2465913935226472058047747)
                  ·
                    refine ⟨3698870902839708087071621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2465913935226472058047747 3698870902839708087071621)
                    ·
                      refine ⟨693538294282445266325929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3698870902839708087071621 693538294282445266325929)
                      ·
                        rfl

theorem cell23_1350661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_1350661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350661 prefixEnd_1350661 := by exact prefixLift 1350661
  have htrace : WordTrace (prefixWord ++ tailWord_1350661) baseStart_1350661 baseEnd_1350661 := by
    simpa [prefixWord, tailWord_1350661, baseEnd_1350661] using wordTrace_append hprefix tailTrace_1350661
  have hstable : (prefixWord ++ tailWord_1350661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350661).length < 2 ^ (prefixWord ++ tailWord_1350661).sum := by decide
  have hdescent : baseEnd_1350661 < baseStart_1350661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350681 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 4, 2, 3]
def baseStart_1350681 : Nat := 118140960795 + 1350681 * 2 ^ 59
def prefixEnd_1350681 : Nat := 4983230072969 + 3 ^ 40 * 1350681 * 2
def baseEnd_1350681 : Nat := 693548563895535188075837

theorem tailTrace_1350681 : CollatzResearch.WordTrace tailWord_1350681 prefixEnd_1350681 693548563895535188075837 := by
  unfold tailWord_1350681
  simp only [CollatzResearch.WordTrace]
  refine ⟨49263383219720889794699897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32842255479813926529799931 49263383219720889794699897)
  ·
    refine ⟨36947537414790667346024923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49263383219720889794699897 36947537414790667346024923)
    ·
      refine ⟨55421306122186001019037385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36947537414790667346024923 55421306122186001019037385)
      ·
        refine ⟨41565979591639500764278039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55421306122186001019037385 41565979591639500764278039)
        ·
          refine ⟨62348969387459251146417059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41565979591639500764278039 62348969387459251146417059)
          ·
            refine ⟨93523454081188876719625589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62348969387459251146417059 93523454081188876719625589)
            ·
              refine ⟨8767823820111457192464899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93523454081188876719625589 8767823820111457192464899)
              ·
                refine ⟨13151735730167185788697349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8767823820111457192464899 13151735730167185788697349)
                ·
                  refine ⟨2465950449406347335380753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13151735730167185788697349 2465950449406347335380753)
                  ·
                    refine ⟨1849462837054760501535565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2465950449406347335380753 1849462837054760501535565)
                    ·
                      refine ⟨693548563895535188075837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1849462837054760501535565 693548563895535188075837)
                      ·
                        rfl

theorem cell23_1350681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 2, 3].length) (baseStart_1350681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350681 prefixEnd_1350681 := by exact prefixLift 1350681
  have htrace : WordTrace (prefixWord ++ tailWord_1350681) baseStart_1350681 baseEnd_1350681 := by
    simpa [prefixWord, tailWord_1350681, baseEnd_1350681] using wordTrace_append hprefix tailTrace_1350681
  have hstable : (prefixWord ++ tailWord_1350681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350681).length < 2 ^ (prefixWord ++ tailWord_1350681).sum := by decide
  have hdescent : baseEnd_1350681 < baseStart_1350681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350751 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 4]
def baseStart_1350751 : Nat := 118140960795 + 1350751 * 2 ^ 59
def prefixEnd_1350751 : Nat := 4983230072969 + 3 ^ 40 * 1350751 * 2
def baseEnd_1350751 : Nat := 693584507541349914200515

theorem tailTrace_1350751 : CollatzResearch.WordTrace tailWord_1350751 prefixEnd_1350751 693584507541349914200515 := by
  unfold tailWord_1350751
  simp only [CollatzResearch.WordTrace]
  refine ⟨49265936329467291749748107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32843957552978194499832071 49265936329467291749748107)
  ·
    refine ⟨73898904494200937624622161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49265936329467291749748107 73898904494200937624622161)
    ·
      refine ⟨55424178370650703218466621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73898904494200937624622161 55424178370650703218466621)
      ·
        refine ⟨20784066888994013706924983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55424178370650703218466621 20784066888994013706924983)
        ·
          refine ⟨31176100333491020560387475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20784066888994013706924983 31176100333491020560387475)
          ·
            refine ⟨46764150500236530840581213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31176100333491020560387475 46764150500236530840581213)
            ·
              refine ⟨17536556437588699065217955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46764150500236530840581213 17536556437588699065217955)
              ·
                refine ⟨26304834656383048597826933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17536556437588699065217955 26304834656383048597826933)
                ·
                  refine ⟨2466078249035910806046275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26304834656383048597826933 2466078249035910806046275)
                  ·
                    refine ⟨3699117373553866209069413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2466078249035910806046275 3699117373553866209069413)
                    ·
                      refine ⟨693584507541349914200515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3699117373553866209069413 693584507541349914200515)
                      ·
                        rfl

theorem cell23_1350751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_1350751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350751 prefixEnd_1350751 := by exact prefixLift 1350751
  have htrace : WordTrace (prefixWord ++ tailWord_1350751) baseStart_1350751 baseEnd_1350751 := by
    simpa [prefixWord, tailWord_1350751, baseEnd_1350751] using wordTrace_append hprefix tailTrace_1350751
  have hstable : (prefixWord ++ tailWord_1350751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350751).length < 2 ^ (prefixWord ++ tailWord_1350751).sum := by decide
  have hdescent : baseEnd_1350751 < baseStart_1350751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350761 : List Nat := [1, 2, 1, 1, 1, 6, 1, 3, 1, 6]
def baseStart_1350761 : Nat := 118140960795 + 1350761 * 2 ^ 59
def prefixEnd_1350761 : Nat := 4983230072969 + 3 ^ 40 * 1350761 * 2
def baseEnd_1350761 : Nat := 231196547449298291691823

theorem tailTrace_1350761 : CollatzResearch.WordTrace tailWord_1350761 prefixEnd_1350761 231196547449298291691823 := by
  unfold tailWord_1350761
  simp only [CollatzResearch.WordTrace]
  refine ⟨49266301059431063457612137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32844200706287375638408091 49266301059431063457612137)
  ·
    refine ⟨36949725794573297593209103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49266301059431063457612137 36949725794573297593209103)
    ·
      refine ⟨55424588691859946389813655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36949725794573297593209103 55424588691859946389813655)
      ·
        refine ⟨83136883037789919584720483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55424588691859946389813655 83136883037789919584720483)
        ·
          refine ⟨124705324556684879377080725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83136883037789919584720483 124705324556684879377080725)
          ·
            refine ⟨5845562088594603720800659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 124705324556684879377080725 5845562088594603720800659)
            ·
              refine ⟨8768343132891905581200989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5845562088594603720800659 8768343132891905581200989)
              ·
                refine ⟨3288128674834464592950371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8768343132891905581200989 3288128674834464592950371)
                ·
                  refine ⟨4932193012251696889425557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3288128674834464592950371 4932193012251696889425557)
                  ·
                    refine ⟨231196547449298291691823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4932193012251696889425557 231196547449298291691823)
                    ·
                      rfl

theorem cell23_1350761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 6].length) (baseStart_1350761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350761 prefixEnd_1350761 := by exact prefixLift 1350761
  have htrace : WordTrace (prefixWord ++ tailWord_1350761) baseStart_1350761 baseEnd_1350761 := by
    simpa [prefixWord, tailWord_1350761, baseEnd_1350761] using wordTrace_append hprefix tailTrace_1350761
  have hstable : (prefixWord ++ tailWord_1350761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350761).length < 2 ^ (prefixWord ++ tailWord_1350761).sum := by decide
  have hdescent : baseEnd_1350761 < baseStart_1350761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350768 : List Nat := [2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 4]
def baseStart_1350768 : Nat := 118140960795 + 1350768 * 2 ^ 59
def prefixEnd_1350768 : Nat := 4983230072969 + 3 ^ 40 * 1350768 * 2
def baseEnd_1350768 : Nat := 693593236712476347687937

theorem tailTrace_1350768 : CollatzResearch.WordTrace tailWord_1350768 prefixEnd_1350768 693593236712476347687937 := by
  unfold tailWord_1350768
  simp only [CollatzResearch.WordTrace]
  refine ⟨24633278185202851826558479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32844370913603802435411305 24633278185202851826558479)
  ·
    refine ⟨36949917277804277739837719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24633278185202851826558479 36949917277804277739837719)
    ·
      refine ⟨55424875916706416609756579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36949917277804277739837719 55424875916706416609756579)
      ·
        refine ⟨83137313875059624914634869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55424875916706416609756579 83137313875059624914634869)
        ·
          refine ⟨7794123175786839835747019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83137313875059624914634869 7794123175786839835747019)
          ·
            refine ⟨11691184763680259753620529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7794123175786839835747019 11691184763680259753620529)
            ·
              refine ⟨8768388572760194815215397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11691184763680259753620529 8768388572760194815215397)
              ·
                refine ⟨1644072857392536527852887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8768388572760194815215397 1644072857392536527852887)
                ·
                  refine ⟨2466109286088804791779331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1644072857392536527852887 2466109286088804791779331)
                  ·
                    refine ⟨3699163929133207187668997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2466109286088804791779331 3699163929133207187668997)
                    ·
                      refine ⟨693593236712476347687937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3699163929133207187668997 693593236712476347687937)
                      ·
                        rfl

theorem cell23_1350768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 4].length) (baseStart_1350768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350768 prefixEnd_1350768 := by exact prefixLift 1350768
  have htrace : WordTrace (prefixWord ++ tailWord_1350768) baseStart_1350768 baseEnd_1350768 := by
    simpa [prefixWord, tailWord_1350768, baseEnd_1350768] using wordTrace_append hprefix tailTrace_1350768
  have hstable : (prefixWord ++ tailWord_1350768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350768).length < 2 ^ (prefixWord ++ tailWord_1350768).sum := by decide
  have hdescent : baseEnd_1350768 < baseStart_1350768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350785 : List Nat := [1, 2, 4, 2, 2, 2, 1, 3, 1, 1, 4]
def baseStart_1350785 : Nat := 118140960795 + 1350785 * 2 ^ 59
def prefixEnd_1350785 : Nat := 4983230072969 + 3 ^ 40 * 1350785 * 2
def baseEnd_1350785 : Nat := 693601965883602781175359

theorem tailTrace_1350785 : CollatzResearch.WordTrace tailWord_1350785 prefixEnd_1350785 693601965883602781175359 := by
  unfold tailWord_1350785
  simp only [CollatzResearch.WordTrace]
  refine ⟨49267176411344115556485809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32844784274229410370990539 49267176411344115556485809)
  ·
    refine ⟨36950382308508086667364357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49267176411344115556485809 36950382308508086667364357)
    ·
      refine ⟨6928196682845266250130817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36950382308508086667364357 6928196682845266250130817)
      ·
        refine ⟨5196147512133949687598113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6928196682845266250130817 5196147512133949687598113)
        ·
          refine ⟨3897110634100462265698585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5196147512133949687598113 3897110634100462265698585)
          ·
            refine ⟨2922832975575346699273939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3897110634100462265698585 2922832975575346699273939)
            ·
              refine ⟨4384249463363020048910909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2922832975575346699273939 4384249463363020048910909)
              ·
                refine ⟨1644093548761132518341591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4384249463363020048910909 1644093548761132518341591)
                ·
                  refine ⟨2466140323141698777512387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1644093548761132518341591 2466140323141698777512387)
                  ·
                    refine ⟨3699210484712548166268581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2466140323141698777512387 3699210484712548166268581)
                    ·
                      refine ⟨693601965883602781175359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3699210484712548166268581 693601965883602781175359)
                      ·
                        rfl

theorem cell23_1350785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 3, 1, 1, 4].length) (baseStart_1350785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350785 prefixEnd_1350785 := by exact prefixLift 1350785
  have htrace : WordTrace (prefixWord ++ tailWord_1350785) baseStart_1350785 baseEnd_1350785 := by
    simpa [prefixWord, tailWord_1350785, baseEnd_1350785] using wordTrace_append hprefix tailTrace_1350785
  have hstable : (prefixWord ++ tailWord_1350785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350785).length < 2 ^ (prefixWord ++ tailWord_1350785).sum := by decide
  have hdescent : baseEnd_1350785 < baseStart_1350785 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350801 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 3]
def baseStart_1350801 : Nat := 118140960795 + 1350801 * 2 ^ 59
def prefixEnd_1350801 : Nat := 4983230072969 + 3 ^ 40 * 1350801 * 2
def baseEnd_1350801 : Nat := 693610181574074718575285

theorem tailTrace_1350801 : CollatzResearch.WordTrace tailWord_1350801 prefixEnd_1350801 693610181574074718575285 := by
  unfold tailWord_1350801
  simp only [CollatzResearch.WordTrace]
  refine ⟨49267759979286150289068257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32845173319524100192712171 49267759979286150289068257)
  ·
    refine ⟨36950819984464612716801193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49267759979286150289068257 36950819984464612716801193)
    ·
      refine ⟨27713114988348459537600895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36950819984464612716801193 27713114988348459537600895)
      ·
        refine ⟨41569672482522689306401343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27713114988348459537600895 41569672482522689306401343)
        ·
          refine ⟨62354508723784033959602015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41569672482522689306401343 62354508723784033959602015)
          ·
            refine ⟨93531763085676050939403023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62354508723784033959602015 93531763085676050939403023)
            ·
              refine ⟨140297644628514076409104535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93531763085676050939403023 140297644628514076409104535)
              ·
                refine ⟨210446466942771114613656803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140297644628514076409104535 210446466942771114613656803)
                ·
                  refine ⟨315669700414156671920485205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210446466942771114613656803 315669700414156671920485205)
                  ·
                    refine ⟨1849627150864199249534093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 315669700414156671920485205 1849627150864199249534093)
                    ·
                      refine ⟨693610181574074718575285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1849627150864199249534093 693610181574074718575285)
                      ·
                        rfl

theorem cell23_1350801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 9, 3].length) (baseStart_1350801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350801 prefixEnd_1350801 := by exact prefixLift 1350801
  have htrace : WordTrace (prefixWord ++ tailWord_1350801) baseStart_1350801 baseEnd_1350801 := by
    simpa [prefixWord, tailWord_1350801, baseEnd_1350801] using wordTrace_append hprefix tailTrace_1350801
  have hstable : (prefixWord ++ tailWord_1350801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350801).length < 2 ^ (prefixWord ++ tailWord_1350801).sum := by decide
  have hdescent : baseEnd_1350801 < baseStart_1350801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350802 : List Nat := [3, 2, 3, 1, 1, 2, 1, 3, 3, 2, 2]
def baseStart_1350802 : Nat := 118140960795 + 1350802 * 2 ^ 59
def prefixEnd_1350802 : Nat := 4983230072969 + 3 ^ 40 * 1350802 * 2
def baseEnd_1350802 : Nat := 693610695054729214662781

theorem tailTrace_1350802 : CollatzResearch.WordTrace tailWord_1350802 prefixEnd_1350802 693610695054729214662781 := by
  unfold tailWord_1350802
  simp only [CollatzResearch.WordTrace]
  refine ⟨12316949113070631864963665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32845197634855018306569773 12316949113070631864963665)
  ·
    refine ⟨9237711834802973898722749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12316949113070631864963665 9237711834802973898722749)
    ·
      refine ⟨3464141938051115212021031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9237711834802973898722749 3464141938051115212021031)
      ·
        refine ⟨5196212907076672818031547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3464141938051115212021031 5196212907076672818031547)
        ·
          refine ⟨7794319360615009227047321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5196212907076672818031547 7794319360615009227047321)
          ·
            refine ⟨5845739520461256920285491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7794319360615009227047321 5845739520461256920285491)
            ·
              refine ⟨8768609280691885380428237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5845739520461256920285491 8768609280691885380428237)
              ·
                refine ⟨3288228480259457017660589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8768609280691885380428237 3288228480259457017660589)
                ·
                  refine ⟨1233085680097296381622721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3288228480259457017660589 1233085680097296381622721)
                  ·
                    refine ⟨924814260072972286217041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1233085680097296381622721 924814260072972286217041)
                    ·
                      refine ⟨693610695054729214662781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 924814260072972286217041 693610695054729214662781)
                      ·
                        rfl

theorem cell23_1350802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 3, 3, 2, 2].length) (baseStart_1350802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350802 prefixEnd_1350802 := by exact prefixLift 1350802
  have htrace : WordTrace (prefixWord ++ tailWord_1350802) baseStart_1350802 baseEnd_1350802 := by
    simpa [prefixWord, tailWord_1350802, baseEnd_1350802] using wordTrace_append hprefix tailTrace_1350802
  have hstable : (prefixWord ++ tailWord_1350802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350802).length < 2 ^ (prefixWord ++ tailWord_1350802).sum := by decide
  have hdescent : baseEnd_1350802 < baseStart_1350802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350812 : List Nat := [2, 2, 3, 2, 1, 3, 3, 1, 2, 4]
def baseStart_1350812 : Nat := 118140960795 + 1350812 * 2 ^ 59
def prefixEnd_1350812 : Nat := 4983230072969 + 3 ^ 40 * 1350812 * 2
def baseEnd_1350812 : Nat := 231205276620424725179245

theorem tailTrace_1350812 : CollatzResearch.WordTrace tailWord_1350812 prefixEnd_1350812 231205276620424725179245 := by
  unfold tailWord_1350812
  simp only [CollatzResearch.WordTrace]
  refine ⟨24634080591123149583859345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32845440788164199445145793 24634080591123149583859345)
  ·
    refine ⟨18475560443342362187894509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24634080591123149583859345 18475560443342362187894509)
    ·
      refine ⟨6928335166253385820460441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18475560443342362187894509 6928335166253385820460441)
      ·
        refine ⟨5196251374690039365345331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6928335166253385820460441 5196251374690039365345331)
        ·
          refine ⟨7794377062035059048017997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5196251374690039365345331 7794377062035059048017997)
          ·
            refine ⟨2922891398263147143006749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7794377062035059048017997 2922891398263147143006749)
            ·
              refine ⟨1096084274348680178627531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2922891398263147143006749 1096084274348680178627531)
              ·
                refine ⟨1644126411523020267941297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1096084274348680178627531 1644126411523020267941297)
                ·
                  refine ⟨1233094808642265200955973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1644126411523020267941297 1233094808642265200955973)
                  ·
                    refine ⟨231205276620424725179245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1233094808642265200955973 231205276620424725179245)
                    ·
                      rfl

theorem cell23_1350812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_1350812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350812 prefixEnd_1350812 := by exact prefixLift 1350812
  have htrace : WordTrace (prefixWord ++ tailWord_1350812) baseStart_1350812 baseEnd_1350812 := by
    simpa [prefixWord, tailWord_1350812, baseEnd_1350812] using wordTrace_append hprefix tailTrace_1350812
  have hstable : (prefixWord ++ tailWord_1350812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350812).length < 2 ^ (prefixWord ++ tailWord_1350812).sum := by decide
  have hdescent : baseEnd_1350812 < baseStart_1350812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350831 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 5]
def baseStart_1350831 : Nat := 118140960795 + 1350831 * 2 ^ 59
def prefixEnd_1350831 : Nat := 4983230072969 + 3 ^ 40 * 1350831 * 2
def baseEnd_1350831 : Nat := 693625585993709601200147

theorem tailTrace_1350831 : CollatzResearch.WordTrace tailWord_1350831 prefixEnd_1350831 693625585993709601200147 := by
  unfold tailWord_1350831
  simp only [CollatzResearch.WordTrace]
  refine ⟨49268854169177465412660347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32845902779451643608440231 49268854169177465412660347)
  ·
    refine ⟨73903281253766198118990521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49268854169177465412660347 73903281253766198118990521)
    ·
      refine ⟨55427460940324648589242891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73903281253766198118990521 55427460940324648589242891)
      ·
        refine ⟨83141191410486972883864337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55427460940324648589242891 83141191410486972883864337)
        ·
          refine ⟨62355893557865229662898253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83141191410486972883864337 62355893557865229662898253)
          ·
            refine ⟨23383460084199461123586845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62355893557865229662898253 23383460084199461123586845)
            ·
              refine ⟨8768797531574797921345067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23383460084199461123586845 8768797531574797921345067)
              ·
                refine ⟨13153196297362196882017601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8768797531574797921345067 13153196297362196882017601)
                ·
                  refine ⟨9864897223021647661513201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13153196297362196882017601 9864897223021647661513201)
                  ·
                    refine ⟨7398672917266235746134901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9864897223021647661513201 7398672917266235746134901)
                    ·
                      refine ⟨693625585993709601200147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7398672917266235746134901 693625585993709601200147)
                      ·
                        rfl

theorem cell23_1350831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_1350831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350831 prefixEnd_1350831 := by exact prefixLift 1350831
  have htrace : WordTrace (prefixWord ++ tailWord_1350831) baseStart_1350831 baseEnd_1350831 := by
    simpa [prefixWord, tailWord_1350831, baseEnd_1350831] using wordTrace_append hprefix tailTrace_1350831
  have hstable : (prefixWord ++ tailWord_1350831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350831).length < 2 ^ (prefixWord ++ tailWord_1350831).sum := by decide
  have hdescent : baseEnd_1350831 < baseStart_1350831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350851 : List Nat := [1, 1, 1, 3, 1, 1, 1, 6, 2, 6]
def baseStart_1350851 : Nat := 118140960795 + 1350851 * 2 ^ 59
def prefixEnd_1350851 : Nat := 4983230072969 + 3 ^ 40 * 1350851 * 2
def baseEnd_1350851 : Nat := 231211951868933174316685

theorem tailTrace_1350851 : CollatzResearch.WordTrace tailWord_1350851 prefixEnd_1350851 231211951868933174316685 := by
  unfold tailWord_1350851
  simp only [CollatzResearch.WordTrace]
  refine ⟨49269583629105008828388407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32846389086070005885592271 49269583629105008828388407)
  ·
    refine ⟨73904375443657513242582611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49269583629105008828388407 73904375443657513242582611)
    ·
      refine ⟨110856563165486269863873917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73904375443657513242582611 110856563165486269863873917)
      ·
        refine ⟨41571211187057351198952719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110856563165486269863873917 41571211187057351198952719)
        ·
          refine ⟨62356816780586026798429079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41571211187057351198952719 62356816780586026798429079)
          ·
            refine ⟨93535225170879040197643619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62356816780586026798429079 93535225170879040197643619)
            ·
              refine ⟨140302837756318560296465429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93535225170879040197643619 140302837756318560296465429)
              ·
                refine ⟨6576695519827432513896817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 140302837756318560296465429 6576695519827432513896817)
                ·
                  refine ⟨4932521639870574385422613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6576695519827432513896817 4932521639870574385422613)
                  ·
                    refine ⟨231211951868933174316685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4932521639870574385422613 231211951868933174316685)
                    ·
                      rfl

theorem cell23_1350851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2, 6].length) (baseStart_1350851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350851 prefixEnd_1350851 := by exact prefixLift 1350851
  have htrace : WordTrace (prefixWord ++ tailWord_1350851) baseStart_1350851 baseEnd_1350851 := by
    simpa [prefixWord, tailWord_1350851, baseEnd_1350851] using wordTrace_append hprefix tailTrace_1350851
  have hstable : (prefixWord ++ tailWord_1350851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350851).length < 2 ^ (prefixWord ++ tailWord_1350851).sum := by decide
  have hdescent : baseEnd_1350851 < baseStart_1350851 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350869 : List Nat := [1, 3, 2, 4, 1, 1, 4, 1, 2, 1, 3]
def baseStart_1350869 : Nat := 118140960795 + 1350869 * 2 ^ 59
def prefixEnd_1350869 : Nat := 4983230072969 + 3 ^ 40 * 1350869 * 2
def baseEnd_1350869 : Nat := 693645098258580452524973

theorem tailTrace_1350869 : CollatzResearch.WordTrace tailWord_1350869 prefixEnd_1350869 693645098258580452524973 := by
  unfold tailWord_1350869
  simp only [CollatzResearch.WordTrace]
  refine ⟨49270240143039797902543661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32846826762026531935029107 49270240143039797902543661)
  ·
    refine ⟨18476340053639924213453873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49270240143039797902543661 18476340053639924213453873)
    ·
      refine ⟨13857255040229943160090405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18476340053639924213453873 13857255040229943160090405)
      ·
        refine ⟨2598235320043114342516951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13857255040229943160090405 2598235320043114342516951)
        ·
          refine ⟨3897352980064671513775427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2598235320043114342516951 3897352980064671513775427)
          ·
            refine ⟨5846029470097007270663141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3897352980064671513775427 5846029470097007270663141)
            ·
              refine ⟨1096130525643188863249339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5846029470097007270663141 1096130525643188863249339)
              ·
                refine ⟨1644195788464783294874009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1096130525643188863249339 1644195788464783294874009)
                ·
                  refine ⟨1233146841348587471155507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1644195788464783294874009 1233146841348587471155507)
                  ·
                    refine ⟨1849720262022881206733261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1233146841348587471155507 1849720262022881206733261)
                    ·
                      refine ⟨693645098258580452524973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1849720262022881206733261 693645098258580452524973)
                      ·
                        rfl

theorem cell23_1350869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 2, 1, 3].length) (baseStart_1350869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350869 prefixEnd_1350869 := by exact prefixLift 1350869
  have htrace : WordTrace (prefixWord ++ tailWord_1350869) baseStart_1350869 baseEnd_1350869 := by
    simpa [prefixWord, tailWord_1350869, baseEnd_1350869] using wordTrace_append hprefix tailTrace_1350869
  have hstable : (prefixWord ++ tailWord_1350869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350869).length < 2 ^ (prefixWord ++ tailWord_1350869).sum := by decide
  have hdescent : baseEnd_1350869 < baseStart_1350869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350915 : List Nat := [1, 1, 1, 3, 2, 5, 1, 4, 5]
def baseStart_1350915 : Nat := 118140960795 + 1350915 * 2 ^ 59
def prefixEnd_1350915 : Nat := 4983230072969 + 3 ^ 40 * 1350915 * 2
def baseEnd_1350915 : Nat := 77074302040965252505529

theorem tailTrace_1350915 : CollatzResearch.WordTrace tailWord_1350915 prefixEnd_1350915 77074302040965252505529 := by
  unfold tailWord_1350915
  simp only [CollatzResearch.WordTrace]
  refine ⟨49271917900873147758718199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32847945267248765172478799 49271917900873147758718199)
  ·
    refine ⟨73907876851309721638077299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49271917900873147758718199 73907876851309721638077299)
    ·
      refine ⟨110861815276964582457115949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73907876851309721638077299 110861815276964582457115949)
      ·
        refine ⟨41573180728861718421418481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110861815276964582457115949 41573180728861718421418481)
        ·
          refine ⟨31179885546646288816063861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41573180728861718421418481 31179885546646288816063861)
          ·
            refine ⟨2923114269998089576505987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31179885546646288816063861 2923114269998089576505987)
            ·
              refine ⟨4384671404997134364758981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2923114269998089576505987 4384671404997134364758981)
              ·
                refine ⟨822125888436962693392309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4384671404997134364758981 822125888436962693392309)
                ·
                  refine ⟨77074302040965252505529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 822125888436962693392309 77074302040965252505529)
                  ·
                    rfl

theorem cell23_1350915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 4, 5].length) (baseStart_1350915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350915 prefixEnd_1350915 := by exact prefixLift 1350915
  have htrace : WordTrace (prefixWord ++ tailWord_1350915) baseStart_1350915 baseEnd_1350915 := by
    simpa [prefixWord, tailWord_1350915, baseEnd_1350915] using wordTrace_append hprefix tailTrace_1350915
  have hstable : (prefixWord ++ tailWord_1350915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350915).length < 2 ^ (prefixWord ++ tailWord_1350915).sum := by decide
  have hdescent : baseEnd_1350915 < baseStart_1350915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350935 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 2, 5, 2]
def baseStart_1350935 : Nat := 118140960795 + 1350935 * 2 ^ 59
def prefixEnd_1350935 : Nat := 4983230072969 + 3 ^ 40 * 1350935 * 2
def baseEnd_1350935 : Nat := 693678987981777194299669

theorem tailTrace_1350935 : CollatzResearch.WordTrace tailWord_1350935 prefixEnd_1350935 693678987981777194299669 := by
  unfold tailWord_1350935
  simp only [CollatzResearch.WordTrace]
  refine ⟨49272647360800691174446259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32848431573867127449630839 49272647360800691174446259)
  ·
    refine ⟨73908971041201036761669389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49272647360800691174446259 73908971041201036761669389)
    ·
      refine ⟨27715864140450388785626021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73908971041201036761669389 27715864140450388785626021)
      ·
        refine ⟨5196724526334447897304879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27715864140450388785626021 5196724526334447897304879)
        ·
          refine ⟨7795086789501671845957319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5196724526334447897304879 7795086789501671845957319)
          ·
            refine ⟨11692630184252507768935979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7795086789501671845957319 11692630184252507768935979)
            ·
              refine ⟨17538945276378761653403969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11692630184252507768935979 17538945276378761653403969)
              ·
                refine ⟨13154208957284071240052977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17538945276378761653403969 13154208957284071240052977)
                ·
                  refine ⟨9865656717963053430039733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13154208957284071240052977 9865656717963053430039733)
                  ·
                    refine ⟨924905317309036259066225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9865656717963053430039733 924905317309036259066225)
                    ·
                      refine ⟨693678987981777194299669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 924905317309036259066225 693678987981777194299669)
                      ·
                        rfl

theorem cell23_1350935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 2, 5, 2].length) (baseStart_1350935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350935 prefixEnd_1350935 := by exact prefixLift 1350935
  have htrace : WordTrace (prefixWord ++ tailWord_1350935) baseStart_1350935 baseEnd_1350935 := by
    simpa [prefixWord, tailWord_1350935, baseEnd_1350935] using wordTrace_append hprefix tailTrace_1350935
  have hstable : (prefixWord ++ tailWord_1350935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350935).length < 2 ^ (prefixWord ++ tailWord_1350935).sum := by decide
  have hdescent : baseEnd_1350935 < baseStart_1350935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1350975 : List Nat := [1, 1, 2, 2, 4, 2, 1, 3, 3, 4]
def baseStart_1350975 : Nat := 118140960795 + 1350975 * 2 ^ 59
def prefixEnd_1350975 : Nat := 4983230072969 + 3 ^ 40 * 1350975 * 2
def baseEnd_1350975 : Nat := 231233175735985679266495

theorem tailTrace_1350975 : CollatzResearch.WordTrace tailWord_1350975 prefixEnd_1350975 231233175735985679266495 := by
  unfold tailWord_1350975
  simp only [CollatzResearch.WordTrace]
  refine ⟨49274106280655778005902379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32849404187103852003934919 49274106280655778005902379)
  ·
    refine ⟨73911159420983667008853569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49274106280655778005902379 73911159420983667008853569)
    ·
      refine ⟨55433369565737750256640177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73911159420983667008853569 55433369565737750256640177)
      ·
        refine ⟨41575027174303312692480133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55433369565737750256640177 41575027174303312692480133)
        ·
          refine ⟨7795317595181871129840025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41575027174303312692480133 7795317595181871129840025)
          ·
            refine ⟨5846488196386403347380019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7795317595181871129840025 5846488196386403347380019)
            ·
              refine ⟨8769732294579605021070029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5846488196386403347380019 8769732294579605021070029)
              ·
                refine ⟨3288649610467351882901261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8769732294579605021070029 3288649610467351882901261)
                ·
                  refine ⟨1233243603925256956087973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3288649610467351882901261 1233243603925256956087973)
                  ·
                    refine ⟨231233175735985679266495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1233243603925256956087973 231233175735985679266495)
                    ·
                      rfl

theorem cell23_1350975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 3, 3, 4].length) (baseStart_1350975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1350975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1350975 prefixEnd_1350975 := by exact prefixLift 1350975
  have htrace : WordTrace (prefixWord ++ tailWord_1350975) baseStart_1350975 baseEnd_1350975 := by
    simpa [prefixWord, tailWord_1350975, baseEnd_1350975] using wordTrace_append hprefix tailTrace_1350975
  have hstable : (prefixWord ++ tailWord_1350975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1350975).length < 2 ^ (prefixWord ++ tailWord_1350975).sum := by decide
  have hdescent : baseEnd_1350975 < baseStart_1350975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1350975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351065 : List Nat := [1, 2, 1, 2, 1, 6, 1, 2, 1, 6]
def baseStart_1351065 : Nat := 118140960795 + 1351065 * 2 ^ 59
def prefixEnd_1351065 : Nat := 4983230072969 + 3 ^ 40 * 1351065 * 2
def baseEnd_1351065 : Nat := 231248580155620561891357

theorem tailTrace_1351065 : CollatzResearch.WordTrace tailWord_1351065 prefixEnd_1351065 231248580155620561891357 := by
  unfold tailWord_1351065
  simp only [CollatzResearch.WordTrace]
  refine ⟨49277388850329723376678649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32851592566886482251119099 49277388850329723376678649)
  ·
    refine ⟨36958041637747292532508987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49277388850329723376678649 36958041637747292532508987)
    ·
      refine ⟨55437062456620938798763481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36958041637747292532508987 55437062456620938798763481)
      ·
        refine ⟨41577796842465704099072611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55437062456620938798763481 41577796842465704099072611)
        ·
          refine ⟨62366695263698556148608917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41577796842465704099072611 62366695263698556148608917)
          ·
            refine ⟨2923438840485869819466043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 62366695263698556148608917 2923438840485869819466043)
            ·
              refine ⟨4385158260728804729199065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2923438840485869819466043 4385158260728804729199065)
              ·
                refine ⟨3288868695546603546899299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4385158260728804729199065 3288868695546603546899299)
                ·
                  refine ⟨4933303043319905320348949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3288868695546603546899299 4933303043319905320348949)
                  ·
                    refine ⟨231248580155620561891357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4933303043319905320348949 231248580155620561891357)
                    ·
                      rfl

theorem cell23_1351065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 2, 1, 6].length) (baseStart_1351065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351065 prefixEnd_1351065 := by exact prefixLift 1351065
  have htrace : WordTrace (prefixWord ++ tailWord_1351065) baseStart_1351065 baseEnd_1351065 := by
    simpa [prefixWord, tailWord_1351065, baseEnd_1351065] using wordTrace_append hprefix tailTrace_1351065
  have hstable : (prefixWord ++ tailWord_1351065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351065).length < 2 ^ (prefixWord ++ tailWord_1351065).sum := by decide
  have hdescent : baseEnd_1351065 < baseStart_1351065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351069 : List Nat := [1, 4, 2, 1, 3, 2, 3, 1, 1, 5]
def baseStart_1351069 : Nat := 118140960795 + 1351069 * 2 ^ 59
def prefixEnd_1351069 : Nat := 4983230072969 + 3 ^ 40 * 1351069 * 2
def baseEnd_1351069 : Nat := 231249264796493223341351

theorem tailTrace_1351069 : CollatzResearch.WordTrace tailWord_1351069 prefixEnd_1351069 231249264796493223341351 := by
  unfold tailWord_1351069
  simp only [CollatzResearch.WordTrace]
  refine ⟨49277534742315232059824261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32851689828210154706549507 49277534742315232059824261)
  ·
    refine ⟨9239537764184106011217049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49277534742315232059824261 9239537764184106011217049)
    ·
      refine ⟨6929653323138079508412787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9239537764184106011217049 6929653323138079508412787)
      ·
        refine ⟨10394479984707119262619181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6929653323138079508412787 10394479984707119262619181)
        ·
          refine ⟨3897929994265169723482193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10394479984707119262619181 3897929994265169723482193)
          ·
            refine ⟨2923447495698877292611645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3897929994265169723482193 2923447495698877292611645)
            ·
              refine ⟨1096292810887078984729367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2923447495698877292611645 1096292810887078984729367)
              ·
                refine ⟨1644439216330618477094051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1096292810887078984729367 1644439216330618477094051)
                ·
                  refine ⟨2466658824495927715641077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1644439216330618477094051 2466658824495927715641077)
                  ·
                    refine ⟨231249264796493223341351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2466658824495927715641077 231249264796493223341351)
                    ·
                      rfl

theorem cell23_1351069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_1351069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351069 prefixEnd_1351069 := by exact prefixLift 1351069
  have htrace : WordTrace (prefixWord ++ tailWord_1351069) baseStart_1351069 baseEnd_1351069 := by
    simpa [prefixWord, tailWord_1351069, baseEnd_1351069] using wordTrace_append hprefix tailTrace_1351069
  have hstable : (prefixWord ++ tailWord_1351069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351069).length < 2 ^ (prefixWord ++ tailWord_1351069).sum := by decide
  have hdescent : baseEnd_1351069 < baseStart_1351069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351088 : List Nat := [2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 7]
def baseStart_1351088 : Nat := 118140960795 + 1351088 * 2 ^ 59
def prefixEnd_1351088 : Nat := 4983230072969 + 3 ^ 40 * 1351088 * 2
def baseEnd_1351088 : Nat := 693757550521915095686465

theorem tailTrace_1351088 : CollatzResearch.WordTrace tailWord_1351088 prefixEnd_1351088 693757550521915095686465 := by
  unfold tailWord_1351088
  simp only [CollatzResearch.WordTrace]
  refine ⟨24639113864623199152382959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32852151819497598869843945 24639113864623199152382959)
  ·
    refine ⟨36958670796934798728574439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24639113864623199152382959 36958670796934798728574439)
    ·
      refine ⟨55438006195402198092861659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36958670796934798728574439 55438006195402198092861659)
      ·
        refine ⟨83157009293103297139292489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55438006195402198092861659 83157009293103297139292489)
        ·
          refine ⟨62367756969827472854469367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83157009293103297139292489 62367756969827472854469367)
          ·
            refine ⟨93551635454741209281704051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62367756969827472854469367 93551635454741209281704051)
            ·
              refine ⟨140327453182111813922556077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93551635454741209281704051 140327453182111813922556077)
              ·
                refine ⟨52622794943291930220958529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140327453182111813922556077 52622794943291930220958529)
                ·
                  refine ⟨39467096207468947665718897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52622794943291930220958529 39467096207468947665718897)
                  ·
                    refine ⟨29600322155601710749289173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39467096207468947665718897 29600322155601710749289173)
                    ·
                      refine ⟨693757550521915095686465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29600322155601710749289173 693757550521915095686465)
                      ·
                        rfl

theorem cell23_1351088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_1351088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351088 prefixEnd_1351088 := by exact prefixLift 1351088
  have htrace : WordTrace (prefixWord ++ tailWord_1351088) baseStart_1351088 baseEnd_1351088 := by
    simpa [prefixWord, tailWord_1351088, baseEnd_1351088] using wordTrace_append hprefix tailTrace_1351088
  have hstable : (prefixWord ++ tailWord_1351088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351088).length < 2 ^ (prefixWord ++ tailWord_1351088).sum := by decide
  have hdescent : baseEnd_1351088 < baseStart_1351088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351089 : List Nat := [1, 2, 2, 4, 1, 1, 2, 3, 3, 2, 2]
def baseStart_1351089 : Nat := 118140960795 + 1351089 * 2 ^ 59
def prefixEnd_1351089 : Nat := 4983230072969 + 3 ^ 40 * 1351089 * 2
def baseEnd_1351089 : Nat := 693758064002569591773961

theorem tailTrace_1351089 : CollatzResearch.WordTrace tailWord_1351089 prefixEnd_1351089 693758064002569591773961 := by
  unfold tailWord_1351089
  simp only [CollatzResearch.WordTrace]
  refine ⟨49278264202242775475552321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32852176134828516983701547 49278264202242775475552321)
  ·
    refine ⟨36958698151682081606664241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49278264202242775475552321 36958698151682081606664241)
    ·
      refine ⟨27719023613761561204998181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36958698151682081606664241 27719023613761561204998181)
      ·
        refine ⟨5197316927580292725937159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27719023613761561204998181 5197316927580292725937159)
        ·
          refine ⟨7795975391370439088905739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5197316927580292725937159 7795975391370439088905739)
          ·
            refine ⟨11693963087055658633358609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7795975391370439088905739 11693963087055658633358609)
            ·
              refine ⟨8770472315291743975018957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11693963087055658633358609 8770472315291743975018957)
              ·
                refine ⟨3288927118234403990632109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8770472315291743975018957 3288927118234403990632109)
                ·
                  refine ⟨1233347669337901496487041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3288927118234403990632109 1233347669337901496487041)
                  ·
                    refine ⟨925010752003426122365281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1233347669337901496487041 925010752003426122365281)
                    ·
                      refine ⟨693758064002569591773961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 925010752003426122365281 693758064002569591773961)
                      ·
                        rfl

theorem cell23_1351089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 3, 3, 2, 2].length) (baseStart_1351089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351089 prefixEnd_1351089 := by exact prefixLift 1351089
  have htrace : WordTrace (prefixWord ++ tailWord_1351089) baseStart_1351089 baseEnd_1351089 := by
    simpa [prefixWord, tailWord_1351089, baseEnd_1351089] using wordTrace_append hprefix tailTrace_1351089
  have hstable : (prefixWord ++ tailWord_1351089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351089).length < 2 ^ (prefixWord ++ tailWord_1351089).sum := by decide
  have hdescent : baseEnd_1351089 < baseStart_1351089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351126 : List Nat := [5, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3]
def baseStart_1351126 : Nat := 118140960795 + 1351126 * 2 ^ 59
def prefixEnd_1351126 : Nat := 4983230072969 + 3 ^ 40 * 1351126 * 2
def baseEnd_1351126 : Nat := 693777062786785947011291

theorem tailTrace_1351126 : CollatzResearch.WordTrace tailWord_1351126 prefixEnd_1351126 693777062786785947011291 := by
  unfold tailWord_1351126
  simp only [CollatzResearch.WordTrace]
  refine ⟨3079975856444295674665577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32853075802072487196432821 3079975856444295674665577)
  ·
    refine ⟨2309981892333221755999183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3079975856444295674665577 2309981892333221755999183)
    ·
      refine ⟨3464972838499832633998775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2309981892333221755999183 3464972838499832633998775)
      ·
        refine ⟨5197459257749748950998163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3464972838499832633998775 5197459257749748950998163)
        ·
          refine ⟨7796188886624623426497245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5197459257749748950998163 7796188886624623426497245)
          ·
            refine ⟨2923570832484233784936467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7796188886624623426497245 2923570832484233784936467)
            ·
              refine ⟨4385356248726350677404701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2923570832484233784936467 4385356248726350677404701)
              ·
                refine ⟨1644508593272381504026763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4385356248726350677404701 1644508593272381504026763)
                ·
                  refine ⟨2466762889908572256040145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1644508593272381504026763 2466762889908572256040145)
                  ·
                    refine ⟨1850072167431429192030109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2466762889908572256040145 1850072167431429192030109)
                    ·
                      refine ⟨693777062786785947011291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1850072167431429192030109 693777062786785947011291)
                      ·
                        rfl

theorem cell23_1351126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3].length) (baseStart_1351126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351126 prefixEnd_1351126 := by exact prefixLift 1351126
  have htrace : WordTrace (prefixWord ++ tailWord_1351126) baseStart_1351126 baseEnd_1351126 := by
    simpa [prefixWord, tailWord_1351126, baseEnd_1351126] using wordTrace_append hprefix tailTrace_1351126
  have hstable : (prefixWord ++ tailWord_1351126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351126).length < 2 ^ (prefixWord ++ tailWord_1351126).sum := by decide
  have hdescent : baseEnd_1351126 < baseStart_1351126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351139 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 4, 1, 3]
def baseStart_1351139 : Nat := 118140960795 + 1351139 * 2 ^ 59
def prefixEnd_1351139 : Nat := 4983230072969 + 3 ^ 40 * 1351139 * 2
def baseEnd_1351139 : Nat := 693783738035294396148731

theorem tailTrace_1351139 : CollatzResearch.WordTrace tailWord_1351139 prefixEnd_1351139 693783738035294396148731 := by
  unfold tailWord_1351139
  simp only [CollatzResearch.WordTrace]
  refine ⟨49280087852061634014872471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32853391901374422676581647 49280087852061634014872471)
  ·
    refine ⟨73920131778092451022308707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49280087852061634014872471 73920131778092451022308707)
    ·
      refine ⟨110880197667138676533463061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73920131778092451022308707 110880197667138676533463061)
      ·
        refine ⟨5197509265647125462506081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 110880197667138676533463061 5197509265647125462506081)
        ·
          refine ⟨3898131949235344096879561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5197509265647125462506081 3898131949235344096879561)
          ·
            refine ⟨2923598961926508072659671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3898131949235344096879561 2923598961926508072659671)
            ·
              refine ⟨4385398442889762108989507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2923598961926508072659671 4385398442889762108989507)
              ·
                refine ⟨6578097664334643163484261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4385398442889762108989507 6578097664334643163484261)
                ·
                  refine ⟨1233393312062745593153299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6578097664334643163484261 1233393312062745593153299)
                  ·
                    refine ⟨1850089968094118389729949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1233393312062745593153299 1850089968094118389729949)
                    ·
                      refine ⟨693783738035294396148731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1850089968094118389729949 693783738035294396148731)
                      ·
                        rfl

theorem cell23_1351139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_1351139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351139 prefixEnd_1351139 := by exact prefixLift 1351139
  have htrace : WordTrace (prefixWord ++ tailWord_1351139) baseStart_1351139 baseEnd_1351139 := by
    simpa [prefixWord, tailWord_1351139, baseEnd_1351139] using wordTrace_append hprefix tailTrace_1351139
  have hstable : (prefixWord ++ tailWord_1351139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351139).length < 2 ^ (prefixWord ++ tailWord_1351139).sum := by decide
  have hdescent : baseEnd_1351139 < baseStart_1351139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351196 : List Nat := [2, 2, 3, 1, 2, 1, 2, 4, 2, 2, 2]
def baseStart_1351196 : Nat := 118140960795 + 1351196 * 2 ^ 59
def prefixEnd_1351196 : Nat := 4983230072969 + 3 ^ 40 * 1351196 * 2
def baseEnd_1351196 : Nat := 693813006432600673135969

theorem tailTrace_1351196 : CollatzResearch.WordTrace tailWord_1351196 prefixEnd_1351196 693813006432600673135969 := by
  unfold tailWord_1351196
  simp only [CollatzResearch.WordTrace]
  refine ⟨24641083406427566374848721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32854777875236755166464961 24641083406427566374848721)
  ·
    refine ⟨18480812554820674781136541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24641083406427566374848721 18480812554820674781136541)
    ·
      refine ⟨6930304708057753042926203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18480812554820674781136541 6930304708057753042926203)
      ·
        refine ⟨10395457062086629564389305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6930304708057753042926203 10395457062086629564389305)
        ·
          refine ⟨7796592796564972173291979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10395457062086629564389305 7796592796564972173291979)
          ·
            refine ⟨11694889194847458259937969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7796592796564972173291979 11694889194847458259937969)
            ·
              refine ⟨8771166896135593694953477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11694889194847458259937969 8771166896135593694953477)
              ·
                refine ⟨1644593793025423817803777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8771166896135593694953477 1644593793025423817803777)
                ·
                  refine ⟨1233445344769067863352833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1644593793025423817803777 1233445344769067863352833)
                  ·
                    refine ⟨925084008576800897514625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1233445344769067863352833 925084008576800897514625)
                    ·
                      refine ⟨693813006432600673135969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 925084008576800897514625 693813006432600673135969)
                      ·
                        rfl

theorem cell23_1351196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_1351196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351196 prefixEnd_1351196 := by exact prefixLift 1351196
  have htrace : WordTrace (prefixWord ++ tailWord_1351196) baseStart_1351196 baseEnd_1351196 := by
    simpa [prefixWord, tailWord_1351196, baseEnd_1351196] using wordTrace_append hprefix tailTrace_1351196
  have hstable : (prefixWord ++ tailWord_1351196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351196).length < 2 ^ (prefixWord ++ tailWord_1351196).sum := by decide
  have hdescent : baseEnd_1351196 < baseStart_1351196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351202 : List Nat := [3, 3, 1, 1, 1, 1, 5, 1, 7]
def baseStart_1351202 : Nat := 118140960795 + 1351202 * 2 ^ 59
def prefixEnd_1351202 : Nat := 4983230072969 + 3 ^ 40 * 1351202 * 2
def baseEnd_1351202 : Nat := 77090676368503072184549

theorem tailTrace_1351202 : CollatzResearch.WordTrace tailWord_1351202 prefixEnd_1351202 77090676368503072184549 := by
  unfold tailWord_1351202
  simp only [CollatzResearch.WordTrace]
  refine ⟨12320596412708348943603965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32854923767222263849610573 12320596412708348943603965)
  ·
    refine ⟨4620223654765630853851487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12320596412708348943603965 4620223654765630853851487)
    ·
      refine ⟨6930335482148446280777231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4620223654765630853851487 6930335482148446280777231)
      ·
        refine ⟨10395503223222669421165847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6930335482148446280777231 10395503223222669421165847)
        ·
          refine ⟨15593254834834004131748771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10395503223222669421165847 15593254834834004131748771)
          ·
            refine ⟨23389882252251006197623157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15593254834834004131748771 23389882252251006197623157)
            ·
              refine ⟨2192801461148531831027171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23389882252251006197623157 2192801461148531831027171)
              ·
                refine ⟨3289202191722797746540757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2192801461148531831027171 3289202191722797746540757)
                ·
                  refine ⟨77090676368503072184549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3289202191722797746540757 77090676368503072184549)
                  ·
                    rfl

theorem cell23_1351202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_1351202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351202 prefixEnd_1351202 := by exact prefixLift 1351202
  have htrace : WordTrace (prefixWord ++ tailWord_1351202) baseStart_1351202 baseEnd_1351202 := by
    simpa [prefixWord, tailWord_1351202, baseEnd_1351202] using wordTrace_append hprefix tailTrace_1351202
  have hstable : (prefixWord ++ tailWord_1351202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351202).length < 2 ^ (prefixWord ++ tailWord_1351202).sum := by decide
  have hdescent : baseEnd_1351202 < baseStart_1351202 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351269 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 1, 6, 2]
def baseStart_1351269 : Nat := 118140960795 + 1351269 * 2 ^ 59
def prefixEnd_1351269 : Nat := 4983230072969 + 3 ^ 40 * 1351269 * 2
def baseEnd_1351269 : Nat := 693850490520378887523133

theorem tailTrace_1351269 : CollatzResearch.WordTrace tailWord_1351269 prefixEnd_1351269 693850490520378887523133 := by
  unfold tailWord_1351269
  simp only [CollatzResearch.WordTrace]
  refine ⟨49284829341590666217104861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32856552894393777478069907 49284829341590666217104861)
  ·
    refine ⟨18481811003096499831414323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49284829341590666217104861 18481811003096499831414323)
    ·
      refine ⟨27722716504644749747121485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18481811003096499831414323 27722716504644749747121485)
      ·
        refine ⟨10396018689241781155170557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27722716504644749747121485 10396018689241781155170557)
        ·
          refine ⟨3898507008465667933188959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10396018689241781155170557 3898507008465667933188959)
          ·
            refine ⟨5847760512698501899783439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3898507008465667933188959 5847760512698501899783439)
            ·
              refine ⟨8771640769047752849675159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5847760512698501899783439 8771640769047752849675159)
              ·
                refine ⟨13157461153571629274512739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8771640769047752849675159 13157461153571629274512739)
                ·
                  refine ⟨19736191730357443911769109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13157461153571629274512739 19736191730357443911769109)
                  ·
                    refine ⟨925133987360505183364177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19736191730357443911769109 925133987360505183364177)
                    ·
                      refine ⟨693850490520378887523133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 925133987360505183364177 693850490520378887523133)
                      ·
                        rfl

theorem cell23_1351269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 1, 6, 2].length) (baseStart_1351269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351269 prefixEnd_1351269 := by exact prefixLift 1351269
  have htrace : WordTrace (prefixWord ++ tailWord_1351269) baseStart_1351269 baseEnd_1351269 := by
    simpa [prefixWord, tailWord_1351269, baseEnd_1351269] using wordTrace_append hprefix tailTrace_1351269
  have hstable : (prefixWord ++ tailWord_1351269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351269).length < 2 ^ (prefixWord ++ tailWord_1351269).sum := by decide
  have hdescent : baseEnd_1351269 < baseStart_1351269 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351286 : List Nat := [5, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4]
def baseStart_1351286 : Nat := 118140960795 + 1351286 * 2 ^ 59
def prefixEnd_1351286 : Nat := 4983230072969 + 3 ^ 40 * 1351286 * 2
def baseEnd_1351286 : Nat := 693859219691505321010555

theorem tailTrace_1351286 : CollatzResearch.WordTrace tailWord_1351286 prefixEnd_1351286 693859219691505321010555 := by
  unfold tailWord_1351286
  simp only [CollatzResearch.WordTrace]
  refine ⟨3080340586408067382529607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32856966255019385413649141 3080340586408067382529607)
  ·
    refine ⟨4620510879612101073794411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3080340586408067382529607 4620510879612101073794411)
    ·
      refine ⟨6930766319418151610691617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4620510879612101073794411 6930766319418151610691617)
      ·
        refine ⟨5198074739563613708018713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6930766319418151610691617 5198074739563613708018713)
        ·
          refine ⟨3898556054672710281014035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5198074739563613708018713 3898556054672710281014035)
          ·
            refine ⟨5847834082009065421521053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3898556054672710281014035 5847834082009065421521053)
            ·
              refine ⟨2192937780753399533070395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5847834082009065421521053 2192937780753399533070395)
              ·
                refine ⟨3289406671130099299605593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2192937780753399533070395 3289406671130099299605593)
                ·
                  refine ⟨2467055003347574474704195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3289406671130099299605593 2467055003347574474704195)
                  ·
                    refine ⟨3700582505021361712056293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2467055003347574474704195 3700582505021361712056293)
                    ·
                      refine ⟨693859219691505321010555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3700582505021361712056293 693859219691505321010555)
                      ·
                        rfl

theorem cell23_1351286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_1351286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351286 prefixEnd_1351286 := by exact prefixLift 1351286
  have htrace : WordTrace (prefixWord ++ tailWord_1351286) baseStart_1351286 baseEnd_1351286 := by
    simpa [prefixWord, tailWord_1351286, baseEnd_1351286] using wordTrace_append hprefix tailTrace_1351286
  have hstable : (prefixWord ++ tailWord_1351286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351286).length < 2 ^ (prefixWord ++ tailWord_1351286).sum := by decide
  have hdescent : baseEnd_1351286 < baseStart_1351286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351296 : List Nat := [2, 1, 1, 2, 1, 4, 4, 3, 1, 4]
def baseStart_1351296 : Nat := 118140960795 + 1351296 * 2 ^ 59
def prefixEnd_1351296 : Nat := 4983230072969 + 3 ^ 40 * 1351296 * 2
def baseEnd_1351296 : Nat := 231288118166016760628503

theorem tailTrace_1351296 : CollatzResearch.WordTrace tailWord_1351296 prefixEnd_1351296 231288118166016760628503 := by
  unfold tailWord_1351296
  simp only [CollatzResearch.WordTrace]
  refine ⟨24642907056246424914168871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32857209408328566552225161 24642907056246424914168871)
  ·
    refine ⟨36964360584369637371253307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24642907056246424914168871 36964360584369637371253307)
    ·
      refine ⟨55446540876554456056879961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36964360584369637371253307 55446540876554456056879961)
      ·
        refine ⟨41584905657415842042659971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55446540876554456056879961 41584905657415842042659971)
        ·
          refine ⟨62377358486123763063989957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41584905657415842042659971 62377358486123763063989957)
          ·
            refine ⟨11695754716148205574498117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62377358486123763063989957 11695754716148205574498117)
            ·
              refine ⟨2192954009277788545218397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11695754716148205574498117 2192954009277788545218397)
              ·
                refine ⟨822357753479170704456899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2192954009277788545218397 822357753479170704456899)
                ·
                  refine ⟨1233536630218756056685349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 822357753479170704456899 1233536630218756056685349)
                  ·
                    refine ⟨231288118166016760628503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1233536630218756056685349 231288118166016760628503)
                    ·
                      rfl

theorem cell23_1351296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 4, 3, 1, 4].length) (baseStart_1351296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351296 prefixEnd_1351296 := by exact prefixLift 1351296
  have htrace : WordTrace (prefixWord ++ tailWord_1351296) baseStart_1351296 baseEnd_1351296 := by
    simpa [prefixWord, tailWord_1351296, baseEnd_1351296] using wordTrace_append hprefix tailTrace_1351296
  have hstable : (prefixWord ++ tailWord_1351296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351296).length < 2 ^ (prefixWord ++ tailWord_1351296).sum := by decide
  have hdescent : baseEnd_1351296 < baseStart_1351296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351352 : List Nat := [2, 1, 2, 1, 2, 1, 1, 6, 1, 6]
def baseStart_1351352 : Nat := 118140960795 + 1351352 * 2 ^ 59
def prefixEnd_1351352 : Nat := 4983230072969 + 3 ^ 40 * 1351352 * 2
def baseEnd_1351352 : Nat := 231297703138234020928417

theorem tailTrace_1351352 : CollatzResearch.WordTrace tailWord_1351352 prefixEnd_1351352 231297703138234020928417 := by
  unfold tailWord_1351352
  simp only [CollatzResearch.WordTrace]
  refine ⟨24643928300144985696188155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32858571066859980928250873 24643928300144985696188155)
  ·
    refine ⟨36965892450217478544282233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24643928300144985696188155 36965892450217478544282233)
    ·
      refine ⟨27724419337663108908211675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36965892450217478544282233 27724419337663108908211675)
      ·
        refine ⟨41586629006494663362317513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27724419337663108908211675 41586629006494663362317513)
        ·
          refine ⟨31189971754870997521738135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41586629006494663362317513 31189971754870997521738135)
          ·
            refine ⟨46784957632306496282607203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31189971754870997521738135 46784957632306496282607203)
            ·
              refine ⟨70177436448459744423910805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46784957632306496282607203 70177436448459744423910805)
              ·
                refine ⟨3289567333521550519870819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70177436448459744423910805 3289567333521550519870819)
                ·
                  refine ⟨4934351000282325779806229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3289567333521550519870819 4934351000282325779806229)
                  ·
                    refine ⟨231297703138234020928417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4934351000282325779806229 231297703138234020928417)
                    ·
                      rfl

theorem cell23_1351352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 6, 1, 6].length) (baseStart_1351352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351352 prefixEnd_1351352 := by exact prefixLift 1351352
  have htrace : WordTrace (prefixWord ++ tailWord_1351352) baseStart_1351352 baseEnd_1351352 := by
    simpa [prefixWord, tailWord_1351352, baseEnd_1351352] using wordTrace_append hprefix tailTrace_1351352
  have hstable : (prefixWord ++ tailWord_1351352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351352).length < 2 ^ (prefixWord ++ tailWord_1351352).sum := by decide
  have hdescent : baseEnd_1351352 < baseStart_1351352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351353 : List Nat := [1, 2, 1, 4, 1, 1, 5, 3, 1, 1, 3]
def baseStart_1351353 : Nat := 118140960795 + 1351353 * 2 ^ 59
def prefixEnd_1351353 : Nat := 4983230072969 + 3 ^ 40 * 1351353 * 2
def baseEnd_1351353 : Nat := 693893622895356558872747

theorem tailTrace_1351353 : CollatzResearch.WordTrace tailWord_1351353 prefixEnd_1351353 693893622895356558872747 := by
  unfold tailWord_1351353
  simp only [CollatzResearch.WordTrace]
  refine ⟨49287893073286348563162713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32858595382190899042108475 49287893073286348563162713)
  ·
    refine ⟨36965919804964761422372035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49287893073286348563162713 36965919804964761422372035)
    ·
      refine ⟨55448879707447142133558053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36965919804964761422372035 55448879707447142133558053)
      ·
        refine ⟨10396664945146339150042135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55448879707447142133558053 10396664945146339150042135)
        ·
          refine ⟨15594997417719508725063203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10396664945146339150042135 15594997417719508725063203)
          ·
            refine ⟨23392496126579263087594805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15594997417719508725063203 23392496126579263087594805)
            ·
              refine ⟨2193046511866805914462013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23392496126579263087594805 2193046511866805914462013)
              ·
                refine ⟨822392441950052217923255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2193046511866805914462013 822392441950052217923255)
                ·
                  refine ⟨1233588662925078326884883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 822392441950052217923255 1233588662925078326884883)
                  ·
                    refine ⟨1850382994387617490327325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1233588662925078326884883 1850382994387617490327325)
                    ·
                      refine ⟨693893622895356558872747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1850382994387617490327325 693893622895356558872747)
                      ·
                        rfl

theorem cell23_1351353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_1351353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351353 prefixEnd_1351353 := by exact prefixLift 1351353
  have htrace : WordTrace (prefixWord ++ tailWord_1351353) baseStart_1351353 baseEnd_1351353 := by
    simpa [prefixWord, tailWord_1351353, baseEnd_1351353] using wordTrace_append hprefix tailTrace_1351353
  have hstable : (prefixWord ++ tailWord_1351353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351353).length < 2 ^ (prefixWord ++ tailWord_1351353).sum := by decide
  have hdescent : baseEnd_1351353 < baseStart_1351353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351359 : List Nat := [1, 1, 2, 2, 2, 3, 1, 5, 1, 1, 4]
def baseStart_1351359 : Nat := 118140960795 + 1351359 * 2 ^ 59
def prefixEnd_1351359 : Nat := 4983230072969 + 3 ^ 40 * 1351359 * 2
def baseEnd_1351359 : Nat := 693896703779283535397719

theorem tailTrace_1351359 : CollatzResearch.WordTrace tailWord_1351359 prefixEnd_1351359 693896703779283535397719 := by
  unfold tailWord_1351359
  simp only [CollatzResearch.WordTrace]
  refine ⟨49288111911264611587881131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32858741274176407725254087 49288111911264611587881131)
  ·
    refine ⟨73932167866896917381821697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49288111911264611587881131 73932167866896917381821697)
    ·
      refine ⟨55449125900172688036366273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73932167866896917381821697 55449125900172688036366273)
      ·
        refine ⟨41586844425129516027274705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55449125900172688036366273 41586844425129516027274705)
        ·
          refine ⟨31190133318847137020456029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41586844425129516027274705 31190133318847137020456029)
          ·
            refine ⟨11696299994567676382671011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31190133318847137020456029 11696299994567676382671011)
            ·
              refine ⟨17544449991851514574006517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11696299994567676382671011 17544449991851514574006517)
              ·
                refine ⟨1644792186736079491313111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17544449991851514574006517 1644792186736079491313111)
                ·
                  refine ⟨2467188280104119236969667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1644792186736079491313111 2467188280104119236969667)
                  ·
                    refine ⟨3700782420156178855454501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2467188280104119236969667 3700782420156178855454501)
                    ·
                      refine ⟨693896703779283535397719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3700782420156178855454501 693896703779283535397719)
                      ·
                        rfl

theorem cell23_1351359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 5, 1, 1, 4].length) (baseStart_1351359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351359 prefixEnd_1351359 := by exact prefixLift 1351359
  have htrace : WordTrace (prefixWord ++ tailWord_1351359) baseStart_1351359 baseEnd_1351359 := by
    simpa [prefixWord, tailWord_1351359, baseEnd_1351359] using wordTrace_append hprefix tailTrace_1351359
  have hstable : (prefixWord ++ tailWord_1351359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351359).length < 2 ^ (prefixWord ++ tailWord_1351359).sum := by decide
  have hdescent : baseEnd_1351359 < baseStart_1351359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351370 : List Nat := [3, 1, 2, 1, 6, 1, 1, 1, 3, 1, 3]
def baseStart_1351370 : Nat := 118140960795 + 1351370 * 2 ^ 59
def prefixEnd_1351370 : Nat := 4983230072969 + 3 ^ 40 * 1351370 * 2
def baseEnd_1351370 : Nat := 693902352066482992360169

theorem tailTrace_1351370 : CollatzResearch.WordTrace tailWord_1351370 prefixEnd_1351370 693902352066482992360169 := by
  unfold tailWord_1351370
  simp only [CollatzResearch.WordTrace]
  refine ⟨12322128278556190116632891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32859008742816506977687709 12322128278556190116632891)
  ·
    refine ⟨18483192417834285174949337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12322128278556190116632891 18483192417834285174949337)
    ·
      refine ⟨13862394313375713881212003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18483192417834285174949337 13862394313375713881212003)
      ·
        refine ⟨20793591470063570821818005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13862394313375713881212003 20793591470063570821818005)
        ·
          refine ⟨974699600159229882272719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20793591470063570821818005 974699600159229882272719)
          ·
            refine ⟨1462049400238844823409079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 974699600159229882272719 1462049400238844823409079)
            ·
              refine ⟨2193074100358267235113619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462049400238844823409079 2193074100358267235113619)
              ·
                refine ⟨3289611150537400852670429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2193074100358267235113619 3289611150537400852670429)
                ·
                  refine ⟨1233604181451525319751411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3289611150537400852670429 1233604181451525319751411)
                  ·
                    refine ⟨1850406272177287979627117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1233604181451525319751411 1850406272177287979627117)
                    ·
                      refine ⟨693902352066482992360169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1850406272177287979627117 693902352066482992360169)
                      ·
                        rfl

theorem cell23_1351370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 3, 1, 3].length) (baseStart_1351370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351370 prefixEnd_1351370 := by exact prefixLift 1351370
  have htrace : WordTrace (prefixWord ++ tailWord_1351370) baseStart_1351370 baseEnd_1351370 := by
    simpa [prefixWord, tailWord_1351370, baseEnd_1351370] using wordTrace_append hprefix tailTrace_1351370
  have hstable : (prefixWord ++ tailWord_1351370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351370).length < 2 ^ (prefixWord ++ tailWord_1351370).sum := by decide
  have hdescent : baseEnd_1351370 < baseStart_1351370 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351376 : List Nat := [2, 1, 1, 1, 1, 2, 1, 7, 3, 2, 2]
def baseStart_1351376 : Nat := 118140960795 + 1351376 * 2 ^ 59
def prefixEnd_1351376 : Nat := 4983230072969 + 3 ^ 40 * 1351376 * 2
def baseEnd_1351376 : Nat := 693905432950409968885141

theorem tailTrace_1351376 : CollatzResearch.WordTrace tailWord_1351376 prefixEnd_1351376 693905432950409968885141 := by
  unfold tailWord_1351376
  simp only [CollatzResearch.WordTrace]
  refine ⟨24644365976101511745624991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32859154634802015660833321 24644365976101511745624991)
  ·
    refine ⟨36966548964152267618437487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24644365976101511745624991 36966548964152267618437487)
    ·
      refine ⟨55449823446228401427656231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36966548964152267618437487 55449823446228401427656231)
      ·
        refine ⟨83174735169342602141484347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55449823446228401427656231 83174735169342602141484347)
        ·
          refine ⟨124762102754013903212226521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83174735169342602141484347 124762102754013903212226521)
          ·
            refine ⟨93571577065510427409169891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124762102754013903212226521 93571577065510427409169891)
            ·
              refine ⟨140357365598265641113754837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93571577065510427409169891 140357365598265641113754837)
              ·
                refine ⟨3289625756209350963603629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 140357365598265641113754837 3289625756209350963603629)
                ·
                  refine ⟨1233609658578506611351361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3289625756209350963603629 1233609658578506611351361)
                  ·
                    refine ⟨925207243933879958513521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1233609658578506611351361 925207243933879958513521)
                    ·
                      refine ⟨693905432950409968885141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 925207243933879958513521 693905432950409968885141)
                      ·
                        rfl

theorem cell23_1351376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 3, 2, 2].length) (baseStart_1351376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351376 prefixEnd_1351376 := by exact prefixLift 1351376
  have htrace : WordTrace (prefixWord ++ tailWord_1351376) baseStart_1351376 baseEnd_1351376 := by
    simpa [prefixWord, tailWord_1351376, baseEnd_1351376] using wordTrace_append hprefix tailTrace_1351376
  have hstable : (prefixWord ++ tailWord_1351376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351376).length < 2 ^ (prefixWord ++ tailWord_1351376).sum := by decide
  have hdescent : baseEnd_1351376 < baseStart_1351376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351386 : List Nat := [3, 1, 1, 2, 2, 4, 1, 3, 2, 4]
def baseStart_1351386 : Nat := 118140960795 + 1351386 * 2 ^ 59
def prefixEnd_1351386 : Nat := 4983230072969 + 3 ^ 40 * 1351386 * 2
def baseEnd_1351386 : Nat := 231303522585651643253365

theorem tailTrace_1351386 : CollatzResearch.WordTrace tailWord_1351386 prefixEnd_1351386 231303522585651643253365 := by
  unfold tailWord_1351386
  simp only [CollatzResearch.WordTrace]
  refine ⟨12322274170541698799778503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32859397788111196799409341 12322274170541698799778503)
  ·
    refine ⟨18483411255812548199667755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12322274170541698799778503 18483411255812548199667755)
    ·
      refine ⟨27725116883718822299501633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18483411255812548199667755 27725116883718822299501633)
      ·
        refine ⟨20793837662789116724626225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27725116883718822299501633 20793837662789116724626225)
        ·
          refine ⟨15595378247091837543469669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20793837662789116724626225 15595378247091837543469669)
          ·
            refine ⟨2924133421329719539400563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15595378247091837543469669 2924133421329719539400563)
            ·
              refine ⟨4386200131994579309100845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2924133421329719539400563 4386200131994579309100845)
              ·
                refine ⟨1644825049497967240912817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4386200131994579309100845 1644825049497967240912817)
                ·
                  refine ⟨1233618787123475430684613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1644825049497967240912817 1233618787123475430684613)
                  ·
                    refine ⟨231303522585651643253365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1233618787123475430684613 231303522585651643253365)
                    ·
                      rfl

theorem cell23_1351386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 3, 2, 4].length) (baseStart_1351386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351386 prefixEnd_1351386 := by exact prefixLift 1351386
  have htrace : WordTrace (prefixWord ++ tailWord_1351386) baseStart_1351386 baseEnd_1351386 := by
    simpa [prefixWord, tailWord_1351386, baseEnd_1351386] using wordTrace_append hprefix tailTrace_1351386
  have hstable : (prefixWord ++ tailWord_1351386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351386).length < 2 ^ (prefixWord ++ tailWord_1351386).sum := by decide
  have hdescent : baseEnd_1351386 < baseStart_1351386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351393 : List Nat := [1, 2, 3, 1, 5, 2, 1, 2, 1, 1, 4]
def baseStart_1351393 : Nat := 118140960795 + 1351393 * 2 ^ 59
def prefixEnd_1351393 : Nat := 4983230072969 + 3 ^ 40 * 1351393 * 2
def baseEnd_1351393 : Nat := 693914162121536402372563

theorem tailTrace_1351393 : CollatzResearch.WordTrace tailWord_1351393 prefixEnd_1351393 693914162121536402372563 := by
  unfold tailWord_1351393
  simp only [CollatzResearch.WordTrace]
  refine ⟨49289351993141435394618833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32859567995427623596412555 49289351993141435394618833)
  ·
    refine ⟨36967013994856076545964125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49289351993141435394618833 36967013994856076545964125)
    ·
      refine ⟨13862630248071028704736547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36967013994856076545964125 13862630248071028704736547)
      ·
        refine ⟨20793945372106543057104821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13862630248071028704736547 20793945372106543057104821)
        ·
          refine ⟨1949432378634988411603577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20793945372106543057104821 1949432378634988411603577)
          ·
            refine ⟨1462074283976241308702683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1949432378634988411603577 1462074283976241308702683)
            ·
              refine ⟨2193111425964361963054025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462074283976241308702683 2193111425964361963054025)
              ·
                refine ⟨1644833569473271472290519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2193111425964361963054025 1644833569473271472290519)
                ·
                  refine ⟨2467250354209907208435779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1644833569473271472290519 2467250354209907208435779)
                  ·
                    refine ⟨3700875531314860812653669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2467250354209907208435779 3700875531314860812653669)
                    ·
                      refine ⟨693914162121536402372563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3700875531314860812653669 693914162121536402372563)
                      ·
                        rfl

theorem cell23_1351393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 1, 2, 1, 1, 4].length) (baseStart_1351393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351393 prefixEnd_1351393 := by exact prefixLift 1351393
  have htrace : WordTrace (prefixWord ++ tailWord_1351393) baseStart_1351393 baseEnd_1351393 := by
    simpa [prefixWord, tailWord_1351393, baseEnd_1351393] using wordTrace_append hprefix tailTrace_1351393
  have hstable : (prefixWord ++ tailWord_1351393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351393).length < 2 ^ (prefixWord ++ tailWord_1351393).sum := by decide
  have hdescent : baseEnd_1351393 < baseStart_1351393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351409 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 3, 3, 3]
def baseStart_1351409 : Nat := 118140960795 + 1351409 * 2 ^ 59
def prefixEnd_1351409 : Nat := 4983230072969 + 3 ^ 40 * 1351409 * 2
def baseEnd_1351409 : Nat := 693922377812008339772489

theorem tailTrace_1351409 : CollatzResearch.WordTrace tailWord_1351409 prefixEnd_1351409 693922377812008339772489 := by
  unfold tailWord_1351409
  simp only [CollatzResearch.WordTrace]
  refine ⟨49289935561083470127201281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32859957040722313418134187 49289935561083470127201281)
  ·
    refine ⟨36967451670812602595400961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49289935561083470127201281 36967451670812602595400961)
    ·
      refine ⟨27725588753109451946550721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36967451670812602595400961 27725588753109451946550721)
      ·
        refine ⟨20794191564832088959913041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27725588753109451946550721 20794191564832088959913041)
        ·
          refine ⟨15595643673624066719934781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20794191564832088959913041 15595643673624066719934781)
          ·
            refine ⟨5848366377609025019975543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15595643673624066719934781 5848366377609025019975543)
            ·
              refine ⟨8772549566413537529963315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5848366377609025019975543 8772549566413537529963315)
              ·
                refine ⟨13158824349620306294944973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8772549566413537529963315 13158824349620306294944973)
                ·
                  refine ⟨4934559131107614860604365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13158824349620306294944973 4934559131107614860604365)
                  ·
                    refine ⟨1850459674165355572726637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4934559131107614860604365 1850459674165355572726637)
                    ·
                      refine ⟨693922377812008339772489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1850459674165355572726637 693922377812008339772489)
                      ·
                        rfl

theorem cell23_1351409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 3, 3].length) (baseStart_1351409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351409 prefixEnd_1351409 := by exact prefixLift 1351409
  have htrace : WordTrace (prefixWord ++ tailWord_1351409) baseStart_1351409 baseEnd_1351409 := by
    simpa [prefixWord, tailWord_1351409, baseEnd_1351409] using wordTrace_append hprefix tailTrace_1351409
  have hstable : (prefixWord ++ tailWord_1351409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351409).length < 2 ^ (prefixWord ++ tailWord_1351409).sum := by decide
  have hdescent : baseEnd_1351409 < baseStart_1351409 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351410 : List Nat := [3, 2, 1, 3, 1, 1, 2, 5, 1, 2, 2]
def baseStart_1351410 : Nat := 118140960795 + 1351410 * 2 ^ 59
def prefixEnd_1351410 : Nat := 4983230072969 + 3 ^ 40 * 1351410 * 2
def baseEnd_1351410 : Nat := 693922891292662835859985

theorem tailTrace_1351410 : CollatzResearch.WordTrace tailWord_1351410 prefixEnd_1351410 693922891292662835859985 := by
  unfold tailWord_1351410
  simp only [CollatzResearch.WordTrace]
  refine ⟨12322493008519961824496921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32859981356053231531991789 12322493008519961824496921)
  ·
    refine ⟨9241869756389971368372691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12322493008519961824496921 9241869756389971368372691)
    ·
      refine ⟨13862804634584957052559037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9241869756389971368372691 13862804634584957052559037)
      ·
        refine ⟨5198551737969358894709639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13862804634584957052559037 5198551737969358894709639)
        ·
          refine ⟨7797827606954038342064459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5198551737969358894709639 7797827606954038342064459)
          ·
            refine ⟨11696741410431057513096689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7797827606954038342064459 11696741410431057513096689)
            ·
              refine ⟨8772556057823293134822517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11696741410431057513096689 8772556057823293134822517)
              ·
                refine ⟨822427130420933731389611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8772556057823293134822517 822427130420933731389611)
                ·
                  refine ⟨1233640695631400597084417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 822427130420933731389611 1233640695631400597084417)
                  ·
                    refine ⟨925230521723550447813313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1233640695631400597084417 925230521723550447813313)
                    ·
                      refine ⟨693922891292662835859985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 925230521723550447813313 693922891292662835859985)
                      ·
                        rfl

theorem cell23_1351410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 5, 1, 2, 2].length) (baseStart_1351410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351410 prefixEnd_1351410 := by exact prefixLift 1351410
  have htrace : WordTrace (prefixWord ++ tailWord_1351410) baseStart_1351410 baseEnd_1351410 := by
    simpa [prefixWord, tailWord_1351410, baseEnd_1351410] using wordTrace_append hprefix tailTrace_1351410
  have hstable : (prefixWord ++ tailWord_1351410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351410).length < 2 ^ (prefixWord ++ tailWord_1351410).sum := by decide
  have hdescent : baseEnd_1351410 < baseStart_1351410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351426 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 3, 3, 3]
def baseStart_1351426 : Nat := 118140960795 + 1351426 * 2 ^ 59
def prefixEnd_1351426 : Nat := 4983230072969 + 3 ^ 40 * 1351426 * 2
def baseEnd_1351426 : Nat := 693931106983134773259911

theorem tailTrace_1351426 : CollatzResearch.WordTrace tailWord_1351426 prefixEnd_1351426 693931106983134773259911 := by
  unfold tailWord_1351426
  simp only [CollatzResearch.WordTrace]
  refine ⟨12322638900505470507642533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32860370401347921353713421 12322638900505470507642533)
  ·
    refine ⟨2310494793844775720182975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12322638900505470507642533 2310494793844775720182975)
    ·
      refine ⟨3465742190767163580274463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2310494793844775720182975 3465742190767163580274463)
      ·
        refine ⟨5198613286150745370411695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3465742190767163580274463 5198613286150745370411695)
        ·
          refine ⟨7797919929226118055617543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5198613286150745370411695 7797919929226118055617543)
          ·
            refine ⟨11696879893839177083426315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7797919929226118055617543 11696879893839177083426315)
            ·
              refine ⟨17545319840758765625139473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11696879893839177083426315 17545319840758765625139473)
              ·
                refine ⟨13158989880569074218854605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17545319840758765625139473 13158989880569074218854605)
                ·
                  refine ⟨4934621205213402832070477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13158989880569074218854605 4934621205213402832070477)
                  ·
                    refine ⟨1850482951955026062026429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4934621205213402832070477 1850482951955026062026429)
                    ·
                      refine ⟨693931106983134773259911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1850482951955026062026429 693931106983134773259911)
                      ·
                        rfl

theorem cell23_1351426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 3, 3, 3].length) (baseStart_1351426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351426 prefixEnd_1351426 := by exact prefixLift 1351426
  have htrace : WordTrace (prefixWord ++ tailWord_1351426) baseStart_1351426 baseEnd_1351426 := by
    simpa [prefixWord, tailWord_1351426, baseEnd_1351426] using wordTrace_append hprefix tailTrace_1351426
  have hstable : (prefixWord ++ tailWord_1351426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351426).length < 2 ^ (prefixWord ++ tailWord_1351426).sum := by decide
  have hdescent : baseEnd_1351426 < baseStart_1351426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351436 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 3, 3, 2]
def baseStart_1351436 : Nat := 118140960795 + 1351436 * 2 ^ 59
def prefixEnd_1351436 : Nat := 4983230072969 + 3 ^ 40 * 1351436 * 2
def baseEnd_1351436 : Nat := 693936241789679734134865

theorem tailTrace_1351436 : CollatzResearch.WordTrace tailWord_1351436 prefixEnd_1351436 693936241789679734134865 := by
  unfold tailWord_1351436
  simp only [CollatzResearch.WordTrace]
  refine ⟨24645460165992826869217081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32860613554657102492289441 24645460165992826869217081)
  ·
    refine ⟨18484095124494620151912811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24645460165992826869217081 18484095124494620151912811)
    ·
      refine ⟨27726142686741930227869217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18484095124494620151912811 27726142686741930227869217)
      ·
        refine ⟨20794607015056447670901913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27726142686741930227869217 20794607015056447670901913)
        ·
          refine ⟨15595955261292335753176435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20794607015056447670901913 15595955261292335753176435)
          ·
            refine ⟨23393932891938503629764653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15595955261292335753176435 23393932891938503629764653)
            ·
              refine ⟨8772724834476938861161745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23393932891938503629764653 8772724834476938861161745)
              ·
                refine ⟨6579543625857704145871309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8772724834476938861161745 6579543625857704145871309)
                ·
                  refine ⟨2467328859696639054701741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6579543625857704145871309 2467328859696639054701741)
                  ·
                    refine ⟨925248322386239645513153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2467328859696639054701741 925248322386239645513153)
                    ·
                      refine ⟨693936241789679734134865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 925248322386239645513153 693936241789679734134865)
                      ·
                        rfl

theorem cell23_1351436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 3, 3, 2].length) (baseStart_1351436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351436 prefixEnd_1351436 := by exact prefixLift 1351436
  have htrace : WordTrace (prefixWord ++ tailWord_1351436) baseStart_1351436 baseEnd_1351436 := by
    simpa [prefixWord, tailWord_1351436, baseEnd_1351436] using wordTrace_append hprefix tailTrace_1351436
  have hstable : (prefixWord ++ tailWord_1351436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351436).length < 2 ^ (prefixWord ++ tailWord_1351436).sum := by decide
  have hdescent : baseEnd_1351436 < baseStart_1351436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351437 : List Nat := [1, 7, 2, 1, 1, 1, 2, 1, 1, 6]
def baseStart_1351437 : Nat := 118140960795 + 1351437 * 2 ^ 59
def prefixEnd_1351437 : Nat := 4983230072969 + 3 ^ 40 * 1351437 * 2
def baseEnd_1351437 : Nat := 231312251756778076740787

theorem tailTrace_1351437 : CollatzResearch.WordTrace tailWord_1351437 prefixEnd_1351437 231312251756778076740787 := by
  unfold tailWord_1351437
  simp only [CollatzResearch.WordTrace]
  refine ⟨49290956804982030909220565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32860637869988020606147043 49290956804982030909220565)
  ·
    refine ⟨1155256800116766349434857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 49290956804982030909220565 1155256800116766349434857)
    ·
      refine ⟨866442600087574762076143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1155256800116766349434857 866442600087574762076143)
      ·
        refine ⟨1299663900131362143114215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 866442600087574762076143 1299663900131362143114215)
        ·
          refine ⟨1949495850197043214671323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1299663900131362143114215 1949495850197043214671323)
          ·
            refine ⟨2924243775295564822006985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1949495850197043214671323 2924243775295564822006985)
            ·
              refine ⟨2193182831471673616505239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2924243775295564822006985 2193182831471673616505239)
              ·
                refine ⟨3289774247207510424757859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2193182831471673616505239 3289774247207510424757859)
                ·
                  refine ⟨4934661370811265637136789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3289774247207510424757859 4934661370811265637136789)
                  ·
                    refine ⟨231312251756778076740787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4934661370811265637136789 231312251756778076740787)
                    ·
                      rfl

theorem cell23_1351437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_1351437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351437 prefixEnd_1351437 := by exact prefixLift 1351437
  have htrace : WordTrace (prefixWord ++ tailWord_1351437) baseStart_1351437 baseEnd_1351437 := by
    simpa [prefixWord, tailWord_1351437, baseEnd_1351437] using wordTrace_append hprefix tailTrace_1351437
  have hstable : (prefixWord ++ tailWord_1351437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351437).length < 2 ^ (prefixWord ++ tailWord_1351437).sum := by decide
  have hdescent : baseEnd_1351437 < baseStart_1351437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351444 : List Nat := [2, 4, 4, 1, 1, 1, 1, 2, 3, 2, 2]
def baseStart_1351444 : Nat := 118140960795 + 1351444 * 2 ^ 59
def prefixEnd_1351444 : Nat := 4983230072969 + 3 ^ 40 * 1351444 * 2
def baseEnd_1351444 : Nat := 693940349634915702834829

theorem tailTrace_1351444 : CollatzResearch.WordTrace tailWord_1351444 prefixEnd_1351444 693940349634915702834829 := by
  unfold tailWord_1351444
  simp only [CollatzResearch.WordTrace]
  refine ⟨24645606057978335552362693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32860808077304447403150257 24645606057978335552362693)
  ·
    refine ⟨4621051135870937916068005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24645606057978335552362693 4621051135870937916068005)
    ·
      refine ⟨866447087975800859262751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4621051135870937916068005 866447087975800859262751)
      ·
        refine ⟨1299670631963701288894127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 866447087975800859262751 1299670631963701288894127)
        ·
          refine ⟨1949505947945551933341191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1299670631963701288894127 1949505947945551933341191)
          ·
            refine ⟨2924258921918327900011787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1949505947945551933341191 2924258921918327900011787)
            ·
              refine ⟨4386388382877491850017681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2924258921918327900011787 4386388382877491850017681)
              ·
                refine ⟨3289791287158118887513261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4386388382877491850017681 3289791287158118887513261)
                ·
                  refine ⟨1233671732684294582817473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3289791287158118887513261 1233671732684294582817473)
                  ·
                    refine ⟨925253799513220937113105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1233671732684294582817473 925253799513220937113105)
                    ·
                      refine ⟨693940349634915702834829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 925253799513220937113105 693940349634915702834829)
                      ·
                        rfl

theorem cell23_1351444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_1351444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351444 prefixEnd_1351444 := by exact prefixLift 1351444
  have htrace : WordTrace (prefixWord ++ tailWord_1351444) baseStart_1351444 baseEnd_1351444 := by
    simpa [prefixWord, tailWord_1351444, baseEnd_1351444] using wordTrace_append hprefix tailTrace_1351444
  have hstable : (prefixWord ++ tailWord_1351444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351444).length < 2 ^ (prefixWord ++ tailWord_1351444).sum := by decide
  have hdescent : baseEnd_1351444 < baseStart_1351444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351476 : List Nat := [2, 5, 1, 1, 2, 1, 1, 2, 2, 6]
def baseStart_1351476 : Nat := 118140960795 + 1351476 * 2 ^ 59
def prefixEnd_1351476 : Nat := 4983230072969 + 3 ^ 40 * 1351476 * 2
def baseEnd_1351476 : Nat := 231318927005286525878227

theorem tailTrace_1351476 : CollatzResearch.WordTrace tailWord_1351476 prefixEnd_1351476 231318927005286525878227 := by
  unfold tailWord_1351476
  simp only [CollatzResearch.WordTrace]
  refine ⟨24646189625920370284945141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32861586167893827046593521 24646189625920370284945141)
  ·
    refine ⟨2310580277430034714213607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24646189625920370284945141 2310580277430034714213607)
    ·
      refine ⟨3465870416145052071320411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2310580277430034714213607 3465870416145052071320411)
      ·
        refine ⟨5198805624217578106980617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3465870416145052071320411 5198805624217578106980617)
        ·
          refine ⟨3899104218163183580235463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5198805624217578106980617 3899104218163183580235463)
          ·
            refine ⟨5848656327244775370353195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3899104218163183580235463 5848656327244775370353195)
            ·
              refine ⟨8772984490867163055529793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5848656327244775370353195 8772984490867163055529793)
              ·
                refine ⟨6579738368150372291647345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8772984490867163055529793 6579738368150372291647345)
                ·
                  refine ⟨4934803776112779218735509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6579738368150372291647345 4934803776112779218735509)
                  ·
                    refine ⟨231318927005286525878227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4934803776112779218735509 231318927005286525878227)
                    ·
                      rfl

theorem cell23_1351476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 2, 2, 6].length) (baseStart_1351476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351476 prefixEnd_1351476 := by exact prefixLift 1351476
  have htrace : WordTrace (prefixWord ++ tailWord_1351476) baseStart_1351476 baseEnd_1351476 := by
    simpa [prefixWord, tailWord_1351476, baseEnd_1351476] using wordTrace_append hprefix tailTrace_1351476
  have hstable : (prefixWord ++ tailWord_1351476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351476).length < 2 ^ (prefixWord ++ tailWord_1351476).sum := by decide
  have hdescent : baseEnd_1351476 < baseStart_1351476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351477 : List Nat := [1, 3, 3, 1, 5, 1, 1, 2, 2, 1, 3]
def baseStart_1351477 : Nat := 118140960795 + 1351477 * 2 ^ 59
def prefixEnd_1351477 : Nat := 4983230072969 + 3 ^ 40 * 1351477 * 2
def baseEnd_1351477 : Nat := 693957294496514073722177

theorem tailTrace_1351477 : CollatzResearch.WordTrace tailWord_1351477 prefixEnd_1351477 693957294496514073722177 := by
  unfold tailWord_1351477
  simp only [CollatzResearch.WordTrace]
  refine ⟨49292415724837117740676685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32861610483224745160451123 49292415724837117740676685)
  ·
    refine ⟨18484655896813919152753757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49292415724837117740676685 18484655896813919152753757)
    ·
      refine ⟨6931745961305219682282659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18484655896813919152753757 6931745961305219682282659)
      ·
        refine ⟨10397618941957829523423989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6931745961305219682282659 10397618941957829523423989)
        ·
          refine ⟨974776775808546517820999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10397618941957829523423989 974776775808546517820999)
          ·
            refine ⟨1462165163712819776731499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 974776775808546517820999 1462165163712819776731499)
            ·
              refine ⟨2193247745569229665097249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462165163712819776731499 2193247745569229665097249)
              ·
                refine ⟨1644935809176922248822937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2193247745569229665097249 1644935809176922248822937)
                ·
                  refine ⟨1233701856882691686617203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1644935809176922248822937 1233701856882691686617203)
                  ·
                    refine ⟨1850552785324037529925805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1233701856882691686617203 1850552785324037529925805)
                    ·
                      refine ⟨693957294496514073722177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1850552785324037529925805 693957294496514073722177)
                      ·
                        rfl

theorem cell23_1351477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_1351477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351477 prefixEnd_1351477 := by exact prefixLift 1351477
  have htrace : WordTrace (prefixWord ++ tailWord_1351477) baseStart_1351477 baseEnd_1351477 := by
    simpa [prefixWord, tailWord_1351477, baseEnd_1351477] using wordTrace_append hprefix tailTrace_1351477
  have hstable : (prefixWord ++ tailWord_1351477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351477).length < 2 ^ (prefixWord ++ tailWord_1351477).sum := by decide
  have hdescent : baseEnd_1351477 < baseStart_1351477 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351494 : List Nat := [6, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3]
def baseStart_1351494 : Nat := 118140960795 + 1351494 * 2 ^ 59
def prefixEnd_1351494 : Nat := 4983230072969 + 3 ^ 40 * 1351494 * 2
def baseEnd_1351494 : Nat := 693966023667640507209599

theorem tailTrace_1351494 : CollatzResearch.WordTrace tailWord_1351494 prefixEnd_1351494 693966023667640507209599 := by
  unfold tailWord_1351494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1540407367680485301376423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32862023843850353096030357 1540407367680485301376423)
  ·
    refine ⟨2310611051520727952064635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1540407367680485301376423 2310611051520727952064635)
    ·
      refine ⟨3465916577281091928096953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2310611051520727952064635 3465916577281091928096953)
      ·
        refine ⟨2599437432960818946072715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3465916577281091928096953 2599437432960818946072715)
        ·
          refine ⟨3899156149441228419109073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2599437432960818946072715 3899156149441228419109073)
          ·
            refine ⟨2924367112080921314331805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3899156149441228419109073 2924367112080921314331805)
            ·
              refine ⟨1096637667030345492874427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2924367112080921314331805 1096637667030345492874427)
              ·
                refine ⟨1644956500545518239311641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1096637667030345492874427 1644956500545518239311641)
                ·
                  refine ⟨1233717375409138679483731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1644956500545518239311641 1233717375409138679483731)
                  ·
                    refine ⟨1850576063113708019225597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1233717375409138679483731 1850576063113708019225597)
                    ·
                      refine ⟨693966023667640507209599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1850576063113708019225597 693966023667640507209599)
                      ·
                        rfl

theorem cell23_1351494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_1351494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351494 prefixEnd_1351494 := by exact prefixLift 1351494
  have htrace : WordTrace (prefixWord ++ tailWord_1351494) baseStart_1351494 baseEnd_1351494 := by
    simpa [prefixWord, tailWord_1351494, baseEnd_1351494] using wordTrace_append hprefix tailTrace_1351494
  have hstable : (prefixWord ++ tailWord_1351494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351494).length < 2 ^ (prefixWord ++ tailWord_1351494).sum := by decide
  have hdescent : baseEnd_1351494 < baseStart_1351494 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351500 : List Nat := [2, 2, 1, 3, 4, 2, 1, 1, 1, 4, 2]
def baseStart_1351500 : Nat := 118140960795 + 1351500 * 2 ^ 59
def prefixEnd_1351500 : Nat := 4983230072969 + 3 ^ 40 * 1351500 * 2
def baseEnd_1351500 : Nat := 693969104551567483734571

theorem tailTrace_1351500 : CollatzResearch.WordTrace tailWord_1351500 prefixEnd_1351500 693969104551567483734571 := by
  unfold tailWord_1351500
  simp only [CollatzResearch.WordTrace]
  refine ⟨24646627301876896334381977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32862169735835861779175969 24646627301876896334381977)
  ·
    refine ⟨18484970476407672250786483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24646627301876896334381977 18484970476407672250786483)
    ·
      refine ⟨27727455714611508376179725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18484970476407672250786483 27727455714611508376179725)
      ·
        refine ⟨10397795892979315641067397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27727455714611508376179725 10397795892979315641067397)
        ·
          refine ⟨1949586729933621682700137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10397795892979315641067397 1949586729933621682700137)
          ·
            refine ⟨1462190047450216262025103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1949586729933621682700137 1462190047450216262025103)
            ·
              refine ⟨2193285071175324393037655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462190047450216262025103 2193285071175324393037655)
              ·
                refine ⟨3289927606762986589556483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2193285071175324393037655 3289927606762986589556483)
                ·
                  refine ⟨4934891410144479884334725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3289927606762986589556483 4934891410144479884334725)
                  ·
                    refine ⟨925292139402089978312761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4934891410144479884334725 925292139402089978312761)
                    ·
                      refine ⟨693969104551567483734571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 925292139402089978312761 693969104551567483734571)
                      ·
                        rfl

theorem cell23_1351500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 1, 1, 1, 4, 2].length) (baseStart_1351500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351500 prefixEnd_1351500 := by exact prefixLift 1351500
  have htrace : WordTrace (prefixWord ++ tailWord_1351500) baseStart_1351500 baseEnd_1351500 := by
    simpa [prefixWord, tailWord_1351500, baseEnd_1351500] using wordTrace_append hprefix tailTrace_1351500
  have hstable : (prefixWord ++ tailWord_1351500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351500).length < 2 ^ (prefixWord ++ tailWord_1351500).sum := by decide
  have hdescent : baseEnd_1351500 < baseStart_1351500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351519 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 1, 7]
def baseStart_1351519 : Nat := 118140960795 + 1351519 * 2 ^ 59
def prefixEnd_1351519 : Nat := 4983230072969 + 3 ^ 40 * 1351519 * 2
def baseEnd_1351519 : Nat := 231326286894667636465661

theorem tailTrace_1351519 : CollatzResearch.WordTrace tailWord_1351519 prefixEnd_1351519 231326286894667636465661 := by
  unfold tailWord_1351519
  simp only [CollatzResearch.WordTrace]
  refine ⟨49293947590684958913705611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32862631727123305942470407 49293947590684958913705611)
  ·
    refine ⟨73940921386027438370558417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49293947590684958913705611 73940921386027438370558417)
    ·
      refine ⟨55455691039520578777918813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73940921386027438370558417 55455691039520578777918813)
      ·
        refine ⟨20795884139820217041719555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55455691039520578777918813 20795884139820217041719555)
        ·
          refine ⟨31193826209730325562579333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20795884139820217041719555 31193826209730325562579333)
          ·
            refine ⟨5848842414324436042983625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31193826209730325562579333 5848842414324436042983625)
            ·
              refine ⟨4386631810743327032237719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5848842414324436042983625 4386631810743327032237719)
              ·
                refine ⟨6579947716114990548356579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4386631810743327032237719 6579947716114990548356579)
                ·
                  refine ⟨9869921574172485822534869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6579947716114990548356579 9869921574172485822534869)
                  ·
                    refine ⟨231326286894667636465661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9869921574172485822534869 231326286894667636465661)
                    ·
                      rfl

theorem cell23_1351519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 1, 7].length) (baseStart_1351519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351519 prefixEnd_1351519 := by exact prefixLift 1351519
  have htrace : WordTrace (prefixWord ++ tailWord_1351519) baseStart_1351519 baseEnd_1351519 := by
    simpa [prefixWord, tailWord_1351519, baseEnd_1351519] using wordTrace_append hprefix tailTrace_1351519
  have hstable : (prefixWord ++ tailWord_1351519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351519).length < 2 ^ (prefixWord ++ tailWord_1351519).sum := by decide
  have hdescent : baseEnd_1351519 < baseStart_1351519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351569 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 4]
def baseStart_1351569 : Nat := 118140960795 + 1351569 * 2 ^ 59
def prefixEnd_1351569 : Nat := 4983230072969 + 3 ^ 40 * 1351569 * 2
def baseEnd_1351569 : Nat := 694004534716727713771753

theorem tailTrace_1351569 : CollatzResearch.WordTrace tailWord_1351569 prefixEnd_1351569 694004534716727713771753 := by
  unfold tailWord_1351569
  simp only [CollatzResearch.WordTrace]
  refine ⟨49295771240503817453025761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32863847493669211635350507 49295771240503817453025761)
  ·
    refine ⟨36971828430377863089769321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49295771240503817453025761 36971828430377863089769321)
    ·
      refine ⟨27728871322783397317326991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36971828430377863089769321 27728871322783397317326991)
      ·
        refine ⟨41593306984175095975990487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27728871322783397317326991 41593306984175095975990487)
        ·
          refine ⟨62389960476262643963985731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41593306984175095975990487 62389960476262643963985731)
          ·
            refine ⟨93584940714393965945978597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62389960476262643963985731 93584940714393965945978597)
            ·
              refine ⟨17547176383948868614870987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93584940714393965945978597 17547176383948868614870987)
              ·
                refine ⟨26320764575923302922306481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17547176383948868614870987 26320764575923302922306481)
                ·
                  refine ⟨19740573431942477191729861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26320764575923302922306481 19740573431942477191729861)
                  ·
                    refine ⟨3701357518489214473449349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19740573431942477191729861 3701357518489214473449349)
                    ·
                      refine ⟨694004534716727713771753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3701357518489214473449349 694004534716727713771753)
                      ·
                        rfl

theorem cell23_1351569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_1351569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351569 prefixEnd_1351569 := by exact prefixLift 1351569
  have htrace : WordTrace (prefixWord ++ tailWord_1351569) baseStart_1351569 baseEnd_1351569 := by
    simpa [prefixWord, tailWord_1351569, baseEnd_1351569] using wordTrace_append hprefix tailTrace_1351569
  have hstable : (prefixWord ++ tailWord_1351569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351569).length < 2 ^ (prefixWord ++ tailWord_1351569).sum := by decide
  have hdescent : baseEnd_1351569 < baseStart_1351569 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351599 : List Nat := [1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 6]
def baseStart_1351599 : Nat := 118140960795 + 1351599 * 2 ^ 59
def prefixEnd_1351599 : Nat := 4983230072969 + 3 ^ 40 * 1351599 * 2
def baseEnd_1351599 : Nat := 694019939136362596396615

theorem tailTrace_1351599 : CollatzResearch.WordTrace tailWord_1351599 prefixEnd_1351599 694019939136362596396615 := by
  unfold tailWord_1351599
  simp only [CollatzResearch.WordTrace]
  refine ⟨49296865430395132576617851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32864576953596755051078567 49296865430395132576617851)
  ·
    refine ⟨73945298145592698864926777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49296865430395132576617851 73945298145592698864926777)
    ·
      refine ⟨55458973609194524148695083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73945298145592698864926777 55458973609194524148695083)
      ·
        refine ⟨83188460413791786223042625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55458973609194524148695083 83188460413791786223042625)
        ·
          refine ⟨62391345310343839667281969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83188460413791786223042625 62391345310343839667281969)
          ·
            refine ⟨46793508982757879750461477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62391345310343839667281969 46793508982757879750461477)
            ·
              refine ⟨8773782934267102453211527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46793508982757879750461477 8773782934267102453211527)
              ·
                refine ⟨13160674401400653679817291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8773782934267102453211527 13160674401400653679817291)
                ·
                  refine ⟨19741011602100980519725937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13160674401400653679817291 19741011602100980519725937)
                  ·
                    refine ⟨14805758701575735389794453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19741011602100980519725937 14805758701575735389794453)
                    ·
                      refine ⟨694019939136362596396615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14805758701575735389794453 694019939136362596396615)
                      ·
                        rfl

theorem cell23_1351599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_1351599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351599 prefixEnd_1351599 := by exact prefixLift 1351599
  have htrace : WordTrace (prefixWord ++ tailWord_1351599) baseStart_1351599 baseEnd_1351599 := by
    simpa [prefixWord, tailWord_1351599, baseEnd_1351599] using wordTrace_append hprefix tailTrace_1351599
  have hstable : (prefixWord ++ tailWord_1351599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351599).length < 2 ^ (prefixWord ++ tailWord_1351599).sum := by decide
  have hdescent : baseEnd_1351599 < baseStart_1351599 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351626 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 3, 5]
def baseStart_1351626 : Nat := 118140960795 + 1351626 * 2 ^ 59
def prefixEnd_1351626 : Nat := 4983230072969 + 3 ^ 40 * 1351626 * 2
def baseEnd_1351626 : Nat := 231344601038011330252997

theorem tailTrace_1351626 : CollatzResearch.WordTrace tailWord_1351626 prefixEnd_1351626 231344601038011330252997 := by
  unfold tailWord_1351626
  simp only [CollatzResearch.WordTrace]
  refine ⟨12324462550324329046962683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32865233467531544125233821 12324462550324329046962683)
  ·
    refine ⟨18486693825486493570444025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12324462550324329046962683 18486693825486493570444025)
    ·
      refine ⟨13865020369114870177833019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18486693825486493570444025 13865020369114870177833019)
      ·
        refine ⟨20797530553672305266749529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13865020369114870177833019 20797530553672305266749529)
        ·
          refine ⟨15598147915254228950062147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20797530553672305266749529 15598147915254228950062147)
          ·
            refine ⟨23397221872881343425093221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15598147915254228950062147 23397221872881343425093221)
            ·
              refine ⟨4386979101165251892204979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23397221872881343425093221 4386979101165251892204979)
              ·
                refine ⟨6580468651747877838307469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4386979101165251892204979 6580468651747877838307469)
                ·
                  refine ⟨2467675744405454189365301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6580468651747877838307469 2467675744405454189365301)
                  ·
                    refine ⟨231344601038011330252997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2467675744405454189365301 231344601038011330252997)
                    ·
                      rfl

theorem cell23_1351626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 3, 5].length) (baseStart_1351626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351626 prefixEnd_1351626 := by exact prefixLift 1351626
  have htrace : WordTrace (prefixWord ++ tailWord_1351626) baseStart_1351626 baseEnd_1351626 := by
    simpa [prefixWord, tailWord_1351626, baseEnd_1351626] using wordTrace_append hprefix tailTrace_1351626
  have hstable : (prefixWord ++ tailWord_1351626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351626).length < 2 ^ (prefixWord ++ tailWord_1351626).sum := by decide
  have hdescent : baseEnd_1351626 < baseStart_1351626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351633 : List Nat := [1, 2, 2, 1, 2, 1, 2, 5, 2, 3, 2]
def baseStart_1351633 : Nat := 118140960795 + 1351633 * 2 ^ 59
def prefixEnd_1351633 : Nat := 4983230072969 + 3 ^ 40 * 1351633 * 2
def baseEnd_1351633 : Nat := 694037397478615463371459

theorem tailTrace_1351633 : CollatzResearch.WordTrace tailWord_1351633 prefixEnd_1351633 694037397478615463371459 := by
  unfold tailWord_1351633
  simp only [CollatzResearch.WordTrace]
  refine ⟨49298105512271956383355553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32865403674847970922237035 49298105512271956383355553)
  ·
    refine ⟨36973579134203967287516665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49298105512271956383355553 36973579134203967287516665)
    ·
      refine ⟨27730184350652975465637499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36973579134203967287516665 27730184350652975465637499)
      ·
        refine ⟨41595276525979463198456249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27730184350652975465637499 41595276525979463198456249)
        ·
          refine ⟨31196457394484597398842187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41595276525979463198456249 31196457394484597398842187)
          ·
            refine ⟨46794686091726896098263281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31196457394484597398842187 46794686091726896098263281)
            ·
              refine ⟨35096014568795172073697461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46794686091726896098263281 35096014568795172073697461)
              ·
                refine ⟨3290251365824547381909137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35096014568795172073697461 3290251365824547381909137)
                ·
                  refine ⟨2467688524368410536431853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3290251365824547381909137 2467688524368410536431853)
                  ·
                    refine ⟨925383196638153951161945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2467688524368410536431853 925383196638153951161945)
                    ·
                      refine ⟨694037397478615463371459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 925383196638153951161945 694037397478615463371459)
                      ·
                        rfl

theorem cell23_1351633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 2, 3, 2].length) (baseStart_1351633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351633 prefixEnd_1351633 := by exact prefixLift 1351633
  have htrace : WordTrace (prefixWord ++ tailWord_1351633) baseStart_1351633 baseEnd_1351633 := by
    simpa [prefixWord, tailWord_1351633, baseEnd_1351633] using wordTrace_append hprefix tailTrace_1351633
  have hstable : (prefixWord ++ tailWord_1351633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351633).length < 2 ^ (prefixWord ++ tailWord_1351633).sum := by decide
  have hdescent : baseEnd_1351633 < baseStart_1351633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351673 : List Nat := [1, 2, 1, 3, 1, 6, 1, 1, 1, 6]
def baseStart_1351673 : Nat := 118140960795 + 1351673 * 2 ^ 59
def prefixEnd_1351673 : Nat := 4983230072969 + 3 ^ 40 * 1351673 * 2
def baseEnd_1351673 : Nat := 231352645568265102290425

theorem tailTrace_1351673 : CollatzResearch.WordTrace tailWord_1351673 prefixEnd_1351673 231352645568265102290425 := by
  unfold tailWord_1351673
  simp only [CollatzResearch.WordTrace]
  refine ⟨49299564432127043214811673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32866376288084695476541115 49299564432127043214811673)
  ·
    refine ⟨36974673324095282411108755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49299564432127043214811673 36974673324095282411108755)
    ·
      refine ⟨55462009986142923616663133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36974673324095282411108755 55462009986142923616663133)
      ·
        refine ⟨20798253744803596356248675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55462009986142923616663133 20798253744803596356248675)
        ·
          refine ⟨31197380617205394534373013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20798253744803596356248675 31197380617205394534373013)
          ·
            refine ⟨1462377216431502868798735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31197380617205394534373013 1462377216431502868798735)
            ·
              refine ⟨2193565824647254303198103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462377216431502868798735 2193565824647254303198103)
              ·
                refine ⟨3290348736970881454797155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2193565824647254303198103 3290348736970881454797155)
                ·
                  refine ⟨4935523105456322182195733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3290348736970881454797155 4935523105456322182195733)
                  ·
                    refine ⟨231352645568265102290425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4935523105456322182195733 231352645568265102290425)
                    ·
                      rfl

theorem cell23_1351673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 1, 1, 1, 6].length) (baseStart_1351673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351673 prefixEnd_1351673 := by exact prefixLift 1351673
  have htrace : WordTrace (prefixWord ++ tailWord_1351673) baseStart_1351673 baseEnd_1351673 := by
    simpa [prefixWord, tailWord_1351673, baseEnd_1351673] using wordTrace_append hprefix tailTrace_1351673
  have hstable : (prefixWord ++ tailWord_1351673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351673).length < 2 ^ (prefixWord ++ tailWord_1351673).sum := by decide
  have hdescent : baseEnd_1351673 < baseStart_1351673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351676 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 1, 1, 6]
def baseStart_1351676 : Nat := 118140960795 + 1351676 * 2 ^ 59
def prefixEnd_1351676 : Nat := 4983230072969 + 3 ^ 40 * 1351676 * 2
def baseEnd_1351676 : Nat := 694059477146758795133761

theorem tailTrace_1351676 : CollatzResearch.WordTrace tailWord_1351676 prefixEnd_1351676 694059477146758795133761 := by
  unfold tailWord_1351676
  simp only [CollatzResearch.WordTrace]
  refine ⟨24649836925558087363585441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32866449234077449818113921 24649836925558087363585441)
  ·
    refine ⟨18487377694168565522689081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24649836925558087363585441 18487377694168565522689081)
    ·
      refine ⟨13865533270626424142016811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18487377694168565522689081 13865533270626424142016811)
      ·
        refine ⟨20798299905939636213025217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13865533270626424142016811 20798299905939636213025217)
        ·
          refine ⟨15598724929454727159768913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20798299905939636213025217 15598724929454727159768913)
          ·
            refine ⟨11699043697091045369826685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15598724929454727159768913 11699043697091045369826685)
            ·
              refine ⟨4387141386409142013685007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11699043697091045369826685 4387141386409142013685007)
              ·
                refine ⟨6580712079613713020527511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4387141386409142013685007 6580712079613713020527511)
                ·
                  refine ⟨9871068119420569530791267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6580712079613713020527511 9871068119420569530791267)
                  ·
                    refine ⟨14806602179130854296186901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9871068119420569530791267 14806602179130854296186901)
                    ·
                      refine ⟨694059477146758795133761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14806602179130854296186901 694059477146758795133761)
                      ·
                        rfl

theorem cell23_1351676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_1351676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351676 prefixEnd_1351676 := by exact prefixLift 1351676
  have htrace : WordTrace (prefixWord ++ tailWord_1351676) baseStart_1351676 baseEnd_1351676 := by
    simpa [prefixWord, tailWord_1351676, baseEnd_1351676] using wordTrace_append hprefix tailTrace_1351676
  have hstable : (prefixWord ++ tailWord_1351676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351676).length < 2 ^ (prefixWord ++ tailWord_1351676).sum := by decide
  have hdescent : baseEnd_1351676 < baseStart_1351676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351703 : List Nat := [1, 1, 3, 5, 2, 2, 9]
def baseStart_1351703 : Nat := 118140960795 + 1351703 * 2 ^ 59
def prefixEnd_1351703 : Nat := 4983230072969 + 3 ^ 40 * 1351703 * 2
def baseEnd_1351703 : Nat := 8568806680548520857977

theorem tailTrace_1351703 : CollatzResearch.WordTrace tailWord_1351703 prefixEnd_1351703 8568806680548520857977 := by
  unfold tailWord_1351703
  simp only [CollatzResearch.WordTrace]
  refine ⟨49300658622018358338403763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32867105748012238892269175 49300658622018358338403763)
  ·
    refine ⟨73950987933027537507605645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49300658622018358338403763 73950987933027537507605645)
    ·
      refine ⟨27731620474885326565352117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73950987933027537507605645 27731620474885326565352117)
      ·
        refine ⟨2599839419520499365501761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 27731620474885326565352117 2599839419520499365501761)
        ·
          refine ⟨1949879564640374524126321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2599839419520499365501761 1949879564640374524126321)
          ·
            refine ⟨1462409673480280893094741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1949879564640374524126321 1462409673480280893094741)
            ·
              refine ⟨8568806680548520857977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1462409673480280893094741 8568806680548520857977)
              ·
                rfl

theorem cell23_1351703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 9].length) (baseStart_1351703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351703 prefixEnd_1351703 := by exact prefixLift 1351703
  have htrace : WordTrace (prefixWord ++ tailWord_1351703) baseStart_1351703 baseEnd_1351703 := by
    simpa [prefixWord, tailWord_1351703, baseEnd_1351703] using wordTrace_append hprefix tailTrace_1351703
  have hstable : (prefixWord ++ tailWord_1351703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351703).length < 2 ^ (prefixWord ++ tailWord_1351703).sum := by decide
  have hdescent : baseEnd_1351703 < baseStart_1351703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351720 : List Nat := [2, 1, 5, 3, 1, 1, 2, 8]
def baseStart_1351720 : Nat := 118140960795 + 1351720 * 2 ^ 59
def prefixEnd_1351720 : Nat := 4983230072969 + 3 ^ 40 * 1351720 * 2
def baseEnd_1351720 : Nat := 25706743344279874925317

theorem tailTrace_1351720 : CollatzResearch.WordTrace tailWord_1351720 prefixEnd_1351720 25706743344279874925317 := by
  unfold tailWord_1351720
  simp only [CollatzResearch.WordTrace]
  refine ⟨24650639331478385120886307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32867519108637846827848409 24650639331478385120886307)
  ·
    refine ⟨36975958997217577681329461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24650639331478385120886307 36975958997217577681329461)
    ·
      refine ⟨3466496155989147907624637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 36975958997217577681329461 3466496155989147907624637)
      ·
        refine ⟨1299936058495930465359239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3466496155989147907624637 1299936058495930465359239)
        ·
          refine ⟨1949904087743895698038859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1299936058495930465359239 1949904087743895698038859)
          ·
            refine ⟨2924856131615843547058289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1949904087743895698038859 2924856131615843547058289)
            ·
              refine ⟨2193642098711882660293717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2924856131615843547058289 2193642098711882660293717)
              ·
                refine ⟨25706743344279874925317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2193642098711882660293717 25706743344279874925317)
                ·
                  rfl

theorem cell23_1351720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 8].length) (baseStart_1351720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351720 prefixEnd_1351720 := by exact prefixLift 1351720
  have htrace : WordTrace (prefixWord ++ tailWord_1351720) baseStart_1351720 baseEnd_1351720 := by
    simpa [prefixWord, tailWord_1351720, baseEnd_1351720] using wordTrace_append hprefix tailTrace_1351720
  have hstable : (prefixWord ++ tailWord_1351720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351720).length < 2 ^ (prefixWord ++ tailWord_1351720).sum := by decide
  have hdescent : baseEnd_1351720 < baseStart_1351720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351740 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 3, 3, 2]
def baseStart_1351740 : Nat := 118140960795 + 1351740 * 2 ^ 59
def prefixEnd_1351740 : Nat := 4983230072969 + 3 ^ 40 * 1351740 * 2
def baseEnd_1351740 : Nat := 694092339908646544733467

theorem tailTrace_1351740 : CollatzResearch.WordTrace tailWord_1351740 prefixEnd_1351740 694092339908646544733467 := by
  unfold tailWord_1351740
  simp only [CollatzResearch.WordTrace]
  refine ⟨24651004061442156828750337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32868005415256209105000449 24651004061442156828750337)
  ·
    refine ⟨18488253046081617621562753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24651004061442156828750337 18488253046081617621562753)
    ·
      refine ⟨13866189784561213216172065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18488253046081617621562753 13866189784561213216172065)
      ·
        refine ⟨10399642338420909912129049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13866189784561213216172065 10399642338420909912129049)
        ·
          refine ⟨7799731753815682434096787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10399642338420909912129049 7799731753815682434096787)
          ·
            refine ⟨11699597630723523651145181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7799731753815682434096787 11699597630723523651145181)
            ·
              refine ⟨4387349111521321369179443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11699597630723523651145181 4387349111521321369179443)
              ·
                refine ⟨6581023667281982053769165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4387349111521321369179443 6581023667281982053769165)
                ·
                  refine ⟨2467883875230743270163437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6581023667281982053769165 2467883875230743270163437)
                  ·
                    refine ⟨925456453211528726311289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2467883875230743270163437 925456453211528726311289)
                    ·
                      refine ⟨694092339908646544733467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 925456453211528726311289 694092339908646544733467)
                      ·
                        rfl

theorem cell23_1351740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 3, 3, 2].length) (baseStart_1351740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351740 prefixEnd_1351740 := by exact prefixLift 1351740
  have htrace : WordTrace (prefixWord ++ tailWord_1351740) baseStart_1351740 baseEnd_1351740 := by
    simpa [prefixWord, tailWord_1351740, baseEnd_1351740] using wordTrace_append hprefix tailTrace_1351740
  have hstable : (prefixWord ++ tailWord_1351740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351740).length < 2 ^ (prefixWord ++ tailWord_1351740).sum := by decide
  have hdescent : baseEnd_1351740 < baseStart_1351740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351783 : List Nat := [1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_1351783 : Nat := 118140960795 + 1351783 * 2 ^ 59
def prefixEnd_1351783 : Nat := 4983230072969 + 3 ^ 40 * 1351783 * 2
def baseEnd_1351783 : Nat := 694114419576789876495769

theorem tailTrace_1351783 : CollatzResearch.WordTrace tailWord_1351783 prefixEnd_1351783 694114419576789876495769 := by
  unfold tailWord_1351783
  simp only [CollatzResearch.WordTrace]
  refine ⟨49303576461728532001316003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32869050974485688000877335 49303576461728532001316003)
  ·
    refine ⟨73955364692592798001974005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49303576461728532001316003 73955364692592798001974005)
    ·
      refine ⟨6933315439930574812685063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 73955364692592798001974005 6933315439930574812685063)
      ·
        refine ⟨10399973159895862219027595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6933315439930574812685063 10399973159895862219027595)
        ·
          refine ⟨15599959739843793328541393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10399973159895862219027595 15599959739843793328541393)
          ·
            refine ⟨11699969804882844996406045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15599959739843793328541393 11699969804882844996406045)
            ·
              refine ⟨4387488676831066873652267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11699969804882844996406045 4387488676831066873652267)
              ·
                refine ⟨6581233015246600310478401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4387488676831066873652267 6581233015246600310478401)
                ·
                  refine ⟨4935924761434950232858801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6581233015246600310478401 4935924761434950232858801)
                  ·
                    refine ⟨3701943571076212674644101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4935924761434950232858801 3701943571076212674644101)
                    ·
                      refine ⟨694114419576789876495769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3701943571076212674644101 694114419576789876495769)
                      ·
                        rfl

theorem cell23_1351783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_1351783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351783 prefixEnd_1351783 := by exact prefixLift 1351783
  have htrace : WordTrace (prefixWord ++ tailWord_1351783) baseStart_1351783 baseEnd_1351783 := by
    simpa [prefixWord, tailWord_1351783, baseEnd_1351783] using wordTrace_append hprefix tailTrace_1351783
  have hstable : (prefixWord ++ tailWord_1351783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351783).length < 2 ^ (prefixWord ++ tailWord_1351783).sum := by decide
  have hdescent : baseEnd_1351783 < baseStart_1351783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351838 : List Nat := [4, 3, 1, 1, 3, 1, 3, 1, 2, 2, 2]
def baseStart_1351838 : Nat := 118140960795 + 1351838 * 2 ^ 59
def prefixEnd_1351838 : Nat := 4983230072969 + 3 ^ 40 * 1351838 * 2
def baseEnd_1351838 : Nat := 694142661012787161308017

theorem tailTrace_1351838 : CollatzResearch.WordTrace tailWord_1351838 prefixEnd_1351838 694142661012787161308017 := by
  unfold tailWord_1351838
  simp only [CollatzResearch.WordTrace]
  refine ⟨6163197809566159549321021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32870388317686184263045445 6163197809566159549321021)
  ·
    refine ⟨2311199178587309830995383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6163197809566159549321021 2311199178587309830995383)
    ·
      refine ⟨3466798767880964746493075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2311199178587309830995383 3466798767880964746493075)
      ·
        refine ⟨5200198151821447119739613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3466798767880964746493075 5200198151821447119739613)
        ·
          refine ⟨1950074306933042669902355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5200198151821447119739613 1950074306933042669902355)
          ·
            refine ⟨2925111460399564004853533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1950074306933042669902355 2925111460399564004853533)
            ·
              refine ⟨1096916797649836501820075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2925111460399564004853533 1096916797649836501820075)
              ·
                refine ⟨1645375196474754752730113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1096916797649836501820075 1645375196474754752730113)
                ·
                  refine ⟨1234031397356066064547585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1645375196474754752730113 1234031397356066064547585)
                  ·
                    refine ⟨925523548017049548410689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1234031397356066064547585 925523548017049548410689)
                    ·
                      refine ⟨694142661012787161308017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 925523548017049548410689 694142661012787161308017)
                      ·
                        rfl

theorem cell23_1351838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 3, 1, 2, 2, 2].length) (baseStart_1351838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351838 prefixEnd_1351838 := by exact prefixLift 1351838
  have htrace : WordTrace (prefixWord ++ tailWord_1351838) baseStart_1351838 baseEnd_1351838 := by
    simpa [prefixWord, tailWord_1351838, baseEnd_1351838] using wordTrace_append hprefix tailTrace_1351838
  have hstable : (prefixWord ++ tailWord_1351838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351838).length < 2 ^ (prefixWord ++ tailWord_1351838).sum := by decide
  have hdescent : baseEnd_1351838 < baseStart_1351838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351861 : List Nat := [1, 3, 3, 4, 2, 1, 1, 3, 5]
def baseStart_1351861 : Nat := 118140960795 + 1351861 * 2 ^ 59
def prefixEnd_1351861 : Nat := 4983230072969 + 3 ^ 40 * 1351861 * 2
def baseEnd_1351861 : Nat := 77128274563093396813379

theorem tailTrace_1351861 : CollatzResearch.WordTrace tailWord_1351861 prefixEnd_1351861 77128274563093396813379 := by
  unfold tailWord_1351861
  simp only [CollatzResearch.WordTrace]
  refine ⟨49306421355445951322655437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32870947570297300881770291 49306421355445951322655437)
  ·
    refine ⟨18489908008292231745995789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49306421355445951322655437 18489908008292231745995789)
    ·
      refine ⟨6933715503109586904748421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18489908008292231745995789 6933715503109586904748421)
      ·
        refine ⟨1300071656833047544640329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6933715503109586904748421 1300071656833047544640329)
        ·
          refine ⟨975053742624785658480247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1300071656833047544640329 975053742624785658480247)
          ·
            refine ⟨1462580613937178487720371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975053742624785658480247 1462580613937178487720371)
            ·
              refine ⟨2193870920905767731580557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462580613937178487720371 2193870920905767731580557)
              ·
                refine ⟨822701595339662899342709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2193870920905767731580557 822701595339662899342709)
                ·
                  refine ⟨77128274563093396813379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 822701595339662899342709 77128274563093396813379)
                  ·
                    rfl

theorem cell23_1351861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 3, 5].length) (baseStart_1351861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351861 prefixEnd_1351861 := by exact prefixLift 1351861
  have htrace : WordTrace (prefixWord ++ tailWord_1351861) baseStart_1351861 baseEnd_1351861 := by
    simpa [prefixWord, tailWord_1351861, baseEnd_1351861] using wordTrace_append hprefix tailTrace_1351861
  have hstable : (prefixWord ++ tailWord_1351861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351861).length < 2 ^ (prefixWord ++ tailWord_1351861).sum := by decide
  have hdescent : baseEnd_1351861 < baseStart_1351861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351874 : List Nat := [3, 5, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_1351874 : Nat := 118140960795 + 1351874 * 2 ^ 59
def prefixEnd_1351874 : Nat := 4983230072969 + 3 ^ 40 * 1351874 * 2
def baseEnd_1351874 : Nat := 231387048772116340152617

theorem tailTrace_1351874 : CollatzResearch.WordTrace tailWord_1351874 prefixEnd_1351874 231387048772116340152617 := by
  unfold tailWord_1351874
  simp only [CollatzResearch.WordTrace]
  refine ⟨12326723876099713635719669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32871263669599236361919117 12326723876099713635719669)
  ·
    refine ⟨1155630363384348153348719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12326723876099713635719669 1155630363384348153348719)
    ·
      refine ⟨1733445545076522230023079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1155630363384348153348719 1733445545076522230023079)
      ·
        refine ⟨2600168317614783345034619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1733445545076522230023079 2600168317614783345034619)
        ·
          refine ⟨3900252476422175017551929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2600168317614783345034619 3900252476422175017551929)
          ·
            refine ⟨2925189357316631263163947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3900252476422175017551929 2925189357316631263163947)
            ·
              refine ⟨4387784035974946894745921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2925189357316631263163947 4387784035974946894745921)
              ·
                refine ⟨3290838026981210171059441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4387784035974946894745921 3290838026981210171059441)
                ·
                  refine ⟨2468128520235907628294581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3290838026981210171059441 2468128520235907628294581)
                  ·
                    refine ⟨231387048772116340152617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2468128520235907628294581 231387048772116340152617)
                    ·
                      rfl

theorem cell23_1351874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_1351874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351874 prefixEnd_1351874 := by exact prefixLift 1351874
  have htrace : WordTrace (prefixWord ++ tailWord_1351874) baseStart_1351874 baseEnd_1351874 := by
    simpa [prefixWord, tailWord_1351874, baseEnd_1351874] using wordTrace_append hprefix tailTrace_1351874
  have hstable : (prefixWord ++ tailWord_1351874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351874).length < 2 ^ (prefixWord ++ tailWord_1351874).sum := by decide
  have hdescent : baseEnd_1351874 < baseStart_1351874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351883 : List Nat := [1, 1, 1, 1, 3, 2, 4, 4, 6]
def baseStart_1351883 : Nat := 118140960795 + 1351883 * 2 ^ 59
def prefixEnd_1351883 : Nat := 4983230072969 + 3 ^ 40 * 1351883 * 2
def baseEnd_1351883 : Nat := 77129529738026609471701

theorem tailTrace_1351883 : CollatzResearch.WordTrace tailWord_1351883 prefixEnd_1351883 77129529738026609471701 := by
  unfold tailWord_1351883
  simp only [CollatzResearch.WordTrace]
  refine ⟨49307223761366249079956303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32871482507577499386637535 49307223761366249079956303)
  ·
    refine ⟨73960835642049373619934455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49307223761366249079956303 73960835642049373619934455)
    ·
      refine ⟨110941253463074060429901683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73960835642049373619934455 110941253463074060429901683)
      ·
        refine ⟨166411880194611090644852525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110941253463074060429901683 166411880194611090644852525)
        ·
          refine ⟨62404455072979158991819697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166411880194611090644852525 62404455072979158991819697)
          ·
            refine ⟨46803341304734369243864773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62404455072979158991819697 46803341304734369243864773)
            ·
              refine ⟨8775626494637694233224645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46803341304734369243864773 8775626494637694233224645)
              ·
                refine ⟨1645429967744567668729621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8775626494637694233224645 1645429967744567668729621)
                ·
                  refine ⟨77129529738026609471701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1645429967744567668729621 77129529738026609471701)
                  ·
                    rfl

theorem cell23_1351883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 6].length) (baseStart_1351883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351883 prefixEnd_1351883 := by exact prefixLift 1351883
  have htrace : WordTrace (prefixWord ++ tailWord_1351883) baseStart_1351883 baseEnd_1351883 := by
    simpa [prefixWord, tailWord_1351883, baseEnd_1351883] using wordTrace_append hprefix tailTrace_1351883
  have hstable : (prefixWord ++ tailWord_1351883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351883).length < 2 ^ (prefixWord ++ tailWord_1351883).sum := by decide
  have hdescent : baseEnd_1351883 < baseStart_1351883 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351913 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 3, 5]
def baseStart_1351913 : Nat := 118140960795 + 1351913 * 2 ^ 59
def prefixEnd_1351913 : Nat := 4983230072969 + 3 ^ 40 * 1351913 * 2
def baseEnd_1351913 : Nat := 231393724020624789290057

theorem tailTrace_1351913 : CollatzResearch.WordTrace tailWord_1351913 prefixEnd_1351913 231393724020624789290057 := by
  unfold tailWord_1351913
  simp only [CollatzResearch.WordTrace]
  refine ⟨49308317951257564203548393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32872211967505042802365595 49308317951257564203548393)
  ·
    refine ⟨36981238463443173152661295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49308317951257564203548393 36981238463443173152661295)
    ·
      refine ⟨55471857695164759728991943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36981238463443173152661295 55471857695164759728991943)
      ·
        refine ⟨83207786542747139593487915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55471857695164759728991943 83207786542747139593487915)
        ·
          refine ⟨124811679814120709390231873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83207786542747139593487915 124811679814120709390231873)
          ·
            refine ⟨93608759860590532042673905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 124811679814120709390231873 93608759860590532042673905)
            ·
              refine ⟨70206569895442899032005429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93608759860590532042673905 70206569895442899032005429)
              ·
                refine ⟨6581865927697771784250509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70206569895442899032005429 6581865927697771784250509)
                ·
                  refine ⟨2468199722886664419093941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6581865927697771784250509 2468199722886664419093941)
                  ·
                    refine ⟨231393724020624789290057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2468199722886664419093941 231393724020624789290057)
                    ·
                      rfl

theorem cell23_1351913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 3, 5].length) (baseStart_1351913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351913 prefixEnd_1351913 := by exact prefixLift 1351913
  have htrace : WordTrace (prefixWord ++ tailWord_1351913) baseStart_1351913 baseEnd_1351913 := by
    simpa [prefixWord, tailWord_1351913, baseEnd_1351913] using wordTrace_append hprefix tailTrace_1351913
  have hstable : (prefixWord ++ tailWord_1351913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351913).length < 2 ^ (prefixWord ++ tailWord_1351913).sum := by decide
  have hdescent : baseEnd_1351913 < baseStart_1351913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351920 : List Nat := [2, 1, 1, 1, 3, 1, 1, 5, 1, 5, 2]
def baseStart_1351920 : Nat := 118140960795 + 1351920 * 2 ^ 59
def prefixEnd_1351920 : Nat := 4983230072969 + 3 ^ 40 * 1351920 * 2
def baseEnd_1351920 : Nat := 694184766426455840482639

theorem tailTrace_1351920 : CollatzResearch.WordTrace tailWord_1351920 prefixEnd_1351920 694184766426455840482639 := by
  unfold tailWord_1351920
  simp only [CollatzResearch.WordTrace]
  refine ⟨24654286631116102199526607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32872382174821469599368809 24654286631116102199526607)
  ·
    refine ⟨36981429946674153299289911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24654286631116102199526607 36981429946674153299289911)
    ·
      refine ⟨55472144920011229948934867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36981429946674153299289911 55472144920011229948934867)
      ·
        refine ⟨83208217380016844923402301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55472144920011229948934867 83208217380016844923402301)
        ·
          refine ⟨31203081517506316846275863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83208217380016844923402301 31203081517506316846275863)
          ·
            refine ⟨46804622276259475269413795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31203081517506316846275863 46804622276259475269413795)
            ·
              refine ⟨70206933414389212904120693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46804622276259475269413795 70206933414389212904120693)
              ·
                refine ⟨6581900007598988709761315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 70206933414389212904120693 6581900007598988709761315)
                ·
                  refine ⟨9872850011398483064641973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6581900007598988709761315 9872850011398483064641973)
                  ·
                    refine ⟨925579688568607787310185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9872850011398483064641973 925579688568607787310185)
                    ·
                      refine ⟨694184766426455840482639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 925579688568607787310185 694184766426455840482639)
                      ·
                        rfl

theorem cell23_1351920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 5, 1, 5, 2].length) (baseStart_1351920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351920 prefixEnd_1351920 := by exact prefixLift 1351920
  have htrace : WordTrace (prefixWord ++ tailWord_1351920) baseStart_1351920 baseEnd_1351920 := by
    simpa [prefixWord, tailWord_1351920, baseEnd_1351920] using wordTrace_append hprefix tailTrace_1351920
  have hstable : (prefixWord ++ tailWord_1351920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351920).length < 2 ^ (prefixWord ++ tailWord_1351920).sum := by decide
  have hdescent : baseEnd_1351920 < baseStart_1351920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351937 : List Nat := [1, 2, 4, 1, 1, 2, 1, 4, 2, 3, 2]
def baseStart_1351937 : Nat := 118140960795 + 1351937 * 2 ^ 59
def prefixEnd_1351937 : Nat := 4983230072969 + 3 ^ 40 * 1351937 * 2
def baseEnd_1351937 : Nat := 694193495597582273970061

theorem tailTrace_1351937 : CollatzResearch.WordTrace tailWord_1351937 prefixEnd_1351937 694193495597582273970061 := by
  unfold tailWord_1351937
  simp only [CollatzResearch.WordTrace]
  refine ⟨49309193303170616302422065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32872795535447077534948043 49309193303170616302422065)
  ·
    refine ⟨36981894977377962226816549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49309193303170616302422065 36981894977377962226816549)
    ·
      refine ⟨6934105308258367917528103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36981894977377962226816549 6934105308258367917528103)
      ·
        refine ⟨10401157962387551876292155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6934105308258367917528103 10401157962387551876292155)
        ·
          refine ⟨15601736943581327814438233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10401157962387551876292155 15601736943581327814438233)
          ·
            refine ⟨11701302707685995860828675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15601736943581327814438233 11701302707685995860828675)
            ·
              refine ⟨17551954061528993791243013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11701302707685995860828675 17551954061528993791243013)
              ·
                refine ⟨3290991386536686335858065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17551954061528993791243013 3290991386536686335858065)
                ·
                  refine ⟨2468243539902514751893549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3290991386536686335858065 2468243539902514751893549)
                  ·
                    refine ⟨925591327463443031960081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2468243539902514751893549 925591327463443031960081)
                    ·
                      refine ⟨694193495597582273970061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 925591327463443031960081 694193495597582273970061)
                      ·
                        rfl

theorem cell23_1351937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 2, 3, 2].length) (baseStart_1351937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351937 prefixEnd_1351937 := by exact prefixLift 1351937
  have htrace : WordTrace (prefixWord ++ tailWord_1351937) baseStart_1351937 baseEnd_1351937 := by
    simpa [prefixWord, tailWord_1351937, baseEnd_1351937] using wordTrace_append hprefix tailTrace_1351937
  have hstable : (prefixWord ++ tailWord_1351937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351937).length < 2 ^ (prefixWord ++ tailWord_1351937).sum := by decide
  have hdescent : baseEnd_1351937 < baseStart_1351937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351938 : List Nat := [3, 4, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_1351938 : Nat := 118140960795 + 1351938 * 2 ^ 59
def prefixEnd_1351938 : Nat := 4983230072969 + 3 ^ 40 * 1351938 * 2
def baseEnd_1351938 : Nat := 231398003026078923352519

theorem tailTrace_1351938 : CollatzResearch.WordTrace tailWord_1351938 prefixEnd_1351938 231398003026078923352519 := by
  unfold tailWord_1351938
  simp only [CollatzResearch.WordTrace]
  refine ⟨12327307444041748368302117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32872819850777995648805645 12327307444041748368302117)
  ·
    refine ⟨2311370145757827819056647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12327307444041748368302117 2311370145757827819056647)
    ·
      refine ⟨3467055218636741728584971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2311370145757827819056647 3467055218636741728584971)
      ·
        refine ⟨5200582827955112592877457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3467055218636741728584971 5200582827955112592877457)
        ·
          refine ⟨3900437120966334444658093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5200582827955112592877457 3900437120966334444658093)
          ·
            refine ⟨1462663920362375416746785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3900437120966334444658093 1462663920362375416746785)
            ·
              refine ⟨1096997940271781562560089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1462663920362375416746785 1096997940271781562560089)
              ·
                refine ⟨822748455203836171920067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1096997940271781562560089 822748455203836171920067)
                ·
                  refine ⟨1234122682805754257880101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 822748455203836171920067 1234122682805754257880101)
                  ·
                    refine ⟨231398003026078923352519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1234122682805754257880101 231398003026078923352519)
                    ·
                      rfl

theorem cell23_1351938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_1351938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351938 prefixEnd_1351938 := by exact prefixLift 1351938
  have htrace : WordTrace (prefixWord ++ tailWord_1351938) baseStart_1351938 baseEnd_1351938 := by
    simpa [prefixWord, tailWord_1351938, baseEnd_1351938] using wordTrace_append hprefix tailTrace_1351938
  have hstable : (prefixWord ++ tailWord_1351938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351938).length < 2 ^ (prefixWord ++ tailWord_1351938).sum := by decide
  have hdescent : baseEnd_1351938 < baseStart_1351938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351950 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4]
def baseStart_1351950 : Nat := 118140960795 + 1351950 * 2 ^ 59
def prefixEnd_1351950 : Nat := 4983230072969 + 3 ^ 40 * 1351950 * 2
def baseEnd_1351950 : Nat := 694200170846090723107501

theorem tailTrace_1351950 : CollatzResearch.WordTrace tailWord_1351950 prefixEnd_1351950 694200170846090723107501 := by
  unfold tailWord_1351950
  simp only [CollatzResearch.WordTrace]
  refine ⟨6163708431515439940330663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32873111634749013015096869 6163708431515439940330663)
  ·
    refine ⟨9245562647273159910495995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6163708431515439940330663 9245562647273159910495995)
    ·
      refine ⟨13868343970909739865743993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9245562647273159910495995 13868343970909739865743993)
      ·
        refine ⟨10401257978182304899307995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13868343970909739865743993 10401257978182304899307995)
        ·
          refine ⟨15601886967273457348961993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10401257978182304899307995 15601886967273457348961993)
          ·
            refine ⟨11701415225455093011721495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15601886967273457348961993 11701415225455093011721495)
            ·
              refine ⟨17552122838182639517582243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11701415225455093011721495 17552122838182639517582243)
              ·
                refine ⟨26328184257273959276373365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17552122838182639517582243 26328184257273959276373365)
                ·
                  refine ⟨2468267274119433682160003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26328184257273959276373365 2468267274119433682160003)
                  ·
                    refine ⟨3702400911179150523240005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2468267274119433682160003 3702400911179150523240005)
                    ·
                      refine ⟨694200170846090723107501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3702400911179150523240005 694200170846090723107501)
                      ·
                        rfl

theorem cell23_1351950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_1351950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351950 prefixEnd_1351950 := by exact prefixLift 1351950
  have htrace : WordTrace (prefixWord ++ tailWord_1351950) baseStart_1351950 baseEnd_1351950 := by
    simpa [prefixWord, tailWord_1351950, baseEnd_1351950] using wordTrace_append hprefix tailTrace_1351950
  have hstable : (prefixWord ++ tailWord_1351950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351950).length < 2 ^ (prefixWord ++ tailWord_1351950).sum := by decide
  have hdescent : baseEnd_1351950 < baseStart_1351950 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351960 : List Nat := [2, 1, 2, 3, 1, 2, 4, 1, 1, 6]
def baseStart_1351960 : Nat := 118140960795 + 1351960 * 2 ^ 59
def prefixEnd_1351960 : Nat := 4983230072969 + 3 ^ 40 * 1351960 * 2
def baseEnd_1351960 : Nat := 231401768550878561327485

theorem tailTrace_1351960 : CollatzResearch.WordTrace tailWord_1351960 prefixEnd_1351960 231401768550878561327485 := by
  unfold tailWord_1351960
  simp only [CollatzResearch.WordTrace]
  refine ⟨24655016091043645615254667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32873354788058194153672889 24655016091043645615254667)
  ·
    refine ⟨36982524136565468422882001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24655016091043645615254667 36982524136565468422882001)
    ·
      refine ⟨27736893102424101317161501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36982524136565468422882001 27736893102424101317161501)
      ·
        refine ⟨10401334913409037993935563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27736893102424101317161501 10401334913409037993935563)
        ·
          refine ⟨15602002370113556990903345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10401334913409037993935563 15602002370113556990903345)
          ·
            refine ⟨11701501777585167743177509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15602002370113556990903345 11701501777585167743177509)
            ·
              refine ⟨2194031583297218951845783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11701501777585167743177509 2194031583297218951845783)
              ·
                refine ⟨3291047374945828427768675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2194031583297218951845783 3291047374945828427768675)
                ·
                  refine ⟨4936571062418742641653013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3291047374945828427768675 4936571062418742641653013)
                  ·
                    refine ⟨231401768550878561327485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4936571062418742641653013 231401768550878561327485)
                    ·
                      rfl

theorem cell23_1351960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 4, 1, 1, 6].length) (baseStart_1351960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351960 prefixEnd_1351960 := by exact prefixLift 1351960
  have htrace : WordTrace (prefixWord ++ tailWord_1351960) baseStart_1351960 baseEnd_1351960 := by
    simpa [prefixWord, tailWord_1351960, baseEnd_1351960] using wordTrace_append hprefix tailTrace_1351960
  have hstable : (prefixWord ++ tailWord_1351960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351960).length < 2 ^ (prefixWord ++ tailWord_1351960).sum := by decide
  have hdescent : baseEnd_1351960 < baseStart_1351960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351963 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 6]
def baseStart_1351963 : Nat := 118140960795 + 1351963 * 2 ^ 59
def prefixEnd_1351963 : Nat := 4983230072969 + 3 ^ 40 * 1351963 * 2
def baseEnd_1351963 : Nat := 694206846094599172244941

theorem tailTrace_1351963 : CollatzResearch.WordTrace tailWord_1351963 prefixEnd_1351963 694206846094599172244941 := by
  unfold tailWord_1351963
  simp only [CollatzResearch.WordTrace]
  refine ⟨49310141601076422742868543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32873427734050948495245695 49310141601076422742868543)
  ·
    refine ⟨73965212401614634114302815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49310141601076422742868543 73965212401614634114302815)
    ·
      refine ⟨110947818602421951171454223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73965212401614634114302815 110947818602421951171454223)
      ·
        refine ⟨166421727903632926757181335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110947818602421951171454223 166421727903632926757181335)
        ·
          refine ⟨249632591855449390135772003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166421727903632926757181335 249632591855449390135772003)
          ·
            refine ⟨374448887783174085203658005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249632591855449390135772003 374448887783174085203658005)
            ·
              refine ⟨17552291614836285243921469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 374448887783174085203658005 17552291614836285243921469)
              ·
                refine ⟨6582109355563606966470551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17552291614836285243921469 6582109355563606966470551)
                ·
                  refine ⟨9873164033345410449705827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6582109355563606966470551 9873164033345410449705827)
                  ·
                    refine ⟨14809746050018115674558741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9873164033345410449705827 14809746050018115674558741)
                    ·
                      refine ⟨694206846094599172244941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14809746050018115674558741 694206846094599172244941)
                      ·
                        rfl

theorem cell23_1351963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 6].length) (baseStart_1351963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351963 prefixEnd_1351963 := by exact prefixLift 1351963
  have htrace : WordTrace (prefixWord ++ tailWord_1351963) baseStart_1351963 baseEnd_1351963 := by
    simpa [prefixWord, tailWord_1351963, baseEnd_1351963] using wordTrace_append hprefix tailTrace_1351963
  have hstable : (prefixWord ++ tailWord_1351963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351963).length < 2 ^ (prefixWord ++ tailWord_1351963).sum := by decide
  have hdescent : baseEnd_1351963 < baseStart_1351963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351978 : List Nat := [3, 1, 4, 2, 2, 1, 2, 3, 1, 1, 3]
def baseStart_1351978 : Nat := 118140960795 + 1351978 * 2 ^ 59
def prefixEnd_1351978 : Nat := 4983230072969 + 3 ^ 40 * 1351978 * 2
def baseEnd_1351978 : Nat := 694214548304416613557373

theorem tailTrace_1351978 : CollatzResearch.WordTrace tailWord_1351978 prefixEnd_1351978 694214548304416613557373 := by
  unfold tailWord_1351978
  simp only [CollatzResearch.WordTrace]
  refine ⟨12327672174005520076166147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32873792464014720203109725 12327672174005520076166147)
  ·
    refine ⟨18491508261008280114249221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12327672174005520076166147 18491508261008280114249221)
    ·
      refine ⟨3467157798939052521421729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18491508261008280114249221 3467157798939052521421729)
      ·
        refine ⟨2600368349204289391066297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3467157798939052521421729 2600368349204289391066297)
        ·
          refine ⟨1950276261903217043299723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2600368349204289391066297 1950276261903217043299723)
          ·
            refine ⟨2925414392854825564949585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1950276261903217043299723 2925414392854825564949585)
            ·
              refine ⟨2194060794641119173712189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2925414392854825564949585 2194060794641119173712189)
              ·
                refine ⟨822772797990419690142071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2194060794641119173712189 822772797990419690142071)
                ·
                  refine ⟨1234159196985629535213107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 822772797990419690142071 1234159196985629535213107)
                  ·
                    refine ⟨1851238795478444302819661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1234159196985629535213107 1851238795478444302819661)
                    ·
                      refine ⟨694214548304416613557373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1851238795478444302819661 694214548304416613557373)
                      ·
                        rfl

theorem cell23_1351978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_1351978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351978 prefixEnd_1351978 := by exact prefixLift 1351978
  have htrace : WordTrace (prefixWord ++ tailWord_1351978) baseStart_1351978 baseEnd_1351978 := by
    simpa [prefixWord, tailWord_1351978, baseEnd_1351978] using wordTrace_append hprefix tailTrace_1351978
  have hstable : (prefixWord ++ tailWord_1351978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351978).length < 2 ^ (prefixWord ++ tailWord_1351978).sum := by decide
  have hdescent : baseEnd_1351978 < baseStart_1351978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351980 : List Nat := [2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 4]
def baseStart_1351980 : Nat := 118140960795 + 1351980 * 2 ^ 59
def prefixEnd_1351980 : Nat := 4983230072969 + 3 ^ 40 * 1351980 * 2
def baseEnd_1351980 : Nat := 694215575265725605732363

theorem tailTrace_1351980 : CollatzResearch.WordTrace tailWord_1351980 prefixEnd_1351980 694215575265725605732363 := by
  unfold tailWord_1351980
  simp only [CollatzResearch.WordTrace]
  refine ⟨24655380821007417323118697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32873841094676556430824929 24655380821007417323118697)
  ·
    refine ⟨18491535615755562992339023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24655380821007417323118697 18491535615755562992339023)
    ·
      refine ⟨27737303423633344488508535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18491535615755562992339023 27737303423633344488508535)
      ·
        refine ⟨41605955135450016732762803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27737303423633344488508535 41605955135450016732762803)
        ·
          refine ⟨62408932703175025099144205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41605955135450016732762803 62408932703175025099144205)
          ·
            refine ⟨23403349763690634412179077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62408932703175025099144205 23403349763690634412179077)
            ·
              refine ⟨4388128080691993952283577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23403349763690634412179077 4388128080691993952283577)
              ·
                refine ⟨3291096060518995464212683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4388128080691993952283577 3291096060518995464212683)
                ·
                  refine ⟨4936644090778493196319025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3291096060518995464212683 4936644090778493196319025)
                  ·
                    refine ⟨3702483068083869897239269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4936644090778493196319025 3702483068083869897239269)
                    ·
                      refine ⟨694215575265725605732363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3702483068083869897239269 694215575265725605732363)
                      ·
                        rfl

theorem cell23_1351980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_1351980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351980 prefixEnd_1351980 := by exact prefixLift 1351980
  have htrace : WordTrace (prefixWord ++ tailWord_1351980) baseStart_1351980 baseEnd_1351980 := by
    simpa [prefixWord, tailWord_1351980, baseEnd_1351980] using wordTrace_append hprefix tailTrace_1351980
  have hstable : (prefixWord ++ tailWord_1351980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351980).length < 2 ^ (prefixWord ++ tailWord_1351980).sum := by decide
  have hdescent : baseEnd_1351980 < baseStart_1351980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351987 : List Nat := [1, 1, 1, 2, 5, 1, 3, 3, 1, 2, 3]
def baseStart_1351987 : Nat := 118140960795 + 1351987 * 2 ^ 59
def prefixEnd_1351987 : Nat := 4983230072969 + 3 ^ 40 * 1351987 * 2
def baseEnd_1351987 : Nat := 694219169630307078344831

theorem tailTrace_1351987 : CollatzResearch.WordTrace tailWord_1351987 prefixEnd_1351987 694219169630307078344831 := by
  unfold tailWord_1351987
  simp only [CollatzResearch.WordTrace]
  refine ⟨49311016952989474841742215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32874011301992983227828143 49311016952989474841742215)
  ·
    refine ⟨73966525429484212262613323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49311016952989474841742215 73966525429484212262613323)
    ·
      refine ⟨110949788144226318393919985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73966525429484212262613323 110949788144226318393919985)
      ·
        refine ⟨83212341108169738795439989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 110949788144226318393919985 83212341108169738795439989)
        ·
          refine ⟨7801156978890913012072499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83212341108169738795439989 7801156978890913012072499)
          ·
            refine ⟨11701735468336369518108749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7801156978890913012072499 11701735468336369518108749)
            ·
              refine ⟨4388150800626138569290781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11701735468336369518108749 4388150800626138569290781)
              ·
                refine ⟨1645556550234801963484043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4388150800626138569290781 1645556550234801963484043)
                ·
                  refine ⟨2468334825352202945226065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1645556550234801963484043 2468334825352202945226065)
                  ·
                    refine ⟨1851251119014152208919549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2468334825352202945226065 1851251119014152208919549)
                    ·
                      refine ⟨694219169630307078344831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1851251119014152208919549 694219169630307078344831)
                      ·
                        rfl

theorem cell23_1351987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 2, 3].length) (baseStart_1351987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351987 prefixEnd_1351987 := by exact prefixLift 1351987
  have htrace : WordTrace (prefixWord ++ tailWord_1351987) baseStart_1351987 baseEnd_1351987 := by
    simpa [prefixWord, tailWord_1351987, baseEnd_1351987] using wordTrace_append hprefix tailTrace_1351987
  have hstable : (prefixWord ++ tailWord_1351987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351987).length < 2 ^ (prefixWord ++ tailWord_1351987).sum := by decide
  have hdescent : baseEnd_1351987 < baseStart_1351987 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1351994 : List Nat := [3, 1, 1, 1, 4, 4, 1, 2, 2, 4]
def baseStart_1351994 : Nat := 118140960795 + 1351994 * 2 ^ 59
def prefixEnd_1351994 : Nat := 4983230072969 + 3 ^ 40 * 1351994 * 2
def baseEnd_1351994 : Nat := 231407587998296183652433

theorem tailTrace_1351994 : CollatzResearch.WordTrace tailWord_1351994 prefixEnd_1351994 231407587998296183652433 := by
  unfold tailWord_1351994
  simp only [CollatzResearch.WordTrace]
  refine ⟨12327818065991028759311759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32874181509309410024831357 12327818065991028759311759)
  ·
    refine ⟨18491727098986543138967639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12327818065991028759311759 18491727098986543138967639)
    ·
      refine ⟨27737590648479814708451459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18491727098986543138967639 27737590648479814708451459)
      ·
        refine ⟨41606385972719722062677189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27737590648479814708451459 41606385972719722062677189)
        ·
          refine ⟨7801197369884947886751973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41606385972719722062677189 7801197369884947886751973)
          ·
            refine ⟨1462724506853427728765995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7801197369884947886751973 1462724506853427728765995)
            ·
              refine ⟨2194086760280141593148993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462724506853427728765995 2194086760280141593148993)
              ·
                refine ⟨1645565070210106194861745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2194086760280141593148993 1645565070210106194861745)
                ·
                  refine ⟨1234173802657579646146309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1645565070210106194861745 1234173802657579646146309)
                  ·
                    refine ⟨231407587998296183652433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1234173802657579646146309 231407587998296183652433)
                    ·
                      rfl

theorem cell23_1351994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 1, 2, 2, 4].length) (baseStart_1351994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1351994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1351994 prefixEnd_1351994 := by exact prefixLift 1351994
  have htrace : WordTrace (prefixWord ++ tailWord_1351994) baseStart_1351994 baseEnd_1351994 := by
    simpa [prefixWord, tailWord_1351994, baseEnd_1351994] using wordTrace_append hprefix tailTrace_1351994
  have hstable : (prefixWord ++ tailWord_1351994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1351994).length < 2 ^ (prefixWord ++ tailWord_1351994).sum := by decide
  have hdescent : baseEnd_1351994 < baseStart_1351994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1351994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352003 : List Nat := [1, 1, 1, 3, 1, 3, 2, 1, 1, 9]
def baseStart_1352003 : Nat := 118140960795 + 1352003 * 2 ^ 59
def prefixEnd_1352003 : Nat := 4983230072969 + 3 ^ 40 * 1352003 * 2
def baseEnd_1352003 : Nat := 231409128440259671914919

theorem tailTrace_1352003 : CollatzResearch.WordTrace tailWord_1352003 prefixEnd_1352003 231409128440259671914919 := by
  unfold tailWord_1352003
  simp only [CollatzResearch.WordTrace]
  refine ⟨49311600520931509574324663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32874400347287673049549775 49311600520931509574324663)
  ·
    refine ⟨73967400781397264361486995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49311600520931509574324663 73967400781397264361486995)
    ·
      refine ⟨110951101172095896542230493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73967400781397264361486995 110951101172095896542230493)
      ·
        refine ⟨41606662939535961203336435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110951101172095896542230493 41606662939535961203336435)
        ·
          refine ⟨62409994409303941805004653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41606662939535961203336435 62409994409303941805004653)
          ·
            refine ⟨23403747903488978176876745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62409994409303941805004653 23403747903488978176876745)
            ·
              refine ⟨17552810927616733632657559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23403747903488978176876745 17552810927616733632657559)
              ·
                refine ⟨26329216391425100448986339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17552810927616733632657559 26329216391425100448986339)
                ·
                  refine ⟨39493824587137650673479509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26329216391425100448986339 39493824587137650673479509)
                  ·
                    refine ⟨231409128440259671914919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 39493824587137650673479509 231409128440259671914919)
                    ·
                      rfl

theorem cell23_1352003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 9].length) (baseStart_1352003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352003 prefixEnd_1352003 := by exact prefixLift 1352003
  have htrace : WordTrace (prefixWord ++ tailWord_1352003) baseStart_1352003 baseEnd_1352003 := by
    simpa [prefixWord, tailWord_1352003, baseEnd_1352003] using wordTrace_append hprefix tailTrace_1352003
  have hstable : (prefixWord ++ tailWord_1352003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352003).length < 2 ^ (prefixWord ++ tailWord_1352003).sum := by decide
  have hdescent : baseEnd_1352003 < baseStart_1352003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352004 : List Nat := [2, 3, 4, 1, 2, 1, 1, 2, 1, 1, 5]
def baseStart_1352004 : Nat := 118140960795 + 1352004 * 2 ^ 59
def prefixEnd_1352004 : Nat := 4983230072969 + 3 ^ 40 * 1352004 * 2
def baseEnd_1352004 : Nat := 694227898801433511832253

theorem tailTrace_1352004 : CollatzResearch.WordTrace tailWord_1352004 prefixEnd_1352004 694227898801433511832253 := by
  unfold tailWord_1352004
  simp only [CollatzResearch.WordTrace]
  refine ⟨24655818496963943372555533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32874424662618591163407377 24655818496963943372555533)
  ·
    refine ⟨9245931936361478764708325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24655818496963943372555533 9245931936361478764708325)
    ·
      refine ⟨1733612238067777268382811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9245931936361478764708325 1733612238067777268382811)
      ·
        refine ⟨2600418357101665902574217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1733612238067777268382811 2600418357101665902574217)
        ·
          refine ⟨1950313767826249426930663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2600418357101665902574217 1950313767826249426930663)
          ·
            refine ⟨2925470651739374140395995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1950313767826249426930663 2925470651739374140395995)
            ·
              refine ⟨4388205977609061210593993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2925470651739374140395995 4388205977609061210593993)
              ·
                refine ⟨3291154483206795907945495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4388205977609061210593993 3291154483206795907945495)
                ·
                  refine ⟨4936731724810193861918243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3291154483206795907945495 4936731724810193861918243)
                  ·
                    refine ⟨7405097587215290792877365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4936731724810193861918243 7405097587215290792877365)
                    ·
                      refine ⟨694227898801433511832253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7405097587215290792877365 694227898801433511832253)
                      ·
                        rfl

theorem cell23_1352004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_1352004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352004 prefixEnd_1352004 := by exact prefixLift 1352004
  have htrace : WordTrace (prefixWord ++ tailWord_1352004) baseStart_1352004 baseEnd_1352004 := by
    simpa [prefixWord, tailWord_1352004, baseEnd_1352004] using wordTrace_append hprefix tailTrace_1352004
  have hstable : (prefixWord ++ tailWord_1352004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352004).length < 2 ^ (prefixWord ++ tailWord_1352004).sum := by decide
  have hdescent : baseEnd_1352004 < baseStart_1352004 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352017 : List Nat := [1, 2, 2, 1, 4, 2, 3, 1, 1, 3, 3]
def baseStart_1352017 : Nat := 118140960795 + 1352017 * 2 ^ 59
def prefixEnd_1352017 : Nat := 4983230072969 + 3 ^ 40 * 1352017 * 2
def baseEnd_1352017 : Nat := 694234574049941960969693

theorem tailTrace_1352017 : CollatzResearch.WordTrace tailWord_1352017 prefixEnd_1352017 694234574049941960969693 := by
  unfold tailWord_1352017
  simp only [CollatzResearch.WordTrace]
  refine ⟨49312111142880789965334305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32874740761920526643556203 49312111142880789965334305)
  ·
    refine ⟨36984083357160592474000729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49312111142880789965334305 36984083357160592474000729)
    ·
      refine ⟨27738062517870444355500547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36984083357160592474000729 27738062517870444355500547)
      ·
        refine ⟨41607093776805666533250821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27738062517870444355500547 41607093776805666533250821)
        ·
          refine ⟨7801330083151062474984529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41607093776805666533250821 7801330083151062474984529)
          ·
            refine ⟨5850997562363296856238397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7801330083151062474984529 5850997562363296856238397)
            ·
              refine ⟨2194124085886236321089399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5850997562363296856238397 2194124085886236321089399)
              ·
                refine ⟨3291186128829354481634099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2194124085886236321089399 3291186128829354481634099)
                ·
                  refine ⟨4936779193244031722451149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3291186128829354481634099 4936779193244031722451149)
                  ·
                    refine ⟨1851292197466511895919181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4936779193244031722451149 1851292197466511895919181)
                    ·
                      refine ⟨694234574049941960969693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1851292197466511895919181 694234574049941960969693)
                      ·
                        rfl

theorem cell23_1352017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 3, 3].length) (baseStart_1352017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352017 prefixEnd_1352017 := by exact prefixLift 1352017
  have htrace : WordTrace (prefixWord ++ tailWord_1352017) baseStart_1352017 baseEnd_1352017 := by
    simpa [prefixWord, tailWord_1352017, baseEnd_1352017] using wordTrace_append hprefix tailTrace_1352017
  have hstable : (prefixWord ++ tailWord_1352017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352017).length < 2 ^ (prefixWord ++ tailWord_1352017).sum := by decide
  have hdescent : baseEnd_1352017 < baseStart_1352017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352034 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 4, 1, 3]
def baseStart_1352034 : Nat := 118140960795 + 1352034 * 2 ^ 59
def prefixEnd_1352034 : Nat := 4983230072969 + 3 ^ 40 * 1352034 * 2
def baseEnd_1352034 : Nat := 694243303221068394457115

theorem tailTrace_1352034 : CollatzResearch.WordTrace tailWord_1352034 prefixEnd_1352034 694243303221068394457115 := by
  unfold tailWord_1352034
  simp only [CollatzResearch.WordTrace]
  refine ⟨12328182795954800467175789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32875154122546134579135437 12328182795954800467175789)
  ·
    refine ⟨4623068548483050175190921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12328182795954800467175789 4623068548483050175190921)
    ·
      refine ⟨3467301411362287631393191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4623068548483050175190921 3467301411362287631393191)
      ·
        refine ⟨5200952117043431447089787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3467301411362287631393191 5200952117043431447089787)
        ·
          refine ⟨7801428175565147170634681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5200952117043431447089787 7801428175565147170634681)
          ·
            refine ⟨5851071131673860377976011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7801428175565147170634681 5851071131673860377976011)
            ·
              refine ⟨8776606697510790566964017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5851071131673860377976011 8776606697510790566964017)
              ·
                refine ⟨6582455023133092925223013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8776606697510790566964017 6582455023133092925223013)
                ·
                  refine ⟨1234210316837454923479315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6582455023133092925223013 1234210316837454923479315)
                  ·
                    refine ⟨1851315475256182385218973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1234210316837454923479315 1851315475256182385218973)
                    ·
                      refine ⟨694243303221068394457115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1851315475256182385218973 694243303221068394457115)
                      ·
                        rfl

theorem cell23_1352034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_1352034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352034 prefixEnd_1352034 := by exact prefixLift 1352034
  have htrace : WordTrace (prefixWord ++ tailWord_1352034) baseStart_1352034 baseEnd_1352034 := by
    simpa [prefixWord, tailWord_1352034, baseEnd_1352034] using wordTrace_append hprefix tailTrace_1352034
  have hstable : (prefixWord ++ tailWord_1352034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352034).length < 2 ^ (prefixWord ++ tailWord_1352034).sum := by decide
  have hdescent : baseEnd_1352034 < baseStart_1352034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352078 : List Nat := [4, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2]
def baseStart_1352078 : Nat := 118140960795 + 1352078 * 2 ^ 59
def prefixEnd_1352078 : Nat := 4983230072969 + 3 ^ 40 * 1352078 * 2
def baseEnd_1352078 : Nat := 694265896369866222306913

theorem tailTrace_1352078 : CollatzResearch.WordTrace tailWord_1352078 prefixEnd_1352078 694265896369866222306913 := by
  unfold tailWord_1352078
  simp only [CollatzResearch.WordTrace]
  refine ⟨6164291999457474672913111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32876223997106531588869925 6164291999457474672913111)
  ·
    refine ⟨9246437999186212009369667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6164291999457474672913111 9246437999186212009369667)
    ·
      refine ⟨13869656998779318014054501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9246437999186212009369667 13869656998779318014054501)
      ·
        refine ⟨2600560687271122127635219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13869656998779318014054501 2600560687271122127635219)
        ·
          refine ⟨3900841030906683191452829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2600560687271122127635219 3900841030906683191452829)
          ·
            refine ⟨1462815386590006196794811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3900841030906683191452829 1462815386590006196794811)
            ·
              refine ⟨2194223079885009295192217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1462815386590006196794811 2194223079885009295192217)
              ·
                refine ⟨1645667309913756971394163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2194223079885009295192217 1645667309913756971394163)
                ·
                  refine ⟨2468500964870635457091245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1645667309913756971394163 2468500964870635457091245)
                  ·
                    refine ⟨925687861826488296409217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2468500964870635457091245 925687861826488296409217)
                    ·
                      refine ⟨694265896369866222306913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 925687861826488296409217 694265896369866222306913)
                      ·
                        rfl

theorem cell23_1352078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 1, 3, 2].length) (baseStart_1352078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352078 prefixEnd_1352078 := by exact prefixLift 1352078
  have htrace : WordTrace (prefixWord ++ tailWord_1352078) baseStart_1352078 baseEnd_1352078 := by
    simpa [prefixWord, tailWord_1352078, baseEnd_1352078] using wordTrace_append hprefix tailTrace_1352078
  have hstable : (prefixWord ++ tailWord_1352078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352078).length < 2 ^ (prefixWord ++ tailWord_1352078).sum := by decide
  have hdescent : baseEnd_1352078 < baseStart_1352078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352094 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1352094 : Nat := 118140960795 + 1352094 * 2 ^ 59
def prefixEnd_1352094 : Nat := 4983230072969 + 3 ^ 40 * 1352094 * 2
def baseEnd_1352094 : Nat := 694274112060338159706839

theorem tailTrace_1352094 : CollatzResearch.WordTrace tailWord_1352094 prefixEnd_1352094 694274112060338159706839 := by
  unfold tailWord_1352094
  simp only [CollatzResearch.WordTrace]
  refine ⟨6164364945450229014485917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32876613042401221410591557 6164364945450229014485917)
  ·
    refine ⟨2311636854543835880432219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6164364945450229014485917 2311636854543835880432219)
    ·
      refine ⟨3467455281815753820648329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2311636854543835880432219 3467455281815753820648329)
      ·
        refine ⟨2600591461361815365486247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3467455281815753820648329 2600591461361815365486247)
        ·
          refine ⟨3900887192042723048229371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2600591461361815365486247 3900887192042723048229371)
          ·
            refine ⟨5851330788064084572344057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3900887192042723048229371 5851330788064084572344057)
            ·
              refine ⟨4388498091048063429258043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5851330788064084572344057 4388498091048063429258043)
              ·
                refine ⟨6582747136572095143887065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4388498091048063429258043 6582747136572095143887065)
                ·
                  refine ⟨4937060352429071357915299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6582747136572095143887065 4937060352429071357915299)
                  ·
                    refine ⟨7405590528643607036872949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4937060352429071357915299 7405590528643607036872949)
                    ·
                      refine ⟨694274112060338159706839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7405590528643607036872949 694274112060338159706839)
                      ·
                        rfl

theorem cell23_1352094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1352094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352094 prefixEnd_1352094 := by exact prefixLift 1352094
  have htrace : WordTrace (prefixWord ++ tailWord_1352094) baseStart_1352094 baseEnd_1352094 := by
    simpa [prefixWord, tailWord_1352094, baseEnd_1352094] using wordTrace_append hprefix tailTrace_1352094
  have hstable : (prefixWord ++ tailWord_1352094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352094).length < 2 ^ (prefixWord ++ tailWord_1352094).sum := by decide
  have hdescent : baseEnd_1352094 < baseStart_1352094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352124 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 2, 3, 3]
def baseStart_1352124 : Nat := 118140960795 + 1352124 * 2 ^ 59
def prefixEnd_1352124 : Nat := 4983230072969 + 3 ^ 40 * 1352124 * 2
def baseEnd_1352124 : Nat := 694289516479973042331701

theorem tailTrace_1352124 : CollatzResearch.WordTrace tailWord_1352124 prefixEnd_1352124 694289516479973042331701 := by
  unfold tailWord_1352124
  simp only [CollatzResearch.WordTrace]
  refine ⟨24658006876746573619739713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32877342502328764826319617 24658006876746573619739713)
  ·
    refine ⟨18493505157559930214804785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24658006876746573619739713 18493505157559930214804785)
    ·
      refine ⟨13870128868169947661103589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18493505157559930214804785 13870128868169947661103589)
      ·
        refine ⟨2600649162781865186456923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13870128868169947661103589 2600649162781865186456923)
        ·
          refine ⟨3900973744172797779685385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2600649162781865186456923 3900973744172797779685385)
          ·
            refine ⟨2925730308129598334764039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3900973744172797779685385 2925730308129598334764039)
            ·
              refine ⟨4388595462194397502146059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2925730308129598334764039 4388595462194397502146059)
              ·
                refine ⟨6582893193291596253219089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4388595462194397502146059 6582893193291596253219089)
                ·
                  refine ⟨4937169894968697189914317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6582893193291596253219089 4937169894968697189914317)
                  ·
                    refine ⟨1851438710613261446217869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4937169894968697189914317 1851438710613261446217869)
                    ·
                      refine ⟨694289516479973042331701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1851438710613261446217869 694289516479973042331701)
                      ·
                        rfl

theorem cell23_1352124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_1352124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352124 prefixEnd_1352124 := by exact prefixLift 1352124
  have htrace : WordTrace (prefixWord ++ tailWord_1352124) baseStart_1352124 baseEnd_1352124 := by
    simpa [prefixWord, tailWord_1352124, baseEnd_1352124] using wordTrace_append hprefix tailTrace_1352124
  have hstable : (prefixWord ++ tailWord_1352124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352124).length < 2 ^ (prefixWord ++ tailWord_1352124).sum := by decide
  have hdescent : baseEnd_1352124 < baseStart_1352124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352160 : List Nat := [2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 6]
def baseStart_1352160 : Nat := 118140960795 + 1352160 * 2 ^ 59
def prefixEnd_1352160 : Nat := 4983230072969 + 3 ^ 40 * 1352160 * 2
def baseEnd_1352160 : Nat := 694308001783534901481535

theorem tailTrace_1352160 : CollatzResearch.WordTrace tailWord_1352160 prefixEnd_1352160 694308001783534901481535 := by
  unfold tailWord_1352160
  simp only [CollatzResearch.WordTrace]
  refine ⟨24658663390681362693894967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32878217854241816925193289 24658663390681362693894967)
  ·
    refine ⟨36987995086022044040842451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24658663390681362693894967 36987995086022044040842451)
    ·
      refine ⟨55481992629033066061263677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36987995086022044040842451 55481992629033066061263677)
      ·
        refine ⟨20805747235887399772973879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55481992629033066061263677 20805747235887399772973879)
        ·
          refine ⟨31208620853831099659460819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20805747235887399772973879 31208620853831099659460819)
          ·
            refine ⟨46812931280746649489191229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31208620853831099659460819 46812931280746649489191229)
            ·
              refine ⟨17554849230279993558446711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46812931280746649489191229 17554849230279993558446711)
              ·
                refine ⟨26332273845419990337670067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17554849230279993558446711 26332273845419990337670067)
                ·
                  refine ⟨39498410768129985506505101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26332273845419990337670067 39498410768129985506505101)
                  ·
                    refine ⟨14811904038048744564939413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39498410768129985506505101 14811904038048744564939413)
                    ·
                      refine ⟨694308001783534901481535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14811904038048744564939413 694308001783534901481535)
                      ·
                        rfl

theorem cell23_1352160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_1352160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352160 prefixEnd_1352160 := by exact prefixLift 1352160
  have htrace : WordTrace (prefixWord ++ tailWord_1352160) baseStart_1352160 baseEnd_1352160 := by
    simpa [prefixWord, tailWord_1352160, baseEnd_1352160] using wordTrace_append hprefix tailTrace_1352160
  have hstable : (prefixWord ++ tailWord_1352160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352160).length < 2 ^ (prefixWord ++ tailWord_1352160).sum := by decide
  have hdescent : baseEnd_1352160 < baseStart_1352160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352174 : List Nat := [4, 1, 2, 1, 2, 2, 1, 3, 3, 4]
def baseStart_1352174 : Nat := 118140960795 + 1352174 * 2 ^ 59
def prefixEnd_1352174 : Nat := 4983230072969 + 3 ^ 40 * 1352174 * 2
def baseEnd_1352174 : Nat := 231438396837565948902157

theorem tailTrace_1352174 : CollatzResearch.WordTrace tailWord_1352174 prefixEnd_1352174 231438396837565948902157 := by
  unfold tailWord_1352174
  simp only [CollatzResearch.WordTrace]
  refine ⟨6164729675414000722349947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32878558268874670519199717 6164729675414000722349947)
  ·
    refine ⟨9247094513121001083524921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6164729675414000722349947 9247094513121001083524921)
    ·
      refine ⟨6935320884840750812643691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9247094513121001083524921 6935320884840750812643691)
      ·
        refine ⟨10402981327261126218965537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6935320884840750812643691 10402981327261126218965537)
        ·
          refine ⟨7802235995445844664224153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10402981327261126218965537 7802235995445844664224153)
          ·
            refine ⟨5851676996584383498168115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7802235995445844664224153 5851676996584383498168115)
            ·
              refine ⟨8777515494876575247252173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5851676996584383498168115 8777515494876575247252173)
              ·
                refine ⟨3291568310578715717719565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8777515494876575247252173 3291568310578715717719565)
                ·
                  refine ⟨1234338116467018394144837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3291568310578715717719565 1234338116467018394144837)
                  ·
                    refine ⟨231438396837565948902157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1234338116467018394144837 231438396837565948902157)
                    ·
                      rfl

theorem cell23_1352174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 3, 3, 4].length) (baseStart_1352174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352174 prefixEnd_1352174 := by exact prefixLift 1352174
  have htrace : WordTrace (prefixWord ++ tailWord_1352174) baseStart_1352174 baseEnd_1352174 := by
    simpa [prefixWord, tailWord_1352174, baseEnd_1352174] using wordTrace_append hprefix tailTrace_1352174
  have hstable : (prefixWord ++ tailWord_1352174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352174).length < 2 ^ (prefixWord ++ tailWord_1352174).sum := by decide
  have hdescent : baseEnd_1352174 < baseStart_1352174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352198 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4]
def baseStart_1352198 : Nat := 118140960795 + 1352198 * 2 ^ 59
def prefixEnd_1352198 : Nat := 4983230072969 + 3 ^ 40 * 1352198 * 2
def baseEnd_1352198 : Nat := 694327514048405752806361

theorem tailTrace_1352198 : CollatzResearch.WordTrace tailWord_1352198 prefixEnd_1352198 694327514048405752806361 := by
  unfold tailWord_1352198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1541209773600783058677289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 32879141836816705251782165 1541209773600783058677289)
  ·
    refine ⟨1155907330200587294007967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1541209773600783058677289 1155907330200587294007967)
    ·
      refine ⟨1733860995300880941011951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1155907330200587294007967 1733860995300880941011951)
      ·
        refine ⟨2600791492951321411517927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1733860995300880941011951 2600791492951321411517927)
        ·
          refine ⟨3901187239426982117276891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2600791492951321411517927 3901187239426982117276891)
          ·
            refine ⟨5851780859140473175915337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3901187239426982117276891 5851780859140473175915337)
            ·
              refine ⟨4388835644355354881936503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5851780859140473175915337 4388835644355354881936503)
              ·
                refine ⟨6583253466533032322904755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4388835644355354881936503 6583253466533032322904755)
                ·
                  refine ⟨9874880199799548484357133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6583253466533032322904755 9874880199799548484357133)
                  ·
                    refine ⟨3703080074924830681633925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9874880199799548484357133 3703080074924830681633925)
                    ·
                      refine ⟨694327514048405752806361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3703080074924830681633925 694327514048405752806361)
                      ·
                        rfl

theorem cell23_1352198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_1352198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352198 prefixEnd_1352198 := by exact prefixLift 1352198
  have htrace : WordTrace (prefixWord ++ tailWord_1352198) baseStart_1352198 baseEnd_1352198 := by
    simpa [prefixWord, tailWord_1352198, baseEnd_1352198] using wordTrace_append hprefix tailTrace_1352198
  have hstable : (prefixWord ++ tailWord_1352198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352198).length < 2 ^ (prefixWord ++ tailWord_1352198).sum := by decide
  have hdescent : baseEnd_1352198 < baseStart_1352198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352238 : List Nat := [4, 1, 3, 1, 3, 2, 2, 1, 6]
def baseStart_1352238 : Nat := 118140960795 + 1352238 * 2 ^ 59
def prefixEnd_1352238 : Nat := 4983230072969 + 3 ^ 40 * 1352238 * 2
def baseEnd_1352238 : Nat := 77149783697176177367353

theorem tailTrace_1352238 : CollatzResearch.WordTrace tailWord_1352238 prefixEnd_1352238 77149783697176177367353 := by
  unfold tailWord_1352238
  simp only [CollatzResearch.WordTrace]
  refine ⟨6165021459385018088641171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32880114450053429806086245 6165021459385018088641171)
  ·
    refine ⟨9247532189077527132961757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6165021459385018088641171 9247532189077527132961757)
    ·
      refine ⟨3467824570904072674860659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9247532189077527132961757 3467824570904072674860659)
      ·
        refine ⟨5201736856356109012290989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3467824570904072674860659 5201736856356109012290989)
        ·
          refine ⟨1950651321133540879609121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5201736856356109012290989 1950651321133540879609121)
          ·
            refine ⟨1462988490850155659706841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1950651321133540879609121 1462988490850155659706841)
            ·
              refine ⟨1097241368137616744780131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1462988490850155659706841 1097241368137616744780131)
              ·
                refine ⟨1645862052206425117170197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1097241368137616744780131 1645862052206425117170197)
                ·
                  refine ⟨77149783697176177367353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1645862052206425117170197 77149783697176177367353)
                  ·
                    rfl

theorem cell23_1352238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 6].length) (baseStart_1352238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352238 prefixEnd_1352238 := by exact prefixLift 1352238
  have htrace : WordTrace (prefixWord ++ tailWord_1352238) baseStart_1352238 baseEnd_1352238 := by
    simpa [prefixWord, tailWord_1352238, baseEnd_1352238] using wordTrace_append hprefix tailTrace_1352238
  have hstable : (prefixWord ++ tailWord_1352238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352238).length < 2 ^ (prefixWord ++ tailWord_1352238).sum := by decide
  have hdescent : baseEnd_1352238 < baseStart_1352238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352247 : List Nat := [1, 1, 3, 1, 2, 3, 2, 3, 1, 6]
def baseStart_1352247 : Nat := 118140960795 + 1352247 * 2 ^ 59
def prefixEnd_1352247 : Nat := 4983230072969 + 3 ^ 40 * 1352247 * 2
def baseEnd_1352247 : Nat := 231450891533492020364545

theorem tailTrace_1352247 : CollatzResearch.WordTrace tailWord_1352247 prefixEnd_1352247 231450891533492020364545 := by
  unfold tailWord_1352247
  simp only [CollatzResearch.WordTrace]
  refine ⟨49320499932047539246206995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32880333288031692830804663 49320499932047539246206995)
  ·
    refine ⟨73980749898071308869310493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49320499932047539246206995 73980749898071308869310493)
    ·
      refine ⟨27742781211776740825991435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 73980749898071308869310493 27742781211776740825991435)
      ·
        refine ⟨41614171817665111238987153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27742781211776740825991435 41614171817665111238987153)
        ·
          refine ⟨31210628863248833429240365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41614171817665111238987153 31210628863248833429240365)
          ·
            refine ⟨11703985823718312535965137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31210628863248833429240365 11703985823718312535965137)
            ·
              refine ⟨8777989367788734401973853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11703985823718312535965137 8777989367788734401973853)
              ·
                refine ⟨3291746012920775400740195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8777989367788734401973853 3291746012920775400740195)
                ·
                  refine ⟨4937619019381163101110293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3291746012920775400740195 4937619019381163101110293)
                  ·
                    refine ⟨231450891533492020364545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4937619019381163101110293 231450891533492020364545)
                    ·
                      rfl

theorem cell23_1352247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_1352247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352247 prefixEnd_1352247 := by exact prefixLift 1352247
  have htrace : WordTrace (prefixWord ++ tailWord_1352247) baseStart_1352247 baseEnd_1352247 := by
    simpa [prefixWord, tailWord_1352247, baseEnd_1352247] using wordTrace_append hprefix tailTrace_1352247
  have hstable : (prefixWord ++ tailWord_1352247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352247).length < 2 ^ (prefixWord ++ tailWord_1352247).sum := by decide
  have hdescent : baseEnd_1352247 < baseStart_1352247 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352267 : List Nat := [1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 4]
def baseStart_1352267 : Nat := 118140960795 + 1352267 * 2 ^ 59
def prefixEnd_1352267 : Nat := 4983230072969 + 3 ^ 40 * 1352267 * 2
def baseEnd_1352267 : Nat := 694362944213565982843543

theorem tailTrace_1352267 : CollatzResearch.WordTrace tailWord_1352267 prefixEnd_1352267 694362944213565982843543 := by
  unfold tailWord_1352267
  simp only [CollatzResearch.WordTrace]
  refine ⟨49321229391975082661935055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32880819594650055107956703 49321229391975082661935055)
  ·
    refine ⟨73981844087962623992902583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49321229391975082661935055 73981844087962623992902583)
    ·
      refine ⟨110972766131943935989353875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73981844087962623992902583 110972766131943935989353875)
      ·
        refine ⟨166459149197915903984030813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 110972766131943935989353875 166459149197915903984030813)
        ·
          refine ⟨62422180949218463994011555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166459149197915903984030813 62422180949218463994011555)
          ·
            refine ⟨93633271423827695991017333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62422180949218463994011555 93633271423827695991017333)
            ·
              refine ⟨8778119195983846499157875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93633271423827695991017333 8778119195983846499157875)
              ·
                refine ⟨13167178793975769748736813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8778119195983846499157875 13167178793975769748736813)
                ·
                  refine ⟨4937692047740913655776305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13167178793975769748736813 4937692047740913655776305)
                  ·
                    refine ⟨3703269035805685241832229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4937692047740913655776305 3703269035805685241832229)
                    ·
                      refine ⟨694362944213565982843543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3703269035805685241832229 694362944213565982843543)
                      ·
                        rfl

theorem cell23_1352267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 4].length) (baseStart_1352267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352267 prefixEnd_1352267 := by exact prefixLift 1352267
  have htrace : WordTrace (prefixWord ++ tailWord_1352267) baseStart_1352267 baseEnd_1352267 := by
    simpa [prefixWord, tailWord_1352267, baseEnd_1352267] using wordTrace_append hprefix tailTrace_1352267
  have hstable : (prefixWord ++ tailWord_1352267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352267).length < 2 ^ (prefixWord ++ tailWord_1352267).sum := by decide
  have hdescent : baseEnd_1352267 < baseStart_1352267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352301 : List Nat := [1, 5, 1, 1, 3, 2, 2, 1, 1, 2, 4]
def baseStart_1352301 : Nat := 118140960795 + 1352301 * 2 ^ 59
def prefixEnd_1352301 : Nat := 4983230072969 + 3 ^ 40 * 1352301 * 2
def baseEnd_1352301 : Nat := 694380402555818849818387

theorem tailTrace_1352301 : CollatzResearch.WordTrace tailWord_1352301 prefixEnd_1352301 694380402555818849818387 := by
  unfold tailWord_1352301
  simp only [CollatzResearch.WordTrace]
  refine ⟨49322469473851906468672757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32881646315901270979115171 49322469473851906468672757)
  ·
    refine ⟨4623981513173616231438071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49322469473851906468672757 4623981513173616231438071)
    ·
      refine ⟨6935972269760424347157107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4623981513173616231438071 6935972269760424347157107)
      ·
        refine ⟨10403958404640636520735661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6935972269760424347157107 10403958404640636520735661)
        ·
          refine ⟨3901484401740238695275873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10403958404640636520735661 3901484401740238695275873)
          ·
            refine ⟨2926113301305179021456905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3901484401740238695275873 2926113301305179021456905)
            ·
              refine ⟨2194584975978884266092679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2926113301305179021456905 2194584975978884266092679)
              ·
                refine ⟨3291877463968326399139019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2194584975978884266092679 3291877463968326399139019)
                ·
                  refine ⟨4937816195952489598708529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3291877463968326399139019 4937816195952489598708529)
                  ·
                    refine ⟨3703362146964367199031397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4937816195952489598708529 3703362146964367199031397)
                    ·
                      refine ⟨694380402555818849818387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3703362146964367199031397 694380402555818849818387)
                      ·
                        rfl

theorem cell23_1352301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_1352301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352301 prefixEnd_1352301 := by exact prefixLift 1352301
  have htrace : WordTrace (prefixWord ++ tailWord_1352301) baseStart_1352301 baseEnd_1352301 := by
    simpa [prefixWord, tailWord_1352301, baseEnd_1352301] using wordTrace_append hprefix tailTrace_1352301
  have hstable : (prefixWord ++ tailWord_1352301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352301).length < 2 ^ (prefixWord ++ tailWord_1352301).sum := by decide
  have hdescent : baseEnd_1352301 < baseStart_1352301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352321 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 4, 1, 3]
def baseStart_1352321 : Nat := 118140960795 + 1352321 * 2 ^ 59
def prefixEnd_1352321 : Nat := 4983230072969 + 3 ^ 40 * 1352321 * 2
def baseEnd_1352321 : Nat := 694390672168908771568295

theorem tailTrace_1352321 : CollatzResearch.WordTrace tailWord_1352321 prefixEnd_1352321 694390672168908771568295 := by
  unfold tailWord_1352321
  simp only [CollatzResearch.WordTrace]
  refine ⟨49323198933779449884400817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32882132622519633256267211 49323198933779449884400817)
  ·
    refine ⟨36992399200334587413300613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49323198933779449884400817 36992399200334587413300613)
    ·
      refine ⟨6936074850062735139993865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36992399200334587413300613 6936074850062735139993865)
      ·
        refine ⟨5202056137547051354995399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6936074850062735139993865 5202056137547051354995399)
        ·
          refine ⟨7803084206320577032493099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5202056137547051354995399 7803084206320577032493099)
          ·
            refine ⟨11704626309480865548739649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7803084206320577032493099 11704626309480865548739649)
            ·
              refine ⟨8778469732110649161554737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11704626309480865548739649 8778469732110649161554737)
              ·
                refine ⟨6583852299082986871166053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8778469732110649161554737 6583852299082986871166053)
                ·
                  refine ⟨1234472306078060038343635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6583852299082986871166053 1234472306078060038343635)
                  ·
                    refine ⟨1851708459117090057515453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1234472306078060038343635 1851708459117090057515453)
                    ·
                      refine ⟨694390672168908771568295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1851708459117090057515453 694390672168908771568295)
                      ·
                        rfl

theorem cell23_1352321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_1352321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352321 prefixEnd_1352321 := by exact prefixLift 1352321
  have htrace : WordTrace (prefixWord ++ tailWord_1352321) baseStart_1352321 baseEnd_1352321 := by
    simpa [prefixWord, tailWord_1352321, baseEnd_1352321] using wordTrace_append hprefix tailTrace_1352321
  have hstable : (prefixWord ++ tailWord_1352321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352321).length < 2 ^ (prefixWord ++ tailWord_1352321).sum := by decide
  have hdescent : baseEnd_1352321 < baseStart_1352321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352322 : List Nat := [3, 4, 3, 1, 1, 1, 1, 3, 1, 1, 4]
def baseStart_1352322 : Nat := 118140960795 + 1352322 * 2 ^ 59
def prefixEnd_1352322 : Nat := 4983230072969 + 3 ^ 40 * 1352322 * 2
def baseEnd_1352322 : Nat := 694391185649563267655791

theorem tailTrace_1352322 : CollatzResearch.WordTrace tailWord_1352322 prefixEnd_1352322 694391185649563267655791 := by
  unfold tailWord_1352322
  simp only [CollatzResearch.WordTrace]
  refine ⟨12330808851693956763796805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32882156937850551370124813 12330808851693956763796805)
  ·
    refine ⟨2312026659692616893211901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12330808851693956763796805 2312026659692616893211901)
    ·
      refine ⟨867009997384731334954463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2312026659692616893211901 867009997384731334954463)
      ·
        refine ⟨1300514996077097002431695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 867009997384731334954463 1300514996077097002431695)
        ·
          refine ⟨1950772494115645503647543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1300514996077097002431695 1950772494115645503647543)
          ·
            refine ⟨2926158741173468255471315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1950772494115645503647543 2926158741173468255471315)
            ·
              refine ⟨4389238111760202383206973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2926158741173468255471315 4389238111760202383206973)
              ·
                refine ⟨1645964291910075893702615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4389238111760202383206973 1645964291910075893702615)
                ·
                  refine ⟨2468946437865113840553923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1645964291910075893702615 2468946437865113840553923)
                  ·
                    refine ⟨3703419656797670760830885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2468946437865113840553923 3703419656797670760830885)
                    ·
                      refine ⟨694391185649563267655791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3703419656797670760830885 694391185649563267655791)
                      ·
                        rfl

theorem cell23_1352322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 3, 1, 1, 4].length) (baseStart_1352322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352322 prefixEnd_1352322 := by exact prefixLift 1352322
  have htrace : WordTrace (prefixWord ++ tailWord_1352322) baseStart_1352322 baseEnd_1352322 := by
    simpa [prefixWord, tailWord_1352322, baseEnd_1352322] using wordTrace_append hprefix tailTrace_1352322
  have hstable : (prefixWord ++ tailWord_1352322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352322).length < 2 ^ (prefixWord ++ tailWord_1352322).sum := by decide
  have hdescent : baseEnd_1352322 < baseStart_1352322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352338 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_1352338 : Nat := 118140960795 + 1352338 * 2 ^ 59
def prefixEnd_1352338 : Nat := 4983230072969 + 3 ^ 40 * 1352338 * 2
def baseEnd_1352338 : Nat := 694399401340035205055717

theorem tailTrace_1352338 : CollatzResearch.WordTrace tailWord_1352338 prefixEnd_1352338 694399401340035205055717 := by
  unfold tailWord_1352338
  simp only [CollatzResearch.WordTrace]
  refine ⟨12330954743679465446942417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32882545983145241191846445 12330954743679465446942417)
  ·
    refine ⟨9248216057759599085206813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12330954743679465446942417 9248216057759599085206813)
    ·
      refine ⟨3468081021659849656952555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9248216057759599085206813 3468081021659849656952555)
      ·
        refine ⟨5202121532489774485428833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3468081021659849656952555 5202121532489774485428833)
        ·
          refine ⟨3901591149367330864071625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5202121532489774485428833 3901591149367330864071625)
          ·
            refine ⟨2926193362025498148053719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3901591149367330864071625 2926193362025498148053719)
            ·
              refine ⟨4389290043038247222080579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2926193362025498148053719 4389290043038247222080579)
              ·
                refine ⟨6583935064557370833120869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4389290043038247222080579 6583935064557370833120869)
                ·
                  refine ⟨1234487824604507031210163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6583935064557370833120869 1234487824604507031210163)
                  ·
                    refine ⟨1851731736906760546815245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1234487824604507031210163 1851731736906760546815245)
                    ·
                      refine ⟨694399401340035205055717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1851731736906760546815245 694399401340035205055717)
                      ·
                        rfl

theorem cell23_1352338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_1352338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352338 prefixEnd_1352338 := by exact prefixLift 1352338
  have htrace : WordTrace (prefixWord ++ tailWord_1352338) baseStart_1352338 baseEnd_1352338 := by
    simpa [prefixWord, tailWord_1352338, baseEnd_1352338] using wordTrace_append hprefix tailTrace_1352338
  have hstable : (prefixWord ++ tailWord_1352338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352338).length < 2 ^ (prefixWord ++ tailWord_1352338).sum := by decide
  have hdescent : baseEnd_1352338 < baseStart_1352338 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352361 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 6, 2, 2]
def baseStart_1352361 : Nat := 118140960795 + 1352361 * 2 ^ 59
def prefixEnd_1352361 : Nat := 4983230072969 + 3 ^ 40 * 1352361 * 2
def baseEnd_1352361 : Nat := 694411211395088615068111

theorem tailTrace_1352361 : CollatzResearch.WordTrace tailWord_1352361 prefixEnd_1352361 694411211395088615068111 := by
  unfold tailWord_1352361
  simp only [CollatzResearch.WordTrace]
  refine ⟨49324657853634536715856937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32883105235756357810571291 49324657853634536715856937)
  ·
    refine ⟨36993493390225902536892703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49324657853634536715856937 36993493390225902536892703)
    ·
      refine ⟨55490240085338853805339055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36993493390225902536892703 55490240085338853805339055)
      ·
        refine ⟨83235360128008280708008583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55490240085338853805339055 83235360128008280708008583)
        ·
          refine ⟨124853040192012421062012875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83235360128008280708008583 124853040192012421062012875)
          ·
            refine ⟨187279560288018631593019313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 124853040192012421062012875 187279560288018631593019313)
            ·
              refine ⟨140459670216013973694764485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187279560288018631593019313 140459670216013973694764485)
              ·
                refine ⟨26336188165502620067768341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140459670216013973694764485 26336188165502620067768341)
                ·
                  refine ⟨1234508820257935315676641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26336188165502620067768341 1234508820257935315676641)
                  ·
                    refine ⟨925881615193451486757481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1234508820257935315676641 925881615193451486757481)
                    ·
                      refine ⟨694411211395088615068111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 925881615193451486757481 694411211395088615068111)
                      ·
                        rfl

theorem cell23_1352361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6, 2, 2].length) (baseStart_1352361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352361 prefixEnd_1352361 := by exact prefixLift 1352361
  have htrace : WordTrace (prefixWord ++ tailWord_1352361) baseStart_1352361 baseEnd_1352361 := by
    simpa [prefixWord, tailWord_1352361, baseEnd_1352361] using wordTrace_append hprefix tailTrace_1352361
  have hstable : (prefixWord ++ tailWord_1352361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352361).length < 2 ^ (prefixWord ++ tailWord_1352361).sum := by decide
  have hdescent : baseEnd_1352361 < baseStart_1352361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352365 : List Nat := [1, 5, 2, 1, 1, 3, 2, 2, 1, 3, 2]
def baseStart_1352365 : Nat := 118140960795 + 1352365 * 2 ^ 59
def prefixEnd_1352365 : Nat := 4983230072969 + 3 ^ 40 * 1352365 * 2
def baseEnd_1352365 : Nat := 694413265317706599418093

theorem tailTrace_1352365 : CollatzResearch.WordTrace tailWord_1352365 prefixEnd_1352365 694413265317706599418093 := by
  unfold tailWord_1352365
  simp only [CollatzResearch.WordTrace]
  refine ⟨49324803745620045399002549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32883202497080030266001699 49324803745620045399002549)
  ·
    refine ⟨4624200351151879256156489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49324803745620045399002549 4624200351151879256156489)
    ·
      refine ⟨3468150263363909442117367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4624200351151879256156489 3468150263363909442117367)
      ·
        refine ⟨5202225395045864163176051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3468150263363909442117367 5202225395045864163176051)
        ·
          refine ⟨7803338092568796244764077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5202225395045864163176051 7803338092568796244764077)
          ·
            refine ⟨2926251784713298591786529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7803338092568796244764077 2926251784713298591786529)
            ·
              refine ⟨2194688838534973943839897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2926251784713298591786529 2194688838534973943839897)
              ·
                refine ⟨1646016628901230457879923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2194688838534973943839897 1646016628901230457879923)
                ·
                  refine ⟨2469024943351845686819885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1646016628901230457879923 2469024943351845686819885)
                  ·
                    refine ⟨925884353756942132557457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2469024943351845686819885 925884353756942132557457)
                    ·
                      refine ⟨694413265317706599418093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 925884353756942132557457 694413265317706599418093)
                      ·
                        rfl

theorem cell23_1352365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 1, 3, 2].length) (baseStart_1352365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352365 prefixEnd_1352365 := by exact prefixLift 1352365
  have htrace : WordTrace (prefixWord ++ tailWord_1352365) baseStart_1352365 baseEnd_1352365 := by
    simpa [prefixWord, tailWord_1352365, baseEnd_1352365] using wordTrace_append hprefix tailTrace_1352365
  have hstable : (prefixWord ++ tailWord_1352365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352365).length < 2 ^ (prefixWord ++ tailWord_1352365).sum := by decide
  have hdescent : baseEnd_1352365 < baseStart_1352365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352387 : List Nat := [1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 6]
def baseStart_1352387 : Nat := 118140960795 + 1352387 * 2 ^ 59
def prefixEnd_1352387 : Nat := 4983230072969 + 3 ^ 40 * 1352387 * 2
def baseEnd_1352387 : Nat := 694424561892105513342991

theorem tailTrace_1352387 : CollatzResearch.WordTrace tailWord_1352387 prefixEnd_1352387 694424561892105513342991 := by
  unfold tailWord_1352387
  simp only [CollatzResearch.WordTrace]
  refine ⟨49325606151540343156303415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32883737434360228770868943 49325606151540343156303415)
  ·
    refine ⟨73988409227310514734455123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49325606151540343156303415 73988409227310514734455123)
    ·
      refine ⟨110982613840965772101682685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73988409227310514734455123 110982613840965772101682685)
      ·
        refine ⟨41618480190362164538131007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110982613840965772101682685 41618480190362164538131007)
        ·
          refine ⟨62427720285543246807196511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41618480190362164538131007 62427720285543246807196511)
          ·
            refine ⟨93641580428314870210794767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62427720285543246807196511 93641580428314870210794767)
            ·
              refine ⟨140462370642472305316192151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93641580428314870210794767 140462370642472305316192151)
              ·
                refine ⟨210693555963708457974288227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140462370642472305316192151 210693555963708457974288227)
                ·
                  refine ⟨316040333945562686961432341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 210693555963708457974288227 316040333945562686961432341)
                  ·
                    refine ⟨14814390653698250951317141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 316040333945562686961432341 14814390653698250951317141)
                    ·
                      refine ⟨694424561892105513342991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14814390653698250951317141 694424561892105513342991)
                      ·
                        rfl

theorem cell23_1352387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_1352387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352387 prefixEnd_1352387 := by exact prefixLift 1352387
  have htrace : WordTrace (prefixWord ++ tailWord_1352387) baseStart_1352387 baseEnd_1352387 := by
    simpa [prefixWord, tailWord_1352387, baseEnd_1352387] using wordTrace_append hprefix tailTrace_1352387
  have hstable : (prefixWord ++ tailWord_1352387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352387).length < 2 ^ (prefixWord ++ tailWord_1352387).sum := by decide
  have hdescent : baseEnd_1352387 < baseStart_1352387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352412 : List Nat := [2, 2, 5, 1, 1, 2, 1, 3, 2, 2, 2]
def baseStart_1352412 : Nat := 118140960795 + 1352412 * 2 ^ 59
def prefixEnd_1352412 : Nat := 4983230072969 + 3 ^ 40 * 1352412 * 2
def baseEnd_1352412 : Nat := 694437398908467915530377

theorem tailTrace_1352412 : CollatzResearch.WordTrace tailWord_1352412 prefixEnd_1352412 694437398908467915530377 := by
  unfold tailWord_1352412
  simp only [CollatzResearch.WordTrace]
  refine ⟨24663258988224886212981745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32884345317633181617308993 24663258988224886212981745)
  ·
    refine ⟨18497444241168664659736309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24663258988224886212981745 18497444241168664659736309)
    ·
      refine ⟨1734135397609562311850279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18497444241168664659736309 1734135397609562311850279)
      ·
        refine ⟨2601203096414343467775419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1734135397609562311850279 2601203096414343467775419)
        ·
          refine ⟨3901804644621515201663129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2601203096414343467775419 3901804644621515201663129)
          ·
            refine ⟨2926353483466136401247347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3901804644621515201663129 2926353483466136401247347)
            ·
              refine ⟨4389530225199204601871021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2926353483466136401247347 4389530225199204601871021)
              ·
                refine ⟨1646073834449701725701633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4389530225199204601871021 1646073834449701725701633)
                ·
                  refine ⟨1234555375837276294276225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1646073834449701725701633 1234555375837276294276225)
                  ·
                    refine ⟨925916531877957220707169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1234555375837276294276225 925916531877957220707169)
                    ·
                      refine ⟨694437398908467915530377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 925916531877957220707169 694437398908467915530377)
                      ·
                        rfl

theorem cell23_1352412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_1352412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352412 prefixEnd_1352412 := by exact prefixLift 1352412
  have htrace : WordTrace (prefixWord ++ tailWord_1352412) baseStart_1352412 baseEnd_1352412 := by
    simpa [prefixWord, tailWord_1352412, baseEnd_1352412] using wordTrace_append hprefix tailTrace_1352412
  have hstable : (prefixWord ++ tailWord_1352412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352412).length < 2 ^ (prefixWord ++ tailWord_1352412).sum := by decide
  have hdescent : baseEnd_1352412 < baseStart_1352412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352431 : List Nat := [1, 1, 2, 1, 5, 3, 2, 1, 2, 5]
def baseStart_1352431 : Nat := 118140960795 + 1352431 * 2 ^ 59
def prefixEnd_1352431 : Nat := 4983230072969 + 3 ^ 40 * 1352431 * 2
def baseEnd_1352431 : Nat := 231482385013634447064263

theorem tailTrace_1352431 : CollatzResearch.WordTrace tailWord_1352431 prefixEnd_1352431 231482385013634447064263 := by
  unfold tailWord_1352431
  simp only [CollatzResearch.WordTrace]
  refine ⟨49327210963380938670905147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32884807308920625780603431 49327210963380938670905147)
  ·
    refine ⟨73990816445071408006357721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49327210963380938670905147 73990816445071408006357721)
    ·
      refine ⟨55493112333803556004768291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73990816445071408006357721 55493112333803556004768291)
      ·
        refine ⟨83239668500705334007152437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55493112333803556004768291 83239668500705334007152437)
        ·
          refine ⟨7803718921941125063170541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83239668500705334007152437 7803718921941125063170541)
          ·
            refine ⟨2926394595727921898688953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7803718921941125063170541 2926394595727921898688953)
            ·
              refine ⟨2194795946795941424016715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2926394595727921898688953 2194795946795941424016715)
              ·
                refine ⟨3292193920193912136025073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2194795946795941424016715 3292193920193912136025073)
                ·
                  refine ⟨2469145440145434102018805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3292193920193912136025073 2469145440145434102018805)
                  ·
                    refine ⟨231482385013634447064263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2469145440145434102018805 231482385013634447064263)
                    ·
                      rfl

theorem cell23_1352431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 2, 5].length) (baseStart_1352431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352431 prefixEnd_1352431 := by exact prefixLift 1352431
  have htrace : WordTrace (prefixWord ++ tailWord_1352431) baseStart_1352431 baseEnd_1352431 := by
    simpa [prefixWord, tailWord_1352431, baseEnd_1352431] using wordTrace_append hprefix tailTrace_1352431
  have hstable : (prefixWord ++ tailWord_1352431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352431).length < 2 ^ (prefixWord ++ tailWord_1352431).sum := by decide
  have hdescent : baseEnd_1352431 < baseStart_1352431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352451 : List Nat := [1, 1, 1, 3, 2, 2, 1, 4, 2, 4, 2]
def baseStart_1352451 : Nat := 118140960795 + 1352451 * 2 ^ 59
def prefixEnd_1352451 : Nat := 4983230072969 + 3 ^ 40 * 1352451 * 2
def baseEnd_1352451 : Nat := 694457424653993262942697

theorem tailTrace_1352451 : CollatzResearch.WordTrace tailWord_1352451 prefixEnd_1352451 694457424653993262942697 := by
  unfold tailWord_1352451
  simp only [CollatzResearch.WordTrace]
  refine ⟨49327940423308482086633207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32885293615538988057755471 49327940423308482086633207)
  ·
    refine ⟨73991910634962723129949811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49327940423308482086633207 73991910634962723129949811)
    ·
      refine ⟨110987865952444084694924717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 73991910634962723129949811 110987865952444084694924717)
      ·
        refine ⟨41620449732166531760596769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 110987865952444084694924717 41620449732166531760596769)
        ·
          refine ⟨31215337299124898820447577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41620449732166531760596769 31215337299124898820447577)
          ·
            refine ⟨23411502974343674115335683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31215337299124898820447577 23411502974343674115335683)
            ·
              refine ⟨35117254461515511173003525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23411502974343674115335683 35117254461515511173003525)
              ·
                refine ⟨6584485211534158344938161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35117254461515511173003525 6584485211534158344938161)
                ·
                  refine ⟨4938363908650618758703621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6584485211534158344938161 4938363908650618758703621)
                  ·
                    refine ⟨925943232871991017256929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4938363908650618758703621 925943232871991017256929)
                    ·
                      refine ⟨694457424653993262942697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 925943232871991017256929 694457424653993262942697)
                      ·
                        rfl

theorem cell23_1352451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 4, 2, 4, 2].length) (baseStart_1352451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352451 prefixEnd_1352451 := by exact prefixLift 1352451
  have htrace : WordTrace (prefixWord ++ tailWord_1352451) baseStart_1352451 baseEnd_1352451 := by
    simpa [prefixWord, tailWord_1352451, baseEnd_1352451] using wordTrace_append hprefix tailTrace_1352451
  have hstable : (prefixWord ++ tailWord_1352451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352451).length < 2 ^ (prefixWord ++ tailWord_1352451).sum := by decide
  have hdescent : baseEnd_1352451 < baseStart_1352451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352538 : List Nat := [3, 1, 1, 2, 1, 5, 2, 2, 1, 5]
def baseStart_1352538 : Nat := 118140960795 + 1352538 * 2 ^ 59
def prefixEnd_1352538 : Nat := 4983230072969 + 3 ^ 40 * 1352538 * 2
def baseEnd_1352538 : Nat := 231500699156978140851599

theorem tailTrace_1352538 : CollatzResearch.WordTrace tailWord_1352538 prefixEnd_1352538 231500699156978140851599 := by
  unfold tailWord_1352538
  simp only [CollatzResearch.WordTrace]
  refine ⟨12332778393498323986262567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32887409049328863963366845 12332778393498323986262567)
  ·
    refine ⟨18499167590247485979393851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12332778393498323986262567 18499167590247485979393851)
    ·
      refine ⟨27748751385371228969090777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18499167590247485979393851 27748751385371228969090777)
      ·
        refine ⟨20811563539028421726818083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27748751385371228969090777 20811563539028421726818083)
        ·
          refine ⟨31217345308542632590227125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20811563539028421726818083 31217345308542632590227125)
          ·
            refine ⟨2926626122675871805333793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 31217345308542632590227125 2926626122675871805333793)
            ·
              refine ⟨2194969592006903854000345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2926626122675871805333793 2194969592006903854000345)
              ·
                refine ⟨1646227194005177890500259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2194969592006903854000345 1646227194005177890500259)
                ·
                  refine ⟨2469340791007766835750389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1646227194005177890500259 2469340791007766835750389)
                  ·
                    refine ⟨231500699156978140851599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2469340791007766835750389 231500699156978140851599)
                    ·
                      rfl

theorem cell23_1352538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 1, 5].length) (baseStart_1352538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352538 prefixEnd_1352538 := by exact prefixLift 1352538
  have htrace : WordTrace (prefixWord ++ tailWord_1352538) baseStart_1352538 baseEnd_1352538 := by
    simpa [prefixWord, tailWord_1352538, baseEnd_1352538] using wordTrace_append hprefix tailTrace_1352538
  have hstable : (prefixWord ++ tailWord_1352538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352538).length < 2 ^ (prefixWord ++ tailWord_1352538).sum := by decide
  have hdescent : baseEnd_1352538 < baseStart_1352538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352552 : List Nat := [2, 1, 4, 2, 1, 2, 3, 3, 1, 1, 3]
def baseStart_1352552 : Nat := 118140960795 + 1352552 * 2 ^ 59
def prefixEnd_1352552 : Nat := 4983230072969 + 3 ^ 40 * 1352552 * 2
def baseEnd_1352552 : Nat := 694509286200097367779733

theorem tailTrace_1352552 : CollatzResearch.WordTrace tailWord_1352552 prefixEnd_1352552 694509286200097367779733 := by
  unfold tailWord_1352552
  simp only [CollatzResearch.WordTrace]
  refine ⟨24665812097971288168029955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32887749463961717557373273 24665812097971288168029955)
  ·
    refine ⟨36998718146956932252044933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24665812097971288168029955 36998718146956932252044933)
    ·
      refine ⟨6937259652554424797258425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36998718146956932252044933 6937259652554424797258425)
      ·
        refine ⟨5202944739415818597943819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6937259652554424797258425 5202944739415818597943819)
        ·
          refine ⟨7804417109123727896915729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5202944739415818597943819 7804417109123727896915729)
          ·
            refine ⟨5853312831842795922686797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7804417109123727896915729 5853312831842795922686797)
            ·
              refine ⟨2194992311941048471007549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5853312831842795922686797 2194992311941048471007549)
              ·
                refine ⟨823122116977893176627831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2194992311941048471007549 823122116977893176627831)
                ·
                  refine ⟨1234683175466839764941747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 823122116977893176627831 1234683175466839764941747)
                  ·
                    refine ⟨1852024763200259647412621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1234683175466839764941747 1852024763200259647412621)
                    ·
                      refine ⟨694509286200097367779733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1852024763200259647412621 694509286200097367779733)
                      ·
                        rfl

theorem cell23_1352552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_1352552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352552 prefixEnd_1352552 := by exact prefixLift 1352552
  have htrace : WordTrace (prefixWord ++ tailWord_1352552) baseStart_1352552 baseEnd_1352552 := by
    simpa [prefixWord, tailWord_1352552, baseEnd_1352552] using wordTrace_append hprefix tailTrace_1352552
  have hstable : (prefixWord ++ tailWord_1352552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352552).length < 2 ^ (prefixWord ++ tailWord_1352552).sum := by decide
  have hdescent : baseEnd_1352552 < baseStart_1352552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352561 : List Nat := [1, 2, 2, 2, 1, 4, 1, 3, 1, 1, 5]
def baseStart_1352561 : Nat := 118140960795 + 1352561 * 2 ^ 59
def prefixEnd_1352561 : Nat := 4983230072969 + 3 ^ 40 * 1352561 * 2
def baseEnd_1352561 : Nat := 694513907525987832567191

theorem tailTrace_1352561 : CollatzResearch.WordTrace tailWord_1352561 prefixEnd_1352561 694513907525987832567191 := by
  unfold tailWord_1352561
  simp only [CollatzResearch.WordTrace]
  refine ⟨49331952452909970873137537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32887968301939980582091691 49331952452909970873137537)
  ·
    refine ⟨36998964339682478154853153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49331952452909970873137537 36998964339682478154853153)
    ·
      refine ⟨27749223254761858616139865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36998964339682478154853153 27749223254761858616139865)
      ·
        refine ⟨20811917441071393962104899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27749223254761858616139865 20811917441071393962104899)
        ·
          refine ⟨31217876161607090943157349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20811917441071393962104899 31217876161607090943157349)
          ·
            refine ⟨5853351780301329551842003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31217876161607090943157349 5853351780301329551842003)
            ·
              refine ⟨8780027670451994327763005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5853351780301329551842003 8780027670451994327763005)
              ·
                refine ⟨3292510376419497872911127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8780027670451994327763005 3292510376419497872911127)
                ·
                  refine ⟨4938765564629246809366691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3292510376419497872911127 4938765564629246809366691)
                  ·
                    refine ⟨7408148346943870214050037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4938765564629246809366691 7408148346943870214050037)
                    ·
                      refine ⟨694513907525987832567191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7408148346943870214050037 694513907525987832567191)
                      ·
                        rfl

theorem cell23_1352561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_1352561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352561 prefixEnd_1352561 := by exact prefixLift 1352561
  have htrace : WordTrace (prefixWord ++ tailWord_1352561) baseStart_1352561 baseEnd_1352561 := by
    simpa [prefixWord, tailWord_1352561, baseEnd_1352561] using wordTrace_append hprefix tailTrace_1352561
  have hstable : (prefixWord ++ tailWord_1352561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352561).length < 2 ^ (prefixWord ++ tailWord_1352561).sum := by decide
  have hdescent : baseEnd_1352561 < baseStart_1352561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352575 : List Nat := [1, 1, 2, 2, 1, 1, 7, 1, 3, 2, 2]
def baseStart_1352575 : Nat := 118140960795 + 1352575 * 2 ^ 59
def prefixEnd_1352575 : Nat := 4983230072969 + 3 ^ 40 * 1352575 * 2
def baseEnd_1352575 : Nat := 694521096255150777792127

theorem tailTrace_1352575 : CollatzResearch.WordTrace tailWord_1352575 prefixEnd_1352575 694521096255150777792127 := by
  unfold tailWord_1352575
  simp only [CollatzResearch.WordTrace]
  refine ⟨49332463074859251264147179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32888308716572834176098119 49332463074859251264147179)
  ·
    refine ⟨73998694612288876896220769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49332463074859251264147179 73998694612288876896220769)
    ·
      refine ⟨55499020959216657672165577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 73998694612288876896220769 55499020959216657672165577)
      ·
        refine ⟨41624265719412493254124183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55499020959216657672165577 41624265719412493254124183)
        ·
          refine ⟨62436398579118739881186275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41624265719412493254124183 62436398579118739881186275)
          ·
            refine ⟨93654597868678109821779413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62436398579118739881186275 93654597868678109821779413)
            ·
              refine ⟨2195029637547143198947955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 93654597868678109821779413 2195029637547143198947955)
              ·
                refine ⟨3292544456320714798421933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2195029637547143198947955 3292544456320714798421933)
                ·
                  refine ⟨1234704171120268049408225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3292544456320714798421933 1234704171120268049408225)
                  ·
                    refine ⟨926028128340201037056169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1234704171120268049408225 926028128340201037056169)
                    ·
                      refine ⟨694521096255150777792127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 926028128340201037056169 694521096255150777792127)
                      ·
                        rfl

theorem cell23_1352575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 7, 1, 3, 2, 2].length) (baseStart_1352575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352575 prefixEnd_1352575 := by exact prefixLift 1352575
  have htrace : WordTrace (prefixWord ++ tailWord_1352575) baseStart_1352575 baseEnd_1352575 := by
    simpa [prefixWord, tailWord_1352575, baseEnd_1352575] using wordTrace_append hprefix tailTrace_1352575
  have hstable : (prefixWord ++ tailWord_1352575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352575).length < 2 ^ (prefixWord ++ tailWord_1352575).sum := by decide
  have hdescent : baseEnd_1352575 < baseStart_1352575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352581 : List Nat := [1, 3, 1, 1, 3, 4, 2, 8]
def baseStart_1352581 : Nat := 118140960795 + 1352581 * 2 ^ 59
def prefixEnd_1352581 : Nat := 4983230072969 + 3 ^ 40 * 1352581 * 2
def baseEnd_1352581 : Nat := 25723117671817694604337

theorem tailTrace_1352581 : CollatzResearch.WordTrace tailWord_1352581 prefixEnd_1352581 25723117671817694604337 := by
  unfold tailWord_1352581
  simp only [CollatzResearch.WordTrace]
  refine ⟨49332681912837514288865597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32888454608558342859243731 49332681912837514288865597)
  ·
    refine ⟨18499755717314067858324599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49332681912837514288865597 18499755717314067858324599)
    ·
      refine ⟨27749633575971101787486899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18499755717314067858324599 27749633575971101787486899)
      ·
        refine ⟨41624450363956652681230349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27749633575971101787486899 41624450363956652681230349)
        ·
          refine ⟨15609168886483744755461381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41624450363956652681230349 15609168886483744755461381)
          ·
            refine ⟨2926719166215702141649009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15609168886483744755461381 2926719166215702141649009)
            ·
              refine ⟨2195039374661776606236757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2926719166215702141649009 2195039374661776606236757)
              ·
                refine ⟨25723117671817694604337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2195039374661776606236757 25723117671817694604337)
                ·
                  rfl

theorem cell23_1352581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 8].length) (baseStart_1352581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352581 prefixEnd_1352581 := by exact prefixLift 1352581
  have htrace : WordTrace (prefixWord ++ tailWord_1352581) baseStart_1352581 baseEnd_1352581 := by
    simpa [prefixWord, tailWord_1352581, baseEnd_1352581] using wordTrace_append hprefix tailTrace_1352581
  have hstable : (prefixWord ++ tailWord_1352581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352581).length < 2 ^ (prefixWord ++ tailWord_1352581).sum := by decide
  have hdescent : baseEnd_1352581 < baseStart_1352581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352585 : List Nat := [1, 2, 1, 1, 5, 2, 4, 1, 2, 4]
def baseStart_1352585 : Nat := 118140960795 + 1352585 * 2 ^ 59
def prefixEnd_1352585 : Nat := 4983230072969 + 3 ^ 40 * 1352585 * 2
def baseEnd_1352585 : Nat := 231508743687231912889027

theorem tailTrace_1352585 : CollatzResearch.WordTrace tailWord_1352585 prefixEnd_1352585 231508743687231912889027 := by
  unfold tailWord_1352585
  simp only [CollatzResearch.WordTrace]
  refine ⟨49332827804823022972011209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32888551869882015314674139 49332827804823022972011209)
  ·
    refine ⟨36999620853617267229008407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49332827804823022972011209 36999620853617267229008407)
    ·
      refine ⟨55499431280425900843512611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36999620853617267229008407 55499431280425900843512611)
      ·
        refine ⟨83249146920638851265268917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55499431280425900843512611 83249146920638851265268917)
        ·
          refine ⟨7804607523809892306118961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83249146920638851265268917 7804607523809892306118961)
          ·
            refine ⟨5853455642857419229589221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7804607523809892306118961 5853455642857419229589221)
            ·
              refine ⟨1097522933035766105547979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5853455642857419229589221 1097522933035766105547979)
              ·
                refine ⟨1646284399553649158321969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1097522933035766105547979 1646284399553649158321969)
                ·
                  refine ⟨1234713299665236868741477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1646284399553649158321969 1234713299665236868741477)
                  ·
                    refine ⟨231508743687231912889027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1234713299665236868741477 231508743687231912889027)
                    ·
                      rfl

theorem cell23_1352585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 4, 1, 2, 4].length) (baseStart_1352585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352585 prefixEnd_1352585 := by exact prefixLift 1352585
  have htrace : WordTrace (prefixWord ++ tailWord_1352585) baseStart_1352585 baseEnd_1352585 := by
    simpa [prefixWord, tailWord_1352585, baseEnd_1352585] using wordTrace_append hprefix tailTrace_1352585
  have hstable : (prefixWord ++ tailWord_1352585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352585).length < 2 ^ (prefixWord ++ tailWord_1352585).sum := by decide
  have hdescent : baseEnd_1352585 < baseStart_1352585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352608 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 6, 1, 3]
def baseStart_1352608 : Nat := 118140960795 + 1352608 * 2 ^ 59
def prefixEnd_1352608 : Nat := 4983230072969 + 3 ^ 40 * 1352608 * 2
def baseEnd_1352608 : Nat := 694538041116749148679475

theorem tailTrace_1352608 : CollatzResearch.WordTrace tailWord_1352608 prefixEnd_1352608 694538041116749148679475 := by
  unfold tailWord_1352608
  simp only [CollatzResearch.WordTrace]
  refine ⟨24666833341869848950049239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32889111122493131933398985 24666833341869848950049239)
  ·
    refine ⟨37000250012804773425073859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24666833341869848950049239 37000250012804773425073859)
    ·
      refine ⟨55500375019207160137610789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37000250012804773425073859 55500375019207160137610789)
      ·
        refine ⟨10406320316101342525802023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55500375019207160137610789 10406320316101342525802023)
        ·
          refine ⟨15609480474152013788703035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10406320316101342525802023 15609480474152013788703035)
          ·
            refine ⟨23414220711228020683054553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15609480474152013788703035 23414220711228020683054553)
            ·
              refine ⟨17560665533421015512290915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23414220711228020683054553 17560665533421015512290915)
              ·
                refine ⟨26340998300131523268436373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17560665533421015512290915 26340998300131523268436373)
                ·
                  refine ⟨1234734295318665153207955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 26340998300131523268436373 1234734295318665153207955)
                  ·
                    refine ⟨1852101442977997729811933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1234734295318665153207955 1852101442977997729811933)
                    ·
                      refine ⟨694538041116749148679475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1852101442977997729811933 694538041116749148679475)
                      ·
                        rfl

theorem cell23_1352608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 6, 1, 3].length) (baseStart_1352608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352608 prefixEnd_1352608 := by exact prefixLift 1352608
  have htrace : WordTrace (prefixWord ++ tailWord_1352608) baseStart_1352608 baseEnd_1352608 := by
    simpa [prefixWord, tailWord_1352608, baseEnd_1352608] using wordTrace_append hprefix tailTrace_1352608
  have hstable : (prefixWord ++ tailWord_1352608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352608).length < 2 ^ (prefixWord ++ tailWord_1352608).sum := by decide
  have hdescent : baseEnd_1352608 < baseStart_1352608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352631 : List Nat := [1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 4]
def baseStart_1352631 : Nat := 118140960795 + 1352631 * 2 ^ 59
def prefixEnd_1352631 : Nat := 4983230072969 + 3 ^ 40 * 1352631 * 2
def baseEnd_1352631 : Nat := 694549851171802558691869

theorem tailTrace_1352631 : CollatzResearch.WordTrace tailWord_1352631 prefixEnd_1352631 694549851171802558691869 := by
  unfold tailWord_1352631
  simp only [CollatzResearch.WordTrace]
  refine ⟨49334505562656372828185747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32889670375104248552123831 49334505562656372828185747)
  ·
    refine ⟨74001758343984559242278621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49334505562656372828185747 74001758343984559242278621)
    ·
      refine ⟨27750659378994209715854483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74001758343984559242278621 27750659378994209715854483)
      ·
        refine ⟨41625989068491314573781725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27750659378994209715854483 41625989068491314573781725)
        ·
          refine ⟨15609745900684242965168147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41625989068491314573781725 15609745900684242965168147)
          ·
            refine ⟨23414618851026364447752221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15609745900684242965168147 23414618851026364447752221)
            ·
              refine ⟨8780482069134886667907083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23414618851026364447752221 8780482069134886667907083)
              ·
                refine ⟨13170723103702330001860625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8780482069134886667907083 13170723103702330001860625)
                ·
                  refine ⟨9878042327776747501395469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13170723103702330001860625 9878042327776747501395469)
                  ·
                    refine ⟨3704265872916280313023301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9878042327776747501395469 3704265872916280313023301)
                    ·
                      refine ⟨694549851171802558691869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3704265872916280313023301 694549851171802558691869)
                      ·
                        rfl

theorem cell23_1352631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 3, 1, 2, 3, 4].length) (baseStart_1352631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352631 prefixEnd_1352631 := by exact prefixLift 1352631
  have htrace : WordTrace (prefixWord ++ tailWord_1352631) baseStart_1352631 baseEnd_1352631 := by
    simpa [prefixWord, tailWord_1352631, baseEnd_1352631] using wordTrace_append hprefix tailTrace_1352631
  have hstable : (prefixWord ++ tailWord_1352631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352631).length < 2 ^ (prefixWord ++ tailWord_1352631).sum := by decide
  have hdescent : baseEnd_1352631 < baseStart_1352631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352665 : List Nat := [1, 2, 1, 2, 5, 1, 2, 2, 1, 4, 2]
def baseStart_1352665 : Nat := 118140960795 + 1352665 * 2 ^ 59
def prefixEnd_1352665 : Nat := 4983230072969 + 3 ^ 40 * 1352665 * 2
def baseEnd_1352665 : Nat := 694567309514055425666713

theorem tailTrace_1352665 : CollatzResearch.WordTrace tailWord_1352665 prefixEnd_1352665 694567309514055425666713 := by
  unfold tailWord_1352665
  simp only [CollatzResearch.WordTrace]
  refine ⟨49335745644533196634923449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32890497096355464423282299 49335745644533196634923449)
  ·
    refine ⟨37001809233399897476192587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49335745644533196634923449 37001809233399897476192587)
    ·
      refine ⟨55502713850099846214288881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37001809233399897476192587 55502713850099846214288881)
      ·
        refine ⟨41627035387574884660716661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55502713850099846214288881 41627035387574884660716661)
        ·
          refine ⟨3902534567585145436942187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41627035387574884660716661 3902534567585145436942187)
          ·
            refine ⟨5853801851377718155413281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3902534567585145436942187 5853801851377718155413281)
            ·
              refine ⟨4390351388533288616559961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5853801851377718155413281 4390351388533288616559961)
              ·
                refine ⟨3292763541399966462419971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4390351388533288616559961 3292763541399966462419971)
                ·
                  refine ⟨4939145312099949693629957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3292763541399966462419971 4939145312099949693629957)
                  ·
                    refine ⟨926089746018740567555617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4939145312099949693629957 926089746018740567555617)
                    ·
                      refine ⟨694567309514055425666713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 926089746018740567555617 694567309514055425666713)
                      ·
                        rfl

theorem cell23_1352665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 2, 1, 4, 2].length) (baseStart_1352665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352665 prefixEnd_1352665 := by exact prefixLift 1352665
  have htrace : WordTrace (prefixWord ++ tailWord_1352665) baseStart_1352665 baseEnd_1352665 := by
    simpa [prefixWord, tailWord_1352665, baseEnd_1352665] using wordTrace_append hprefix tailTrace_1352665
  have hstable : (prefixWord ++ tailWord_1352665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352665).length < 2 ^ (prefixWord ++ tailWord_1352665).sum := by decide
  have hdescent : baseEnd_1352665 < baseStart_1352665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352669 : List Nat := [1, 4, 3, 1, 2, 1, 4, 1, 1, 3, 2]
def baseStart_1352669 : Nat := 118140960795 + 1352669 * 2 ^ 59
def prefixEnd_1352669 : Nat := 4983230072969 + 3 ^ 40 * 1352669 * 2
def baseEnd_1352669 : Nat := 694569363436673410016695

theorem tailTrace_1352669 : CollatzResearch.WordTrace tailWord_1352669 prefixEnd_1352669 694569363436673410016695 := by
  unfold tailWord_1352669
  simp only [CollatzResearch.WordTrace]
  refine ⟨49335891536518705318069061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32890594357679136878712707 49335891536518705318069061)
  ·
    refine ⟨9250479663097257247137949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49335891536518705318069061 9250479663097257247137949)
    ·
      refine ⟨3468929873661471467676731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9250479663097257247137949 3468929873661471467676731)
      ·
        refine ⟨5203394810492207201515097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3468929873661471467676731 5203394810492207201515097)
        ·
          refine ⟨3902546107869155401136323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5203394810492207201515097 3902546107869155401136323)
          ·
            refine ⟨5853819161803733101704485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3902546107869155401136323 5853819161803733101704485)
            ·
              refine ⟨1097591092838199956569591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5853819161803733101704485 1097591092838199956569591)
              ·
                refine ⟨1646386639257299934854387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1097591092838199956569591 1646386639257299934854387)
                ·
                  refine ⟨2469579958885949902281581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1646386639257299934854387 2469579958885949902281581)
                  ·
                    refine ⟨926092484582231213355593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2469579958885949902281581 926092484582231213355593)
                    ·
                      refine ⟨694569363436673410016695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 926092484582231213355593 694569363436673410016695)
                      ·
                        rfl

theorem cell23_1352669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 1, 3, 2].length) (baseStart_1352669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352669 prefixEnd_1352669 := by exact prefixLift 1352669
  have htrace : WordTrace (prefixWord ++ tailWord_1352669) baseStart_1352669 baseEnd_1352669 := by
    simpa [prefixWord, tailWord_1352669, baseEnd_1352669] using wordTrace_append hprefix tailTrace_1352669
  have hstable : (prefixWord ++ tailWord_1352669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352669).length < 2 ^ (prefixWord ++ tailWord_1352669).sum := by decide
  have hdescent : baseEnd_1352669 < baseStart_1352669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352682 : List Nat := [3, 1, 3, 1, 2, 3, 1, 1, 4, 2, 2]
def baseStart_1352682 : Nat := 118140960795 + 1352682 * 2 ^ 59
def prefixEnd_1352682 : Nat := 4983230072969 + 3 ^ 40 * 1352682 * 2
def baseEnd_1352682 : Nat := 694576038685181859154135

theorem tailTrace_1352682 : CollatzResearch.WordTrace tailWord_1352682 prefixEnd_1352682 694576038685181859154135 := by
  unfold tailWord_1352682
  simp only [CollatzResearch.WordTrace]
  refine ⟨12334091421367902134573075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32890910456981072358861533 12334091421367902134573075)
  ·
    refine ⟨18501137132051853201859613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12334091421367902134573075 18501137132051853201859613)
    ·
      refine ⟨6937926424519444950697355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18501137132051853201859613 6937926424519444950697355)
      ·
        refine ⟨10406889636779167426046033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6937926424519444950697355 10406889636779167426046033)
        ·
          refine ⟨7805167227584375569534525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10406889636779167426046033 7805167227584375569534525)
          ·
            refine ⟨2926937710344140838575447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7805167227584375569534525 2926937710344140838575447)
            ·
              refine ⟨4390406565516211257863171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2926937710344140838575447 4390406565516211257863171)
              ·
                refine ⟨6585609848274316886794757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4390406565516211257863171 6585609848274316886794757)
                ·
                  refine ⟨1234801846551434416274017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6585609848274316886794757 1234801846551434416274017)
                  ·
                    refine ⟨926101384913575812205513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1234801846551434416274017 926101384913575812205513)
                    ·
                      refine ⟨694576038685181859154135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 926101384913575812205513 694576038685181859154135)
                      ·
                        rfl

theorem cell23_1352682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 1, 4, 2, 2].length) (baseStart_1352682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352682 prefixEnd_1352682 := by exact prefixLift 1352682
  have htrace : WordTrace (prefixWord ++ tailWord_1352682) baseStart_1352682 baseEnd_1352682 := by
    simpa [prefixWord, tailWord_1352682, baseEnd_1352682] using wordTrace_append hprefix tailTrace_1352682
  have hstable : (prefixWord ++ tailWord_1352682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352682).length < 2 ^ (prefixWord ++ tailWord_1352682).sum := by decide
  have hdescent : baseEnd_1352682 < baseStart_1352682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352718 : List Nat := [4, 1, 1, 2, 2, 2, 2, 1, 1, 7]
def baseStart_1352718 : Nat := 118140960795 + 1352718 * 2 ^ 59
def prefixEnd_1352718 : Nat := 4983230072969 + 3 ^ 40 * 1352718 * 2
def baseEnd_1352718 : Nat := 231531507996247906101323

theorem tailTrace_1352718 : CollatzResearch.WordTrace tailWord_1352718 prefixEnd_1352718 231531507996247906101323 := by
  unfold tailWord_1352718
  simp only [CollatzResearch.WordTrace]
  refine ⟨6167209839167648335825351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32891785808894124457735205 6167209839167648335825351)
  ·
    refine ⟨9250814758751472503738027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6167209839167648335825351 9250814758751472503738027)
    ·
      refine ⟨13876222138127208755607041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9250814758751472503738027 13876222138127208755607041)
      ·
        refine ⟨10407166603595406566705281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13876222138127208755607041 10407166603595406566705281)
        ·
          refine ⟨7805374952696554925028961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10407166603595406566705281 7805374952696554925028961)
          ·
            refine ⟨5854031214522416193771721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7805374952696554925028961 5854031214522416193771721)
            ·
              refine ⟨4390523410891812145328791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5854031214522416193771721 4390523410891812145328791)
              ·
                refine ⟨6585785116337718217993187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4390523410891812145328791 6585785116337718217993187)
                ·
                  refine ⟨9878677674506577326989781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6585785116337718217993187 9878677674506577326989781)
                  ·
                    refine ⟨231531507996247906101323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9878677674506577326989781 231531507996247906101323)
                    ·
                      rfl

theorem cell23_1352718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_1352718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352718 prefixEnd_1352718 := by exact prefixLift 1352718
  have htrace : WordTrace (prefixWord ++ tailWord_1352718) baseStart_1352718 baseEnd_1352718 := by
    simpa [prefixWord, tailWord_1352718, baseEnd_1352718] using wordTrace_append hprefix tailTrace_1352718
  have hstable : (prefixWord ++ tailWord_1352718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352718).length < 2 ^ (prefixWord ++ tailWord_1352718).sum := by decide
  have hdescent : baseEnd_1352718 < baseStart_1352718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352751 : List Nat := [1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 6]
def baseStart_1352751 : Nat := 118140960795 + 1352751 * 2 ^ 59
def prefixEnd_1352751 : Nat := 4983230072969 + 3 ^ 40 * 1352751 * 2
def baseEnd_1352751 : Nat := 694611468850342089191317

theorem tailTrace_1352751 : CollatzResearch.WordTrace tailWord_1352751 prefixEnd_1352751 694611468850342089191317 := by
  unfold tailWord_1352751
  simp only [CollatzResearch.WordTrace]
  refine ⟨49338882322221633322554107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32892588214814422215036071 49338882322221633322554107)
  ·
    refine ⟨74008323483332449983831161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49338882322221633322554107 74008323483332449983831161)
    ·
      refine ⟨55506242612499337487873371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74008323483332449983831161 55506242612499337487873371)
      ·
        refine ⟨83259363918749006231810057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55506242612499337487873371 83259363918749006231810057)
        ·
          refine ⟨62444522939061754673857543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83259363918749006231810057 62444522939061754673857543)
          ·
            refine ⟨93666784408592632010786315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62444522939061754673857543 93666784408592632010786315)
            ·
              refine ⟨140500176612888948016179473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93666784408592632010786315 140500176612888948016179473)
              ·
                refine ⟨105375132459666711012134605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140500176612888948016179473 105375132459666711012134605)
                ·
                  refine ⟨39515674672375016629550477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105375132459666711012134605 39515674672375016629550477)
                  ·
                    refine ⟨14818378002140631236081429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39515674672375016629550477 14818378002140631236081429)
                    ·
                      refine ⟨694611468850342089191317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14818378002140631236081429 694611468850342089191317)
                      ·
                        rfl

theorem cell23_1352751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_1352751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352751 prefixEnd_1352751 := by exact prefixLift 1352751
  have htrace : WordTrace (prefixWord ++ tailWord_1352751) baseStart_1352751 baseEnd_1352751 := by
    simpa [prefixWord, tailWord_1352751, baseEnd_1352751] using wordTrace_append hprefix tailTrace_1352751
  have hstable : (prefixWord ++ tailWord_1352751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352751).length < 2 ^ (prefixWord ++ tailWord_1352751).sum := by decide
  have hdescent : baseEnd_1352751 < baseStart_1352751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352775 : List Nat := [1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 3]
def baseStart_1352775 : Nat := 118140960795 + 1352775 * 2 ^ 59
def prefixEnd_1352775 : Nat := 4983230072969 + 3 ^ 40 * 1352775 * 2
def baseEnd_1352775 : Nat := 694623792386049995291207

theorem tailTrace_1352775 : CollatzResearch.WordTrace tailWord_1352775 prefixEnd_1352775 694623792386049995291207 := by
  unfold tailWord_1352775
  simp only [CollatzResearch.WordTrace]
  refine ⟨49339757674134685421427779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32893171782756456947618519 49339757674134685421427779)
  ·
    refine ⟨74009636511202028132141669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49339757674134685421427779 74009636511202028132141669)
    ·
      refine ⟨13876806845850380274776563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74009636511202028132141669 13876806845850380274776563)
      ·
        refine ⟨20815210268775570412164845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13876806845850380274776563 20815210268775570412164845)
        ·
          refine ⟨7805703850790838904561817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20815210268775570412164845 7805703850790838904561817)
          ·
            refine ⟨5854277888093129178421363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7805703850790838904561817 5854277888093129178421363)
            ·
              refine ⟨8781416832139693767632045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5854277888093129178421363 8781416832139693767632045)
              ·
                refine ⟨3293031312052385162862017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8781416832139693767632045 3293031312052385162862017)
                ·
                  refine ⟨2469773484039288872146513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3293031312052385162862017 2469773484039288872146513)
                  ·
                    refine ⟨1852330113029466654109885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2469773484039288872146513 1852330113029466654109885)
                    ·
                      refine ⟨694623792386049995291207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1852330113029466654109885 694623792386049995291207)
                      ·
                        rfl

theorem cell23_1352775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_1352775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352775 prefixEnd_1352775 := by exact prefixLift 1352775
  have htrace : WordTrace (prefixWord ++ tailWord_1352775) baseStart_1352775 baseEnd_1352775 := by
    simpa [prefixWord, tailWord_1352775, baseEnd_1352775] using wordTrace_append hprefix tailTrace_1352775
  have hstable : (prefixWord ++ tailWord_1352775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352775).length < 2 ^ (prefixWord ++ tailWord_1352775).sum := by decide
  have hdescent : baseEnd_1352775 < baseStart_1352775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352782 : List Nat := [4, 1, 1, 1, 1, 3, 2, 5, 1, 4]
def baseStart_1352782 : Nat := 118140960795 + 1352782 * 2 ^ 59
def prefixEnd_1352782 : Nat := 4983230072969 + 3 ^ 40 * 1352782 * 2
def baseEnd_1352782 : Nat := 231542462250210489301225

theorem tailTrace_1352782 : CollatzResearch.WordTrace tailWord_1352782 prefixEnd_1352782 231542462250210489301225 := by
  unfold tailWord_1352782
  simp only [CollatzResearch.WordTrace]
  refine ⟨6167501623138665702116575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32893341990072883744621733 6167501623138665702116575)
  ·
    refine ⟨9251252434707998553174863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6167501623138665702116575 9251252434707998553174863)
    ·
      refine ⟨13876878652061997829762295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9251252434707998553174863 13876878652061997829762295)
      ·
        refine ⟨20815317978092996744643443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13876878652061997829762295 20815317978092996744643443)
        ·
          refine ⟨31222976967139495116965165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20815317978092996744643443 31222976967139495116965165)
          ·
            refine ⟨11708616362677310668861937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31222976967139495116965165 11708616362677310668861937)
            ·
              refine ⟨8781462272007983001646453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11708616362677310668861937 8781462272007983001646453)
              ·
                refine ⟨823262088000748406404355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8781462272007983001646453 823262088000748406404355)
                ·
                  refine ⟨1234893132001122609606533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 823262088000748406404355 1234893132001122609606533)
                  ·
                    refine ⟨231542462250210489301225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1234893132001122609606533 231542462250210489301225)
                    ·
                      rfl

theorem cell23_1352782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_1352782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352782 prefixEnd_1352782 := by exact prefixLift 1352782
  have htrace : WordTrace (prefixWord ++ tailWord_1352782) baseStart_1352782 baseEnd_1352782 := by
    simpa [prefixWord, tailWord_1352782, baseEnd_1352782] using wordTrace_append hprefix tailTrace_1352782
  have hstable : (prefixWord ++ tailWord_1352782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352782).length < 2 ^ (prefixWord ++ tailWord_1352782).sum := by decide
  have hdescent : baseEnd_1352782 < baseStart_1352782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352815 : List Nat := [1, 1, 2, 1, 3, 3, 2, 2, 1, 5, 2]
def baseStart_1352815 : Nat := 118140960795 + 1352815 * 2 ^ 59
def prefixEnd_1352815 : Nat := 4983230072969 + 3 ^ 40 * 1352815 * 2
def baseEnd_1352815 : Nat := 694644331612229838791023

theorem tailTrace_1352815 : CollatzResearch.WordTrace tailWord_1352815 prefixEnd_1352815 694644331612229838791023 := by
  unfold tailWord_1352815
  simp only [CollatzResearch.WordTrace]
  refine ⟨49341216593989772252883899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32894144395993181501922599 49341216593989772252883899)
  ·
    refine ⟨74011824890984658379325849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49341216593989772252883899 74011824890984658379325849)
    ·
      refine ⟨55508868668238493784494387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74011824890984658379325849 55508868668238493784494387)
      ·
        refine ⟨83263303002357740676741581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55508868668238493784494387 83263303002357740676741581)
        ·
          refine ⟨31223738625884152753778093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83263303002357740676741581 31223738625884152753778093)
          ·
            refine ⟨11708901984706557282666785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31223738625884152753778093 11708901984706557282666785)
            ·
              refine ⟨8781676488529917962000089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11708901984706557282666785 8781676488529917962000089)
              ·
                refine ⟨6586257366397438471500067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8781676488529917962000089 6586257366397438471500067)
                ·
                  refine ⟨9879386049596157707250101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6586257366397438471500067 9879386049596157707250101)
                  ·
                    refine ⟨926192442149639785054697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9879386049596157707250101 926192442149639785054697)
                    ·
                      refine ⟨694644331612229838791023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 926192442149639785054697 694644331612229838791023)
                      ·
                        rfl

theorem cell23_1352815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 2, 1, 5, 2].length) (baseStart_1352815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352815 prefixEnd_1352815 := by exact prefixLift 1352815
  have htrace : WordTrace (prefixWord ++ tailWord_1352815) baseStart_1352815 baseEnd_1352815 := by
    simpa [prefixWord, tailWord_1352815, baseEnd_1352815] using wordTrace_append hprefix tailTrace_1352815
  have hstable : (prefixWord ++ tailWord_1352815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352815).length < 2 ^ (prefixWord ++ tailWord_1352815).sum := by decide
  have hdescent : baseEnd_1352815 < baseStart_1352815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352818 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 2, 1, 7]
def baseStart_1352818 : Nat := 118140960795 + 1352818 * 2 ^ 59
def prefixEnd_1352818 : Nat := 4983230072969 + 3 ^ 40 * 1352818 * 2
def baseEnd_1352818 : Nat := 694645872054193327053509

theorem tailTrace_1352818 : CollatzResearch.WordTrace tailWord_1352818 prefixEnd_1352818 694645872054193327053509 := by
  unfold tailWord_1352818
  simp only [CollatzResearch.WordTrace]
  refine ⟨12335331503244725941310777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32894217341985935843495405 12335331503244725941310777)
  ·
    refine ⟨9251498627433544455983083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12335331503244725941310777 9251498627433544455983083)
    ·
      refine ⟨13877247941150316683974625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9251498627433544455983083 13877247941150316683974625)
      ·
        refine ⟨10407935955862737512980969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13877247941150316683974625 10407935955862737512980969)
        ·
          refine ⟨7805951966897053134735727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10407935955862737512980969 7805951966897053134735727)
          ·
            refine ⟨11708927950345579702103591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7805951966897053134735727 11708927950345579702103591)
            ·
              refine ⟨17563391925518369553155387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11708927950345579702103591 17563391925518369553155387)
              ·
                refine ⟨26345087888277554329733081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17563391925518369553155387 26345087888277554329733081)
                ·
                  refine ⟨19758815916208165747299811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26345087888277554329733081 19758815916208165747299811)
                  ·
                    refine ⟨29638223874312248620949717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19758815916208165747299811 29638223874312248620949717)
                    ·
                      refine ⟨694645872054193327053509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29638223874312248620949717 694645872054193327053509)
                      ·
                        rfl

theorem cell23_1352818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 2, 1, 7].length) (baseStart_1352818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352818 prefixEnd_1352818 := by exact prefixLift 1352818
  have htrace : WordTrace (prefixWord ++ tailWord_1352818) baseStart_1352818 baseEnd_1352818 := by
    simpa [prefixWord, tailWord_1352818, baseEnd_1352818] using wordTrace_append hprefix tailTrace_1352818
  have hstable : (prefixWord ++ tailWord_1352818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352818).length < 2 ^ (prefixWord ++ tailWord_1352818).sum := by decide
  have hdescent : baseEnd_1352818 < baseStart_1352818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352832 : List Nat := [2, 1, 1, 2, 1, 3, 5, 1, 2, 3, 2]
def baseStart_1352832 : Nat := 118140960795 + 1352832 * 2 ^ 59
def prefixEnd_1352832 : Nat := 4983230072969 + 3 ^ 40 * 1352832 * 2
def baseEnd_1352832 : Nat := 694653060783356272278445

theorem tailTrace_1352832 : CollatzResearch.WordTrace tailWord_1352832 prefixEnd_1352832 694653060783356272278445 := by
  unfold tailWord_1352832
  simp only [CollatzResearch.WordTrace]
  refine ⟨24670918317464092078126375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32894557756618789437501833 24670918317464092078126375)
  ·
    refine ⟨37006377476196138117189563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24670918317464092078126375 37006377476196138117189563)
    ·
      refine ⟨55509566214294207175784345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37006377476196138117189563 55509566214294207175784345)
      ·
        refine ⟨41632174660720655381838259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55509566214294207175784345 41632174660720655381838259)
        ·
          refine ⟨62448261991080983072757389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41632174660720655381838259 62448261991080983072757389)
          ·
            refine ⟨23418098246655368652284021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62448261991080983072757389 23418098246655368652284021)
            ·
              refine ⟨2195446710623940811151627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 23418098246655368652284021 2195446710623940811151627)
              ·
                refine ⟨3293170065935911216727441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2195446710623940811151627 3293170065935911216727441)
                ·
                  refine ⟨2469877549451933412545581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3293170065935911216727441 2469877549451933412545581)
                  ·
                    refine ⟨926204081044475029704593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2469877549451933412545581 926204081044475029704593)
                    ·
                      refine ⟨694653060783356272278445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 926204081044475029704593 694653060783356272278445)
                      ·
                        rfl

theorem cell23_1352832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 2, 3, 2].length) (baseStart_1352832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352832 prefixEnd_1352832 := by exact prefixLift 1352832
  have htrace : WordTrace (prefixWord ++ tailWord_1352832) baseStart_1352832 baseEnd_1352832 := by
    simpa [prefixWord, tailWord_1352832, baseEnd_1352832] using wordTrace_append hprefix tailTrace_1352832
  have hstable : (prefixWord ++ tailWord_1352832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352832).length < 2 ^ (prefixWord ++ tailWord_1352832).sum := by decide
  have hdescent : baseEnd_1352832 < baseStart_1352832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352865 : List Nat := [1, 2, 3, 3, 1, 1, 3, 2, 1, 1, 5]
def baseStart_1352865 : Nat := 118140960795 + 1352865 * 2 ^ 59
def prefixEnd_1352865 : Nat := 4983230072969 + 3 ^ 40 * 1352865 * 2
def baseEnd_1352865 : Nat := 694670005644954643165793

theorem tailTrace_1352865 : CollatzResearch.WordTrace tailWord_1352865 prefixEnd_1352865 694670005644954643165793 := by
  unfold tailWord_1352865
  simp only [CollatzResearch.WordTrace]
  refine ⟨49343040243808630792204049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32895360162539087194802699 49343040243808630792204049)
  ·
    refine ⟨37007280182856473094153037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49343040243808630792204049 37007280182856473094153037)
    ·
      refine ⟨13877730068571177410307389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37007280182856473094153037 13877730068571177410307389)
      ·
        refine ⟨5204148775714191528865271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13877730068571177410307389 5204148775714191528865271)
        ·
          refine ⟨7806223163571287293297907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5204148775714191528865271 7806223163571287293297907)
          ·
            refine ⟨11709334745356930939946861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7806223163571287293297907 11709334745356930939946861)
            ·
              refine ⟨4391000529508849102480073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11709334745356930939946861 4391000529508849102480073)
              ·
                refine ⟨3293250397131636826860055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4391000529508849102480073 3293250397131636826860055)
                ·
                  refine ⟨4939875595697455240290083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3293250397131636826860055 4939875595697455240290083)
                  ·
                    refine ⟨7409813393546182860435125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4939875595697455240290083 7409813393546182860435125)
                    ·
                      refine ⟨694670005644954643165793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7409813393546182860435125 694670005644954643165793)
                      ·
                        rfl

theorem cell23_1352865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_1352865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352865 prefixEnd_1352865 := by exact prefixLift 1352865
  have htrace : WordTrace (prefixWord ++ tailWord_1352865) baseStart_1352865 baseEnd_1352865 := by
    simpa [prefixWord, tailWord_1352865, baseEnd_1352865] using wordTrace_append hprefix tailTrace_1352865
  have hstable : (prefixWord ++ tailWord_1352865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352865).length < 2 ^ (prefixWord ++ tailWord_1352865).sum := by decide
  have hdescent : baseEnd_1352865 < baseStart_1352865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352882 : List Nat := [3, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3]
def baseStart_1352882 : Nat := 118140960795 + 1352882 * 2 ^ 59
def prefixEnd_1352882 : Nat := 4983230072969 + 3 ^ 40 * 1352882 * 2
def baseEnd_1352882 : Nat := 694678734816081076653215

theorem tailTrace_1352882 : CollatzResearch.WordTrace tailWord_1352882 prefixEnd_1352882 694678734816081076653215 := by
  unfold tailWord_1352882
  simp only [CollatzResearch.WordTrace]
  refine ⟨12335915071186760673893225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32895773523164695130381933 12335915071186760673893225)
  ·
    refine ⟨9251936303390070505419919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12335915071186760673893225 9251936303390070505419919)
    ·
      refine ⟨13877904455085105758129879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9251936303390070505419919 13877904455085105758129879)
      ·
        refine ⟨20816856682627658637194819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13877904455085105758129879 20816856682627658637194819)
        ·
          refine ⟨31225285023941487955792229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20816856682627658637194819 31225285023941487955792229)
          ·
            refine ⟨5854740941989028991711043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31225285023941487955792229 5854740941989028991711043)
            ·
              refine ⟨8782111412983543487566565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5854740941989028991711043 8782111412983543487566565)
              ·
                refine ⟨1646645889934414403918731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8782111412983543487566565 1646645889934414403918731)
                ·
                  refine ⟨2469968834901621605878097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1646645889934414403918731 2469968834901621605878097)
                  ·
                    refine ⟨1852476626176216204408573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2469968834901621605878097 1852476626176216204408573)
                    ·
                      refine ⟨694678734816081076653215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1852476626176216204408573 694678734816081076653215)
                      ·
                        rfl

theorem cell23_1352882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 1, 2, 3].length) (baseStart_1352882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352882 prefixEnd_1352882 := by exact prefixLift 1352882
  have htrace : WordTrace (prefixWord ++ tailWord_1352882) baseStart_1352882 baseEnd_1352882 := by
    simpa [prefixWord, tailWord_1352882, baseEnd_1352882] using wordTrace_append hprefix tailTrace_1352882
  have hstable : (prefixWord ++ tailWord_1352882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352882).length < 2 ^ (prefixWord ++ tailWord_1352882).sum := by decide
  have hdescent : baseEnd_1352882 < baseStart_1352882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352895 : List Nat := [1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 3]
def baseStart_1352895 : Nat := 118140960795 + 1352895 * 2 ^ 59
def prefixEnd_1352895 : Nat := 4983230072969 + 3 ^ 40 * 1352895 * 2
def baseEnd_1352895 : Nat := 694685410064589525790655

theorem tailTrace_1352895 : CollatzResearch.WordTrace tailWord_1352895 prefixEnd_1352895 694685410064589525790655 := by
  unfold tailWord_1352895
  simp only [CollatzResearch.WordTrace]
  refine ⟨49344134433699945915796139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32896089622466630610530759 49344134433699945915796139)
  ·
    refine ⟨74016201650549918873694209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49344134433699945915796139 74016201650549918873694209)
    ·
      refine ⟨55512151237912439155270657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74016201650549918873694209 55512151237912439155270657)
      ·
        refine ⟨41634113428434329366452993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55512151237912439155270657 41634113428434329366452993)
        ·
          refine ⟨31225585071325747024839745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41634113428434329366452993 31225585071325747024839745)
          ·
            refine ⟨23419188803494310268629809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31225585071325747024839745 23419188803494310268629809)
            ·
              refine ⟨17564391602620732701472357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23419188803494310268629809 17564391602620732701472357)
              ·
                refine ⟨3293323425491387381526067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17564391602620732701472357 3293323425491387381526067)
                ·
                  refine ⟨4939985138237081072289101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3293323425491387381526067 4939985138237081072289101)
                  ·
                    refine ⟨1852494426838905402108413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4939985138237081072289101 1852494426838905402108413)
                    ·
                      refine ⟨694685410064589525790655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1852494426838905402108413 694685410064589525790655)
                      ·
                        rfl

theorem cell23_1352895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 3].length) (baseStart_1352895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352895 prefixEnd_1352895 := by exact prefixLift 1352895
  have htrace : WordTrace (prefixWord ++ tailWord_1352895) baseStart_1352895 baseEnd_1352895 := by
    simpa [prefixWord, tailWord_1352895, baseEnd_1352895] using wordTrace_append hprefix tailTrace_1352895
  have hstable : (prefixWord ++ tailWord_1352895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352895).length < 2 ^ (prefixWord ++ tailWord_1352895).sum := by decide
  have hdescent : baseEnd_1352895 < baseStart_1352895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352905 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 1, 9, 2]
def baseStart_1352905 : Nat := 118140960795 + 1352905 * 2 ^ 59
def prefixEnd_1352905 : Nat := 4983230072969 + 3 ^ 40 * 1352905 * 2
def baseEnd_1352905 : Nat := 694690544871134486665609

theorem tailTrace_1352905 : CollatzResearch.WordTrace tailWord_1352905 prefixEnd_1352905 694690544871134486665609 := by
  unfold tailWord_1352905
  simp only [CollatzResearch.WordTrace]
  refine ⟨49344499163663717623660169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32896332775775811749106779 49344499163663717623660169)
  ·
    refine ⟨37008374372747788217745127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49344499163663717623660169 37008374372747788217745127)
    ·
      refine ⟨55512561559121682326617691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37008374372747788217745127 55512561559121682326617691)
      ·
        refine ⟨83268842338682523489926537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55512561559121682326617691 83268842338682523489926537)
        ·
          refine ⟨62451631754011892617444903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83268842338682523489926537 62451631754011892617444903)
          ·
            refine ⟨93677447631017838926167355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62451631754011892617444903 93677447631017838926167355)
            ·
              refine ⟨140516171446526758389251033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93677447631017838926167355 140516171446526758389251033)
              ·
                refine ⟨105387128584895068791938275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140516171446526758389251033 105387128584895068791938275)
                ·
                  refine ⟨158080692877342603187907413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105387128584895068791938275 158080692877342603187907413)
                  ·
                    refine ⟨926254059828179315554145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 158080692877342603187907413 926254059828179315554145)
                    ·
                      refine ⟨694690544871134486665609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 926254059828179315554145 694690544871134486665609)
                      ·
                        rfl

theorem cell23_1352905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 9, 2].length) (baseStart_1352905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352905 prefixEnd_1352905 := by exact prefixLift 1352905
  have htrace : WordTrace (prefixWord ++ tailWord_1352905) baseStart_1352905 baseEnd_1352905 := by
    simpa [prefixWord, tailWord_1352905, baseEnd_1352905] using wordTrace_append hprefix tailTrace_1352905
  have hstable : (prefixWord ++ tailWord_1352905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352905).length < 2 ^ (prefixWord ++ tailWord_1352905).sum := by decide
  have hdescent : baseEnd_1352905 < baseStart_1352905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352922 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2]
def baseStart_1352922 : Nat := 118140960795 + 1352922 * 2 ^ 59
def prefixEnd_1352922 : Nat := 4983230072969 + 3 ^ 40 * 1352922 * 2
def baseEnd_1352922 : Nat := 694699274042260920153031

theorem tailTrace_1352922 : CollatzResearch.WordTrace tailWord_1352922 prefixEnd_1352922 694699274042260920153031 := by
  unfold tailWord_1352922
  simp only [CollatzResearch.WordTrace]
  refine ⟨12336279801150532381757255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32896746136401419684686013 12336279801150532381757255)
  ·
    refine ⟨18504419701725798572635883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12336279801150532381757255 18504419701725798572635883)
    ·
      refine ⟨27756629552588697858953825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18504419701725798572635883 27756629552588697858953825)
      ·
        refine ⟨20817472164441523394215369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27756629552588697858953825 20817472164441523394215369)
        ·
          refine ⟨15613104123331142545661527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20817472164441523394215369 15613104123331142545661527)
          ·
            refine ⟨23419656184996713818492291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15613104123331142545661527 23419656184996713818492291)
            ·
              refine ⟨35129484277495070727738437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23419656184996713818492291 35129484277495070727738437)
              ·
                refine ⟨6586778302030325761450957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35129484277495070727738437 6586778302030325761450957)
                ·
                  refine ⟨2470041863261372160544109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6586778302030325761450957 2470041863261372160544109)
                  ·
                    refine ⟨926265698723014560204041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2470041863261372160544109 926265698723014560204041)
                    ·
                      refine ⟨694699274042260920153031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 926265698723014560204041 694699274042260920153031)
                      ·
                        rfl

theorem cell23_1352922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 2].length) (baseStart_1352922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352922 prefixEnd_1352922 := by exact prefixLift 1352922
  have htrace : WordTrace (prefixWord ++ tailWord_1352922) baseStart_1352922 baseEnd_1352922 := by
    simpa [prefixWord, tailWord_1352922, baseEnd_1352922] using wordTrace_append hprefix tailTrace_1352922
  have hstable : (prefixWord ++ tailWord_1352922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352922).length < 2 ^ (prefixWord ++ tailWord_1352922).sum := by decide
  have hdescent : baseEnd_1352922 < baseStart_1352922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352929 : List Nat := [1, 2, 3, 1, 3, 3, 1, 3, 2, 1, 3]
def baseStart_1352929 : Nat := 118140960795 + 1352929 * 2 ^ 59
def prefixEnd_1352929 : Nat := 4983230072969 + 3 ^ 40 * 1352929 * 2
def baseEnd_1352929 : Nat := 694702868406842392765499

theorem tailTrace_1352929 : CollatzResearch.WordTrace tailWord_1352929 prefixEnd_1352929 694702868406842392765499 := by
  unfold tailWord_1352929
  simp only [CollatzResearch.WordTrace]
  refine ⟨49345374515576769722533841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32896916343717846481689227 49345374515576769722533841)
  ·
    refine ⟨37009030886682577291900381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49345374515576769722533841 37009030886682577291900381)
    ·
      refine ⟨13878386582505966484462643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37009030886682577291900381 13878386582505966484462643)
      ·
        refine ⟨20817579873758949726693965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13878386582505966484462643 20817579873758949726693965)
        ·
          refine ⟨7806592452659606147510237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20817579873758949726693965 7806592452659606147510237)
          ·
            refine ⟨2927472169747352305316339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7806592452659606147510237 2927472169747352305316339)
            ·
              refine ⟨4391208254621028457974509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2927472169747352305316339 4391208254621028457974509)
              ·
                refine ⟨1646703095482885671740441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4391208254621028457974509 1646703095482885671740441)
                ·
                  refine ⟨1235027321612164253805331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1646703095482885671740441 1235027321612164253805331)
                  ·
                    refine ⟨1852540982418246380707997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1235027321612164253805331 1852540982418246380707997)
                    ·
                      refine ⟨694702868406842392765499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1852540982418246380707997 694702868406842392765499)
                      ·
                        rfl

theorem cell23_1352929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 1, 3].length) (baseStart_1352929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352929 prefixEnd_1352929 := by exact prefixLift 1352929
  have htrace : WordTrace (prefixWord ++ tailWord_1352929) baseStart_1352929 baseEnd_1352929 := by
    simpa [prefixWord, tailWord_1352929, baseEnd_1352929] using wordTrace_append hprefix tailTrace_1352929
  have hstable : (prefixWord ++ tailWord_1352929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352929).length < 2 ^ (prefixWord ++ tailWord_1352929).sum := by decide
  have hdescent : baseEnd_1352929 < baseStart_1352929 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352939 : List Nat := [1, 1, 1, 1, 2, 6, 3, 2, 1, 3, 2]
def baseStart_1352939 : Nat := 118140960795 + 1352939 * 2 ^ 59
def prefixEnd_1352939 : Nat := 4983230072969 + 3 ^ 40 * 1352939 * 2
def baseEnd_1352939 : Nat := 694708003213387353640453

theorem tailTrace_1352939 : CollatzResearch.WordTrace tailWord_1352939 prefixEnd_1352939 694708003213387353640453 := by
  unfold tailWord_1352939
  simp only [CollatzResearch.WordTrace]
  refine ⟨49345739245540541430397871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32897159497027027620265247 49345739245540541430397871)
  ·
    refine ⟨74018608868310812145596807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49345739245540541430397871 74018608868310812145596807)
    ·
      refine ⟨111027913302466218218395211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74018608868310812145596807 111027913302466218218395211)
      ·
        refine ⟨166541869953699327327592817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111027913302466218218395211 166541869953699327327592817)
        ·
          refine ⟨124906402465274495495694613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 166541869953699327327592817 124906402465274495495694613)
          ·
            refine ⟨5854987615559741976360685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 124906402465274495495694613 5854987615559741976360685)
            ·
              refine ⟨2195620355834903241135257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5854987615559741976360685 2195620355834903241135257)
              ·
                refine ⟨1646715266876177430851443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2195620355834903241135257 1646715266876177430851443)
                ·
                  refine ⟨2470072900314266146277165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1646715266876177430851443 2470072900314266146277165)
                  ·
                    refine ⟨926277337617849804853937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2470072900314266146277165 926277337617849804853937)
                    ·
                      refine ⟨694708003213387353640453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 926277337617849804853937 694708003213387353640453)
                      ·
                        rfl

theorem cell23_1352939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 1, 3, 2].length) (baseStart_1352939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352939 prefixEnd_1352939 := by exact prefixLift 1352939
  have htrace : WordTrace (prefixWord ++ tailWord_1352939) baseStart_1352939 baseEnd_1352939 := by
    simpa [prefixWord, tailWord_1352939, baseEnd_1352939] using wordTrace_append hprefix tailTrace_1352939
  have hstable : (prefixWord ++ tailWord_1352939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352939).length < 2 ^ (prefixWord ++ tailWord_1352939).sum := by decide
  have hdescent : baseEnd_1352939 < baseStart_1352939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352965 : List Nat := [1, 3, 1, 1, 2, 1, 4, 2, 2, 2, 4]
def baseStart_1352965 : Nat := 118140960795 + 1352965 * 2 ^ 59
def prefixEnd_1352965 : Nat := 4983230072969 + 3 ^ 40 * 1352965 * 2
def baseEnd_1352965 : Nat := 694721353710404251915333

theorem tailTrace_1352965 : CollatzResearch.WordTrace tailWord_1352965 prefixEnd_1352965 694721353710404251915333 := by
  unfold tailWord_1352965
  simp only [CollatzResearch.WordTrace]
  refine ⟨49346687543446347870844349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32897791695630898580562899 49346687543446347870844349)
  ·
    refine ⟨18505007828792380451566631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49346687543446347870844349 18505007828792380451566631)
    ·
      refine ⟨27757511743188570677349947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18505007828792380451566631 27757511743188570677349947)
      ·
        refine ⟨41636267614782856016024921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27757511743188570677349947 41636267614782856016024921)
        ·
          refine ⟨31227200711087142012018691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41636267614782856016024921 31227200711087142012018691)
          ·
            refine ⟨46840801066630713018028037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31227200711087142012018691 46840801066630713018028037)
            ·
              refine ⟨8782650199993258690880257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46840801066630713018028037 8782650199993258690880257)
              ·
                refine ⟨6586987649994944018160193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8782650199993258690880257 6586987649994944018160193)
                ·
                  refine ⟨4940240737496208013620145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6586987649994944018160193 4940240737496208013620145)
                  ·
                    refine ⟨3705180553122156010215109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4940240737496208013620145 3705180553122156010215109)
                    ·
                      refine ⟨694721353710404251915333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3705180553122156010215109 694721353710404251915333)
                      ·
                        rfl

theorem cell23_1352965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 4, 2, 2, 2, 4].length) (baseStart_1352965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352965 prefixEnd_1352965 := by exact prefixLift 1352965
  have htrace : WordTrace (prefixWord ++ tailWord_1352965) baseStart_1352965 baseEnd_1352965 := by
    simpa [prefixWord, tailWord_1352965, baseEnd_1352965] using wordTrace_append hprefix tailTrace_1352965
  have hstable : (prefixWord ++ tailWord_1352965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352965).length < 2 ^ (prefixWord ++ tailWord_1352965).sum := by decide
  have hdescent : baseEnd_1352965 < baseStart_1352965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352986 : List Nat := [3, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2]
def baseStart_1352986 : Nat := 118140960795 + 1352986 * 2 ^ 59
def prefixEnd_1352986 : Nat := 4983230072969 + 3 ^ 40 * 1352986 * 2
def baseEnd_1352986 : Nat := 694732136804148669752737

theorem tailTrace_1352986 : CollatzResearch.WordTrace tailWord_1352986 prefixEnd_1352986 694732136804148669752737 := by
  unfold tailWord_1352986
  simp only [CollatzResearch.WordTrace]
  refine ⟨12336863369092567114339703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32898302317580178971572541 12336863369092567114339703)
  ·
    refine ⟨18505295053638850671509555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12336863369092567114339703 18505295053638850671509555)
    ·
      refine ⟨27757942580458276007264333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18505295053638850671509555 27757942580458276007264333)
      ·
        refine ⟨10409228467671853502724125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27757942580458276007264333 10409228467671853502724125)
        ·
          refine ⟨3903460675376945063521547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10409228467671853502724125 3903460675376945063521547)
          ·
            refine ⟨5855191013065417595282321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3903460675376945063521547 5855191013065417595282321)
            ·
              refine ⟨4391393259799063196461741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5855191013065417595282321 4391393259799063196461741)
              ·
                refine ⟨1646772472424648698673153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4391393259799063196461741 1646772472424648698673153)
                ·
                  refine ⟨1235079354318486524004865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1646772472424648698673153 1235079354318486524004865)
                  ·
                    refine ⟨926309515738864893003649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1235079354318486524004865 926309515738864893003649)
                    ·
                      refine ⟨694732136804148669752737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 926309515738864893003649 694732136804148669752737)
                      ·
                        rfl

theorem cell23_1352986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 2, 3, 2, 2, 2].length) (baseStart_1352986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352986 prefixEnd_1352986 := by exact prefixLift 1352986
  have htrace : WordTrace (prefixWord ++ tailWord_1352986) baseStart_1352986 baseEnd_1352986 := by
    simpa [prefixWord, tailWord_1352986, baseEnd_1352986] using wordTrace_append hprefix tailTrace_1352986
  have hstable : (prefixWord ++ tailWord_1352986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352986).length < 2 ^ (prefixWord ++ tailWord_1352986).sum := by decide
  have hdescent : baseEnd_1352986 < baseStart_1352986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1352992 : List Nat := [2, 1, 1, 5, 3, 1, 1, 2, 7]
def baseStart_1352992 : Nat := 118140960795 + 1352992 * 2 ^ 59
def prefixEnd_1352992 : Nat := 4983230072969 + 3 ^ 40 * 1352992 * 2
def baseEnd_1352992 : Nat := 77192801965341738475301

theorem tailTrace_1352992 : CollatzResearch.WordTrace tailWord_1352992 prefixEnd_1352992 77192801965341738475301 := by
  unfold tailWord_1352992
  simp only [CollatzResearch.WordTrace]
  refine ⟨24673836157174265741038615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32898448209565687654718153 24673836157174265741038615)
  ·
    refine ⟨37010754235761398611557923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24673836157174265741038615 37010754235761398611557923)
    ·
      refine ⟨55516131353642097917336885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37010754235761398611557923 55516131353642097917336885)
      ·
        refine ⟨5204637314403946679750333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 55516131353642097917336885 5204637314403946679750333)
        ·
          refine ⟨1951738992901480004906375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5204637314403946679750333 1951738992901480004906375)
          ·
            refine ⟨2927608489352220007359563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1951738992901480004906375 2927608489352220007359563)
            ·
              refine ⟨4391412734028330011039345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2927608489352220007359563 4391412734028330011039345)
              ·
                refine ⟨3293559550521247508279509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4391412734028330011039345 3293559550521247508279509)
                ·
                  refine ⟨77192801965341738475301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3293559550521247508279509 77192801965341738475301)
                  ·
                    rfl

theorem cell23_1352992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 2, 7].length) (baseStart_1352992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1352992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1352992 prefixEnd_1352992 := by exact prefixLift 1352992
  have htrace : WordTrace (prefixWord ++ tailWord_1352992) baseStart_1352992 baseEnd_1352992 := by
    simpa [prefixWord, tailWord_1352992, baseEnd_1352992] using wordTrace_append hprefix tailTrace_1352992
  have hstable : (prefixWord ++ tailWord_1352992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1352992).length < 2 ^ (prefixWord ++ tailWord_1352992).sum := by decide
  have hdescent : baseEnd_1352992 < baseStart_1352992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1352992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353009 : List Nat := [1, 2, 2, 3, 3, 2, 2, 3, 5]
def baseStart_1353009 : Nat := 118140960795 + 1353009 * 2 ^ 59
def prefixEnd_1353009 : Nat := 4983230072969 + 3 ^ 40 * 1353009 * 2
def baseEnd_1353009 : Nat := 77193771873244675529459

theorem tailTrace_1353009 : CollatzResearch.WordTrace tailWord_1353009 prefixEnd_1353009 77193771873244675529459 := by
  unfold tailWord_1353009
  simp only [CollatzResearch.WordTrace]
  refine ⟨49348292355286943385446081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32898861570191295590297387 49348292355286943385446081)
  ·
    refine ⟨37011219266465207539084561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49348292355286943385446081 37011219266465207539084561)
    ·
      refine ⟨27758414449848905654313421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37011219266465207539084561 27758414449848905654313421)
      ·
        refine ⟨10409405418693339620367533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27758414449848905654313421 10409405418693339620367533)
        ·
          refine ⟨3903527032010002357637825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10409405418693339620367533 3903527032010002357637825)
          ·
            refine ⟨2927645274007501768228369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3903527032010002357637825 2927645274007501768228369)
            ·
              refine ⟨2195733955505626326171277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2927645274007501768228369 2195733955505626326171277)
              ·
                refine ⟨823400233314609872314229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2195733955505626326171277 823400233314609872314229)
                ·
                  refine ⟨77193771873244675529459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 823400233314609872314229 77193771873244675529459)
                  ·
                    rfl

theorem cell23_1353009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 2, 3, 5].length) (baseStart_1353009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353009 prefixEnd_1353009 := by exact prefixLift 1353009
  have htrace : WordTrace (prefixWord ++ tailWord_1353009) baseStart_1353009 baseEnd_1353009 := by
    simpa [prefixWord, tailWord_1353009, baseEnd_1353009] using wordTrace_append hprefix tailTrace_1353009
  have hstable : (prefixWord ++ tailWord_1353009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353009).length < 2 ^ (prefixWord ++ tailWord_1353009).sum := by decide
  have hdescent : baseEnd_1353009 < baseStart_1353009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353022 : List Nat := [4, 2, 1, 2, 1, 1, 2, 1, 4, 5]
def baseStart_1353022 : Nat := 118140960795 + 1353022 * 2 ^ 59
def prefixEnd_1353022 : Nat := 4983230072969 + 3 ^ 40 * 1353022 * 2
def baseEnd_1353022 : Nat := 231583540702570176300857

theorem tailTrace_1353022 : CollatzResearch.WordTrace tailWord_1353022 prefixEnd_1353022 231583540702570176300857 := by
  unfold tailWord_1353022
  simp only [CollatzResearch.WordTrace]
  refine ⟨6168595813029980825708665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32899177669493231070446213 6168595813029980825708665)
  ·
    refine ⟨4626446859772485619281499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6168595813029980825708665 4626446859772485619281499)
    ·
      refine ⟨6939670289658728428922249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4626446859772485619281499 6939670289658728428922249)
      ·
        refine ⟨5204752717244046321691687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6939670289658728428922249 5204752717244046321691687)
        ·
          refine ⟨7807129075866069482537531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5204752717244046321691687 7807129075866069482537531)
          ·
            refine ⟨11710693613799104223806297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7807129075866069482537531 11710693613799104223806297)
            ·
              refine ⟨8783020210349328167854723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11710693613799104223806297 8783020210349328167854723)
              ·
                refine ⟨13174530315523992251782085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8783020210349328167854723 13174530315523992251782085)
                ·
                  refine ⟨2470224434160748547209141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13174530315523992251782085 2470224434160748547209141)
                  ·
                    refine ⟨231583540702570176300857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2470224434160748547209141 231583540702570176300857)
                    ·
                      rfl

theorem cell23_1353022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_1353022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353022 prefixEnd_1353022 := by exact prefixLift 1353022
  have htrace : WordTrace (prefixWord ++ tailWord_1353022) baseStart_1353022 baseEnd_1353022 := by
    simpa [prefixWord, tailWord_1353022, baseEnd_1353022] using wordTrace_append hprefix tailTrace_1353022
  have hstable : (prefixWord ++ tailWord_1353022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353022).length < 2 ^ (prefixWord ++ tailWord_1353022).sum := by decide
  have hdescent : baseEnd_1353022 < baseStart_1353022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353037 : List Nat := [1, 6, 1, 3, 1, 1, 3, 1, 2, 2, 2]
def baseStart_1353037 : Nat := 118140960795 + 1353037 * 2 ^ 59
def prefixEnd_1353037 : Nat := 4983230072969 + 3 ^ 40 * 1353037 * 2
def baseEnd_1353037 : Nat := 694758324317527970215003

theorem tailTrace_1353037 : CollatzResearch.WordTrace tailWord_1353037 prefixEnd_1353037 694758324317527970215003 := by
  unfold tailWord_1353037
  simp only [CollatzResearch.WordTrace]
  refine ⟨49349313599185504167465365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32899542399457002778310243 49349313599185504167465365)
  ·
    refine ⟨2313249074961820507849939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 49349313599185504167465365 2313249074961820507849939)
    ·
      refine ⟨3469873612442730761774909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2313249074961820507849939 3469873612442730761774909)
      ·
        refine ⟨1301202604666024035665591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3469873612442730761774909 1301202604666024035665591)
        ·
          refine ⟨1951803906999036053498387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1301202604666024035665591 1951803906999036053498387)
          ·
            refine ⟨2927705860498554080247581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1951803906999036053498387 2927705860498554080247581)
            ·
              refine ⟨1097889697686957780092843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2927705860498554080247581 1097889697686957780092843)
              ·
                refine ⟨1646834546530436670139265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1097889697686957780092843 1646834546530436670139265)
                ·
                  refine ⟨1235125909897827502604449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1646834546530436670139265 1235125909897827502604449)
                  ·
                    refine ⟨926344432423370626953337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1235125909897827502604449 926344432423370626953337)
                    ·
                      refine ⟨694758324317527970215003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 926344432423370626953337 694758324317527970215003)
                      ·
                        rfl

theorem cell23_1353037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_1353037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353037 prefixEnd_1353037 := by exact prefixLift 1353037
  have htrace : WordTrace (prefixWord ++ tailWord_1353037) baseStart_1353037 baseEnd_1353037 := by
    simpa [prefixWord, tailWord_1353037, baseEnd_1353037] using wordTrace_append hprefix tailTrace_1353037
  have hstable : (prefixWord ++ tailWord_1353037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353037).length < 2 ^ (prefixWord ++ tailWord_1353037).sum := by decide
  have hdescent : baseEnd_1353037 < baseStart_1353037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353055 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 4]
def baseStart_1353055 : Nat := 118140960795 + 1353055 * 2 ^ 59
def prefixEnd_1353055 : Nat := 4983230072969 + 3 ^ 40 * 1353055 * 2
def baseEnd_1353055 : Nat := 694767566969308899789919

theorem tailTrace_1353055 : CollatzResearch.WordTrace tailWord_1353055 prefixEnd_1353055 694767566969308899789919 := by
  unfold tailWord_1353055
  simp only [CollatzResearch.WordTrace]
  refine ⟨49349970113120293241620619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32899980075413528827747079 49349970113120293241620619)
  ·
    refine ⟨74024955169680439862430929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49349970113120293241620619 74024955169680439862430929)
    ·
      refine ⟨55518716377260329896823197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74024955169680439862430929 55518716377260329896823197)
      ·
        refine ⟨20819518641472623711308699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55518716377260329896823197 20819518641472623711308699)
        ·
          refine ⟨31229277962208935566963049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20819518641472623711308699 31229277962208935566963049)
          ·
            refine ⟨23421958471656701675222287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31229277962208935566963049 23421958471656701675222287)
            ·
              refine ⟨35132937707485052512833431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23421958471656701675222287 35132937707485052512833431)
              ·
                refine ⟨52699406561227578769250147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35132937707485052512833431 52699406561227578769250147)
                ·
                  refine ⟨79049109841841368153875221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52699406561227578769250147 79049109841841368153875221)
                  ·
                    refine ⟨3705427023836314132212901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79049109841841368153875221 3705427023836314132212901)
                    ·
                      refine ⟨694767566969308899789919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3705427023836314132212901 694767566969308899789919)
                      ·
                        rfl

theorem cell23_1353055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_1353055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353055 prefixEnd_1353055 := by exact prefixLift 1353055
  have htrace : WordTrace (prefixWord ++ tailWord_1353055) baseStart_1353055 baseEnd_1353055 := by
    simpa [prefixWord, tailWord_1353055, baseEnd_1353055] using wordTrace_append hprefix tailTrace_1353055
  have hstable : (prefixWord ++ tailWord_1353055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353055).length < 2 ^ (prefixWord ++ tailWord_1353055).sum := by decide
  have hdescent : baseEnd_1353055 < baseStart_1353055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353105 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 7]
def baseStart_1353105 : Nat := 118140960795 + 1353105 * 2 ^ 59
def prefixEnd_1353105 : Nat := 4983230072969 + 3 ^ 40 * 1353105 * 2
def baseEnd_1353105 : Nat := 694793241002033704164689

theorem tailTrace_1353105 : CollatzResearch.WordTrace tailWord_1353105 prefixEnd_1353105 694793241002033704164689 := by
  unfold tailWord_1353105
  simp only [CollatzResearch.WordTrace]
  refine ⟨49351793762939151780940769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32901195841959434520627179 49351793762939151780940769)
  ·
    refine ⟨37013845322204363835705577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49351793762939151780940769 37013845322204363835705577)
    ·
      refine ⟨27760383991653272876779183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37013845322204363835705577 27760383991653272876779183)
      ·
        refine ⟨41640575987479909315168775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27760383991653272876779183 41640575987479909315168775)
        ·
          refine ⟨62460863981219863972753163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41640575987479909315168775 62460863981219863972753163)
          ·
            refine ⟨93691295971829795959129745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62460863981219863972753163 93691295971829795959129745)
            ·
              refine ⟨70268471978872346969347309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93691295971829795959129745 70268471978872346969347309)
              ·
                refine ⟨26350676992077130113505241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70268471978872346969347309 26350676992077130113505241)
                ·
                  refine ⟨19763007744057847585128931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26350676992077130113505241 19763007744057847585128931)
                  ·
                    refine ⟨29644511616086771377693397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19763007744057847585128931 29644511616086771377693397)
                    ·
                      refine ⟨694793241002033704164689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 29644511616086771377693397 694793241002033704164689)
                      ·
                        rfl

theorem cell23_1353105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 7].length) (baseStart_1353105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353105 prefixEnd_1353105 := by exact prefixLift 1353105
  have htrace : WordTrace (prefixWord ++ tailWord_1353105) baseStart_1353105 baseEnd_1353105 := by
    simpa [prefixWord, tailWord_1353105, baseEnd_1353105] using wordTrace_append hprefix tailTrace_1353105
  have hstable : (prefixWord ++ tailWord_1353105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353105).length < 2 ^ (prefixWord ++ tailWord_1353105).sum := by decide
  have hdescent : baseEnd_1353105 < baseStart_1353105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353109 : List Nat := [1, 3, 2, 1, 1, 2, 2, 4, 3, 1, 3]
def baseStart_1353109 : Nat := 118140960795 + 1353109 * 2 ^ 59
def prefixEnd_1353109 : Nat := 4983230072969 + 3 ^ 40 * 1353109 * 2
def baseEnd_1353109 : Nat := 694795294924651688514671

theorem tailTrace_1353109 : CollatzResearch.WordTrace tailWord_1353109 prefixEnd_1353109 694795294924651688514671 := by
  unfold tailWord_1353109
  simp only [CollatzResearch.WordTrace]
  refine ⟨49351939654924660464086381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32901293103283106976057587 49351939654924660464086381)
  ·
    refine ⟨18506977370596747674032393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49351939654924660464086381 18506977370596747674032393)
    ·
      refine ⟨13880233027947560755524295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18506977370596747674032393 13880233027947560755524295)
      ·
        refine ⟨20820349541921341133286443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13880233027947560755524295 20820349541921341133286443)
        ·
          refine ⟨31230524312882011699929665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20820349541921341133286443 31230524312882011699929665)
          ·
            refine ⟨23422893234661508774947249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31230524312882011699929665 23422893234661508774947249)
            ·
              refine ⟨17567169925996131581210437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23422893234661508774947249 17567169925996131581210437)
              ·
                refine ⟨3293844361124274671476957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17567169925996131581210437 3293844361124274671476957)
                ·
                  refine ⟨1235191635421603001803859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3293844361124274671476957 1235191635421603001803859)
                  ·
                    refine ⟨1852787453132404502705789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1235191635421603001803859 1852787453132404502705789)
                    ·
                      refine ⟨694795294924651688514671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1852787453132404502705789 694795294924651688514671)
                      ·
                        rfl

theorem cell23_1353109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 1, 3].length) (baseStart_1353109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353109 prefixEnd_1353109 := by exact prefixLift 1353109
  have htrace : WordTrace (prefixWord ++ tailWord_1353109) baseStart_1353109 baseEnd_1353109 := by
    simpa [prefixWord, tailWord_1353109, baseEnd_1353109] using wordTrace_append hprefix tailTrace_1353109
  have hstable : (prefixWord ++ tailWord_1353109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353109).length < 2 ^ (prefixWord ++ tailWord_1353109).sum := by decide
  have hdescent : baseEnd_1353109 < baseStart_1353109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353152 : List Nat := [2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 5]
def baseStart_1353152 : Nat := 118140960795 + 1353152 * 2 ^ 59
def prefixEnd_1353152 : Nat := 4983230072969 + 3 ^ 40 * 1353152 * 2
def baseEnd_1353152 : Nat := 694817374592795020276973

theorem tailTrace_1353152 : CollatzResearch.WordTrace tailWord_1353152 prefixEnd_1353152 694817374592795020276973 := by
  unfold tailWord_1353152
  simp only [CollatzResearch.WordTrace]
  refine ⟨24676753996884439403950855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32902338662512585871934473 24676753996884439403950855)
  ·
    refine ⟨37015130995326659105926283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24676753996884439403950855 37015130995326659105926283)
    ·
      refine ⟨55522696492989988658889425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37015130995326659105926283 55522696492989988658889425)
      ·
        refine ⟨41642022369742491494167069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55522696492989988658889425 41642022369742491494167069)
        ·
          refine ⟨15615758388653434310312651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41642022369742491494167069 15615758388653434310312651)
          ·
            refine ⟨23423637582980151465468977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15615758388653434310312651 23423637582980151465468977)
            ·
              refine ⟨17567728187235113599101733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23423637582980151465468977 17567728187235113599101733)
              ·
                refine ⟨3293949035106583799831575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17567728187235113599101733 3293949035106583799831575)
                ·
                  refine ⟨4940923552659875699747363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3293949035106583799831575 4940923552659875699747363)
                  ·
                    refine ⟨7411385328989813549621045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4940923552659875699747363 7411385328989813549621045)
                    ·
                      refine ⟨694817374592795020276973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7411385328989813549621045 694817374592795020276973)
                      ·
                        rfl

theorem cell23_1353152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_1353152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353152 prefixEnd_1353152 := by exact prefixLift 1353152
  have htrace : WordTrace (prefixWord ++ tailWord_1353152) baseStart_1353152 baseEnd_1353152 := by
    simpa [prefixWord, tailWord_1353152, baseEnd_1353152] using wordTrace_append hprefix tailTrace_1353152
  have hstable : (prefixWord ++ tailWord_1353152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353152).length < 2 ^ (prefixWord ++ tailWord_1353152).sum := by decide
  have hdescent : baseEnd_1353152 < baseStart_1353152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353159 : List Nat := [1, 1, 4, 1, 1, 3, 1, 5, 2, 4]
def baseStart_1353159 : Nat := 118140960795 + 1353159 * 2 ^ 59
def prefixEnd_1353159 : Nat := 4983230072969 + 3 ^ 40 * 1353159 * 2
def baseEnd_1353159 : Nat := 231606989652458830963147

theorem tailTrace_1353159 : CollatzResearch.WordTrace tailWord_1353159 prefixEnd_1353159 231606989652458830963147 := by
  unfold tailWord_1353159
  simp only [CollatzResearch.WordTrace]
  refine ⟨49353763304743519003406531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32902508869829012668937687 49353763304743519003406531)
  ·
    refine ⟨74030644957115278505109797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49353763304743519003406531 74030644957115278505109797)
    ·
      refine ⟨13880745929459114719708087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74030644957115278505109797 13880745929459114719708087)
      ·
        refine ⟨20821118894188672079562131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13880745929459114719708087 20821118894188672079562131)
        ·
          refine ⟨31231678341283008119343197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20821118894188672079562131 31231678341283008119343197)
          ·
            refine ⟨11711879377981128044753699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31231678341283008119343197 11711879377981128044753699)
            ·
              refine ⟨17567819066971692067130549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11711879377981128044753699 17567819066971692067130549)
              ·
                refine ⟨1646983037528596131293489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17567819066971692067130549 1646983037528596131293489)
                ·
                  refine ⟨1235237278146447098470117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1646983037528596131293489 1235237278146447098470117)
                  ·
                    refine ⟨231606989652458830963147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1235237278146447098470117 231606989652458830963147)
                    ·
                      rfl

theorem cell23_1353159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 5, 2, 4].length) (baseStart_1353159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353159 prefixEnd_1353159 := by exact prefixLift 1353159
  have htrace : WordTrace (prefixWord ++ tailWord_1353159) baseStart_1353159 baseEnd_1353159 := by
    simpa [prefixWord, tailWord_1353159, baseEnd_1353159] using wordTrace_append hprefix tailTrace_1353159
  have hstable : (prefixWord ++ tailWord_1353159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353159).length < 2 ^ (prefixWord ++ tailWord_1353159).sum := by decide
  have hdescent : baseEnd_1353159 < baseStart_1353159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353166 : List Nat := [4, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2]
def baseStart_1353166 : Nat := 118140960795 + 1353166 * 2 ^ 59
def prefixEnd_1353166 : Nat := 4983230072969 + 3 ^ 40 * 1353166 * 2
def baseEnd_1353166 : Nat := 694824563321957965501909

theorem tailTrace_1353166 : CollatzResearch.WordTrace tailWord_1353166 prefixEnd_1353166 694824563321957965501909 := by
  unfold tailWord_1353166
  simp only [CollatzResearch.WordTrace]
  refine ⟨6169252326964769899863919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32902679077145439465940901 6169252326964769899863919)
  ·
    refine ⟨9253878490447154849795879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6169252326964769899863919 9253878490447154849795879)
    ·
      refine ⟨13880817735670732274693819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9253878490447154849795879 13880817735670732274693819)
      ·
        refine ⟨20821226603506098412040729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13880817735670732274693819 20821226603506098412040729)
        ·
          refine ⟨15615919952629573809030547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20821226603506098412040729 15615919952629573809030547)
          ·
            refine ⟨23423879928944360713545821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15615919952629573809030547 23423879928944360713545821)
            ·
              refine ⟨8783954973354135267579683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23423879928944360713545821 8783954973354135267579683)
              ·
                refine ⟨13175932460031202901369525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8783954973354135267579683 13175932460031202901369525)
                ·
                  refine ⟨1235243668127925272003393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13175932460031202901369525 1235243668127925272003393)
                  ·
                    refine ⟨926432751095943954002545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1235243668127925272003393 926432751095943954002545)
                    ·
                      refine ⟨694824563321957965501909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 926432751095943954002545 694824563321957965501909)
                      ·
                        rfl

theorem cell23_1353166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 1, 5, 2, 2].length) (baseStart_1353166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353166 prefixEnd_1353166 := by exact prefixLift 1353166
  have htrace : WordTrace (prefixWord ++ tailWord_1353166) baseStart_1353166 baseEnd_1353166 := by
    simpa [prefixWord, tailWord_1353166, baseEnd_1353166] using wordTrace_append hprefix tailTrace_1353166
  have hstable : (prefixWord ++ tailWord_1353166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353166).length < 2 ^ (prefixWord ++ tailWord_1353166).sum := by decide
  have hdescent : baseEnd_1353166 < baseStart_1353166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353277 : List Nat := [1, 4, 1, 3, 4, 1, 1, 2, 1, 3, 2]
def baseStart_1353277 : Nat := 118140960795 + 1353277 * 2 ^ 59
def prefixEnd_1353277 : Nat := 4983230072969 + 3 ^ 40 * 1353277 * 2
def baseEnd_1353277 : Nat := 694881559674607031213899

theorem tailTrace_1353277 : CollatzResearch.WordTrace tailWord_1353277 prefixEnd_1353277 694881559674607031213899 := by
  unfold tailWord_1353277
  simp only [CollatzResearch.WordTrace]
  refine ⟨49358067118316025156202085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32905378078877350104134723 49358067118316025156202085)
  ·
    refine ⟨9254637584684254716787891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49358067118316025156202085 9254637584684254716787891)
    ·
      refine ⟨13881956377026382075181837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9254637584684254716787891 13881956377026382075181837)
      ·
        refine ⟨5205733641384893278193189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13881956377026382075181837 5205733641384893278193189)
        ·
          refine ⟨976075057759667489661223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5205733641384893278193189 976075057759667489661223)
          ·
            refine ⟨1464112586639501234491835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976075057759667489661223 1464112586639501234491835)
            ·
              refine ⟨2196168879959251851737753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1464112586639501234491835 2196168879959251851737753)
              ·
                refine ⟨1647126659969438888803315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2196168879959251851737753 1647126659969438888803315)
                ·
                  refine ⟨2470689989954158333204973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1647126659969438888803315 2470689989954158333204973)
                  ·
                    refine ⟨926508746232809374951865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2470689989954158333204973 926508746232809374951865)
                    ·
                      refine ⟨694881559674607031213899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 926508746232809374951865 694881559674607031213899)
                      ·
                        rfl

theorem cell23_1353277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_1353277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353277 prefixEnd_1353277 := by exact prefixLift 1353277
  have htrace : WordTrace (prefixWord ++ tailWord_1353277) baseStart_1353277 baseEnd_1353277 := by
    simpa [prefixWord, tailWord_1353277, baseEnd_1353277] using wordTrace_append hprefix tailTrace_1353277
  have hstable : (prefixWord ++ tailWord_1353277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353277).length < 2 ^ (prefixWord ++ tailWord_1353277).sum := by decide
  have hdescent : baseEnd_1353277 < baseStart_1353277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353316 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 2, 5, 2]
def baseStart_1353316 : Nat := 118140960795 + 1353316 * 2 ^ 59
def prefixEnd_1353316 : Nat := 4983230072969 + 3 ^ 40 * 1353316 * 2
def baseEnd_1353316 : Nat := 694901585420132378626219

theorem tailTrace_1353316 : CollatzResearch.WordTrace tailWord_1353316 prefixEnd_1353316 694901585420132378626219 := by
  unfold tailWord_1353316
  simp only [CollatzResearch.WordTrace]
  refine ⟨24679744782587367408435901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32906326376783156544581201 24679744782587367408435901)
  ·
    refine ⟨9254904293470262778163463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24679744782587367408435901 9254904293470262778163463)
    ·
      refine ⟨13882356440205394167245195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9254904293470262778163463 13882356440205394167245195)
      ·
        refine ⟨20823534660308091250867793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13882356440205394167245195 20823534660308091250867793)
        ·
          refine ⟨15617650995231068438150845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20823534660308091250867793 15617650995231068438150845)
          ·
            refine ⟨5856619123211650664306567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15617650995231068438150845 5856619123211650664306567)
            ·
              refine ⟨8784928684817475996459851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5856619123211650664306567 8784928684817475996459851)
              ·
                refine ⟨13177393027226213994689777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8784928684817475996459851 13177393027226213994689777)
                ·
                  refine ⟨9883044770419660496017333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13177393027226213994689777 9883044770419660496017333)
                  ·
                    refine ⟨926535447226843171501625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9883044770419660496017333 926535447226843171501625)
                    ·
                      refine ⟨694901585420132378626219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 926535447226843171501625 694901585420132378626219)
                      ·
                        rfl

theorem cell23_1353316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 2, 5, 2].length) (baseStart_1353316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353316 prefixEnd_1353316 := by exact prefixLift 1353316
  have htrace : WordTrace (prefixWord ++ tailWord_1353316) baseStart_1353316 baseEnd_1353316 := by
    simpa [prefixWord, tailWord_1353316, baseEnd_1353316] using wordTrace_append hprefix tailTrace_1353316
  have hstable : (prefixWord ++ tailWord_1353316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353316).length < 2 ^ (prefixWord ++ tailWord_1353316).sum := by decide
  have hdescent : baseEnd_1353316 < baseStart_1353316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353319 : List Nat := [1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_1353319 : Nat := 118140960795 + 1353319 * 2 ^ 59
def prefixEnd_1353319 : Nat := 4983230072969 + 3 ^ 40 * 1353319 * 2
def baseEnd_1353319 : Nat := 694903125862095866888705

theorem tailTrace_1353319 : CollatzResearch.WordTrace tailWord_1353319 prefixEnd_1353319 694903125862095866888705 := by
  unfold tailWord_1353319
  simp only [CollatzResearch.WordTrace]
  refine ⟨49359598984163866329231011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32906399322775910886154007 49359598984163866329231011)
  ·
    refine ⟨74039398476245799493846517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49359598984163866329231011 74039398476245799493846517)
    ·
      refine ⟨6941193607148043702548111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74039398476245799493846517 6941193607148043702548111)
      ·
        refine ⟨10411790410722065553822167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6941193607148043702548111 10411790410722065553822167)
        ·
          refine ⟨15617685616083098330733251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10411790410722065553822167 15617685616083098330733251)
          ·
            refine ⟨23426528424124647496099877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15617685616083098330733251 23426528424124647496099877)
            ·
              refine ⟨4392474079523371405518727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23426528424124647496099877 4392474079523371405518727)
              ·
                refine ⟨6588711119285057108278091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4392474079523371405518727 6588711119285057108278091)
                ·
                  refine ⟨9883066678927585662417137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6588711119285057108278091 9883066678927585662417137)
                  ·
                    refine ⟨7412300009195689246812853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9883066678927585662417137 7412300009195689246812853)
                    ·
                      refine ⟨694903125862095866888705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7412300009195689246812853 694903125862095866888705)
                      ·
                        rfl

theorem cell23_1353319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_1353319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353319 prefixEnd_1353319 := by exact prefixLift 1353319
  have htrace : WordTrace (prefixWord ++ tailWord_1353319) baseStart_1353319 baseEnd_1353319 := by
    simpa [prefixWord, tailWord_1353319, baseEnd_1353319] using wordTrace_append hprefix tailTrace_1353319
  have hstable : (prefixWord ++ tailWord_1353319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353319).length < 2 ^ (prefixWord ++ tailWord_1353319).sum := by decide
  have hdescent : baseEnd_1353319 < baseStart_1353319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353329 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 4, 1, 4]
def baseStart_1353329 : Nat := 118140960795 + 1353329 * 2 ^ 59
def prefixEnd_1353329 : Nat := 4983230072969 + 3 ^ 40 * 1353329 * 2
def baseEnd_1353329 : Nat := 694908260668640827763659

theorem tailTrace_1353329 : CollatzResearch.WordTrace tailWord_1353329 prefixEnd_1353329 694908260668640827763659 := by
  unfold tailWord_1353329
  simp only [CollatzResearch.WordTrace]
  refine ⟨49359963714127638037095041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32906642476085092024730027 49359963714127638037095041)
  ·
    refine ⟨37019972785595728527821281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49359963714127638037095041 37019972785595728527821281)
    ·
      refine ⟨27764979589196796395865961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37019972785595728527821281 27764979589196796395865961)
      ·
        refine ⟨20823734691897597296899471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27764979589196796395865961 20823734691897597296899471)
        ·
          refine ⟨31235602037846395945349207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20823734691897597296899471 31235602037846395945349207)
          ·
            refine ⟨46853403056769593918023811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31235602037846395945349207 46853403056769593918023811)
            ·
              refine ⟨70280104585154390877035717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46853403056769593918023811 70280104585154390877035717)
              ·
                refine ⟨13177519609716448289444197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70280104585154390877035717 13177519609716448289444197)
                ·
                  refine ⟨2470784926821834054270787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13177519609716448289444197 2470784926821834054270787)
                  ·
                    refine ⟨3706177390232751081406181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2470784926821834054270787 3706177390232751081406181)
                    ·
                      refine ⟨694908260668640827763659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3706177390232751081406181 694908260668640827763659)
                      ·
                        rfl

theorem cell23_1353329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 4, 1, 4].length) (baseStart_1353329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353329 prefixEnd_1353329 := by exact prefixLift 1353329
  have htrace : WordTrace (prefixWord ++ tailWord_1353329) baseStart_1353329 baseEnd_1353329 := by
    simpa [prefixWord, tailWord_1353329, baseEnd_1353329] using wordTrace_append hprefix tailTrace_1353329
  have hstable : (prefixWord ++ tailWord_1353329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353329).length < 2 ^ (prefixWord ++ tailWord_1353329).sum := by decide
  have hdescent : baseEnd_1353329 < baseStart_1353329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353369 : List Nat := [1, 2, 1, 2, 1, 2, 2, 6, 6]
def baseStart_1353369 : Nat := 118140960795 + 1353369 * 2 ^ 59
def prefixEnd_1353369 : Nat := 4983230072969 + 3 ^ 40 * 1353369 * 2
def baseEnd_1353369 : Nat := 77214311099424519029275

theorem tailTrace_1353369 : CollatzResearch.WordTrace tailWord_1353369 prefixEnd_1353369 77214311099424519029275 := by
  unfold tailWord_1353369
  simp only [CollatzResearch.WordTrace]
  refine ⟨49361422633982724868551161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32907615089321816579034107 49361422633982724868551161)
  ·
    refine ⟨37021066975487043651413371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49361422633982724868551161 37021066975487043651413371)
    ·
      refine ⟨55531600463230565477120057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37021066975487043651413371 55531600463230565477120057)
      ·
        refine ⟨41648700347422924107840043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55531600463230565477120057 41648700347422924107840043)
        ·
          refine ⟨62473050521134386161760065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41648700347422924107840043 62473050521134386161760065)
          ·
            refine ⟨46854787890850789621320049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62473050521134386161760065 46854787890850789621320049)
            ·
              refine ⟨35141090918138092215990037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46854787890850789621320049 35141090918138092215990037)
              ·
                refine ⟨1647238636787723072624533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 35141090918138092215990037 1647238636787723072624533)
                ·
                  refine ⟨77214311099424519029275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1647238636787723072624533 77214311099424519029275)
                  ·
                    rfl

theorem cell23_1353369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 6, 6].length) (baseStart_1353369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353369 prefixEnd_1353369 := by exact prefixLift 1353369
  have htrace : WordTrace (prefixWord ++ tailWord_1353369) baseStart_1353369 baseEnd_1353369 := by
    simpa [prefixWord, tailWord_1353369, baseEnd_1353369] using wordTrace_append hprefix tailTrace_1353369
  have hstable : (prefixWord ++ tailWord_1353369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353369).length < 2 ^ (prefixWord ++ tailWord_1353369).sum := by decide
  have hdescent : baseEnd_1353369 < baseStart_1353369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353416 : List Nat := [2, 1, 3, 1, 2, 2, 1, 5, 1, 5]
def baseStart_1353416 : Nat := 118140960795 + 1353416 * 2 ^ 59
def prefixEnd_1353416 : Nat := 4983230072969 + 3 ^ 40 * 1353416 * 2
def baseEnd_1353416 : Nat := 231650977828527329125253

theorem tailTrace_1353416 : CollatzResearch.WordTrace tailWord_1353416 prefixEnd_1353416 231650977828527329125253 := by
  unfold tailWord_1353416
  simp only [CollatzResearch.WordTrace]
  refine ⟨24681568432406225947756051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32908757909874967930341401 24681568432406225947756051)
  ·
    refine ⟨37022352648609338921634077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24681568432406225947756051 37022352648609338921634077)
    ·
      refine ⟨13883382243228502095612779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37022352648609338921634077 13883382243228502095612779)
      ·
        refine ⟨20825073364842753143419169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13883382243228502095612779 20825073364842753143419169)
        ·
          refine ⟨15618805023632064857564377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20825073364842753143419169 15618805023632064857564377)
          ·
            refine ⟨11714103767724048643173283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15618805023632064857564377 11714103767724048643173283)
            ·
              refine ⟨17571155651586072964759925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11714103767724048643173283 17571155651586072964759925)
              ·
                refine ⟨1647295842336194340446243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17571155651586072964759925 1647295842336194340446243)
                ·
                  refine ⟨2470943763504291510669365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1647295842336194340446243 2470943763504291510669365)
                  ·
                    refine ⟨231650977828527329125253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2470943763504291510669365 231650977828527329125253)
                    ·
                      rfl

theorem cell23_1353416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 5, 1, 5].length) (baseStart_1353416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353416 prefixEnd_1353416 := by exact prefixLift 1353416
  have htrace : WordTrace (prefixWord ++ tailWord_1353416) baseStart_1353416 baseEnd_1353416 := by
    simpa [prefixWord, tailWord_1353416, baseEnd_1353416] using wordTrace_append hprefix tailTrace_1353416
  have hstable : (prefixWord ++ tailWord_1353416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353416).length < 2 ^ (prefixWord ++ tailWord_1353416).sum := by decide
  have hdescent : baseEnd_1353416 < baseStart_1353416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353437 : List Nat := [1, 4, 3, 3, 1, 2, 2, 1, 6]
def baseStart_1353437 : Nat := 118140960795 + 1353437 * 2 ^ 59
def prefixEnd_1353437 : Nat := 4983230072969 + 3 ^ 40 * 1353437 * 2
def baseEnd_1353437 : Nat := 77218190731036267245907

theorem tailTrace_1353437 : CollatzResearch.WordTrace tailWord_1353437 prefixEnd_1353437 77218190731036267245907 := by
  unfold tailWord_1353437
  simp only [CollatzResearch.WordTrace]
  refine ⟨49363902797736372482026565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32909268531824248321351043 49363902797736372482026565)
  ·
    refine ⟨9255731774575569840379981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49363902797736372482026565 9255731774575569840379981)
    ·
      refine ⟨3470899415465838690142493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9255731774575569840379981 3470899415465838690142493)
      ·
        refine ⟨1301587280799689508803435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3470899415465838690142493 1301587280799689508803435)
        ·
          refine ⟨1952380921199534263205153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1301587280799689508803435 1952380921199534263205153)
          ·
            refine ⟨1464285690899650697403865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1952380921199534263205153 1464285690899650697403865)
            ·
              refine ⟨1098214268174738023052899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1464285690899650697403865 1098214268174738023052899)
              ·
                refine ⟨1647321402262107034579349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098214268174738023052899 1647321402262107034579349)
                ·
                  refine ⟨77218190731036267245907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1647321402262107034579349 77218190731036267245907)
                  ·
                    rfl

theorem cell23_1353437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 6].length) (baseStart_1353437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353437 prefixEnd_1353437 := by exact prefixLift 1353437
  have htrace : WordTrace (prefixWord ++ tailWord_1353437) baseStart_1353437 baseEnd_1353437 := by
    simpa [prefixWord, tailWord_1353437, baseEnd_1353437] using wordTrace_append hprefix tailTrace_1353437
  have hstable : (prefixWord ++ tailWord_1353437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353437).length < 2 ^ (prefixWord ++ tailWord_1353437).sum := by decide
  have hdescent : baseEnd_1353437 < baseStart_1353437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353453 : List Nat := [1, 5, 1, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_1353453 : Nat := 118140960795 + 1353453 * 2 ^ 59
def prefixEnd_1353453 : Nat := 4983230072969 + 3 ^ 40 * 1353453 * 2
def baseEnd_1353453 : Nat := 694971932269798342613089

theorem tailTrace_1353453 : CollatzResearch.WordTrace tailWord_1353453 prefixEnd_1353453 694971932269798342613089 := by
  unfold tailWord_1353453
  simp only [CollatzResearch.WordTrace]
  refine ⟨49364486365678407214609013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32909657577118938143072675 49364486365678407214609013)
  ·
    refine ⟨4627920596782350676369595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 49364486365678407214609013 4627920596782350676369595)
    ·
      refine ⟨6941880895173526014554393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4627920596782350676369595 6941880895173526014554393)
      ·
        refine ⟨5206410671380144510915795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6941880895173526014554393 5206410671380144510915795)
        ·
          refine ⟨7809616007070216766373693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5206410671380144510915795 7809616007070216766373693)
          ·
            refine ⟨2928606002651331287390135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7809616007070216766373693 2928606002651331287390135)
            ·
              refine ⟨4392909003976996931085203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2928606002651331287390135 4392909003976996931085203)
              ·
                refine ⟨6589363505965495396627805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4392909003976996931085203 6589363505965495396627805)
                ·
                  refine ⟨2471011314737060773735427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6589363505965495396627805 2471011314737060773735427)
                  ·
                    refine ⟨3706516972105591160603141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2471011314737060773735427 3706516972105591160603141)
                    ·
                      refine ⟨694971932269798342613089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3706516972105591160603141 694971932269798342613089)
                      ·
                        rfl

theorem cell23_1353453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_1353453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353453 prefixEnd_1353453 := by exact prefixLift 1353453
  have htrace : WordTrace (prefixWord ++ tailWord_1353453) baseStart_1353453 baseEnd_1353453 := by
    simpa [prefixWord, tailWord_1353453, baseEnd_1353453] using wordTrace_append hprefix tailTrace_1353453
  have hstable : (prefixWord ++ tailWord_1353453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353453).length < 2 ^ (prefixWord ++ tailWord_1353453).sum := by decide
  have hdescent : baseEnd_1353453 < baseStart_1353453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353459 : List Nat := [1, 1, 1, 2, 2, 3, 4, 9]
def baseStart_1353459 : Nat := 118140960795 + 1353459 * 2 ^ 59
def prefixEnd_1353459 : Nat := 4983230072969 + 3 ^ 40 * 1353459 * 2
def baseEnd_1353459 : Nat := 25739815301989826634743

theorem tailTrace_1353459 : CollatzResearch.WordTrace tailWord_1353459 prefixEnd_1353459 25739815301989826634743 := by
  unfold tailWord_1353459
  simp only [CollatzResearch.WordTrace]
  refine ⟨49364705203656670239327431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32909803469104446826218287 49364705203656670239327431)
  ·
    refine ⟨74047057805485005358991147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49364705203656670239327431 74047057805485005358991147)
    ·
      refine ⟨111070586708227508038486721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74047057805485005358991147 111070586708227508038486721)
      ·
        refine ⟨83302940031170631028865041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111070586708227508038486721 83302940031170631028865041)
        ·
          refine ⟨62477205023377973271648781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83302940031170631028865041 62477205023377973271648781)
          ·
            refine ⟨23428951883766739976868293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62477205023377973271648781 23428951883766739976868293)
            ·
              refine ⟨4392928478206263745662805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23428951883766739976868293 4392928478206263745662805)
              ·
                refine ⟨25739815301989826634743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4392928478206263745662805 25739815301989826634743)
                ·
                  rfl

theorem cell23_1353459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 9].length) (baseStart_1353459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353459 prefixEnd_1353459 := by exact prefixLift 1353459
  have htrace : WordTrace (prefixWord ++ tailWord_1353459) baseStart_1353459 baseEnd_1353459 := by
    simpa [prefixWord, tailWord_1353459, baseEnd_1353459] using wordTrace_append hprefix tailTrace_1353459
  have hstable : (prefixWord ++ tailWord_1353459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353459).length < 2 ^ (prefixWord ++ tailWord_1353459).sum := by decide
  have hdescent : baseEnd_1353459 < baseStart_1353459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353473 : List Nat := [1, 2, 4, 1, 1, 1, 2, 5, 1, 2, 3]
def baseStart_1353473 : Nat := 118140960795 + 1353473 * 2 ^ 59
def prefixEnd_1353473 : Nat := 4983230072969 + 3 ^ 40 * 1353473 * 2
def baseEnd_1353473 : Nat := 694982201882888264362997

theorem tailTrace_1353473 : CollatzResearch.WordTrace tailWord_1353473 prefixEnd_1353473 694982201882888264362997 := by
  unfold tailWord_1353473
  simp only [CollatzResearch.WordTrace]
  refine ⟨49365215825605950630337073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32910143883737300420224715 49365215825605950630337073)
  ·
    refine ⟨37023911869204462972752805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49365215825605950630337073 37023911869204462972752805)
    ·
      refine ⟨6941983475475836807391151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37023911869204462972752805 6941983475475836807391151)
      ·
        refine ⟨10412975213213755211086727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6941983475475836807391151 10412975213213755211086727)
        ·
          refine ⟨15619462819820632816630091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10412975213213755211086727 15619462819820632816630091)
          ·
            refine ⟨23429194229730949224945137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15619462819820632816630091 23429194229730949224945137)
            ·
              refine ⟨17571895672298211918708853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23429194229730949224945137 17571895672298211918708853)
              ·
                refine ⟨1647365219277957367378955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17571895672298211918708853 1647365219277957367378955)
                ·
                  refine ⟨2471047828916936051068433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1647365219277957367378955 2471047828916936051068433)
                  ·
                    refine ⟨1853285871687702038301325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2471047828916936051068433 1853285871687702038301325)
                    ·
                      refine ⟨694982201882888264362997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1853285871687702038301325 694982201882888264362997)
                      ·
                        rfl

theorem cell23_1353473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 2, 3].length) (baseStart_1353473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353473 prefixEnd_1353473 := by exact prefixLift 1353473
  have htrace : WordTrace (prefixWord ++ tailWord_1353473) baseStart_1353473 baseEnd_1353473 := by
    simpa [prefixWord, tailWord_1353473, baseEnd_1353473] using wordTrace_append hprefix tailTrace_1353473
  have hstable : (prefixWord ++ tailWord_1353473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353473).length < 2 ^ (prefixWord ++ tailWord_1353473).sum := by decide
  have hdescent : baseEnd_1353473 < baseStart_1353473 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353490 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_1353490 : Nat := 118140960795 + 1353490 * 2 ^ 59
def prefixEnd_1353490 : Nat := 4983230072969 + 3 ^ 40 * 1353490 * 2
def baseEnd_1353490 : Nat := 694990931054014697850419

theorem tailTrace_1353490 : CollatzResearch.WordTrace tailWord_1353490 prefixEnd_1353490 694990931054014697850419 := by
  unfold tailWord_1353490
  simp only [CollatzResearch.WordTrace]
  refine ⟨12341458966636090633426481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32910557244362908355803949 12341458966636090633426481)
  ·
    refine ⟨9256094224977067975069861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12341458966636090633426481 9256094224977067975069861)
    ·
      refine ⟨1735517667183200245325599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9256094224977067975069861 1735517667183200245325599)
      ·
        refine ⟨2603276500774800367988399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1735517667183200245325599 2603276500774800367988399)
        ·
          refine ⟨3904914751162200551982599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2603276500774800367988399 3904914751162200551982599)
          ·
            refine ⟨5857372126743300827973899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3904914751162200551982599 5857372126743300827973899)
            ·
              refine ⟨8786058190114951241960849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5857372126743300827973899 8786058190114951241960849)
              ·
                refine ⟨6589543642586213431470637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8786058190114951241960849 6589543642586213431470637)
                ·
                  refine ⟨2471078865969830036801489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6589543642586213431470637 2471078865969830036801489)
                  ·
                    refine ⟨1853309149477372527601117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2471078865969830036801489 1853309149477372527601117)
                    ·
                      refine ⟨694990931054014697850419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1853309149477372527601117 694990931054014697850419)
                      ·
                        rfl

theorem cell23_1353490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_1353490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353490 prefixEnd_1353490 := by exact prefixLift 1353490
  have htrace : WordTrace (prefixWord ++ tailWord_1353490) baseStart_1353490 baseEnd_1353490 := by
    simpa [prefixWord, tailWord_1353490, baseEnd_1353490] using wordTrace_append hprefix tailTrace_1353490
  have hstable : (prefixWord ++ tailWord_1353490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353490).length < 2 ^ (prefixWord ++ tailWord_1353490).sum := by decide
  have hdescent : baseEnd_1353490 < baseStart_1353490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353503 : List Nat := [1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 3]
def baseStart_1353503 : Nat := 118140960795 + 1353503 * 2 ^ 59
def prefixEnd_1353503 : Nat := 4983230072969 + 3 ^ 40 * 1353503 * 2
def baseEnd_1353503 : Nat := 694997606302523146987859

theorem tailTrace_1353503 : CollatzResearch.WordTrace tailWord_1353503 prefixEnd_1353503 694997606302523146987859 := by
  unfold tailWord_1353503
  simp only [CollatzResearch.WordTrace]
  refine ⟨49366310015497265753929163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32910873343664843835952775 49366310015497265753929163)
  ·
    refine ⟨74049465023245898630893745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49366310015497265753929163 74049465023245898630893745)
    ·
      refine ⟨55537098767434423973170309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74049465023245898630893745 55537098767434423973170309)
      ·
        refine ⟨10413206018893954494969433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 55537098767434423973170309 10413206018893954494969433)
        ·
          refine ⟨7809904514170465871227075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10413206018893954494969433 7809904514170465871227075)
          ·
            refine ⟨11714856771255698806840613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7809904514170465871227075 11714856771255698806840613)
            ·
              refine ⟨2196535644610443526282615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11714856771255698806840613 2196535644610443526282615)
              ·
                refine ⟨3294803466915665289423923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2196535644610443526282615 3294803466915665289423923)
                ·
                  refine ⟨4942205200373497934135885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3294803466915665289423923 4942205200373497934135885)
                  ·
                    refine ⟨1853326950140061725300957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4942205200373497934135885 1853326950140061725300957)
                    ·
                      refine ⟨694997606302523146987859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1853326950140061725300957 694997606302523146987859)
                      ·
                        rfl

theorem cell23_1353503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_1353503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353503 prefixEnd_1353503 := by exact prefixLift 1353503
  have htrace : WordTrace (prefixWord ++ tailWord_1353503) baseStart_1353503 baseEnd_1353503 := by
    simpa [prefixWord, tailWord_1353503, baseEnd_1353503] using wordTrace_append hprefix tailTrace_1353503
  have hstable : (prefixWord ++ tailWord_1353503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353503).length < 2 ^ (prefixWord ++ tailWord_1353503).sum := by decide
  have hdescent : baseEnd_1353503 < baseStart_1353503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353506 : List Nat := [3, 3, 1, 1, 2, 1, 1, 2, 2, 7]
def baseStart_1353506 : Nat := 118140960795 + 1353506 * 2 ^ 59
def prefixEnd_1353506 : Nat := 4983230072969 + 3 ^ 40 * 1353506 * 2
def baseEnd_1353506 : Nat := 231666382248162211750115

theorem tailTrace_1353506 : CollatzResearch.WordTrace tailWord_1353506 prefixEnd_1353506 231666382248162211750115 := by
  unfold tailWord_1353506
  simp only [CollatzResearch.WordTrace]
  refine ⟨12341604858621599316572093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32910946289657598177525581 12341604858621599316572093)
  ·
    refine ⟨4628101821983099743714535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12341604858621599316572093 4628101821983099743714535)
    ·
      refine ⟨6942152732974649615571803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4628101821983099743714535 6942152732974649615571803)
      ·
        refine ⟨10413229099461974423357705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6942152732974649615571803 10413229099461974423357705)
        ·
          refine ⟨7809921824596480817518279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10413229099461974423357705 7809921824596480817518279)
          ·
            refine ⟨11714882736894721226277419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7809921824596480817518279 11714882736894721226277419)
            ·
              refine ⟨17572324105342081839416129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11714882736894721226277419 17572324105342081839416129)
              ·
                refine ⟨13179243079006561379562097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17572324105342081839416129 13179243079006561379562097)
                ·
                  refine ⟨9884432309254921034671573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13179243079006561379562097 9884432309254921034671573)
                  ·
                    refine ⟨231666382248162211750115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9884432309254921034671573 231666382248162211750115)
                    ·
                      rfl

theorem cell23_1353506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_1353506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353506 prefixEnd_1353506 := by exact prefixLift 1353506
  have htrace : WordTrace (prefixWord ++ tailWord_1353506) baseStart_1353506 baseEnd_1353506 := by
    simpa [prefixWord, tailWord_1353506, baseEnd_1353506] using wordTrace_append hprefix tailTrace_1353506
  have hstable : (prefixWord ++ tailWord_1353506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353506).length < 2 ^ (prefixWord ++ tailWord_1353506).sum := by decide
  have hdescent : baseEnd_1353506 < baseStart_1353506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353524 : List Nat := [2, 5, 1, 1, 2, 3, 2, 1, 1, 2, 3]
def baseStart_1353524 : Nat := 118140960795 + 1353524 * 2 ^ 59
def prefixEnd_1353524 : Nat := 4983230072969 + 3 ^ 40 * 1353524 * 2
def baseEnd_1353524 : Nat := 695008389396267564825263

theorem tailTrace_1353524 : CollatzResearch.WordTrace tailWord_1353524 prefixEnd_1353524 695008389396267564825263 := by
  unfold tailWord_1353524
  simp only [CollatzResearch.WordTrace]
  refine ⟨24683537974210593170221813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32911383965614124226962417 24683537974210593170221813)
  ·
    refine ⟨2314081685082243109708295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24683537974210593170221813 2314081685082243109708295)
    ·
      refine ⟨3471122527623364664562443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2314081685082243109708295 3471122527623364664562443)
      ·
        refine ⟨5206683791435046996843665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3471122527623364664562443 5206683791435046996843665)
        ·
          refine ⟨3905012843576285247632749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5206683791435046996843665 3905012843576285247632749)
          ·
            refine ⟨1464379816341106967862281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3905012843576285247632749 1464379816341106967862281)
            ·
              refine ⟨1098284862255830225896711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1464379816341106967862281 1098284862255830225896711)
              ·
                refine ⟨1647427293383745338845067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098284862255830225896711 1647427293383745338845067)
                ·
                  refine ⟨2471140940075618008267601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1647427293383745338845067 2471140940075618008267601)
                  ·
                    refine ⟨1853355705056713506200701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2471140940075618008267601 1853355705056713506200701)
                    ·
                      refine ⟨695008389396267564825263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1853355705056713506200701 695008389396267564825263)
                      ·
                        rfl

theorem cell23_1353524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 1, 2, 3].length) (baseStart_1353524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353524 prefixEnd_1353524 := by exact prefixLift 1353524
  have htrace : WordTrace (prefixWord ++ tailWord_1353524) baseStart_1353524 baseEnd_1353524 := by
    simpa [prefixWord, tailWord_1353524, baseEnd_1353524] using wordTrace_append hprefix tailTrace_1353524
  have hstable : (prefixWord ++ tailWord_1353524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353524).length < 2 ^ (prefixWord ++ tailWord_1353524).sum := by decide
  have hdescent : baseEnd_1353524 < baseStart_1353524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353543 : List Nat := [1, 1, 4, 1, 2, 1, 2, 2, 3, 4, 2]
def baseStart_1353543 : Nat := 118140960795 + 1353543 * 2 ^ 59
def prefixEnd_1353543 : Nat := 4983230072969 + 3 ^ 40 * 1353543 * 2
def baseEnd_1353543 : Nat := 695018145528702990487675

theorem tailTrace_1353543 : CollatzResearch.WordTrace tailWord_1353543 prefixEnd_1353543 695018145528702990487675 := by
  unfold tailWord_1353543
  simp only [CollatzResearch.WordTrace]
  refine ⟨49367768935352352585385283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32911845956901568390256855 49367768935352352585385283)
  ·
    refine ⟨74051653403028528878077925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49367768935352352585385283 74051653403028528878077925)
    ·
      refine ⟨13884685013067849164639611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74051653403028528878077925 13884685013067849164639611)
      ·
        refine ⟨20827027519601773746959417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13884685013067849164639611 20827027519601773746959417)
        ·
          refine ⟨15620270639701330310219563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20827027519601773746959417 15620270639701330310219563)
          ·
            refine ⟨23430405959551995465329345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15620270639701330310219563 23430405959551995465329345)
            ·
              refine ⟨17572804469663996598997009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23430405959551995465329345 17572804469663996598997009)
              ·
                refine ⟨13179603352247997449247757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17572804469663996598997009 13179603352247997449247757)
                ·
                  refine ⟨4942351257092999043467909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13179603352247997449247757 4942351257092999043467909)
                  ·
                    refine ⟨926690860704937320650233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4942351257092999043467909 926690860704937320650233)
                    ·
                      refine ⟨695018145528702990487675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 926690860704937320650233 695018145528702990487675)
                      ·
                        rfl

theorem cell23_1353543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 3, 4, 2].length) (baseStart_1353543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353543 prefixEnd_1353543 := by exact prefixLift 1353543
  have htrace : WordTrace (prefixWord ++ tailWord_1353543) baseStart_1353543 baseEnd_1353543 := by
    simpa [prefixWord, tailWord_1353543, baseEnd_1353543] using wordTrace_append hprefix tailTrace_1353543
  have hstable : (prefixWord ++ tailWord_1353543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353543).length < 2 ^ (prefixWord ++ tailWord_1353543).sum := by decide
  have hdescent : baseEnd_1353543 < baseStart_1353543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353564 : List Nat := [2, 2, 4, 2, 2, 1, 2, 2, 1, 3, 2]
def baseStart_1353564 : Nat := 118140960795 + 1353564 * 2 ^ 59
def prefixEnd_1353564 : Nat := 4983230072969 + 3 ^ 40 * 1353564 * 2
def baseEnd_1353564 : Nat := 695028928622447408325079

theorem tailTrace_1353564 : CollatzResearch.WordTrace tailWord_1353564 prefixEnd_1353564 695028928622447408325079 := by
  unfold tailWord_1353564
  simp only [CollatzResearch.WordTrace]
  refine ⟨24684267434138136585949873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32912356578850848781266497 24684267434138136585949873)
  ·
    refine ⟨18513200575603602439462405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24684267434138136585949873 18513200575603602439462405)
    ·
      refine ⟨3471225107925675457399201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18513200575603602439462405 3471225107925675457399201)
      ·
        refine ⟨2603418830944256593049401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3471225107925675457399201 2603418830944256593049401)
        ·
          refine ⟨1952564123208192444787051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2603418830944256593049401 1952564123208192444787051)
          ·
            refine ⟨2928846184812288667180577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1952564123208192444787051 2928846184812288667180577)
            ·
              refine ⟨2196634638609216500385433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2928846184812288667180577 2196634638609216500385433)
              ·
                refine ⟨1647475978956912375289075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2196634638609216500385433 1647475978956912375289075)
                ·
                  refine ⟨2471213968435368562933613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1647475978956912375289075 2471213968435368562933613)
                  ·
                    refine ⟨926705238163263211100105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2471213968435368562933613 926705238163263211100105)
                    ·
                      refine ⟨695028928622447408325079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 926705238163263211100105 695028928622447408325079)
                      ·
                        rfl

theorem cell23_1353564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 2, 2, 1, 3, 2].length) (baseStart_1353564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353564 prefixEnd_1353564 := by exact prefixLift 1353564
  have htrace : WordTrace (prefixWord ++ tailWord_1353564) baseStart_1353564 baseEnd_1353564 := by
    simpa [prefixWord, tailWord_1353564, baseEnd_1353564] using wordTrace_append hprefix tailTrace_1353564
  have hstable : (prefixWord ++ tailWord_1353564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353564).length < 2 ^ (prefixWord ++ tailWord_1353564).sum := by decide
  have hdescent : baseEnd_1353564 < baseStart_1353564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353600 : List Nat := [2, 1, 1, 2, 1, 2, 7, 2, 5]
def baseStart_1353600 : Nat := 118140960795 + 1353600 * 2 ^ 59
def prefixEnd_1353600 : Nat := 4983230072969 + 3 ^ 40 * 1353600 * 2
def baseEnd_1353600 : Nat := 77227490436223251941657

theorem tailTrace_1353600 : CollatzResearch.WordTrace tailWord_1353600 prefixEnd_1353600 77227490436223251941657 := by
  unfold tailWord_1353600
  simp only [CollatzResearch.WordTrace]
  refine ⟨24684923948072925660105127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32913231930763900880140169 24684923948072925660105127)
  ·
    refine ⟨37027385922109388490157691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24684923948072925660105127 37027385922109388490157691)
    ·
      refine ⟨55541078883164082735236537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37027385922109388490157691 55541078883164082735236537)
      ·
        refine ⟨41655809162373062051427403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55541078883164082735236537 41655809162373062051427403)
        ·
          refine ⟨62483713743559593077141105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41655809162373062051427403 62483713743559593077141105)
          ·
            refine ⟨46862785307669694807855829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62483713743559593077141105 46862785307669694807855829)
            ·
              refine ⟨1098346530648508472059121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 46862785307669694807855829 1098346530648508472059121)
              ·
                refine ⟨823759897986381354044341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1098346530648508472059121 823759897986381354044341)
                ·
                  refine ⟨77227490436223251941657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 823759897986381354044341 77227490436223251941657)
                  ·
                    rfl

theorem cell23_1353600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 7, 2, 5].length) (baseStart_1353600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353600 prefixEnd_1353600 := by exact prefixLift 1353600
  have htrace : WordTrace (prefixWord ++ tailWord_1353600) baseStart_1353600 baseEnd_1353600 := by
    simpa [prefixWord, tailWord_1353600, baseEnd_1353600] using wordTrace_append hprefix tailTrace_1353600
  have hstable : (prefixWord ++ tailWord_1353600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353600).length < 2 ^ (prefixWord ++ tailWord_1353600).sum := by decide
  have hdescent : baseEnd_1353600 < baseStart_1353600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353700 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 5, 1, 3]
def baseStart_1353700 : Nat := 118140960795 + 1353700 * 2 ^ 59
def prefixEnd_1353700 : Nat := 4983230072969 + 3 ^ 40 * 1353700 * 2
def baseEnd_1353700 : Nat := 695098761991458876224453

theorem tailTrace_1353700 : CollatzResearch.WordTrace tailWord_1353700 prefixEnd_1353700 695098761991458876224453 := by
  unfold tailWord_1353700
  simp only [CollatzResearch.WordTrace]
  refine ⟨24686747597891784199425277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32915663463855712265900369 24686747597891784199425277)
  ·
    refine ⟨9257530349209419074784479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24686747597891784199425277 9257530349209419074784479)
    ·
      refine ⟨13886295523814128612176719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9257530349209419074784479 13886295523814128612176719)
      ·
        refine ⟨20829443285721192918265079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13886295523814128612176719 20829443285721192918265079)
        ·
          refine ⟨31244164928581789377397619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20829443285721192918265079 31244164928581789377397619)
          ·
            refine ⟨46866247392872684066096429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31244164928581789377397619 46866247392872684066096429)
            ·
              refine ⟨17574842772327256524786161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46866247392872684066096429 17574842772327256524786161)
              ·
                refine ⟨13181132079245442393589621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17574842772327256524786161 13181132079245442393589621)
                ·
                  refine ⟨1235731132429260224399027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 13181132079245442393589621 1235731132429260224399027)
                  ·
                    refine ⟨1853596698643890336598541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1235731132429260224399027 1853596698643890336598541)
                    ·
                      refine ⟨695098761991458876224453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1853596698643890336598541 695098761991458876224453)
                      ·
                        rfl

theorem cell23_1353700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_1353700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353700 prefixEnd_1353700 := by exact prefixLift 1353700
  have htrace : WordTrace (prefixWord ++ tailWord_1353700) baseStart_1353700 baseEnd_1353700 := by
    simpa [prefixWord, tailWord_1353700, baseEnd_1353700] using wordTrace_append hprefix tailTrace_1353700
  have hstable : (prefixWord ++ tailWord_1353700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353700).length < 2 ^ (prefixWord ++ tailWord_1353700).sum := by decide
  have hdescent : baseEnd_1353700 < baseStart_1353700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353723 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 4]
def baseStart_1353723 : Nat := 118140960795 + 1353723 * 2 ^ 59
def prefixEnd_1353723 : Nat := 4983230072969 + 3 ^ 40 * 1353723 * 2
def baseEnd_1353723 : Nat := 695110572046512286236847

theorem tailTrace_1353723 : CollatzResearch.WordTrace tailWord_1353723 prefixEnd_1353723 695110572046512286236847 := by
  unfold tailWord_1353723
  simp only [CollatzResearch.WordTrace]
  refine ⟨49374334074700243326937823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32916222716466828884625215 49374334074700243326937823)
  ·
    refine ⟨74061501112050364990406735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49374334074700243326937823 74061501112050364990406735)
    ·
      refine ⟨111092251668075547485610103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74061501112050364990406735 111092251668075547485610103)
      ·
        refine ⟨166638377502113321228415155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111092251668075547485610103 166638377502113321228415155)
        ·
          refine ⟨249957566253169981842622733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 166638377502113321228415155 249957566253169981842622733)
          ·
            refine ⟨93734087344938743190983525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 249957566253169981842622733 93734087344938743190983525)
            ·
              refine ⟨17575141377176014348309411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93734087344938743190983525 17575141377176014348309411)
              ·
                refine ⟨26362712065764021522464117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17575141377176014348309411 26362712065764021522464117)
                ·
                  refine ⟨2471504256165377017731011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 26362712065764021522464117 2471504256165377017731011)
                  ·
                    refine ⟨3707256384248065526596517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2471504256165377017731011 3707256384248065526596517)
                    ·
                      refine ⟨695110572046512286236847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3707256384248065526596517 695110572046512286236847)
                      ·
                        rfl

theorem cell23_1353723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 4].length) (baseStart_1353723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353723 prefixEnd_1353723 := by exact prefixLift 1353723
  have htrace : WordTrace (prefixWord ++ tailWord_1353723) baseStart_1353723 baseEnd_1353723 := by
    simpa [prefixWord, tailWord_1353723, baseEnd_1353723] using wordTrace_append hprefix tailTrace_1353723
  have hstable : (prefixWord ++ tailWord_1353723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353723).length < 2 ^ (prefixWord ++ tailWord_1353723).sum := by decide
  have hdescent : baseEnd_1353723 < baseStart_1353723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353740 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 2, 6, 2]
def baseStart_1353740 : Nat := 118140960795 + 1353740 * 2 ^ 59
def prefixEnd_1353740 : Nat := 4983230072969 + 3 ^ 40 * 1353740 * 2
def baseEnd_1353740 : Nat := 695119301217638719724269

theorem tailTrace_1353740 : CollatzResearch.WordTrace tailWord_1353740 prefixEnd_1353740 695119301217638719724269 := by
  unfold tailWord_1353740
  simp only [CollatzResearch.WordTrace]
  refine ⟨24687477057819327615153337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32916636077092436820204449 24687477057819327615153337)
  ·
    refine ⟨18515607793364495711365003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24687477057819327615153337 18515607793364495711365003)
    ·
      refine ⟨27773411690046743567047505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18515607793364495711365003 27773411690046743567047505)
      ·
        refine ⟨20830058767535057675285629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27773411690046743567047505 20830058767535057675285629)
        ·
          refine ⟨7811272037825646628232111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20830058767535057675285629 7811272037825646628232111)
          ·
            refine ⟨11716908056738469942348167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7811272037825646628232111 11716908056738469942348167)
            ·
              refine ⟨17575362085107704913522251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11716908056738469942348167 17575362085107704913522251)
              ·
                refine ⟨26363043127661557370283377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17575362085107704913522251 26363043127661557370283377)
                ·
                  refine ⟨19772282345746168027712533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26363043127661557370283377 19772282345746168027712533)
                  ·
                    refine ⟨926825734956851626299025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19772282345746168027712533 926825734956851626299025)
                    ·
                      refine ⟨695119301217638719724269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 926825734956851626299025 695119301217638719724269)
                      ·
                        rfl

theorem cell23_1353740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 2, 6, 2].length) (baseStart_1353740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353740 prefixEnd_1353740 := by exact prefixLift 1353740
  have htrace : WordTrace (prefixWord ++ tailWord_1353740) baseStart_1353740 baseEnd_1353740 := by
    simpa [prefixWord, tailWord_1353740, baseEnd_1353740] using wordTrace_append hprefix tailTrace_1353740
  have hstable : (prefixWord ++ tailWord_1353740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353740).length < 2 ^ (prefixWord ++ tailWord_1353740).sum := by decide
  have hdescent : baseEnd_1353740 < baseStart_1353740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353753 : List Nat := [1, 2, 1, 2, 1, 1, 3, 3, 3, 2, 4]
def baseStart_1353753 : Nat := 118140960795 + 1353753 * 2 ^ 59
def prefixEnd_1353753 : Nat := 4983230072969 + 3 ^ 40 * 1353753 * 2
def baseEnd_1353753 : Nat := 695125976466147168861709

theorem tailTrace_1353753 : CollatzResearch.WordTrace tailWord_1353753 prefixEnd_1353753 695125976466147168861709 := by
  unfold tailWord_1353753
  simp only [CollatzResearch.WordTrace]
  refine ⟨49375428264591558450529913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32916952176394372300353275 49375428264591558450529913)
  ·
    refine ⟨37031571198443668837897435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49375428264591558450529913 37031571198443668837897435)
    ·
      refine ⟨55547356797665503256846153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37031571198443668837897435 55547356797665503256846153)
      ·
        refine ⟨41660517598249127442634615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55547356797665503256846153 41660517598249127442634615)
        ·
          refine ⟨62490776397373691163951923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41660517598249127442634615 62490776397373691163951923)
          ·
            refine ⟨93736164596060536745927885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62490776397373691163951923 93736164596060536745927885)
            ·
              refine ⟨35151061723522701279722957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93736164596060536745927885 35151061723522701279722957)
              ·
                refine ⟨13181648146321012979896109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35151061723522701279722957 13181648146321012979896109)
                ·
                  refine ⟨4943118054870379867461041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13181648146321012979896109 4943118054870379867461041)
                  ·
                    refine ⟨3707338541152784900595781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4943118054870379867461041 3707338541152784900595781)
                    ·
                      refine ⟨695125976466147168861709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3707338541152784900595781 695125976466147168861709)
                      ·
                        rfl

theorem cell23_1353753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 3, 2, 4].length) (baseStart_1353753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353753 prefixEnd_1353753 := by exact prefixLift 1353753
  have htrace : WordTrace (prefixWord ++ tailWord_1353753) baseStart_1353753 baseEnd_1353753 := by
    simpa [prefixWord, tailWord_1353753, baseEnd_1353753] using wordTrace_append hprefix tailTrace_1353753
  have hstable : (prefixWord ++ tailWord_1353753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353753).length < 2 ^ (prefixWord ++ tailWord_1353753).sum := by decide
  have hdescent : baseEnd_1353753 < baseStart_1353753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353757 : List Nat := [1, 4, 2, 2, 2, 1, 2, 3, 1, 1, 4]
def baseStart_1353757 : Nat := 118140960795 + 1353757 * 2 ^ 59
def prefixEnd_1353757 : Nat := 4983230072969 + 3 ^ 40 * 1353757 * 2
def baseEnd_1353757 : Nat := 695128030388765153211691

theorem tailTrace_1353757 : CollatzResearch.WordTrace tailWord_1353757 prefixEnd_1353757 695128030388765153211691 := by
  unfold tailWord_1353757
  simp only [CollatzResearch.WordTrace]
  refine ⟨49375574156577067133675525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32917049437718044755783683 49375574156577067133675525)
  ·
    refine ⟨9257920154358200087564161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49375574156577067133675525 9257920154358200087564161)
    ·
      refine ⟨6943440115768650065673121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9257920154358200087564161 6943440115768650065673121)
      ·
        refine ⟨5207580086826487549254841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6943440115768650065673121 5207580086826487549254841)
        ·
          refine ⟨3905685065119865661941131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5207580086826487549254841 3905685065119865661941131)
          ·
            refine ⟨5858527597679798492911697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3905685065119865661941131 5858527597679798492911697)
            ·
              refine ⟨4393895698259848869683773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5858527597679798492911697 4393895698259848869683773)
              ·
                refine ⟨1647710886847443326131415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4393895698259848869683773 1647710886847443326131415)
                ·
                  refine ⟨2471566330271164989197123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1647710886847443326131415 2471566330271164989197123)
                  ·
                    refine ⟨3707349495406747483795685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2471566330271164989197123 3707349495406747483795685)
                    ·
                      refine ⟨695128030388765153211691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3707349495406747483795685 695128030388765153211691)
                      ·
                        rfl

theorem cell23_1353757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_1353757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353757 prefixEnd_1353757 := by exact prefixLift 1353757
  have htrace : WordTrace (prefixWord ++ tailWord_1353757) baseStart_1353757 baseEnd_1353757 := by
    simpa [prefixWord, tailWord_1353757, baseEnd_1353757] using wordTrace_append hprefix tailTrace_1353757
  have hstable : (prefixWord ++ tailWord_1353757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353757).length < 2 ^ (prefixWord ++ tailWord_1353757).sum := by decide
  have hdescent : baseEnd_1353757 < baseStart_1353757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353768 : List Nat := [2, 1, 5, 3, 2, 1, 1, 1, 3, 1, 3]
def baseStart_1353768 : Nat := 118140960795 + 1353768 * 2 ^ 59
def prefixEnd_1353768 : Nat := 4983230072969 + 3 ^ 40 * 1353768 * 2
def baseEnd_1353768 : Nat := 695133678675964610174141

theorem tailTrace_1353768 : CollatzResearch.WordTrace tailWord_1353768 prefixEnd_1353768 695133678675964610174141 := by
  unfold tailWord_1353768
  simp only [CollatzResearch.WordTrace]
  refine ⟨24687987679768608006162979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32917316906358144008217305 24687987679768608006162979)
  ·
    refine ⟨37031981519652912009244469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24687987679768608006162979 37031981519652912009244469)
    ·
      refine ⟨3471748267467460500866669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 37031981519652912009244469 3471748267467460500866669)
      ·
        refine ⟨1301905600300297687825001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3471748267467460500866669 1301905600300297687825001)
        ·
          refine ⟨976429200225223265868751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1301905600300297687825001 976429200225223265868751)
          ·
            refine ⟨1464643800337834898803127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976429200225223265868751 1464643800337834898803127)
            ·
              refine ⟨2196965700506752348204691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1464643800337834898803127 2196965700506752348204691)
              ·
                refine ⟨3295448550760128522307037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2196965700506752348204691 3295448550760128522307037)
                ·
                  refine ⟨1235793206535048195865139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3295448550760128522307037 1235793206535048195865139)
                  ·
                    refine ⟨1853689809802572293797709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1235793206535048195865139 1853689809802572293797709)
                    ·
                      refine ⟨695133678675964610174141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1853689809802572293797709 695133678675964610174141)
                      ·
                        rfl

theorem cell23_1353768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_1353768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353768 prefixEnd_1353768 := by exact prefixLift 1353768
  have htrace : WordTrace (prefixWord ++ tailWord_1353768) baseStart_1353768 baseEnd_1353768 := by
    simpa [prefixWord, tailWord_1353768, baseEnd_1353768] using wordTrace_append hprefix tailTrace_1353768
  have hstable : (prefixWord ++ tailWord_1353768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353768).length < 2 ^ (prefixWord ++ tailWord_1353768).sum := by decide
  have hdescent : baseEnd_1353768 < baseStart_1353768 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353770 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_1353770 : Nat := 118140960795 + 1353770 * 2 ^ 59
def prefixEnd_1353770 : Nat := 4983230072969 + 3 ^ 40 * 1353770 * 2
def baseEnd_1353770 : Nat := 695134705637273602349131

theorem tailTrace_1353770 : CollatzResearch.WordTrace tailWord_1353770 prefixEnd_1353770 695134705637273602349131 := by
  unfold tailWord_1353770
  simp only [CollatzResearch.WordTrace]
  refine ⟨12344012076382492588474691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32917365537019980235932509 12344012076382492588474691)
  ·
    refine ⟨18516018114573738882712037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12344012076382492588474691 18516018114573738882712037)
    ·
      refine ⟨3471753396482576040508507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18516018114573738882712037 3471753396482576040508507)
      ·
        refine ⟨5207630094723864060762761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3471753396482576040508507 5207630094723864060762761)
        ·
          refine ⟨3905722571042898045572071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5207630094723864060762761 3905722571042898045572071)
          ·
            refine ⟨5858583856564347068358107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3905722571042898045572071 5858583856564347068358107)
            ·
              refine ⟨8787875784846520602537161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5858583856564347068358107 8787875784846520602537161)
              ·
                refine ⟨6590906838634890451902871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8787875784846520602537161 6590906838634890451902871)
                ·
                  refine ⟨9886360257952335677854307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6590906838634890451902871 9886360257952335677854307)
                  ·
                    refine ⟨14829540386928503516781461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9886360257952335677854307 14829540386928503516781461)
                    ·
                      refine ⟨695134705637273602349131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14829540386928503516781461 695134705637273602349131)
                      ·
                        rfl

theorem cell23_1353770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_1353770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353770 prefixEnd_1353770 := by exact prefixLift 1353770
  have htrace : WordTrace (prefixWord ++ tailWord_1353770) baseStart_1353770 baseEnd_1353770 := by
    simpa [prefixWord, tailWord_1353770, baseEnd_1353770] using wordTrace_append hprefix tailTrace_1353770
  have hstable : (prefixWord ++ tailWord_1353770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353770).length < 2 ^ (prefixWord ++ tailWord_1353770).sum := by decide
  have hdescent : baseEnd_1353770 < baseStart_1353770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353824 : List Nat := [2, 1, 1, 3, 2, 4, 2, 2, 2, 1, 3]
def baseStart_1353824 : Nat := 118140960795 + 1353824 * 2 ^ 59
def prefixEnd_1353824 : Nat := 4983230072969 + 3 ^ 40 * 1353824 * 2
def baseEnd_1353824 : Nat := 695162433592616391073883

theorem tailTrace_1353824 : CollatzResearch.WordTrace tailWord_1353824 prefixEnd_1353824 695162433592616391073883 := by
  unfold tailWord_1353824
  simp only [CollatzResearch.WordTrace]
  refine ⟨24689008923667168788182263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32918678564889558384243017 24689008923667168788182263)
  ·
    refine ⟨37033513385500753182273395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24689008923667168788182263 37033513385500753182273395)
    ·
      refine ⟨55550270078251129773410093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37033513385500753182273395 55550270078251129773410093)
      ·
        refine ⟨20831351279344173665028785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55550270078251129773410093 20831351279344173665028785)
        ·
          refine ⟨15623513459508130248771589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20831351279344173665028785 15623513459508130248771589)
          ·
            refine ⟨2929408773657774421644673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15623513459508130248771589 2929408773657774421644673)
            ·
              refine ⟨2197056580243330816233505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2929408773657774421644673 2197056580243330816233505)
              ·
                refine ⟨1647792435182498112175129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2197056580243330816233505 1647792435182498112175129)
                ·
                  refine ⟨1235844326386873584131347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1647792435182498112175129 1235844326386873584131347)
                  ·
                    refine ⟨1853766489580310376197021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1235844326386873584131347 1853766489580310376197021)
                    ·
                      refine ⟨695162433592616391073883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1853766489580310376197021 695162433592616391073883)
                      ·
                        rfl

theorem cell23_1353824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 2, 1, 3].length) (baseStart_1353824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353824 prefixEnd_1353824 := by exact prefixLift 1353824
  have htrace : WordTrace (prefixWord ++ tailWord_1353824) baseStart_1353824 baseEnd_1353824 := by
    simpa [prefixWord, tailWord_1353824, baseEnd_1353824] using wordTrace_append hprefix tailTrace_1353824
  have hstable : (prefixWord ++ tailWord_1353824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353824).length < 2 ^ (prefixWord ++ tailWord_1353824).sum := by decide
  have hdescent : baseEnd_1353824 < baseStart_1353824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353840 : List Nat := [2, 1, 1, 1, 5, 3, 1, 1, 2, 6]
def baseStart_1353840 : Nat := 118140960795 + 1353840 * 2 ^ 59
def prefixEnd_1353840 : Nat := 4983230072969 + 3 ^ 40 * 1353840 * 2
def baseEnd_1353840 : Nat := 231723549761029442824603

theorem tailTrace_1353840 : CollatzResearch.WordTrace tailWord_1353840 prefixEnd_1353840 231723549761029442824603 := by
  unfold tailWord_1353840
  simp only [CollatzResearch.WordTrace]
  refine ⟨24689300707638186154473487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32919067610184248205964649 24689300707638186154473487)
  ·
    refine ⟨37033951061457279231710231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24689300707638186154473487 37033951061457279231710231)
    ·
      refine ⟨55550926592185918847565347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37033951061457279231710231 55550926592185918847565347)
      ·
        refine ⟨83326389888278878271348021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55550926592185918847565347 83326389888278878271348021)
        ·
          refine ⟨7811849052026144837938877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83326389888278878271348021 7811849052026144837938877)
          ·
            refine ⟨2929443394509804314227079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7811849052026144837938877 2929443394509804314227079)
            ·
              refine ⟨4394165091764706471340619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2929443394509804314227079 4394165091764706471340619)
              ·
                refine ⟨6591247637647059707010929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4394165091764706471340619 6591247637647059707010929)
                ·
                  refine ⟨4943435728235294780258197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6591247637647059707010929 4943435728235294780258197)
                  ·
                    refine ⟨231723549761029442824603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4943435728235294780258197 231723549761029442824603)
                    ·
                      rfl

theorem cell23_1353840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 2, 6].length) (baseStart_1353840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353840 prefixEnd_1353840 := by exact prefixLift 1353840
  have htrace : WordTrace (prefixWord ++ tailWord_1353840) baseStart_1353840 baseEnd_1353840 := by
    simpa [prefixWord, tailWord_1353840, baseEnd_1353840] using wordTrace_append hprefix tailTrace_1353840
  have hstable : (prefixWord ++ tailWord_1353840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353840).length < 2 ^ (prefixWord ++ tailWord_1353840).sum := by decide
  have hdescent : baseEnd_1353840 < baseStart_1353840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353847 : List Nat := [1, 1, 3, 1, 1, 5, 1, 3, 1, 4, 2]
def baseStart_1353847 : Nat := 118140960795 + 1353847 * 2 ^ 59
def prefixEnd_1353847 : Nat := 4983230072969 + 3 ^ 40 * 1353847 * 2
def baseEnd_1353847 : Nat := 695174243647669801086277

theorem tailTrace_1353847 : CollatzResearch.WordTrace tailWord_1353847 prefixEnd_1353847 695174243647669801086277 := by
  unfold tailWord_1353847
  simp only [CollatzResearch.WordTrace]
  refine ⟨49378856726251012504451795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32919237817500675002967863 49378856726251012504451795)
  ·
    refine ⟨74068285089376518756677693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49378856726251012504451795 74068285089376518756677693)
    ·
      refine ⟨27775606908516194533754135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74068285089376518756677693 27775606908516194533754135)
      ·
        refine ⟨41663410362774291800631203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27775606908516194533754135 41663410362774291800631203)
        ·
          refine ⟨62495115544161437700946805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41663410362774291800631203 62495115544161437700946805)
          ·
            refine ⟨5858917082265134784463763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62495115544161437700946805 5858917082265134784463763)
            ·
              refine ⟨8788375623397702176695645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5858917082265134784463763 8788375623397702176695645)
              ·
                refine ⟨3295640858774138316260867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8788375623397702176695645 3295640858774138316260867)
                ·
                  refine ⟨4943461288161207474391301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3295640858774138316260867 4943461288161207474391301)
                  ·
                    refine ⟨926898991530226401448369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4943461288161207474391301 926898991530226401448369)
                    ·
                      refine ⟨695174243647669801086277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 926898991530226401448369 695174243647669801086277)
                      ·
                        rfl

theorem cell23_1353847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 3, 1, 4, 2].length) (baseStart_1353847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353847 prefixEnd_1353847 := by exact prefixLift 1353847
  have htrace : WordTrace (prefixWord ++ tailWord_1353847) baseStart_1353847 baseEnd_1353847 := by
    simpa [prefixWord, tailWord_1353847, baseEnd_1353847] using wordTrace_append hprefix tailTrace_1353847
  have hstable : (prefixWord ++ tailWord_1353847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353847).length < 2 ^ (prefixWord ++ tailWord_1353847).sum := by decide
  have hdescent : baseEnd_1353847 < baseStart_1353847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353860 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_1353860 : Nat := 118140960795 + 1353860 * 2 ^ 59
def prefixEnd_1353860 : Nat := 4983230072969 + 3 ^ 40 * 1353860 * 2
def baseEnd_1353860 : Nat := 695180918896178250223717

theorem tailTrace_1353860 : CollatzResearch.WordTrace tailWord_1353860 prefixEnd_1353860 695180918896178250223717 := by
  unfold tailWord_1353860
  simp only [CollatzResearch.WordTrace]
  refine ⟨24689665437601957862337517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32919553916802610483116689 24689665437601957862337517)
  ·
    refine ⟨9258624539100734198376569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24689665437601957862337517 9258624539100734198376569)
    ·
      refine ⟨6943968404325550648782427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9258624539100734198376569 6943968404325550648782427)
      ·
        refine ⟨10415952606488325973173641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6943968404325550648782427 10415952606488325973173641)
        ·
          refine ⟨7811964454866244479880231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10415952606488325973173641 7811964454866244479880231)
          ·
            refine ⟨11717946682299366719820347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7811964454866244479880231 11717946682299366719820347)
            ·
              refine ⟨17576920023449050079730521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11717946682299366719820347 17576920023449050079730521)
              ·
                refine ⟨13182690017586787559797891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17576920023449050079730521 13182690017586787559797891)
                ·
                  refine ⟨19774035026380181339696837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13182690017586787559797891 19774035026380181339696837)
                  ·
                    refine ⟨3707631567446284001193157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19774035026380181339696837 3707631567446284001193157)
                    ·
                      refine ⟨695180918896178250223717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3707631567446284001193157 695180918896178250223717)
                      ·
                        rfl

theorem cell23_1353860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_1353860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353860 prefixEnd_1353860 := by exact prefixLift 1353860
  have htrace : WordTrace (prefixWord ++ tailWord_1353860) baseStart_1353860 baseEnd_1353860 := by
    simpa [prefixWord, tailWord_1353860, baseEnd_1353860] using wordTrace_append hprefix tailTrace_1353860
  have hstable : (prefixWord ++ tailWord_1353860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353860).length < 2 ^ (prefixWord ++ tailWord_1353860).sum := by decide
  have hdescent : baseEnd_1353860 < baseStart_1353860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353864 : List Nat := [2, 1, 3, 4, 1, 1, 2, 2, 1, 4, 2]
def baseStart_1353864 : Nat := 118140960795 + 1353864 * 2 ^ 59
def prefixEnd_1353864 : Nat := 4983230072969 + 3 ^ 40 * 1353864 * 2
def baseEnd_1353864 : Nat := 695182972818796234573699

theorem tailTrace_1353864 : CollatzResearch.WordTrace tailWord_1353864 prefixEnd_1353864 695182972818796234573699 := by
  unfold tailWord_1353864
  simp only [CollatzResearch.WordTrace]
  refine ⟨24689738383594712203910323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32919651178126282938547097 24689738383594712203910323)
  ·
    refine ⟨37034607575392068305865485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24689738383594712203910323 37034607575392068305865485)
    ·
      refine ⟨13887977840772025614699557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37034607575392068305865485 13887977840772025614699557)
      ·
        refine ⟨2603995845144754802756167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13887977840772025614699557 2603995845144754802756167)
        ·
          refine ⟨3905993767717132204134251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2603995845144754802756167 3905993767717132204134251)
          ·
            refine ⟨5858990651575698306201377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3905993767717132204134251 5858990651575698306201377)
            ·
              refine ⟨4394242988681773729651033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5858990651575698306201377 4394242988681773729651033)
              ·
                refine ⟨3295682241511330297238275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4394242988681773729651033 3295682241511330297238275)
                ·
                  refine ⟨4943523362266995445857413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3295682241511330297238275 4943523362266995445857413)
                  ·
                    refine ⟨926910630425061646098265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4943523362266995445857413 926910630425061646098265)
                    ·
                      refine ⟨695182972818796234573699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 926910630425061646098265 695182972818796234573699)
                      ·
                        rfl

theorem cell23_1353864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 1, 4, 2].length) (baseStart_1353864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353864 prefixEnd_1353864 := by exact prefixLift 1353864
  have htrace : WordTrace (prefixWord ++ tailWord_1353864) baseStart_1353864 baseEnd_1353864 := by
    simpa [prefixWord, tailWord_1353864, baseEnd_1353864] using wordTrace_append hprefix tailTrace_1353864
  have hstable : (prefixWord ++ tailWord_1353864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353864).length < 2 ^ (prefixWord ++ tailWord_1353864).sum := by decide
  have hdescent : baseEnd_1353864 < baseStart_1353864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353887 : List Nat := [1, 1, 2, 6, 1, 2, 2, 1, 7]
def baseStart_1353887 : Nat := 118140960795 + 1353887 * 2 ^ 59
def prefixEnd_1353887 : Nat := 4983230072969 + 3 ^ 40 * 1353887 * 2
def baseEnd_1353887 : Nat := 77243864763761071620677

theorem tailTrace_1353887 : CollatzResearch.WordTrace tailWord_1353887 prefixEnd_1353887 77243864763761071620677 := by
  unfold tailWord_1353887
  simp only [CollatzResearch.WordTrace]
  refine ⟨49380315646106099335907915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32920210430737399557271943 49380315646106099335907915)
  ·
    refine ⟨74070473469159149003861873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49380315646106099335907915 74070473469159149003861873)
    ·
      refine ⟨55552855101869361752896405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74070473469159149003861873 55552855101869361752896405)
      ·
        refine ⟨2604040082900126332167019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55552855101869361752896405 2604040082900126332167019)
        ·
          refine ⟨3906060124350189498250529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2604040082900126332167019 3906060124350189498250529)
          ·
            refine ⟨2929545093262642123687897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3906060124350189498250529 2929545093262642123687897)
            ·
              refine ⟨2197158819946981592765923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2929545093262642123687897 2197158819946981592765923)
              ·
                refine ⟨3295738229920472389148885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2197158819946981592765923 3295738229920472389148885)
                ·
                  refine ⟨77243864763761071620677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3295738229920472389148885 77243864763761071620677)
                  ·
                    rfl

theorem cell23_1353887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 7].length) (baseStart_1353887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353887 prefixEnd_1353887 := by exact prefixLift 1353887
  have htrace : WordTrace (prefixWord ++ tailWord_1353887) baseStart_1353887 baseEnd_1353887 := by
    simpa [prefixWord, tailWord_1353887, baseEnd_1353887] using wordTrace_append hprefix tailTrace_1353887
  have hstable : (prefixWord ++ tailWord_1353887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353887).length < 2 ^ (prefixWord ++ tailWord_1353887).sum := by decide
  have hdescent : baseEnd_1353887 < baseStart_1353887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353898 : List Nat := [3, 1, 5, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_1353898 : Nat := 118140960795 + 1353898 * 2 ^ 59
def prefixEnd_1353898 : Nat := 4983230072969 + 3 ^ 40 * 1353898 * 2
def baseEnd_1353898 : Nat := 695200431161049101548543

theorem tailTrace_1353898 : CollatzResearch.WordTrace tailWord_1353898 prefixEnd_1353898 695200431161049101548543 := by
  unfold tailWord_1353898
  simp only [CollatzResearch.WordTrace]
  refine ⟨12345179212266562053639587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32920477899377498809705565 12345179212266562053639587)
  ·
    refine ⟨18517768818399843080459381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12345179212266562053639587 18517768818399843080459381)
    ·
      refine ⟨1736040826724985288793067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18517768818399843080459381 1736040826724985288793067)
      ·
        refine ⟨2604061240087477933189601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1736040826724985288793067 2604061240087477933189601)
        ·
          refine ⟨1953045930065608449892201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2604061240087477933189601 1953045930065608449892201)
          ·
            refine ⟨1464784447549206337419151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1953045930065608449892201 1464784447549206337419151)
            ·
              refine ⟨2197176671323809506128727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1464784447549206337419151 2197176671323809506128727)
              ·
                refine ⟨3295765006985714259193091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2197176671323809506128727 3295765006985714259193091)
                ·
                  refine ⟨4943647510478571388789637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3295765006985714259193091 4943647510478571388789637)
                  ·
                    refine ⟨926933908214732135398057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4943647510478571388789637 926933908214732135398057)
                    ·
                      refine ⟨695200431161049101548543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 926933908214732135398057 695200431161049101548543)
                      ·
                        rfl

theorem cell23_1353898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_1353898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353898 prefixEnd_1353898 := by exact prefixLift 1353898
  have htrace : WordTrace (prefixWord ++ tailWord_1353898) baseStart_1353898 baseEnd_1353898 := by
    simpa [prefixWord, tailWord_1353898, baseEnd_1353898] using wordTrace_append hprefix tailTrace_1353898
  have hstable : (prefixWord ++ tailWord_1353898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353898).length < 2 ^ (prefixWord ++ tailWord_1353898).sum := by decide
  have hdescent : baseEnd_1353898 < baseStart_1353898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353937 : List Nat := [1, 2, 2, 1, 2, 2, 2, 1, 4, 4, 2]
def baseStart_1353937 : Nat := 118140960795 + 1353937 * 2 ^ 59
def prefixEnd_1353937 : Nat := 4983230072969 + 3 ^ 40 * 1353937 * 2
def baseEnd_1353937 : Nat := 695220456906574448960863

theorem tailTrace_1353937 : CollatzResearch.WordTrace tailWord_1353937 prefixEnd_1353937 695220456906574448960863 := by
  unfold tailWord_1353937
  simp only [CollatzResearch.WordTrace]
  refine ⟨49382139295924957875228065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32921426197283305250152043 49382139295924957875228065)
  ·
    refine ⟨37036604471943718406421049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49382139295924957875228065 37036604471943718406421049)
    ·
      refine ⟨27777453353957788804815787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37036604471943718406421049 27777453353957788804815787)
      ·
        refine ⟨41666180030936683207223681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27777453353957788804815787 41666180030936683207223681)
        ·
          refine ⟨31249635023202512405417761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41666180030936683207223681 31249635023202512405417761)
          ·
            refine ⟨23437226267401884304063321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31249635023202512405417761 23437226267401884304063321)
            ·
              refine ⟨17577919700551413228047491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23437226267401884304063321 17577919700551413228047491)
              ·
                refine ⟨26366879550827119842071237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17577919700551413228047491 26366879550827119842071237)
                ·
                  refine ⟨4943789915780084970388357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26366879550827119842071237 4943789915780084970388357)
                  ·
                    refine ⟨926960609208765931947817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4943789915780084970388357 926960609208765931947817)
                    ·
                      refine ⟨695220456906574448960863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 926960609208765931947817 695220456906574448960863)
                      ·
                        rfl

theorem cell23_1353937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 1, 4, 4, 2].length) (baseStart_1353937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353937 prefixEnd_1353937 := by exact prefixLift 1353937
  have htrace : WordTrace (prefixWord ++ tailWord_1353937) baseStart_1353937 baseEnd_1353937 := by
    simpa [prefixWord, tailWord_1353937, baseEnd_1353937] using wordTrace_append hprefix tailTrace_1353937
  have hstable : (prefixWord ++ tailWord_1353937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353937).length < 2 ^ (prefixWord ++ tailWord_1353937).sum := by decide
  have hdescent : baseEnd_1353937 < baseStart_1353937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1353974 : List Nat := [5, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3]
def baseStart_1353974 : Nat := 118140960795 + 1353974 * 2 ^ 59
def prefixEnd_1353974 : Nat := 4983230072969 + 3 ^ 40 * 1353974 * 2
def baseEnd_1353974 : Nat := 695239455690790804198193

theorem tailTrace_1353974 : CollatzResearch.WordTrace tailWord_1353974 prefixEnd_1353974 695239455690790804198193 := by
  unfold tailWord_1353974
  simp only [CollatzResearch.WordTrace]
  refine ⟨3086468049799432074645311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32922325864527275462883317 3086468049799432074645311)
  ·
    refine ⟨4629702074699148111967967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3086468049799432074645311 4629702074699148111967967)
    ·
      refine ⟨6944553112048722167951951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4629702074699148111967967 6944553112048722167951951)
      ·
        refine ⟨10416829668073083251927927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6944553112048722167951951 10416829668073083251927927)
        ·
          refine ⟨15625244502109624877891891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10416829668073083251927927 15625244502109624877891891)
          ·
            refine ⟨23437866753164437316837837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15625244502109624877891891 23437866753164437316837837)
            ·
              refine ⟨8789200032436663993814189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23437866753164437316837837 8789200032436663993814189)
              ·
                refine ⟨3295950012163748997680321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8789200032436663993814189 3295950012163748997680321)
                ·
                  refine ⟨2471962509122811748260241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3295950012163748997680321 2471962509122811748260241)
                  ·
                    refine ⟨1853971881842108811195181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2471962509122811748260241 1853971881842108811195181)
                    ·
                      refine ⟨695239455690790804198193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1853971881842108811195181 695239455690790804198193)
                      ·
                        rfl

theorem cell23_1353974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_1353974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1353974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1353974 prefixEnd_1353974 := by exact prefixLift 1353974
  have htrace : WordTrace (prefixWord ++ tailWord_1353974) baseStart_1353974 baseEnd_1353974 := by
    simpa [prefixWord, tailWord_1353974, baseEnd_1353974] using wordTrace_append hprefix tailTrace_1353974
  have hstable : (prefixWord ++ tailWord_1353974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1353974).length < 2 ^ (prefixWord ++ tailWord_1353974).sum := by decide
  have hdescent : baseEnd_1353974 < baseStart_1353974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1353974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354007 : List Nat := [1, 1, 3, 4, 1, 2, 1, 2, 3, 5]
def baseStart_1354007 : Nat := 118140960795 + 1354007 * 2 ^ 59
def prefixEnd_1354007 : Nat := 4983230072969 + 3 ^ 40 * 1354007 * 2
def baseEnd_1354007 : Nat := 231752133517463058361847

theorem tailTrace_1354007 : CollatzResearch.WordTrace tailWord_1354007 prefixEnd_1354007 231752133517463058361847 := by
  unfold tailWord_1354007
  simp only [CollatzResearch.WordTrace]
  refine ⟨49384692405671359830276275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32923128270447573220184183 49384692405671359830276275)
  ·
    refine ⟨74077038608507039745414413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49384692405671359830276275 74077038608507039745414413)
    ·
      refine ⟨27778889478190139904530405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74077038608507039745414413 27778889478190139904530405)
      ·
        refine ⟨5208541777160651232099451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27778889478190139904530405 5208541777160651232099451)
        ·
          refine ⟨7812812665740976848149177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5208541777160651232099451 7812812665740976848149177)
          ·
            refine ⟨5859609499305732636111883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7812812665740976848149177 5859609499305732636111883)
            ·
              refine ⟨8789414248958598954167825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5859609499305732636111883 8789414248958598954167825)
              ·
                refine ⟨6592060686718949215625869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8789414248958598954167825 6592060686718949215625869)
                ·
                  refine ⟨2472022757519605955859701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6592060686718949215625869 2472022757519605955859701)
                  ·
                    refine ⟨231752133517463058361847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2472022757519605955859701 231752133517463058361847)
                    ·
                      rfl

theorem cell23_1354007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_1354007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354007 prefixEnd_1354007 := by exact prefixLift 1354007
  have htrace : WordTrace (prefixWord ++ tailWord_1354007) baseStart_1354007 baseEnd_1354007 := by
    simpa [prefixWord, tailWord_1354007, baseEnd_1354007] using wordTrace_append hprefix tailTrace_1354007
  have hstable : (prefixWord ++ tailWord_1354007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354007).length < 2 ^ (prefixWord ++ tailWord_1354007).sum := by decide
  have hdescent : baseEnd_1354007 < baseStart_1354007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354021 : List Nat := [1, 3, 1, 2, 5, 1, 1, 2, 3, 1, 3]
def baseStart_1354021 : Nat := 118140960795 + 1354021 * 2 ^ 59
def prefixEnd_1354021 : Nat := 4983230072969 + 3 ^ 40 * 1354021 * 2
def baseEnd_1354021 : Nat := 695263589281552120310477

theorem tailTrace_1354021 : CollatzResearch.WordTrace tailWord_1354021 prefixEnd_1354021 695263589281552120310477 := by
  unfold tailWord_1354021
  simp only [CollatzResearch.WordTrace]
  refine ⟨49385203027620640221285917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32923468685080426814190611 49385203027620640221285917)
  ·
    refine ⟨18519451135357740082982219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49385203027620640221285917 18519451135357740082982219)
    ·
      refine ⟨27779176703036610124473329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18519451135357740082982219 27779176703036610124473329)
      ·
        refine ⟨20834382527277457593354997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27779176703036610124473329 20834382527277457593354997)
        ·
          refine ⟨1953223361932261649377031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20834382527277457593354997 1953223361932261649377031)
          ·
            refine ⟨2929835042898392474065547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1953223361932261649377031 2929835042898392474065547)
            ·
              refine ⟨4394752564347588711098321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2929835042898392474065547 4394752564347588711098321)
              ·
                refine ⟨3296064423260691533323741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4394752564347588711098321 3296064423260691533323741)
                ·
                  refine ⟨1236024158722759324996403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3296064423260691533323741 1236024158722759324996403)
                  ·
                    refine ⟨1854036238084138987494605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1236024158722759324996403 1854036238084138987494605)
                    ·
                      refine ⟨695263589281552120310477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1854036238084138987494605 695263589281552120310477)
                      ·
                        rfl

theorem cell23_1354021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 1, 3].length) (baseStart_1354021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354021 prefixEnd_1354021 := by exact prefixLift 1354021
  have htrace : WordTrace (prefixWord ++ tailWord_1354021) baseStart_1354021 baseEnd_1354021 := by
    simpa [prefixWord, tailWord_1354021, baseEnd_1354021] using wordTrace_append hprefix tailTrace_1354021
  have hstable : (prefixWord ++ tailWord_1354021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354021).length < 2 ^ (prefixWord ++ tailWord_1354021).sum := by decide
  have hdescent : baseEnd_1354021 < baseStart_1354021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354037 : List Nat := [1, 3, 3, 1, 2, 1, 1, 4, 1, 6]
def baseStart_1354037 : Nat := 118140960795 + 1354037 * 2 ^ 59
def prefixEnd_1354037 : Nat := 4983230072969 + 3 ^ 40 * 1354037 * 2
def baseEnd_1354037 : Nat := 231757268324008019236801

theorem tailTrace_1354037 : CollatzResearch.WordTrace tailWord_1354037 prefixEnd_1354037 231757268324008019236801 := by
  unfold tailWord_1354037
  simp only [CollatzResearch.WordTrace]
  refine ⟨49385786595562674953868365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32923857730375116635912243 49385786595562674953868365)
  ·
    refine ⟨18519669973336003107700637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49385786595562674953868365 18519669973336003107700637)
    ·
      refine ⟨6944876240001001165387739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18519669973336003107700637 6944876240001001165387739)
      ·
        refine ⟨10417314360001501748081609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6944876240001001165387739 10417314360001501748081609)
        ·
          refine ⟨7812985770001126311061207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10417314360001501748081609 7812985770001126311061207)
          ·
            refine ⟨11719478655001689466591811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7812985770001126311061207 11719478655001689466591811)
            ·
              refine ⟨17579217982502534199887717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11719478655001689466591811 17579217982502534199887717)
              ·
                refine ⟨3296103371719225162478947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17579217982502534199887717 3296103371719225162478947)
                ·
                  refine ⟨4944155057578837743718421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3296103371719225162478947 4944155057578837743718421)
                  ·
                    refine ⟨231757268324008019236801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4944155057578837743718421 231757268324008019236801)
                    ·
                      rfl

theorem cell23_1354037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_1354037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354037 prefixEnd_1354037 := by exact prefixLift 1354037
  have htrace : WordTrace (prefixWord ++ tailWord_1354037) baseStart_1354037 baseEnd_1354037 := by
    simpa [prefixWord, tailWord_1354037, baseEnd_1354037] using wordTrace_append hprefix tailTrace_1354037
  have hstable : (prefixWord ++ tailWord_1354037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354037).length < 2 ^ (prefixWord ++ tailWord_1354037).sum := by decide
  have hdescent : baseEnd_1354037 < baseStart_1354037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354041 : List Nat := [1, 2, 1, 6, 1, 1, 4, 1, 1, 5]
def baseStart_1354041 : Nat := 118140960795 + 1354041 * 2 ^ 59
def prefixEnd_1354041 : Nat := 4983230072969 + 3 ^ 40 * 1354041 * 2
def baseEnd_1354041 : Nat := 231757952964880680686795

theorem tailTrace_1354041 : CollatzResearch.WordTrace tailWord_1354041 prefixEnd_1354041 231757952964880680686795 := by
  unfold tailWord_1354041
  simp only [CollatzResearch.WordTrace]
  refine ⟨49385932487548183637013977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32923954991698789091342651 49385932487548183637013977)
  ·
    refine ⟨37039449365661137727760483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49385932487548183637013977 37039449365661137727760483)
    ·
      refine ⟨55559174048491706591640725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37039449365661137727760483 55559174048491706591640725)
      ·
        refine ⟨2604336283523048746483159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 55559174048491706591640725 2604336283523048746483159)
        ·
          refine ⟨3906504425284573119724739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2604336283523048746483159 3906504425284573119724739)
          ·
            refine ⟨5859756637926859679587109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3906504425284573119724739 5859756637926859679587109)
            ·
              refine ⟨1098704369611286189922583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5859756637926859679587109 1098704369611286189922583)
              ·
                refine ⟨1648056554416929284883875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098704369611286189922583 1648056554416929284883875)
                ·
                  refine ⟨2472084831625393927325813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1648056554416929284883875 2472084831625393927325813)
                  ·
                    refine ⟨231757952964880680686795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2472084831625393927325813 231757952964880680686795)
                    ·
                      rfl

theorem cell23_1354041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 4, 1, 1, 5].length) (baseStart_1354041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354041 prefixEnd_1354041 := by exact prefixLift 1354041
  have htrace : WordTrace (prefixWord ++ tailWord_1354041) baseStart_1354041 baseEnd_1354041 := by
    simpa [prefixWord, tailWord_1354041, baseEnd_1354041] using wordTrace_append hprefix tailTrace_1354041
  have hstable : (prefixWord ++ tailWord_1354041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354041).length < 2 ^ (prefixWord ++ tailWord_1354041).sum := by decide
  have hdescent : baseEnd_1354041 < baseStart_1354041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354044 : List Nat := [2, 2, 2, 2, 1, 2, 3, 3, 1, 1, 4]
def baseStart_1354044 : Nat := 118140960795 + 1354044 * 2 ^ 59
def prefixEnd_1354044 : Nat := 4983230072969 + 3 ^ 40 * 1354044 * 2
def baseEnd_1354044 : Nat := 695275399336605530322871

theorem tailTrace_1354044 : CollatzResearch.WordTrace tailWord_1354044 prefixEnd_1354044 695275399336605530322871 := by
  unfold tailWord_1354044
  simp only [CollatzResearch.WordTrace]
  refine ⟨24693020953268657574686593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32924027937691543432915457 24693020953268657574686593)
  ·
    refine ⟨18519765714951493181014945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24693020953268657574686593 18519765714951493181014945)
    ·
      refine ⟨13889824286213619885761209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18519765714951493181014945 13889824286213619885761209)
      ·
        refine ⟨10417368214660214914320907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13889824286213619885761209 10417368214660214914320907)
        ·
          refine ⟨15626052321990322371481361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10417368214660214914320907 15626052321990322371481361)
          ·
            refine ⟨11719539241492741778611021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15626052321990322371481361 11719539241492741778611021)
            ·
              refine ⟨4394827215559778166979133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11719539241492741778611021 4394827215559778166979133)
              ·
                refine ⟨1648060205834916812617175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4394827215559778166979133 1648060205834916812617175)
                ·
                  refine ⟨2472090308752375218925763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1648060205834916812617175 2472090308752375218925763)
                  ·
                    refine ⟨3708135463128562828388645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2472090308752375218925763 3708135463128562828388645)
                    ·
                      refine ⟨695275399336605530322871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3708135463128562828388645 695275399336605530322871)
                      ·
                        rfl

theorem cell23_1354044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_1354044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354044 prefixEnd_1354044 := by exact prefixLift 1354044
  have htrace : WordTrace (prefixWord ++ tailWord_1354044) baseStart_1354044 baseEnd_1354044 := by
    simpa [prefixWord, tailWord_1354044, baseEnd_1354044] using wordTrace_append hprefix tailTrace_1354044
  have hstable : (prefixWord ++ tailWord_1354044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354044).length < 2 ^ (prefixWord ++ tailWord_1354044).sum := by decide
  have hdescent : baseEnd_1354044 < baseStart_1354044 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354047 : List Nat := [1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 5]
def baseStart_1354047 : Nat := 118140960795 + 1354047 * 2 ^ 59
def prefixEnd_1354047 : Nat := 4983230072969 + 3 ^ 40 * 1354047 * 2
def baseEnd_1354047 : Nat := 695276939778569018585357

theorem tailTrace_1354047 : CollatzResearch.WordTrace tailWord_1354047 prefixEnd_1354047 695276939778569018585357 := by
  unfold tailWord_1354047
  simp only [CollatzResearch.WordTrace]
  refine ⟨49386151325526446661732395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32924100883684297774488263 49386151325526446661732395)
  ·
    refine ⟨74079226988289669992598593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49386151325526446661732395 74079226988289669992598593)
    ·
      refine ⟨55559420241217252494448945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74079226988289669992598593 55559420241217252494448945)
      ·
        refine ⟨41669565180912939370836709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55559420241217252494448945 41669565180912939370836709)
        ·
          refine ⟨7813043471421176132031883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41669565180912939370836709 7813043471421176132031883)
          ·
            refine ⟨11719565207131764198047825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7813043471421176132031883 11719565207131764198047825)
            ·
              refine ⟨8789673905348823148535869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11719565207131764198047825 8789673905348823148535869)
              ·
                refine ⟨3296127714505808680700951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8789673905348823148535869 3296127714505808680700951)
                ·
                  refine ⟨4944191571758713021051427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3296127714505808680700951 4944191571758713021051427)
                  ·
                    refine ⟨7416287357638069531577141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4944191571758713021051427 7416287357638069531577141)
                    ·
                      refine ⟨695276939778569018585357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7416287357638069531577141 695276939778569018585357)
                      ·
                        rfl

theorem cell23_1354047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_1354047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354047 prefixEnd_1354047 := by exact prefixLift 1354047
  have htrace : WordTrace (prefixWord ++ tailWord_1354047) baseStart_1354047 baseEnd_1354047 := by
    simpa [prefixWord, tailWord_1354047, baseEnd_1354047] using wordTrace_append hprefix tailTrace_1354047
  have hstable : (prefixWord ++ tailWord_1354047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354047).length < 2 ^ (prefixWord ++ tailWord_1354047).sum := by decide
  have hdescent : baseEnd_1354047 < baseStart_1354047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354071 : List Nat := [1, 1, 3, 2, 3, 1, 5, 1, 2, 4]
def baseStart_1354071 : Nat := 118140960795 + 1354071 * 2 ^ 59
def prefixEnd_1354071 : Nat := 4983230072969 + 3 ^ 40 * 1354071 * 2
def baseEnd_1354071 : Nat := 231763087771425641561749

theorem tailTrace_1354071 : CollatzResearch.WordTrace tailWord_1354071 prefixEnd_1354071 231763087771425641561749 := by
  unfold tailWord_1354071
  simp only [CollatzResearch.WordTrace]
  refine ⟨49387026677439498760606067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32924684451626332507070711 49387026677439498760606067)
  ·
    refine ⟨74080540016159248140909101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49387026677439498760606067 74080540016159248140909101)
    ·
      refine ⟨27780202506059718052840913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74080540016159248140909101 27780202506059718052840913)
      ·
        refine ⟨20835151879544788539630685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27780202506059718052840913 20835151879544788539630685)
        ·
          refine ⟨7813181954829295702361507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20835151879544788539630685 7813181954829295702361507)
          ·
            refine ⟨11719772932243943553542261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7813181954829295702361507 11719772932243943553542261)
            ·
              refine ⟨1098728712397869708144587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11719772932243943553542261 1098728712397869708144587)
              ·
                refine ⟨1648093068596804562216881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098728712397869708144587 1648093068596804562216881)
                ·
                  refine ⟨1236069801447603421662661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1648093068596804562216881 1236069801447603421662661)
                  ·
                    refine ⟨231763087771425641561749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1236069801447603421662661 231763087771425641561749)
                    ·
                      rfl

theorem cell23_1354071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 5, 1, 2, 4].length) (baseStart_1354071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354071 prefixEnd_1354071 := by exact prefixLift 1354071
  have htrace : WordTrace (prefixWord ++ tailWord_1354071) baseStart_1354071 baseEnd_1354071 := by
    simpa [prefixWord, tailWord_1354071, baseEnd_1354071] using wordTrace_append hprefix tailTrace_1354071
  have hstable : (prefixWord ++ tailWord_1354071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354071).length < 2 ^ (prefixWord ++ tailWord_1354071).sum := by decide
  have hdescent : baseEnd_1354071 < baseStart_1354071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354117 : List Nat := [1, 3, 1, 1, 3, 1, 1, 3, 2, 3, 4]
def baseStart_1354117 : Nat := 118140960795 + 1354117 * 2 ^ 59
def prefixEnd_1354117 : Nat := 4983230072969 + 3 ^ 40 * 1354117 * 2
def baseEnd_1354117 : Nat := 695312883424383744710035

theorem tailTrace_1354117 : CollatzResearch.WordTrace tailWord_1354117 prefixEnd_1354117 695312883424383744710035 := by
  unfold tailWord_1354117
  simp only [CollatzResearch.WordTrace]
  refine ⟨49388704435272848616780605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32925802956848565744520403 49388704435272848616780605)
  ·
    refine ⟨18520764163227318231292727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49388704435272848616780605 18520764163227318231292727)
    ·
      refine ⟨27781146244840977346939091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18520764163227318231292727 27781146244840977346939091)
      ·
        refine ⟨41671719367261466020408637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27781146244840977346939091 41671719367261466020408637)
        ·
          refine ⟨15626894762723049757653239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41671719367261466020408637 15626894762723049757653239)
          ·
            refine ⟨23440342144084574636479859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15626894762723049757653239 23440342144084574636479859)
            ·
              refine ⟨35160513216126861954719789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23440342144084574636479859 35160513216126861954719789)
              ·
                refine ⟨13185192456047573233019921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35160513216126861954719789 13185192456047573233019921)
                ·
                  refine ⟨9888894342035679924764941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13185192456047573233019921 9888894342035679924764941)
                  ·
                    refine ⟨3708335378263379971786853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9888894342035679924764941 3708335378263379971786853)
                    ·
                      refine ⟨695312883424383744710035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3708335378263379971786853 695312883424383744710035)
                      ·
                        rfl

theorem cell23_1354117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 3, 2, 3, 4].length) (baseStart_1354117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354117 prefixEnd_1354117 := by exact prefixLift 1354117
  have htrace : WordTrace (prefixWord ++ tailWord_1354117) baseStart_1354117 baseEnd_1354117 := by
    simpa [prefixWord, tailWord_1354117, baseEnd_1354117] using wordTrace_append hprefix tailTrace_1354117
  have hstable : (prefixWord ++ tailWord_1354117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354117).length < 2 ^ (prefixWord ++ tailWord_1354117).sum := by decide
  have hdescent : baseEnd_1354117 < baseStart_1354117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354122 : List Nat := [3, 1, 2, 5, 2, 1, 2, 1, 2, 4]
def baseStart_1354122 : Nat := 118140960795 + 1354122 * 2 ^ 59
def prefixEnd_1354122 : Nat := 4983230072969 + 3 ^ 40 * 1354122 * 2
def baseEnd_1354122 : Nat := 231771816942552075049171

theorem tailTrace_1354122 : CollatzResearch.WordTrace tailWord_1354122 prefixEnd_1354122 231771816942552075049171 := by
  unfold tailWord_1354122
  simp only [CollatzResearch.WordTrace]
  refine ⟨12347221700063683617678155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32925924533503156313808413 12347221700063683617678155)
  ·
    refine ⟨18520832550095525426517233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12347221700063683617678155 18520832550095525426517233)
    ·
      refine ⟨13890624412571644069887925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18520832550095525426517233 13890624412571644069887925)
      ·
        refine ⟨1302246038678591631551993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13890624412571644069887925 1302246038678591631551993)
        ·
          refine ⟨976684529008943723663995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1302246038678591631551993 976684529008943723663995)
          ·
            refine ⟨1465026793513415585495993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 976684529008943723663995 1465026793513415585495993)
            ·
              refine ⟨1098770095135061689121995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1465026793513415585495993 1098770095135061689121995)
              ·
                refine ⟨1648155142702592533682993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1098770095135061689121995 1648155142702592533682993)
                ·
                  refine ⟨1236116357026944400262245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1648155142702592533682993 1236116357026944400262245)
                  ·
                    refine ⟨231771816942552075049171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1236116357026944400262245 231771816942552075049171)
                    ·
                      rfl

theorem cell23_1354122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_1354122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354122 prefixEnd_1354122 := by exact prefixLift 1354122
  have htrace : WordTrace (prefixWord ++ tailWord_1354122) baseStart_1354122 baseEnd_1354122 := by
    simpa [prefixWord, tailWord_1354122, baseEnd_1354122] using wordTrace_append hprefix tailTrace_1354122
  have hstable : (prefixWord ++ tailWord_1354122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354122).length < 2 ^ (prefixWord ++ tailWord_1354122).sum := by decide
  have hdescent : baseEnd_1354122 < baseStart_1354122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354137 : List Nat := [1, 2, 1, 2, 1, 4, 1, 1, 4, 1, 5]
def baseStart_1354137 : Nat := 118140960795 + 1354137 * 2 ^ 59
def prefixEnd_1354137 : Nat := 4983230072969 + 3 ^ 40 * 1354137 * 2
def baseEnd_1354137 : Nat := 695323153037473666459943

theorem tailTrace_1354137 : CollatzResearch.WordTrace tailWord_1354137 prefixEnd_1354137 695323153037473666459943 := by
  unfold tailWord_1354137
  simp only [CollatzResearch.WordTrace]
  refine ⟨49389433895200392032508665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32926289263466928021672443 49389433895200392032508665)
  ·
    refine ⟨37042075421400294024381499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49389433895200392032508665 37042075421400294024381499)
    ·
      refine ⟨55563113132100441036572249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37042075421400294024381499 55563113132100441036572249)
      ·
        refine ⟨41672334849075330777429187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55563113132100441036572249 41672334849075330777429187)
        ·
          refine ⟨62508502273612996166143781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41672334849075330777429187 62508502273612996166143781)
          ·
            refine ⟨11720344176302436781151959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62508502273612996166143781 11720344176302436781151959)
            ·
              refine ⟨17580516264453655171727939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11720344176302436781151959 17580516264453655171727939)
              ·
                refine ⟨26370774396680482757591909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17580516264453655171727939 26370774396680482757591909)
                ·
                  refine ⟨4944520199377590517048483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26370774396680482757591909 4944520199377590517048483)
                  ·
                    refine ⟨7416780299066385775572725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4944520199377590517048483 7416780299066385775572725)
                    ·
                      refine ⟨695323153037473666459943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7416780299066385775572725 695323153037473666459943)
                      ·
                        rfl

theorem cell23_1354137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 1, 5].length) (baseStart_1354137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354137 prefixEnd_1354137 := by exact prefixLift 1354137
  have htrace : WordTrace (prefixWord ++ tailWord_1354137) baseStart_1354137 baseEnd_1354137 := by
    simpa [prefixWord, tailWord_1354137, baseEnd_1354137] using wordTrace_append hprefix tailTrace_1354137
  have hstable : (prefixWord ++ tailWord_1354137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354137).length < 2 ^ (prefixWord ++ tailWord_1354137).sum := by decide
  have hdescent : baseEnd_1354137 < baseStart_1354137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354138 : List Nat := [3, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2]
def baseStart_1354138 : Nat := 118140960795 + 1354138 * 2 ^ 59
def prefixEnd_1354138 : Nat := 4983230072969 + 3 ^ 40 * 1354138 * 2
def baseEnd_1354138 : Nat := 695323666518128162547439

theorem tailTrace_1354138 : CollatzResearch.WordTrace tailWord_1354138 prefixEnd_1354138 695323666518128162547439 := by
  unfold tailWord_1354138
  simp only [CollatzResearch.WordTrace]
  refine ⟨12347367592049192300823767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32926313578797846135530045 12347367592049192300823767)
  ·
    refine ⟨18521051388073788451235651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12347367592049192300823767 18521051388073788451235651)
    ·
      refine ⟨27781577082110682676853477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18521051388073788451235651 27781577082110682676853477)
      ·
        refine ⟨5209045702895753001910027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27781577082110682676853477 5209045702895753001910027)
        ·
          refine ⟨7813568554343629502865041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5209045702895753001910027 7813568554343629502865041)
          ·
            refine ⟨5860176415757722127148781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7813568554343629502865041 5860176415757722127148781)
            ·
              refine ⟨2197566155909145797680793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5860176415757722127148781 2197566155909145797680793)
              ·
                refine ⟨1648174616931859348260595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2197566155909145797680793 1648174616931859348260595)
                ·
                  refine ⟨2472261925397789022390893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1648174616931859348260595 2472261925397789022390893)
                  ·
                    refine ⟨927098222024170883396585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2472261925397789022390893 927098222024170883396585)
                    ·
                      refine ⟨695323666518128162547439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 927098222024170883396585 695323666518128162547439)
                      ·
                        rfl

theorem cell23_1354138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_1354138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354138 prefixEnd_1354138 := by exact prefixLift 1354138
  have htrace : WordTrace (prefixWord ++ tailWord_1354138) baseStart_1354138 baseEnd_1354138 := by
    simpa [prefixWord, tailWord_1354138, baseEnd_1354138] using wordTrace_append hprefix tailTrace_1354138
  have hstable : (prefixWord ++ tailWord_1354138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354138).length < 2 ^ (prefixWord ++ tailWord_1354138).sum := by decide
  have hdescent : baseEnd_1354138 < baseStart_1354138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354151 : List Nat := [1, 1, 6, 1, 1, 2, 1, 1, 3, 4, 2]
def baseStart_1354151 : Nat := 118140960795 + 1354151 * 2 ^ 59
def prefixEnd_1354151 : Nat := 4983230072969 + 3 ^ 40 * 1354151 * 2
def baseEnd_1354151 : Nat := 695330341766636611684879

theorem tailTrace_1354151 : CollatzResearch.WordTrace tailWord_1354151 prefixEnd_1354151 695330341766636611684879 := by
  unfold tailWord_1354151
  simp only [CollatzResearch.WordTrace]
  refine ⟨49389944517149672423518307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32926629678099781615678871 49389944517149672423518307)
  ·
    refine ⟨74084916775724508635277461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49389944517149672423518307 74084916775724508635277461)
    ·
      refine ⟨3472730473862086342278631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 74084916775724508635277461 3472730473862086342278631)
      ·
        refine ⟨5209095710793129513417947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3472730473862086342278631 5209095710793129513417947)
        ·
          refine ⟨7813643566189694270126921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5209095710793129513417947 7813643566189694270126921)
          ·
            refine ⟨5860232674642270702595191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7813643566189694270126921 5860232674642270702595191)
            ·
              refine ⟨8790349011963406053892787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5860232674642270702595191 8790349011963406053892787)
              ·
                refine ⟨13185523517945109080839181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8790349011963406053892787 13185523517945109080839181)
                ·
                  refine ⟨4944571319229415905314693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13185523517945109080839181 4944571319229415905314693)
                  ·
                    refine ⟨927107122355515482246505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4944571319229415905314693 927107122355515482246505)
                    ·
                      refine ⟨695330341766636611684879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 927107122355515482246505 695330341766636611684879)
                      ·
                        rfl

theorem cell23_1354151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_1354151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354151 prefixEnd_1354151 := by exact prefixLift 1354151
  have htrace : WordTrace (prefixWord ++ tailWord_1354151) baseStart_1354151 baseEnd_1354151 := by
    simpa [prefixWord, tailWord_1354151, baseEnd_1354151] using wordTrace_append hprefix tailTrace_1354151
  have hstable : (prefixWord ++ tailWord_1354151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354151).length < 2 ^ (prefixWord ++ tailWord_1354151).sum := by decide
  have hdescent : baseEnd_1354151 < baseStart_1354151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354184 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 1, 5, 3]
def baseStart_1354184 : Nat := 118140960795 + 1354184 * 2 ^ 59
def prefixEnd_1354184 : Nat := 4983230072969 + 3 ^ 40 * 1354184 * 2
def baseEnd_1354184 : Nat := 695347286628234982572227

theorem tailTrace_1354184 : CollatzResearch.WordTrace tailWord_1354184 prefixEnd_1354184 695347286628234982572227 := by
  unfold tailWord_1354184
  simp only [CollatzResearch.WordTrace]
  refine ⟨24695574063015059529734803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32927432084020079372979737 24695574063015059529734803)
  ·
    refine ⟨37043361094522589294602205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24695574063015059529734803 37043361094522589294602205)
    ·
      refine ⟨13891260410445970985475827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37043361094522589294602205 13891260410445970985475827)
      ·
        refine ⟨20836890615668956478213741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13891260410445970985475827 20836890615668956478213741)
        ·
          refine ⟨7813833980875858679330153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20836890615668956478213741 7813833980875858679330153)
          ·
            refine ⟨5860375485656894009497615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7813833980875858679330153 5860375485656894009497615)
            ·
              refine ⟨8790563228485341014246423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5860375485656894009497615 8790563228485341014246423)
              ·
                refine ⟨13185844842728011521369635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8790563228485341014246423 13185844842728011521369635)
                ·
                  refine ⟨19778767264092017282054453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13185844842728011521369635 19778767264092017282054453)
                  ·
                    refine ⟨1854259431008626620192605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19778767264092017282054453 1854259431008626620192605)
                    ·
                      refine ⟨695347286628234982572227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1854259431008626620192605 695347286628234982572227)
                      ·
                        rfl

theorem cell23_1354184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 1, 5, 3].length) (baseStart_1354184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354184 prefixEnd_1354184 := by exact prefixLift 1354184
  have htrace : WordTrace (prefixWord ++ tailWord_1354184) baseStart_1354184 baseEnd_1354184 := by
    simpa [prefixWord, tailWord_1354184, baseEnd_1354184] using wordTrace_append hprefix tailTrace_1354184
  have hstable : (prefixWord ++ tailWord_1354184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354184).length < 2 ^ (prefixWord ++ tailWord_1354184).sum := by decide
  have hdescent : baseEnd_1354184 < baseStart_1354184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354187 : List Nat := [1, 1, 1, 1, 3, 3, 1, 4, 1, 7]
def baseStart_1354187 : Nat := 118140960795 + 1354187 * 2 ^ 59
def prefixEnd_1354187 : Nat := 4983230072969 + 3 ^ 40 * 1354187 * 2
def baseEnd_1354187 : Nat := 231782942356732823611571

theorem tailTrace_1354187 : CollatzResearch.WordTrace tailWord_1354187 prefixEnd_1354187 231782942356732823611571 := by
  unfold tailWord_1354187
  simp only [CollatzResearch.WordTrace]
  refine ⟨49391257545019250571828815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32927505030012833714552543 49391257545019250571828815)
  ·
    refine ⟨74086886317528875857743223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49391257545019250571828815 74086886317528875857743223)
    ·
      refine ⟨111130329476293313786614835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74086886317528875857743223 111130329476293313786614835)
      ·
        refine ⟨166695494214439970679922253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111130329476293313786614835 166695494214439970679922253)
        ·
          refine ⟨62510810330414989004970845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 166695494214439970679922253 62510810330414989004970845)
          ·
            refine ⟨23441553873905620876864067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62510810330414989004970845 23441553873905620876864067)
            ·
              refine ⟨35162330810858431315296101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23441553873905620876864067 35162330810858431315296101)
              ·
                refine ⟨6592937027035955871618019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35162330810858431315296101 6592937027035955871618019)
                ·
                  refine ⟨9889405540553933807427029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6592937027035955871618019 9889405540553933807427029)
                  ·
                    refine ⟨231782942356732823611571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9889405540553933807427029 231782942356732823611571)
                    ·
                      rfl

theorem cell23_1354187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 7].length) (baseStart_1354187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354187 prefixEnd_1354187 := by exact prefixLift 1354187
  have htrace : WordTrace (prefixWord ++ tailWord_1354187) baseStart_1354187 baseEnd_1354187 := by
    simpa [prefixWord, tailWord_1354187, baseEnd_1354187] using wordTrace_append hprefix tailTrace_1354187
  have hstable : (prefixWord ++ tailWord_1354187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354187).length < 2 ^ (prefixWord ++ tailWord_1354187).sum := by decide
  have hdescent : baseEnd_1354187 < baseStart_1354187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354224 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 4]
def baseStart_1354224 : Nat := 118140960795 + 1354224 * 2 ^ 59
def prefixEnd_1354224 : Nat := 4983230072969 + 3 ^ 40 * 1354224 * 2
def baseEnd_1354224 : Nat := 695367825854414826072043

theorem tailTrace_1354224 : CollatzResearch.WordTrace tailWord_1354224 prefixEnd_1354224 695367825854414826072043 := by
  unfold tailWord_1354224
  simp only [CollatzResearch.WordTrace]
  refine ⟨24696303522942602945462863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32928404697256803927283817 24696303522942602945462863)
  ·
    refine ⟨37044455284413904418194295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24696303522942602945462863 37044455284413904418194295)
    ·
      refine ⟨55566682926620856627291443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37044455284413904418194295 55566682926620856627291443)
      ·
        refine ⟨83350024389931284940937165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55566682926620856627291443 83350024389931284940937165)
        ·
          refine ⟨31256259146224231852851437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83350024389931284940937165 31256259146224231852851437)
          ·
            refine ⟨11721097179834086944819289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31256259146224231852851437 11721097179834086944819289)
            ·
              refine ⟨8790822884875565208614467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11721097179834086944819289 8790822884875565208614467)
              ·
                refine ⟨13186234327313347812921701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8790822884875565208614467 13186234327313347812921701)
                ·
                  refine ⟨2472418936371252714922819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13186234327313347812921701 2472418936371252714922819)
                  ·
                    refine ⟨3708628404556879072384229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2472418936371252714922819 3708628404556879072384229)
                    ·
                      refine ⟨695367825854414826072043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3708628404556879072384229 695367825854414826072043)
                      ·
                        rfl

theorem cell23_1354224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 4, 1, 4].length) (baseStart_1354224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354224 prefixEnd_1354224 := by exact prefixLift 1354224
  have htrace : WordTrace (prefixWord ++ tailWord_1354224) baseStart_1354224 baseEnd_1354224 := by
    simpa [prefixWord, tailWord_1354224, baseEnd_1354224] using wordTrace_append hprefix tailTrace_1354224
  have hstable : (prefixWord ++ tailWord_1354224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354224).length < 2 ^ (prefixWord ++ tailWord_1354224).sum := by decide
  have hdescent : baseEnd_1354224 < baseStart_1354224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354251 : List Nat := [1, 1, 1, 1, 7, 1, 2, 2, 3, 4]
def baseStart_1354251 : Nat := 118140960795 + 1354251 * 2 ^ 59
def prefixEnd_1354251 : Nat := 4983230072969 + 3 ^ 40 * 1354251 * 2
def baseEnd_1354251 : Nat := 231793896610695406811473

theorem tailTrace_1354251 : CollatzResearch.WordTrace tailWord_1354251 prefixEnd_1354251 231793896610695406811473 := by
  unfold tailWord_1354251
  simp only [CollatzResearch.WordTrace]
  refine ⟨49393591816787389502158607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32929061211191593001439071 49393591816787389502158607)
  ·
    refine ⟨74090387725181084253237911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49393591816787389502158607 74090387725181084253237911)
    ·
      refine ⟨111135581587771626379856867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74090387725181084253237911 111135581587771626379856867)
      ·
        refine ⟨166703372381657439569785301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111135581587771626379856867 166703372381657439569785301)
        ·
          refine ⟨3907110290195096239916843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 166703372381657439569785301 3907110290195096239916843)
          ·
            refine ⟨5860665435292644359875265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3907110290195096239916843 5860665435292644359875265)
            ·
              refine ⟨4395499076469483269906449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5860665435292644359875265 4395499076469483269906449)
              ·
                refine ⟨3296624307352112452429837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4395499076469483269906449 3296624307352112452429837)
                ·
                  refine ⟨1236234115257042169661189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3296624307352112452429837 1236234115257042169661189)
                  ·
                    refine ⟨231793896610695406811473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1236234115257042169661189 231793896610695406811473)
                    ·
                      rfl

theorem cell23_1354251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3, 4].length) (baseStart_1354251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354251 prefixEnd_1354251 := by exact prefixLift 1354251
  have htrace : WordTrace (prefixWord ++ tailWord_1354251) baseStart_1354251 baseEnd_1354251 := by
    simpa [prefixWord, tailWord_1354251, baseEnd_1354251] using wordTrace_append hprefix tailTrace_1354251
  have hstable : (prefixWord ++ tailWord_1354251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354251).length < 2 ^ (prefixWord ++ tailWord_1354251).sum := by decide
  have hdescent : baseEnd_1354251 < baseStart_1354251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354261 : List Nat := [1, 3, 2, 1, 3, 1, 2, 3, 2, 2, 3]
def baseStart_1354261 : Nat := 118140960795 + 1354261 * 2 ^ 59
def prefixEnd_1354261 : Nat := 4983230072969 + 3 ^ 40 * 1354261 * 2
def baseEnd_1354261 : Nat := 695386824638631181309373

theorem tailTrace_1354261 : CollatzResearch.WordTrace tailWord_1354261 prefixEnd_1354261 695386824638631181309373 := by
  unfold tailWord_1354261
  simp only [CollatzResearch.WordTrace]
  refine ⟨49393956546751161210022637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32929304364500774140015091 49393956546751161210022637)
  ·
    refine ⟨18522733705031685453758489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49393956546751161210022637 18522733705031685453758489)
    ·
      refine ⟨13892050278773764090318867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18522733705031685453758489 13892050278773764090318867)
      ·
        refine ⟨20838075418160646135478301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13892050278773764090318867 20838075418160646135478301)
        ·
          refine ⟨7814278281810242300804363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20838075418160646135478301 7814278281810242300804363)
          ·
            refine ⟨11721417422715363451206545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7814278281810242300804363 11721417422715363451206545)
            ·
              refine ⟨8791063067036522588404909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11721417422715363451206545 8791063067036522588404909)
              ·
                refine ⟨3296648650138695970651841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8791063067036522588404909 3296648650138695970651841)
                ·
                  refine ⟨2472486487604021977988881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3296648650138695970651841 2472486487604021977988881)
                  ·
                    refine ⟨1854364865703016483491661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2472486487604021977988881 1854364865703016483491661)
                    ·
                      refine ⟨695386824638631181309373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1854364865703016483491661 695386824638631181309373)
                      ·
                        rfl

theorem cell23_1354261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 2, 3].length) (baseStart_1354261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354261 prefixEnd_1354261 := by exact prefixLift 1354261
  have htrace : WordTrace (prefixWord ++ tailWord_1354261) baseStart_1354261 baseEnd_1354261 := by
    simpa [prefixWord, tailWord_1354261, baseEnd_1354261] using wordTrace_append hprefix tailTrace_1354261
  have hstable : (prefixWord ++ tailWord_1354261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354261).length < 2 ^ (prefixWord ++ tailWord_1354261).sum := by decide
  have hdescent : baseEnd_1354261 < baseStart_1354261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1354264 : List Nat := [2, 1, 2, 3, 3, 1, 1, 2, 8]
def baseStart_1354264 : Nat := 118140960795 + 1354264 * 2 ^ 59
def prefixEnd_1354264 : Nat := 4983230072969 + 3 ^ 40 * 1354264 * 2
def baseEnd_1354264 : Nat := 77265373897843852174651

theorem tailTrace_1354264 : CollatzResearch.WordTrace tailWord_1354264 prefixEnd_1354264 77265373897843852174651 := by
  unfold tailWord_1354264
  simp only [CollatzResearch.WordTrace]
  refine ⟨24697032982870146361190923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32929377310493528481587897 24697032982870146361190923)
  ·
    refine ⟨37045549474305219541786385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24697032982870146361190923 37045549474305219541786385)
    ·
      refine ⟨27784162105728914656339789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37045549474305219541786385 27784162105728914656339789)
      ·
        refine ⟨10419060789648342996127421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27784162105728914656339789 10419060789648342996127421)
        ·
          refine ⟨3907147796118128623547783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10419060789648342996127421 3907147796118128623547783)
          ·
            refine ⟨5860721694177192935321675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3907147796118128623547783 5860721694177192935321675)
            ·
              refine ⟨8791082541265789402982513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5860721694177192935321675 8791082541265789402982513)
              ·
                refine ⟨6593311905949342052236885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8791082541265789402982513 6593311905949342052236885)
                ·
                  refine ⟨77265373897843852174651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6593311905949342052236885 77265373897843852174651)
                  ·
                    rfl

theorem cell23_1354264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 2, 8].length) (baseStart_1354264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1354264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1354264 prefixEnd_1354264 := by exact prefixLift 1354264
  have htrace : WordTrace (prefixWord ++ tailWord_1354264) baseStart_1354264 baseEnd_1354264 := by
    simpa [prefixWord, tailWord_1354264, baseEnd_1354264] using wordTrace_append hprefix tailTrace_1354264
  have hstable : (prefixWord ++ tailWord_1354264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1354264).length < 2 ^ (prefixWord ++ tailWord_1354264).sum := by decide
  have hdescent : baseEnd_1354264 < baseStart_1354264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1354264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
