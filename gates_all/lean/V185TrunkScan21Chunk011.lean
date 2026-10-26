import V185TrunkScan21Chunk010

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_130708 : List Nat := [2, 4, 2, 2, 2, 9]
def baseStart_130708 : Nat := 118140960795 + 130708 * 2 ^ 59
def prefixEnd_130708 : Nat := 4983230072969 + 3 ^ 40 * 130708 * 2
def baseEnd_130708 : Nat := 1104790607209544659241

theorem tailTrace_130708 : CollatzResearch.WordTrace tailWord_130708 prefixEnd_130708 1104790607209544659241 := by
  unfold tailWord_130708
  simp only [CollatzResearch.WordTrace]
  refine ⟨2383656205237356997136389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3178208273649809329515185 2383656205237356997136389)
  ·
    refine ⟨446935538482004436963073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2383656205237356997136389 446935538482004436963073)
    ·
      refine ⟨335201653861503327722305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 446935538482004436963073 335201653861503327722305)
      ·
        refine ⟨251401240396127495791729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 335201653861503327722305 251401240396127495791729)
        ·
          refine ⟨188550930297095621843797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251401240396127495791729 188550930297095621843797)
          ·
            refine ⟨1104790607209544659241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 188550930297095621843797 1104790607209544659241)
            ·
              rfl

theorem cell21_130708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 2, 9].length) (baseStart_130708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130708 prefixEnd_130708 := by exact prefixLift 130708
  have htrace : WordTrace (prefixWord ++ tailWord_130708) baseStart_130708 baseEnd_130708 := by
    simpa [prefixWord, tailWord_130708, baseEnd_130708] using wordTrace_append hprefix tailTrace_130708
  have hstable : (prefixWord ++ tailWord_130708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130708).length < 2 ^ (prefixWord ++ tailWord_130708).sum := by decide
  have hdescent : baseEnd_130708 < baseStart_130708 := by decide
  rcases family_descends (prefixWord ++ tailWord_130708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130742 : List Nat := [5, 1, 3, 1, 1, 2, 3, 5]
def baseStart_130742 : Nat := 118140960795 + 130742 * 2 ^ 59
def prefixEnd_130742 : Nat := 4983230072969 + 3 ^ 40 * 130742 * 2
def baseEnd_130742 : Nat := 9945701885960400744257

theorem tailTrace_130742 : CollatzResearch.WordTrace tailWord_130742 prefixEnd_130742 9945701885960400744257 := by
  unfold tailWord_130742
  simp only [CollatzResearch.WordTrace]
  refine ⟨298034530771971112563155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3179034994901025200673653 298034530771971112563155)
  ·
    refine ⟨447051796157956668844733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 298034530771971112563155 447051796157956668844733)
    ·
      refine ⟨167644423559233750816775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 447051796157956668844733 167644423559233750816775)
      ·
        refine ⟨251466635338850626225163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 167644423559233750816775 251466635338850626225163)
        ·
          refine ⟨377199953008275939337745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 251466635338850626225163 377199953008275939337745)
          ·
            refine ⟨282899964756206954503309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 377199953008275939337745 282899964756206954503309)
            ·
              refine ⟨106087486783577607938741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282899964756206954503309 106087486783577607938741)
              ·
                refine ⟨9945701885960400744257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106087486783577607938741 9945701885960400744257)
                ·
                  rfl

theorem cell21_130742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_130742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130742 prefixEnd_130742 := by exact prefixLift 130742
  have htrace : WordTrace (prefixWord ++ tailWord_130742) baseStart_130742 baseEnd_130742 := by
    simpa [prefixWord, tailWord_130742, baseEnd_130742] using wordTrace_append hprefix tailTrace_130742
  have hstable : (prefixWord ++ tailWord_130742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130742).length < 2 ^ (prefixWord ++ tailWord_130742).sum := by decide
  have hdescent : baseEnd_130742 < baseStart_130742 := by decide
  rcases family_descends (prefixWord ++ tailWord_130742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130756 : List Nat := [2, 3, 3, 1, 1, 1, 4, 3, 3]
def baseStart_130756 : Nat := 118140960795 + 130756 * 2 ^ 59
def prefixEnd_130756 : Nat := 4983230072969 + 3 ^ 40 * 130756 * 2
def baseEnd_130756 : Nat := 29840300648620288999409

theorem tailTrace_130756 : CollatzResearch.WordTrace tailWord_130756 prefixEnd_130756 29840300648620288999409 := by
  unfold tailWord_130756
  simp only [CollatzResearch.WordTrace]
  refine ⟨2384531557150409096010061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3179375409533878794680081 2384531557150409096010061)
  ·
    refine ⟨894199333931403411003773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2384531557150409096010061 894199333931403411003773)
    ·
      refine ⟨335324750224276279126415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 894199333931403411003773 335324750224276279126415)
      ·
        refine ⟨502987125336414418689623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 335324750224276279126415 502987125336414418689623)
        ·
          refine ⟨754480688004621628034435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 502987125336414418689623 754480688004621628034435)
          ·
            refine ⟨1131721032006932442051653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754480688004621628034435 1131721032006932442051653)
            ·
              refine ⟨212197693501299832884685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1131721032006932442051653 212197693501299832884685)
              ·
                refine ⟨79574135062987437331757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212197693501299832884685 79574135062987437331757)
                ·
                  refine ⟨29840300648620288999409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79574135062987437331757 29840300648620288999409)
                  ·
                    rfl

theorem cell21_130756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_130756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130756 prefixEnd_130756 := by exact prefixLift 130756
  have htrace : WordTrace (prefixWord ++ tailWord_130756) baseStart_130756 baseEnd_130756 := by
    simpa [prefixWord, tailWord_130756, baseEnd_130756] using wordTrace_append hprefix tailTrace_130756
  have hstable : (prefixWord ++ tailWord_130756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130756).length < 2 ^ (prefixWord ++ tailWord_130756).sum := by decide
  have hdescent : baseEnd_130756 < baseStart_130756 := by decide
  rcases family_descends (prefixWord ++ tailWord_130756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130770 : List Nat := [3, 2, 2, 2, 2, 1, 3, 2, 4]
def baseStart_130770 : Nat := 118140960795 + 130770 * 2 ^ 59
def prefixEnd_130770 : Nat := 4983230072969 + 3 ^ 40 * 130770 * 2
def baseEnd_130770 : Nat := 29843495639359375766047

theorem tailTrace_130770 : CollatzResearch.WordTrace tailWord_130770 prefixEnd_130770 29843495639359375766047 := by
  unfold tailWord_130770
  simp only [CollatzResearch.WordTrace]
  refine ⟨1192393434062524645757441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3179715824166732388686509 1192393434062524645757441)
  ·
    refine ⟨894295075546893484318081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1192393434062524645757441 894295075546893484318081)
    ·
      refine ⟨670721306660170113238561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 894295075546893484318081 670721306660170113238561)
      ·
        refine ⟨503040979995127584928921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 670721306660170113238561 503040979995127584928921)
        ·
          refine ⟨377280734996345688696691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 503040979995127584928921 377280734996345688696691)
          ·
            refine ⟨565921102494518533045037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 377280734996345688696691 565921102494518533045037)
            ·
              refine ⟨212220413435444449891889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 565921102494518533045037 212220413435444449891889)
              ·
                refine ⟨159165310076583337418917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212220413435444449891889 159165310076583337418917)
                ·
                  refine ⟨29843495639359375766047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159165310076583337418917 29843495639359375766047)
                  ·
                    rfl

theorem cell21_130770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 2, 4].length) (baseStart_130770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130770 prefixEnd_130770 := by exact prefixLift 130770
  have htrace : WordTrace (prefixWord ++ tailWord_130770) baseStart_130770 baseEnd_130770 := by
    simpa [prefixWord, tailWord_130770, baseEnd_130770] using wordTrace_append hprefix tailTrace_130770
  have hstable : (prefixWord ++ tailWord_130770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130770).length < 2 ^ (prefixWord ++ tailWord_130770).sum := by decide
  have hdescent : baseEnd_130770 < baseStart_130770 := by decide
  rcases family_descends (prefixWord ++ tailWord_130770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130787 : List Nat := [1, 1, 1, 7, 2, 1, 3, 1, 4]
def baseStart_130787 : Nat := 118140960795 + 130787 * 2 ^ 59
def prefixEnd_130787 : Nat := 4983230072969 + 3 ^ 40 * 130787 * 2
def baseEnd_130787 : Nat := 29847375270971123982679

theorem tailTrace_130787 : CollatzResearch.WordTrace tailWord_130787 prefixEnd_130787 29847375270971123982679 := by
  unfold tailWord_130787
  simp only [CollatzResearch.WordTrace]
  refine ⟨4770193777188510486398615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3180129184792340324265743 4770193777188510486398615)
  ·
    refine ⟨7155290665782765729597923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4770193777188510486398615 7155290665782765729597923)
    ·
      refine ⟨10732935998674148594396885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7155290665782765729597923 10732935998674148594396885)
      ·
        refine ⟨251553187468925357681177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 10732935998674148594396885 251553187468925357681177)
        ·
          refine ⟨188664890601694018260883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 251553187468925357681177 188664890601694018260883)
          ·
            refine ⟨282997335902541027391325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 188664890601694018260883 282997335902541027391325)
            ·
              refine ⟨106124000963452885271747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 282997335902541027391325 106124000963452885271747)
              ·
                refine ⟨159186001445179327907621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106124000963452885271747 159186001445179327907621)
                ·
                  refine ⟨29847375270971123982679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159186001445179327907621 29847375270971123982679)
                  ·
                    rfl

theorem cell21_130787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 4].length) (baseStart_130787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130787 prefixEnd_130787 := by exact prefixLift 130787
  have htrace : WordTrace (prefixWord ++ tailWord_130787) baseStart_130787 baseEnd_130787 := by
    simpa [prefixWord, tailWord_130787, baseEnd_130787] using wordTrace_append hprefix tailTrace_130787
  have hstable : (prefixWord ++ tailWord_130787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130787).length < 2 ^ (prefixWord ++ tailWord_130787).sum := by decide
  have hdescent : baseEnd_130787 < baseStart_130787 := by decide
  rcases family_descends (prefixWord ++ tailWord_130787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130798 : List Nat := [4, 1, 2, 1, 1, 2, 1, 4, 5]
def baseStart_130798 : Nat := 118140960795 + 130798 * 2 ^ 59
def prefixEnd_130798 : Nat := 4983230072969 + 3 ^ 40 * 130798 * 2
def baseEnd_130798 : Nat := 29849885620837549299323

theorem tailTrace_130798 : CollatzResearch.WordTrace tailWord_130798 prefixEnd_130798 29849885620837549299323 := by
  unfold tailWord_130798
  simp only [CollatzResearch.WordTrace]
  refine ⟨596324372518582420631131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3180396653432439576699365 596324372518582420631131)
  ·
    refine ⟨894486558777873630946697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 596324372518582420631131 894486558777873630946697)
    ·
      refine ⟨670864919083405223210023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 894486558777873630946697 670864919083405223210023)
      ·
        refine ⟨1006297378625107834815035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 670864919083405223210023 1006297378625107834815035)
        ·
          refine ⟨1509446067937661752222553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1006297378625107834815035 1509446067937661752222553)
          ·
            refine ⟨1132084550953246314166915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1509446067937661752222553 1132084550953246314166915)
            ·
              refine ⟨1698126826429869471250373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132084550953246314166915 1698126826429869471250373)
              ·
                refine ⟨318398779955600525859445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1698126826429869471250373 318398779955600525859445)
                ·
                  refine ⟨29849885620837549299323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 318398779955600525859445 29849885620837549299323)
                  ·
                    rfl

theorem cell21_130798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_130798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130798 prefixEnd_130798 := by exact prefixLift 130798
  have htrace : WordTrace (prefixWord ++ tailWord_130798) baseStart_130798 baseEnd_130798 := by
    simpa [prefixWord, tailWord_130798, baseEnd_130798] using wordTrace_append hprefix tailTrace_130798
  have hstable : (prefixWord ++ tailWord_130798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130798).length < 2 ^ (prefixWord ++ tailWord_130798).sum := by decide
  have hdescent : baseEnd_130798 < baseStart_130798 := by decide
  rcases family_descends (prefixWord ++ tailWord_130798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130812 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 8]
def baseStart_130812 : Nat := 118140960795 + 130812 * 2 ^ 59
def prefixEnd_130812 : Nat := 4983230072969 + 3 ^ 40 * 130812 * 2
def baseEnd_130812 : Nat := 29853080611576636065961

theorem tailTrace_130812 : CollatzResearch.WordTrace tailWord_130812 prefixEnd_130812 29853080611576636065961 := by
  unfold tailWord_130812
  simp only [CollatzResearch.WordTrace]
  refine ⟨2385552801048969878029345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3180737068065293170705793 2385552801048969878029345)
  ·
    refine ⟨1789164600786727408522009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2385552801048969878029345 1789164600786727408522009)
    ·
      refine ⟨1341873450590045556391507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1789164600786727408522009 1341873450590045556391507)
      ·
        refine ⟨2012810175885068334587261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1341873450590045556391507 2012810175885068334587261)
        ·
          refine ⟨754803815956900625470223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2012810175885068334587261 754803815956900625470223)
          ·
            refine ⟨1132205723935350938205335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 754803815956900625470223 1132205723935350938205335)
            ·
              refine ⟨1698308585903026407308003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1132205723935350938205335 1698308585903026407308003)
              ·
                refine ⟨2547462878854539610962005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1698308585903026407308003 2547462878854539610962005)
                ·
                  refine ⟨29853080611576636065961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2547462878854539610962005 29853080611576636065961)
                  ·
                    rfl

theorem cell21_130812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 8].length) (baseStart_130812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130812 prefixEnd_130812 := by exact prefixLift 130812
  have htrace : WordTrace (prefixWord ++ tailWord_130812) baseStart_130812 baseEnd_130812 := by
    simpa [prefixWord, tailWord_130812, baseEnd_130812] using wordTrace_append hprefix tailTrace_130812
  have hstable : (prefixWord ++ tailWord_130812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130812).length < 2 ^ (prefixWord ++ tailWord_130812).sum := by decide
  have hdescent : baseEnd_130812 < baseStart_130812 := by decide
  rcases family_descends (prefixWord ++ tailWord_130812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_130815 : List Nat := [1, 1, 2, 2, 1, 3, 5, 3, 3]
def baseStart_130815 : Nat := 118140960795 + 130815 * 2 ^ 59
def prefixEnd_130815 : Nat := 4983230072969 + 3 ^ 40 * 130815 * 2
def baseEnd_130815 : Nat := 29853765252449297515955

theorem tailTrace_130815 : CollatzResearch.WordTrace tailWord_130815 prefixEnd_130815 29853765252449297515955 := by
  unfold tailWord_130815
  simp only [CollatzResearch.WordTrace]
  refine ⟨4771215021087071268417899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3180810014058047512278599 4771215021087071268417899)
  ·
    refine ⟨7156822531630606902626849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4771215021087071268417899 7156822531630606902626849)
    ·
      refine ⟨5367616898722955176970137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7156822531630606902626849 5367616898722955176970137)
      ·
        refine ⟨4025712674042216382727603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5367616898722955176970137 4025712674042216382727603)
        ·
          refine ⟨6038569011063324574091405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4025712674042216382727603 6038569011063324574091405)
          ·
            refine ⟨2264463379148746715284277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6038569011063324574091405 2264463379148746715284277)
            ·
              refine ⟨212293441795195004557901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2264463379148746715284277 212293441795195004557901)
              ·
                refine ⟨79610040673198126709213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 212293441795195004557901 79610040673198126709213)
                ·
                  refine ⟨29853765252449297515955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 79610040673198126709213 29853765252449297515955)
                  ·
                    rfl

theorem cell21_130815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 3, 3].length) (baseStart_130815 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_130815 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_130815 prefixEnd_130815 := by exact prefixLift 130815
  have htrace : WordTrace (prefixWord ++ tailWord_130815) baseStart_130815 baseEnd_130815 := by
    simpa [prefixWord, tailWord_130815, baseEnd_130815] using wordTrace_append hprefix tailTrace_130815
  have hstable : (prefixWord ++ tailWord_130815).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_130815).length < 2 ^ (prefixWord ++ tailWord_130815).sum := by decide
  have hdescent : baseEnd_130815 < baseStart_130815 := by decide
  rcases family_descends (prefixWord ++ tailWord_130815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131116 : List Nat := [2, 2, 1, 1, 1, 2, 2, 6, 4]
def baseStart_131116 : Nat := 118140960795 + 131116 * 2 ^ 59
def prefixEnd_131116 : Nat := 4983230072969 + 3 ^ 40 * 131116 * 2
def baseEnd_131116 : Nat := 29922457553339662998673

theorem tailTrace_131116 : CollatzResearch.WordTrace tailWord_131116 prefixEnd_131116 29922457553339662998673 := by
  unfold tailWord_131116
  simp only [CollatzResearch.WordTrace]
  refine ⟨2391096696498299837562601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3188128928664399783416801 2391096696498299837562601)
  ·
    refine ⟨1793322522373724878171951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2391096696498299837562601 1793322522373724878171951)
    ·
      refine ⟨2689983783560587317257927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1793322522373724878171951 2689983783560587317257927)
      ·
        refine ⟨4034975675340880975886891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2689983783560587317257927 4034975675340880975886891)
        ·
          refine ⟨6052463513011321463830337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4034975675340880975886891 6052463513011321463830337)
          ·
            refine ⟨4539347634758491097872753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6052463513011321463830337 4539347634758491097872753)
            ·
              refine ⟨3404510726068868323404565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4539347634758491097872753 3404510726068868323404565)
              ·
                refine ⟨159586440284478202659589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3404510726068868323404565 159586440284478202659589)
                ·
                  refine ⟨29922457553339662998673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159586440284478202659589 29922457553339662998673)
                  ·
                    rfl

theorem cell21_131116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 4].length) (baseStart_131116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131116 prefixEnd_131116 := by exact prefixLift 131116
  have htrace : WordTrace (prefixWord ++ tailWord_131116) baseStart_131116 baseEnd_131116 := by
    simpa [prefixWord, tailWord_131116, baseEnd_131116] using wordTrace_append hprefix tailTrace_131116
  have hstable : (prefixWord ++ tailWord_131116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131116).length < 2 ^ (prefixWord ++ tailWord_131116).sum := by decide
  have hdescent : baseEnd_131116 < baseStart_131116 := by decide
  rcases family_descends (prefixWord ++ tailWord_131116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131130 : List Nat := [3, 1, 1, 1, 3, 1, 1, 10]
def baseStart_131130 : Nat := 118140960795 + 131130 * 2 ^ 59
def prefixEnd_131130 : Nat := 4983230072969 + 3 ^ 40 * 131130 * 2
def baseEnd_131130 : Nat := 9975217514692916588437

theorem tailTrace_131130 : CollatzResearch.WordTrace tailWord_131130 prefixEnd_131130 9975217514692916588437 := by
  unfold tailWord_131130
  simp only [CollatzResearch.WordTrace]
  refine ⟨1195676003736470016533711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3188469343297253377423229 1195676003736470016533711)
  ·
    refine ⟨1793514005604705024800567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1195676003736470016533711 1793514005604705024800567)
    ·
      refine ⟨2690271008407057537200851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1793514005604705024800567 2690271008407057537200851)
      ·
        refine ⟨4035406512610586305801277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2690271008407057537200851 4035406512610586305801277)
        ·
          refine ⟨1513277442228969864675479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4035406512610586305801277 1513277442228969864675479)
          ·
            refine ⟨2269916163343454797013219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1513277442228969864675479 2269916163343454797013219)
            ·
              refine ⟨3404874245015182195519829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2269916163343454797013219 3404874245015182195519829)
              ·
                refine ⟨9975217514692916588437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3404874245015182195519829 9975217514692916588437)
                ·
                  rfl

theorem cell21_131130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 10].length) (baseStart_131130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131130 prefixEnd_131130 := by exact prefixLift 131130
  have htrace : WordTrace (prefixWord ++ tailWord_131130) baseStart_131130 baseEnd_131130 := by
    simpa [prefixWord, tailWord_131130, baseEnd_131130] using wordTrace_append hprefix tailTrace_131130
  have hstable : (prefixWord ++ tailWord_131130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131130).length < 2 ^ (prefixWord ++ tailWord_131130).sum := by decide
  have hdescent : baseEnd_131130 < baseStart_131130 := by decide
  rcases family_descends (prefixWord ++ tailWord_131130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131223 : List Nat := [1, 1, 3, 3, 5, 8]
def baseStart_131223 : Nat := 118140960795 + 131223 * 2 ^ 59
def prefixEnd_131223 : Nat := 4983230072969 + 3 ^ 40 * 131223 * 2
def baseEnd_131223 : Nat := 1109143570782639063523

theorem tailTrace_131223 : CollatzResearch.WordTrace tailWord_131223 prefixEnd_131223 1109143570782639063523 := by
  unfold tailWord_131223
  simp only [CollatzResearch.WordTrace]
  refine ⟨4786096003608956949270323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3190730669072637966180215 4786096003608956949270323)
  ·
    refine ⟨7179144005413435423905485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4786096003608956949270323 7179144005413435423905485)
    ·
      refine ⟨2692179002030038283964557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7179144005413435423905485 2692179002030038283964557)
      ·
        refine ⟨1009567125761264356486709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2692179002030038283964557 1009567125761264356486709)
        ·
          refine ⟨94646918040118533420629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1009567125761264356486709 94646918040118533420629)
          ·
            refine ⟨1109143570782639063523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 94646918040118533420629 1109143570782639063523)
            ·
              rfl

theorem cell21_131223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 8].length) (baseStart_131223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131223 prefixEnd_131223 := by exact prefixLift 131223
  have htrace : WordTrace (prefixWord ++ tailWord_131223) baseStart_131223 baseEnd_131223 := by
    simpa [prefixWord, tailWord_131223, baseEnd_131223] using wordTrace_append hprefix tailTrace_131223
  have hstable : (prefixWord ++ tailWord_131223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131223).length < 2 ^ (prefixWord ++ tailWord_131223).sum := by decide
  have hdescent : baseEnd_131223 < baseStart_131223 := by decide
  rcases family_descends (prefixWord ++ tailWord_131223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131226 : List Nat := [3, 1, 1, 5, 2, 1, 2, 2, 4]
def baseStart_131226 : Nat := 118140960795 + 131226 * 2 ^ 59
def prefixEnd_131226 : Nat := 4983230072969 + 3 ^ 40 * 131226 * 2
def baseEnd_131226 : Nat := 29947561052003916165115

theorem tailTrace_131226 : CollatzResearch.WordTrace tailWord_131226 prefixEnd_131226 29947561052003916165115 := by
  unfold tailWord_131226
  simp only [CollatzResearch.WordTrace]
  refine ⟨1196551355649522115407383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3190803615065392307753021 1196551355649522115407383)
  ·
    refine ⟨1794827033474283173111075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1196551355649522115407383 1794827033474283173111075)
    ·
      refine ⟨2692240550211424759666613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1794827033474283173111075 2692240550211424759666613)
      ·
        refine ⟨252397551582321071218745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2692240550211424759666613 252397551582321071218745)
        ·
          refine ⟨189298163686740803414059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252397551582321071218745 189298163686740803414059)
          ·
            refine ⟨283947245530111205121089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189298163686740803414059 283947245530111205121089)
            ·
              refine ⟨212960434147583403840817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 283947245530111205121089 212960434147583403840817)
              ·
                refine ⟨159720325610687552880613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 212960434147583403840817 159720325610687552880613)
                ·
                  refine ⟨29947561052003916165115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159720325610687552880613 29947561052003916165115)
                  ·
                    rfl

theorem cell21_131226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 4].length) (baseStart_131226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131226 prefixEnd_131226 := by exact prefixLift 131226
  have htrace : WordTrace (prefixWord ++ tailWord_131226) baseStart_131226 baseEnd_131226 := by
    simpa [prefixWord, tailWord_131226, baseEnd_131226] using wordTrace_append hprefix tailTrace_131226
  have hstable : (prefixWord ++ tailWord_131226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131226).length < 2 ^ (prefixWord ++ tailWord_131226).sum := by decide
  have hdescent : baseEnd_131226 < baseStart_131226 := by decide
  rcases family_descends (prefixWord ++ tailWord_131226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131237 : List Nat := [1, 3, 1, 2, 1, 3, 2, 3, 5]
def baseStart_131237 : Nat := 118140960795 + 131237 * 2 ^ 59
def prefixEnd_131237 : Nat := 4983230072969 + 3 ^ 40 * 131237 * 2
def baseEnd_131237 : Nat := 29950071401870341481759

theorem tailTrace_131237 : CollatzResearch.WordTrace tailWord_131237 prefixEnd_131237 29950071401870341481759 := by
  unfold tailWord_131237
  simp only [CollatzResearch.WordTrace]
  refine ⟨4786606625558237340279965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3191071083705491560186643 4786606625558237340279965)
  ·
    refine ⟨1794977484584339002604987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4786606625558237340279965 1794977484584339002604987)
    ·
      refine ⟨2692466226876508503907481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1794977484584339002604987 2692466226876508503907481)
      ·
        refine ⟨2019349670157381377930611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2692466226876508503907481 2019349670157381377930611)
        ·
          refine ⟨3029024505236072066895917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2019349670157381377930611 3029024505236072066895917)
          ·
            refine ⟨1135884189463527025085969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3029024505236072066895917 1135884189463527025085969)
            ·
              refine ⟨851913142097645268814477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1135884189463527025085969 851913142097645268814477)
              ·
                refine ⟨319467428286616975805429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 851913142097645268814477 319467428286616975805429)
                ·
                  refine ⟨29950071401870341481759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 319467428286616975805429 29950071401870341481759)
                  ·
                    rfl

theorem cell21_131237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_131237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131237 prefixEnd_131237 := by exact prefixLift 131237
  have htrace : WordTrace (prefixWord ++ tailWord_131237) baseStart_131237 baseEnd_131237 := by
    simpa [prefixWord, tailWord_131237, baseEnd_131237] using wordTrace_append hprefix tailTrace_131237
  have hstable : (prefixWord ++ tailWord_131237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131237).length < 2 ^ (prefixWord ++ tailWord_131237).sum := by decide
  have hdescent : baseEnd_131237 < baseStart_131237 := by decide
  rcases family_descends (prefixWord ++ tailWord_131237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131251 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 8]
def baseStart_131251 : Nat := 118140960795 + 131251 * 2 ^ 59
def prefixEnd_131251 : Nat := 4983230072969 + 3 ^ 40 * 131251 * 2
def baseEnd_131251 : Nat := 29953266392609428248397

theorem tailTrace_131251 : CollatzResearch.WordTrace tailWord_131251 prefixEnd_131251 29953266392609428248397 := by
  unfold tailWord_131251
  simp only [CollatzResearch.WordTrace]
  refine ⟨4787117247507517731289607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3191411498338345154193071 4787117247507517731289607)
  ·
    refine ⟨7180675871261276596934411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4787117247507517731289607 7180675871261276596934411)
    ·
      refine ⟨10771013806891914895401617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7180675871261276596934411 10771013806891914895401617)
      ·
        refine ⟨8078260355168936171551213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10771013806891914895401617 8078260355168936171551213)
        ·
          refine ⟨3029347633188351064331705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8078260355168936171551213 3029347633188351064331705)
          ·
            refine ⟨2272010724891263298248779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3029347633188351064331705 2272010724891263298248779)
            ·
              refine ⟨3408016087336894947373169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2272010724891263298248779 3408016087336894947373169)
              ·
                refine ⟨2556012065502671210529877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3408016087336894947373169 2556012065502671210529877)
                ·
                  refine ⟨29953266392609428248397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2556012065502671210529877 29953266392609428248397)
                  ·
                    rfl

theorem cell21_131251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 8].length) (baseStart_131251 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131251 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131251 prefixEnd_131251 := by exact prefixLift 131251
  have htrace : WordTrace (prefixWord ++ tailWord_131251) baseStart_131251 baseEnd_131251 := by
    simpa [prefixWord, tailWord_131251, baseEnd_131251] using wordTrace_append hprefix tailTrace_131251
  have hstable : (prefixWord ++ tailWord_131251).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131251).length < 2 ^ (prefixWord ++ tailWord_131251).sum := by decide
  have hdescent : baseEnd_131251 < baseStart_131251 := by decide
  rcases family_descends (prefixWord ++ tailWord_131251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131285 : List Nat := [1, 3, 2, 4, 2, 1, 1, 1, 6]
def baseStart_131285 : Nat := 118140960795 + 131285 * 2 ^ 59
def prefixEnd_131285 : Nat := 4983230072969 + 3 ^ 40 * 131285 * 2
def baseEnd_131285 : Nat := 29961025655832924681661

theorem tailTrace_131285 : CollatzResearch.WordTrace tailWord_131285 prefixEnd_131285 29961025655832924681661 := by
  unfold tailWord_131285
  simp only [CollatzResearch.WordTrace]
  refine ⟨4788357329384341538027309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3192238219589561025351539 4788357329384341538027309)
  ·
    refine ⟨1795633998519128076760241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4788357329384341538027309 1795633998519128076760241)
    ·
      refine ⟨1346725498889346057570181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1795633998519128076760241 1346725498889346057570181)
      ·
        refine ⟨252511031041752385794409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1346725498889346057570181 252511031041752385794409)
        ·
          refine ⟨189383273281314289345807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 252511031041752385794409 189383273281314289345807)
          ·
            refine ⟨284074909921971434018711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 189383273281314289345807 284074909921971434018711)
            ·
              refine ⟨426112364882957151028067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 284074909921971434018711 426112364882957151028067)
              ·
                refine ⟨639168547324435726542101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 426112364882957151028067 639168547324435726542101)
                ·
                  refine ⟨29961025655832924681661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 639168547324435726542101 29961025655832924681661)
                  ·
                    rfl

theorem cell21_131285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 1, 1, 6].length) (baseStart_131285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131285 prefixEnd_131285 := by exact prefixLift 131285
  have htrace : WordTrace (prefixWord ++ tailWord_131285) baseStart_131285 baseEnd_131285 := by
    simpa [prefixWord, tailWord_131285, baseEnd_131285] using wordTrace_append hprefix tailTrace_131285
  have hstable : (prefixWord ++ tailWord_131285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131285).length < 2 ^ (prefixWord ++ tailWord_131285).sum := by decide
  have hdescent : baseEnd_131285 < baseStart_131285 := by decide
  rcases family_descends (prefixWord ++ tailWord_131285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131313 : List Nat := [1, 2, 2, 2, 2, 1, 4, 2, 5]
def baseStart_131313 : Nat := 118140960795 + 131313 * 2 ^ 59
def prefixEnd_131313 : Nat := 4983230072969 + 3 ^ 40 * 131313 * 2
def baseEnd_131313 : Nat := 29967415637311098214937

theorem tailTrace_131313 : CollatzResearch.WordTrace tailWord_131313 prefixEnd_131313 29967415637311098214937 := by
  unfold tailWord_131313
  simp only [CollatzResearch.WordTrace]
  refine ⟨4789378573282902320046593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3192919048855268213364395 4789378573282902320046593)
  ·
    refine ⟨3592033929962176740034945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4789378573282902320046593 3592033929962176740034945)
    ·
      refine ⟨2694025447471632555026209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3592033929962176740034945 2694025447471632555026209)
      ·
        refine ⟨2020519085603724416269657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2694025447471632555026209 2020519085603724416269657)
        ·
          refine ⟨1515389314202793312202243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2020519085603724416269657 1515389314202793312202243)
          ·
            refine ⟨2273083971304189968303365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1515389314202793312202243 2273083971304189968303365)
            ·
              refine ⟨426203244619535619056881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2273083971304189968303365 426203244619535619056881)
              ·
                refine ⟨319652433464651714292661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 426203244619535619056881 319652433464651714292661)
                ·
                  refine ⟨29967415637311098214937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 319652433464651714292661 29967415637311098214937)
                  ·
                    rfl

theorem cell21_131313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 4, 2, 5].length) (baseStart_131313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131313 prefixEnd_131313 := by exact prefixLift 131313
  have htrace : WordTrace (prefixWord ++ tailWord_131313) baseStart_131313 baseEnd_131313 := by
    simpa [prefixWord, tailWord_131313, baseEnd_131313] using wordTrace_append hprefix tailTrace_131313
  have hstable : (prefixWord ++ tailWord_131313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131313).length < 2 ^ (prefixWord ++ tailWord_131313).sum := by decide
  have hdescent : baseEnd_131313 < baseStart_131313 := by decide
  rcases family_descends (prefixWord ++ tailWord_131313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131327 : List Nat := [1, 1, 2, 2, 1, 4, 1, 1, 8]
def baseStart_131327 : Nat := 118140960795 + 131327 * 2 ^ 59
def prefixEnd_131327 : Nat := 4983230072969 + 3 ^ 40 * 131327 * 2
def baseEnd_131327 : Nat := 29970610628050184981575

theorem tailTrace_131327 : CollatzResearch.WordTrace tailWord_131327 prefixEnd_131327 29970610628050184981575 := by
  unfold tailWord_131327
  simp only [CollatzResearch.WordTrace]
  refine ⟨4789889195232182711056235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3193259463488121807370823 4789889195232182711056235)
  ·
    refine ⟨7184833792848274066584353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4789889195232182711056235 7184833792848274066584353)
    ·
      refine ⟨5388625344636205549938265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7184833792848274066584353 5388625344636205549938265)
      ·
        refine ⟨4041469008477154162453699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5388625344636205549938265 4041469008477154162453699)
        ·
          refine ⟨6062203512715731243680549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4041469008477154162453699 6062203512715731243680549)
          ·
            refine ⟨1136663158634199608190103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6062203512715731243680549 1136663158634199608190103)
            ·
              refine ⟨1704994737951299412285155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1136663158634199608190103 1704994737951299412285155)
              ·
                refine ⟨2557492106926949118427733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1704994737951299412285155 2557492106926949118427733)
                ·
                  refine ⟨29970610628050184981575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2557492106926949118427733 29970610628050184981575)
                  ·
                    rfl

theorem cell21_131327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 8].length) (baseStart_131327 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131327 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131327 prefixEnd_131327 := by exact prefixLift 131327
  have htrace : WordTrace (prefixWord ++ tailWord_131327) baseStart_131327 baseEnd_131327 := by
    simpa [prefixWord, tailWord_131327, baseEnd_131327] using wordTrace_append hprefix tailTrace_131327
  have hstable : (prefixWord ++ tailWord_131327).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131327).length < 2 ^ (prefixWord ++ tailWord_131327).sum := by decide
  have hdescent : baseEnd_131327 < baseStart_131327 := by decide
  rcases family_descends (prefixWord ++ tailWord_131327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131361 : List Nat := [1, 2, 3, 2, 1, 1, 6, 1, 4]
def baseStart_131361 : Nat := 118140960795 + 131361 * 2 ^ 59
def prefixEnd_131361 : Nat := 4983230072969 + 3 ^ 40 * 131361 * 2
def baseEnd_131361 : Nat := 29978369891273681414839

theorem tailTrace_131361 : CollatzResearch.WordTrace tailWord_131361 prefixEnd_131361 29978369891273681414839 := by
  unfold tailWord_131361
  simp only [CollatzResearch.WordTrace]
  refine ⟨4791129277109006517793937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3194086184739337678529291 4791129277109006517793937)
  ·
    refine ⟨3593346957831754888345453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4791129277109006517793937 3593346957831754888345453)
    ·
      refine ⟨1347505109186908083129545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3593346957831754888345453 1347505109186908083129545)
      ·
        refine ⟨1010628831890181062347159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1347505109186908083129545 1010628831890181062347159)
        ·
          refine ⟨1515943247835271593520739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1010628831890181062347159 1515943247835271593520739)
          ·
            refine ⟨2273914871752907390281109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1515943247835271593520739 2273914871752907390281109)
            ·
              refine ⟨106589759613417533919427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2273914871752907390281109 106589759613417533919427)
              ·
                refine ⟨159884639420126300879141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 106589759613417533919427 159884639420126300879141)
                ·
                  refine ⟨29978369891273681414839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 159884639420126300879141 29978369891273681414839)
                  ·
                    rfl

theorem cell21_131361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 6, 1, 4].length) (baseStart_131361 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131361 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131361 prefixEnd_131361 := by exact prefixLift 131361
  have htrace : WordTrace (prefixWord ++ tailWord_131361) baseStart_131361 baseEnd_131361 := by
    simpa [prefixWord, tailWord_131361, baseEnd_131361] using wordTrace_append hprefix tailTrace_131361
  have hstable : (prefixWord ++ tailWord_131361).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131361).length < 2 ^ (prefixWord ++ tailWord_131361).sum := by decide
  have hdescent : baseEnd_131361 < baseStart_131361 := by decide
  rcases family_descends (prefixWord ++ tailWord_131361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131465 : List Nat := [1, 2, 1, 1, 6, 1, 1, 3, 5]
def baseStart_131465 : Nat := 118140960795 + 131465 * 2 ^ 59
def prefixEnd_131465 : Nat := 4983230072969 + 3 ^ 40 * 131465 * 2
def baseEnd_131465 : Nat := 30002104108192611681293

theorem tailTrace_131465 : CollatzResearch.WordTrace tailWord_131465 prefixEnd_131465 30002104108192611681293 := by
  unfold tailWord_131465
  simp only [CollatzResearch.WordTrace]
  refine ⟨4794922468732232279579849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3196614979154821519719899 4794922468732232279579849)
  ·
    refine ⟨3596191851549174209684887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4794922468732232279579849 3596191851549174209684887)
    ·
      refine ⟨5394287777323761314527331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3596191851549174209684887 5394287777323761314527331)
      ·
        refine ⟨8091431665985641971790997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5394287777323761314527331 8091431665985641971790997)
        ·
          refine ⟨379285859343076967427703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8091431665985641971790997 379285859343076967427703)
          ·
            refine ⟨568928789014615451141555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 379285859343076967427703 568928789014615451141555)
            ·
              refine ⟨853393183521923176712333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 568928789014615451141555 853393183521923176712333)
              ·
                refine ⟨320022443820721191267125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 853393183521923176712333 320022443820721191267125)
                ·
                  refine ⟨30002104108192611681293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 320022443820721191267125 30002104108192611681293)
                  ·
                    rfl

theorem cell21_131465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 1, 1, 3, 5].length) (baseStart_131465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131465 prefixEnd_131465 := by exact prefixLift 131465
  have htrace : WordTrace (prefixWord ++ tailWord_131465) baseStart_131465 baseEnd_131465 := by
    simpa [prefixWord, tailWord_131465, baseEnd_131465] using wordTrace_append hprefix tailTrace_131465
  have hstable : (prefixWord ++ tailWord_131465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131465).length < 2 ^ (prefixWord ++ tailWord_131465).sum := by decide
  have hdescent : baseEnd_131465 < baseStart_131465 := by decide
  rcases family_descends (prefixWord ++ tailWord_131465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131485 : List Nat := [1, 4, 2, 1, 5, 1, 2, 5]
def baseStart_131485 : Nat := 118140960795 + 131485 * 2 ^ 59
def prefixEnd_131485 : Nat := 4983230072969 + 3 ^ 40 * 131485 * 2
def baseEnd_131485 : Nat := 10002222793559007115973

theorem tailTrace_131485 : CollatzResearch.WordTrace tailWord_131485 prefixEnd_131485 10002222793559007115973 := by
  unfold tailWord_131485
  simp only [CollatzResearch.WordTrace]
  refine ⟨4795651928659775695307909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3197101285773183796871939 4795651928659775695307909)
  ·
    refine ⟨899184736623707942870233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4795651928659775695307909 899184736623707942870233)
    ·
      refine ⟨674388552467780957152675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 899184736623707942870233 674388552467780957152675)
      ·
        refine ⟨1011582828701671435729013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 674388552467780957152675 1011582828701671435729013)
        ·
          refine ⟨94835890190781697099595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1011582828701671435729013 94835890190781697099595)
          ·
            refine ⟨142253835286172545649393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 94835890190781697099595 142253835286172545649393)
            ·
              refine ⟨106690376464629409237045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142253835286172545649393 106690376464629409237045)
              ·
                refine ⟨10002222793559007115973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 106690376464629409237045 10002222793559007115973)
                ·
                  rfl

theorem cell21_131485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 5, 1, 2, 5].length) (baseStart_131485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131485 prefixEnd_131485 := by exact prefixLift 131485
  have htrace : WordTrace (prefixWord ++ tailWord_131485) baseStart_131485 baseEnd_131485 := by
    simpa [prefixWord, tailWord_131485, baseEnd_131485] using wordTrace_append hprefix tailTrace_131485
  have hstable : (prefixWord ++ tailWord_131485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131485).length < 2 ^ (prefixWord ++ tailWord_131485).sum := by decide
  have hdescent : baseEnd_131485 < baseStart_131485 := by decide
  rcases family_descends (prefixWord ++ tailWord_131485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131516 : List Nat := [2, 2, 2, 4, 1, 2, 3, 2, 3]
def baseStart_131516 : Nat := 118140960795 + 131516 * 2 ^ 59
def prefixEnd_131516 : Nat := 4983230072969 + 3 ^ 40 * 131516 * 2
def baseEnd_131516 : Nat := 30013743003027856331189

theorem tailTrace_131516 : CollatzResearch.WordTrace tailWord_131516 prefixEnd_131516 30013743003027856331189 := by
  unfold tailWord_131516
  simp only [CollatzResearch.WordTrace]
  refine ⟨2398391295773733994843201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3197855061031645326457601 2398391295773733994843201)
  ·
    refine ⟨1798793471830300496132401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2398391295773733994843201 1798793471830300496132401)
    ·
      refine ⟨1349095103872725372099301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1798793471830300496132401 1349095103872725372099301)
      ·
        refine ⟨252955331976136007268619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1349095103872725372099301 252955331976136007268619)
        ·
          refine ⟨379432997964204010902929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 252955331976136007268619 379432997964204010902929)
          ·
            refine ⟨284574748473153008177197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 379432997964204010902929 284574748473153008177197)
            ·
              refine ⟨106715530677432378066449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 284574748473153008177197 106715530677432378066449)
              ·
                refine ⟨80036648008074283549837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106715530677432378066449 80036648008074283549837)
                ·
                  refine ⟨30013743003027856331189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80036648008074283549837 30013743003027856331189)
                  ·
                    rfl

theorem cell21_131516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 3].length) (baseStart_131516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131516 prefixEnd_131516 := by exact prefixLift 131516
  have htrace : WordTrace (prefixWord ++ tailWord_131516) baseStart_131516 baseEnd_131516 := by
    simpa [prefixWord, tailWord_131516, baseEnd_131516] using wordTrace_append hprefix tailTrace_131516
  have hstable : (prefixWord ++ tailWord_131516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131516).length < 2 ^ (prefixWord ++ tailWord_131516).sum := by decide
  have hdescent : baseEnd_131516 < baseStart_131516 := by decide
  rcases family_descends (prefixWord ++ tailWord_131516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131623 : List Nat := [1, 1, 7, 2, 1, 2, 1, 2, 4]
def baseStart_131623 : Nat := 118140960795 + 131623 * 2 ^ 59
def prefixEnd_131623 : Nat := 4983230072969 + 3 ^ 40 * 131623 * 2
def baseEnd_131623 : Nat := 30038161860819448047637

theorem tailTrace_131623 : CollatzResearch.WordTrace tailWord_131623 prefixEnd_131623 30038161860819448047637 := by
  unfold tailWord_131623
  simp only [CollatzResearch.WordTrace]
  refine ⟨4800685202159825263831523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3200456801439883509221015 4800685202159825263831523)
  ·
    refine ⟨7201027803239737895747285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4800685202159825263831523 7201027803239737895747285)
    ·
      refine ⟨168774089138431356931577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 7201027803239737895747285 168774089138431356931577)
      ·
        refine ⟨126580566853823517698683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 168774089138431356931577 126580566853823517698683)
        ·
          refine ⟨189870850280735276548025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 126580566853823517698683 189870850280735276548025)
          ·
            refine ⟨142403137710551457411019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 189870850280735276548025 142403137710551457411019)
            ·
              refine ⟨213604706565827186116529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142403137710551457411019 213604706565827186116529)
              ·
                refine ⟨160203529924370389587397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213604706565827186116529 160203529924370389587397)
                ·
                  refine ⟨30038161860819448047637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160203529924370389587397 30038161860819448047637)
                  ·
                    rfl

theorem cell21_131623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 2, 1, 2, 4].length) (baseStart_131623 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131623 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131623 prefixEnd_131623 := by exact prefixLift 131623
  have htrace : WordTrace (prefixWord ++ tailWord_131623) baseStart_131623 baseEnd_131623 := by
    simpa [prefixWord, tailWord_131623, baseEnd_131623] using wordTrace_append hprefix tailTrace_131623
  have hstable : (prefixWord ++ tailWord_131623).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131623).length < 2 ^ (prefixWord ++ tailWord_131623).sum := by decide
  have hdescent : baseEnd_131623 < baseStart_131623 := by decide
  rcases family_descends (prefixWord ++ tailWord_131623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131634 : List Nat := [3, 2, 1, 1, 2, 1, 4, 4, 3]
def baseStart_131634 : Nat := 118140960795 + 131634 * 2 ^ 59
def prefixEnd_131634 : Nat := 4983230072969 + 3 ^ 40 * 131634 * 2
def baseEnd_131634 : Nat := 30040672210685873364281

theorem tailTrace_131634 : CollatzResearch.WordTrace tailWord_131634 prefixEnd_131634 30040672210685873364281 := by
  unfold tailWord_131634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1200271601279993535620489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3200724270079982761654637 1200271601279993535620489)
  ·
    refine ⟨900203700959995151715367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1200271601279993535620489 900203700959995151715367)
    ·
      refine ⟨1350305551439992727573051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 900203700959995151715367 1350305551439992727573051)
      ·
        refine ⟨2025458327159989091359577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1350305551439992727573051 2025458327159989091359577)
        ·
          refine ⟨1519093745369991818519683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2025458327159989091359577 1519093745369991818519683)
          ·
            refine ⟨2278640618054987727779525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1519093745369991818519683 2278640618054987727779525)
            ·
              refine ⟨427245115885310198958661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2278640618054987727779525 427245115885310198958661)
              ·
                refine ⟨80108459228495662304749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 427245115885310198958661 80108459228495662304749)
                ·
                  refine ⟨30040672210685873364281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80108459228495662304749 30040672210685873364281)
                  ·
                    rfl

theorem cell21_131634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 4, 4, 3].length) (baseStart_131634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131634 prefixEnd_131634 := by exact prefixLift 131634
  have htrace : WordTrace (prefixWord ++ tailWord_131634) baseStart_131634 baseEnd_131634 := by
    simpa [prefixWord, tailWord_131634, baseEnd_131634] using wordTrace_append hprefix tailTrace_131634
  have hstable : (prefixWord ++ tailWord_131634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131634).length < 2 ^ (prefixWord ++ tailWord_131634).sum := by decide
  have hdescent : baseEnd_131634 < baseStart_131634 := by decide
  rcases family_descends (prefixWord ++ tailWord_131634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131738 : List Nat := [3, 1, 1, 6, 10]
def baseStart_131738 : Nat := 118140960795 + 131738 * 2 ^ 59
def prefixEnd_131738 : Nat := 4983230072969 + 3 ^ 40 * 131738 * 2
def baseEnd_131738 : Nat := 371165511451911155935

theorem tailTrace_131738 : CollatzResearch.WordTrace tailWord_131738 prefixEnd_131738 371165511451911155935 := by
  unfold tailWord_131738
  simp only [CollatzResearch.WordTrace]
  refine ⟨1201219899185799976066967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3203253064495466602845245 1201219899185799976066967)
  ·
    refine ⟨1801829848778699964100451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1201219899185799976066967 1801829848778699964100451)
    ·
      refine ⟨2702744773168049946150677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1801829848778699964100451 2702744773168049946150677)
      ·
        refine ⟨126691161242252341225813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2702744773168049946150677 126691161242252341225813)
        ·
          refine ⟨371165511451911155935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 126691161242252341225813 371165511451911155935)
          ·
            rfl

theorem cell21_131738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 10].length) (baseStart_131738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131738 prefixEnd_131738 := by exact prefixLift 131738
  have htrace : WordTrace (prefixWord ++ tailWord_131738) baseStart_131738 baseEnd_131738 := by
    simpa [prefixWord, tailWord_131738, baseEnd_131738] using wordTrace_append hprefix tailTrace_131738
  have hstable : (prefixWord ++ tailWord_131738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131738).length < 2 ^ (prefixWord ++ tailWord_131738).sum := by decide
  have hdescent : baseEnd_131738 < baseStart_131738 := by decide
  rcases family_descends (prefixWord ++ tailWord_131738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131744 : List Nat := [2, 1, 1, 4, 4, 2, 2, 2, 3]
def baseStart_131744 : Nat := 118140960795 + 131744 * 2 ^ 59
def prefixEnd_131744 : Nat := 4983230072969 + 3 ^ 40 * 131744 * 2
def baseEnd_131744 : Nat := 30065775709350126530723

theorem tailTrace_131744 : CollatzResearch.WordTrace tailWord_131744 prefixEnd_131744 30065775709350126530723 := by
  unfold tailWord_131744
  simp only [CollatzResearch.WordTrace]
  refine ⟨2402549217360731464493143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3203398956480975285990857 2402549217360731464493143)
  ·
    refine ⟨3603823826041097196739715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2402549217360731464493143 3603823826041097196739715)
    ·
      refine ⟨5405735739061645795109573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3603823826041097196739715 5405735739061645795109573)
      ·
        refine ⟨1013575451074058586583045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5405735739061645795109573 1013575451074058586583045)
        ·
          refine ⟨190045397076385984984321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1013575451074058586583045 190045397076385984984321)
          ·
            refine ⟨142534047807289488738241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 190045397076385984984321 142534047807289488738241)
            ·
              refine ⟨106900535855467116553681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 142534047807289488738241 106900535855467116553681)
              ·
                refine ⟨80175401891600337415261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 106900535855467116553681 80175401891600337415261)
                ·
                  refine ⟨30065775709350126530723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80175401891600337415261 30065775709350126530723)
                  ·
                    rfl

theorem cell21_131744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 2, 2, 3].length) (baseStart_131744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131744 prefixEnd_131744 := by exact prefixLift 131744
  have htrace : WordTrace (prefixWord ++ tailWord_131744) baseStart_131744 baseEnd_131744 := by
    simpa [prefixWord, tailWord_131744, baseEnd_131744] using wordTrace_append hprefix tailTrace_131744
  have hstable : (prefixWord ++ tailWord_131744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131744).length < 2 ^ (prefixWord ++ tailWord_131744).sum := by decide
  have hdescent : baseEnd_131744 < baseStart_131744 := by decide
  rcases family_descends (prefixWord ++ tailWord_131744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131786 : List Nat := [3, 1, 2, 1, 4, 1, 1, 5, 3]
def baseStart_131786 : Nat := 118140960795 + 131786 * 2 ^ 59
def prefixEnd_131786 : Nat := 4983230072969 + 3 ^ 40 * 131786 * 2
def baseEnd_131786 : Nat := 30075360681567386830637

theorem tailTrace_131786 : CollatzResearch.WordTrace tailWord_131786 prefixEnd_131786 30075360681567386830637 := by
  unfold tailWord_131786
  simp only [CollatzResearch.WordTrace]
  refine ⟨1201657575142326025503803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3204420200379536068010141 1201657575142326025503803)
  ·
    refine ⟨1802486362713489038255705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1201657575142326025503803 1802486362713489038255705)
    ·
      refine ⟨1351864772035116778691779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1802486362713489038255705 1351864772035116778691779)
      ·
        refine ⟨2027797158052675168037669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1351864772035116778691779 2027797158052675168037669)
        ·
          refine ⟨380211967134876594007063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2027797158052675168037669 380211967134876594007063)
          ·
            refine ⟨570317950702314891010595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 380211967134876594007063 570317950702314891010595)
            ·
              refine ⟨855476926053472336515893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 570317950702314891010595 855476926053472336515893)
              ·
                refine ⟨80200961817513031548365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 855476926053472336515893 80200961817513031548365)
                ·
                  refine ⟨30075360681567386830637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80200961817513031548365 30075360681567386830637)
                  ·
                    rfl

theorem cell21_131786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 3].length) (baseStart_131786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131786 prefixEnd_131786 := by exact prefixLift 131786
  have htrace : WordTrace (prefixWord ++ tailWord_131786) baseStart_131786 baseEnd_131786 := by
    simpa [prefixWord, tailWord_131786, baseEnd_131786] using wordTrace_append hprefix tailTrace_131786
  have hstable : (prefixWord ++ tailWord_131786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131786).length < 2 ^ (prefixWord ++ tailWord_131786).sum := by decide
  have hdescent : baseEnd_131786 < baseStart_131786 := by decide
  rcases family_descends (prefixWord ++ tailWord_131786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131800 : List Nat := [2, 1, 2, 2, 3, 2, 3, 2, 4]
def baseStart_131800 : Nat := 118140960795 + 131800 * 2 ^ 59
def prefixEnd_131800 : Nat := 4983230072969 + 3 ^ 40 * 131800 * 2
def baseEnd_131800 : Nat := 30078555672306473597275

theorem tailTrace_131800 : CollatzResearch.WordTrace tailWord_131800 prefixEnd_131800 30078555672306473597275 := by
  unfold tailWord_131800
  simp only [CollatzResearch.WordTrace]
  refine ⟨2403570461259292246512427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3204760615012389662016569 2403570461259292246512427)
  ·
    refine ⟨3605355691888938369768641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2403570461259292246512427 3605355691888938369768641)
    ·
      refine ⟨2704016768916703777326481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3605355691888938369768641 2704016768916703777326481)
      ·
        refine ⟨2028012576687527832994861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2704016768916703777326481 2028012576687527832994861)
        ·
          refine ⟨760504716257822937373073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2028012576687527832994861 760504716257822937373073)
          ·
            refine ⟨570378537193367203029805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 760504716257822937373073 570378537193367203029805)
            ·
              refine ⟨213891951447512701136177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 570378537193367203029805 213891951447512701136177)
              ·
                refine ⟨160418963585634525852133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 213891951447512701136177 160418963585634525852133)
                ·
                  refine ⟨30078555672306473597275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160418963585634525852133 30078555672306473597275)
                  ·
                    rfl

theorem cell21_131800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 4].length) (baseStart_131800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131800 prefixEnd_131800 := by exact prefixLift 131800
  have htrace : WordTrace (prefixWord ++ tailWord_131800) baseStart_131800 baseEnd_131800 := by
    simpa [prefixWord, tailWord_131800, baseEnd_131800] using wordTrace_append hprefix tailTrace_131800
  have hstable : (prefixWord ++ tailWord_131800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131800).length < 2 ^ (prefixWord ++ tailWord_131800).sum := by decide
  have hdescent : baseEnd_131800 < baseStart_131800 := by decide
  rcases family_descends (prefixWord ++ tailWord_131800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131859 : List Nat := [1, 1, 1, 2, 1, 3, 4, 4, 4]
def baseStart_131859 : Nat := 118140960795 + 131859 * 2 ^ 59
def prefixEnd_131859 : Nat := 4983230072969 + 3 ^ 40 * 131859 * 2
def baseEnd_131859 : Nat := 30092020276135482113821

theorem tailTrace_131859 : CollatzResearch.WordTrace tailWord_131859 prefixEnd_131859 30092020276135482113821 := by
  unfold tailWord_131859
  simp only [CollatzResearch.WordTrace]
  refine ⟨4809292829304837569422631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3206195219536558379615087 4809292829304837569422631)
  ·
    refine ⟨7213939243957256354133947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4809292829304837569422631 7213939243957256354133947)
    ·
      refine ⟨10820908865935884531200921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7213939243957256354133947 10820908865935884531200921)
      ·
        refine ⟨8115681649451913398400691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10820908865935884531200921 8115681649451913398400691)
        ·
          refine ⟨12173522474177870097601037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8115681649451913398400691 12173522474177870097601037)
          ·
            refine ⟨4565070927816701286600389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12173522474177870097601037 4565070927816701286600389)
            ·
              refine ⟨855950798965631491237573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4565070927816701286600389 855950798965631491237573)
              ·
                refine ⟨160490774806055904607045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 855950798965631491237573 160490774806055904607045)
                ·
                  refine ⟨30092020276135482113821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160490774806055904607045 30092020276135482113821)
                  ·
                    rfl

theorem cell21_131859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 4, 4, 4].length) (baseStart_131859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131859 prefixEnd_131859 := by exact prefixLift 131859
  have htrace : WordTrace (prefixWord ++ tailWord_131859) baseStart_131859 baseEnd_131859 := by
    simpa [prefixWord, tailWord_131859, baseEnd_131859] using wordTrace_append hprefix tailTrace_131859
  have hstable : (prefixWord ++ tailWord_131859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131859).length < 2 ^ (prefixWord ++ tailWord_131859).sum := by decide
  have hdescent : baseEnd_131859 < baseStart_131859 := by decide
  rcases family_descends (prefixWord ++ tailWord_131859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131924 : List Nat := [2, 4, 1, 1, 5, 1, 1, 6]
def baseStart_131924 : Nat := 118140960795 + 131924 * 2 ^ 59
def prefixEnd_131924 : Nat := 4983230072969 + 3 ^ 40 * 131924 * 2
def baseEnd_131924 : Nat := 10035618053903271176785

theorem tailTrace_131924 : CollatzResearch.WordTrace tailWord_131924 prefixEnd_131924 10035618053903271176785 := by
  unfold tailWord_131924
  simp only [CollatzResearch.WordTrace]
  refine ⟨2405831787034676835269413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3207775716046235780359217 2405831787034676835269413)
  ·
    refine ⟨451093460069001906613015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2405831787034676835269413 451093460069001906613015)
    ·
      refine ⟨676640190103502859919523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 451093460069001906613015 676640190103502859919523)
      ·
        refine ⟨1014960285155254289879285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676640190103502859919523 1014960285155254289879285)
        ·
          refine ⟨95152526733305089676183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1014960285155254289879285 95152526733305089676183)
          ·
            refine ⟨142728790099957634514275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95152526733305089676183 142728790099957634514275)
            ·
              refine ⟨214093185149936451771413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142728790099957634514275 214093185149936451771413)
              ·
                refine ⟨10035618053903271176785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 214093185149936451771413 10035618053903271176785)
                ·
                  rfl

theorem cell21_131924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 5, 1, 1, 6].length) (baseStart_131924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131924 prefixEnd_131924 := by exact prefixLift 131924
  have htrace : WordTrace (prefixWord ++ tailWord_131924) baseStart_131924 baseEnd_131924 := by
    simpa [prefixWord, tailWord_131924, baseEnd_131924] using wordTrace_append hprefix tailTrace_131924
  have hstable : (prefixWord ++ tailWord_131924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131924).length < 2 ^ (prefixWord ++ tailWord_131924).sum := by decide
  have hdescent : baseEnd_131924 < baseStart_131924 := by decide
  rcases family_descends (prefixWord ++ tailWord_131924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131935 : List Nat := [1, 1, 2, 3, 1, 3, 1, 5, 4]
def baseStart_131935 : Nat := 118140960795 + 131935 * 2 ^ 59
def prefixEnd_131935 : Nat := 4983230072969 + 3 ^ 40 * 131935 * 2
def baseEnd_131935 : Nat := 30109364511576238846999

theorem tailTrace_131935 : CollatzResearch.WordTrace tailWord_131935 prefixEnd_131935 30109364511576238846999 := by
  unfold tailWord_131935
  simp only [CollatzResearch.WordTrace]
  refine ⟨4812064777029502549189259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3208043184686335032792839 4812064777029502549189259)
  ·
    refine ⟨7218097165544253823783889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4812064777029502549189259 7218097165544253823783889)
    ·
      refine ⟨5413572874158190367837917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7218097165544253823783889 5413572874158190367837917)
      ·
        refine ⟨2030089827809321387939219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5413572874158190367837917 2030089827809321387939219)
        ·
          refine ⟨3045134741713982081908829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2030089827809321387939219 3045134741713982081908829)
          ·
            refine ⟨1141925528142743280715811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3045134741713982081908829 1141925528142743280715811)
            ·
              refine ⟨1712888292214114921073717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141925528142743280715811 1712888292214114921073717)
              ·
                refine ⟨160583277395073273850661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1712888292214114921073717 160583277395073273850661)
                ·
                  refine ⟨30109364511576238846999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160583277395073273850661 30109364511576238846999)
                  ·
                    rfl

theorem cell21_131935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 5, 4].length) (baseStart_131935 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131935 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131935 prefixEnd_131935 := by exact prefixLift 131935
  have htrace : WordTrace (prefixWord ++ tailWord_131935) baseStart_131935 baseEnd_131935 := by
    simpa [prefixWord, tailWord_131935, baseEnd_131935] using wordTrace_append hprefix tailTrace_131935
  have hstable : (prefixWord ++ tailWord_131935).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131935).length < 2 ^ (prefixWord ++ tailWord_131935).sum := by decide
  have hdescent : baseEnd_131935 < baseStart_131935 := by decide
  rcases family_descends (prefixWord ++ tailWord_131935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131938 : List Nat := [3, 3, 2, 1, 3, 1, 1, 2, 5]
def baseStart_131938 : Nat := 118140960795 + 131938 * 2 ^ 59
def prefixEnd_131938 : Nat := 4983230072969 + 3 ^ 40 * 131938 * 2
def baseEnd_131938 : Nat := 30110049152448900296993

theorem tailTrace_131938 : CollatzResearch.WordTrace tailWord_131938 prefixEnd_131938 30110049152448900296993 := by
  unfold tailWord_131938
  simp only [CollatzResearch.WordTrace]
  refine ⟨1203043549004658515387117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3208116130679089374365645 1203043549004658515387117)
  ·
    refine ⟨451141330876746943270169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1203043549004658515387117 451141330876746943270169)
    ·
      refine ⟨338355998157560207452627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 451141330876746943270169 338355998157560207452627)
      ·
        refine ⟨507533997236340311178941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338355998157560207452627 507533997236340311178941)
        ·
          refine ⟨190325248963627616692103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 507533997236340311178941 190325248963627616692103)
          ·
            refine ⟨285487873445441425038155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190325248963627616692103 285487873445441425038155)
            ·
              refine ⟨428231810168162137557233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 285487873445441425038155 428231810168162137557233)
              ·
                refine ⟨321173857626121603167925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428231810168162137557233 321173857626121603167925)
                ·
                  refine ⟨30110049152448900296993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 321173857626121603167925 30110049152448900296993)
                  ·
                    rfl

theorem cell21_131938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_131938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131938 prefixEnd_131938 := by exact prefixLift 131938
  have htrace : WordTrace (prefixWord ++ tailWord_131938) baseStart_131938 baseEnd_131938 := by
    simpa [prefixWord, tailWord_131938, baseEnd_131938] using wordTrace_append hprefix tailTrace_131938
  have hstable : (prefixWord ++ tailWord_131938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131938).length < 2 ^ (prefixWord ++ tailWord_131938).sum := by decide
  have hdescent : baseEnd_131938 < baseStart_131938 := by decide
  rcases family_descends (prefixWord ++ tailWord_131938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131980 : List Nat := [2, 2, 1, 2, 1, 2, 3, 3, 5]
def baseStart_131980 : Nat := 118140960795 + 131980 * 2 ^ 59
def prefixEnd_131980 : Nat := 4983230072969 + 3 ^ 40 * 131980 * 2
def baseEnd_131980 : Nat := 30119634124666160596907

theorem tailTrace_131980 : CollatzResearch.WordTrace tailWord_131980 prefixEnd_131980 30119634124666160596907 := by
  unfold tailWord_131980
  simp only [CollatzResearch.WordTrace]
  refine ⟨2406853030933237617288697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3209137374577650156384929 2406853030933237617288697)
  ·
    refine ⟨1805139773199928212966523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2406853030933237617288697 1805139773199928212966523)
    ·
      refine ⟨2707709659799892319449785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1805139773199928212966523 2707709659799892319449785)
      ·
        refine ⟨2030782244849919239587339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2707709659799892319449785 2030782244849919239587339)
        ·
          refine ⟨3046173367274878859381009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2030782244849919239587339 3046173367274878859381009)
          ·
            refine ⟨2284630025456159144535757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3046173367274878859381009 2284630025456159144535757)
            ·
              refine ⟨856736259546059679200909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2284630025456159144535757 856736259546059679200909)
              ·
                refine ⟨321276097329772379700341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 856736259546059679200909 321276097329772379700341)
                ·
                  refine ⟨30119634124666160596907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 321276097329772379700341 30119634124666160596907)
                  ·
                    rfl

theorem cell21_131980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 5].length) (baseStart_131980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131980 prefixEnd_131980 := by exact prefixLift 131980
  have htrace : WordTrace (prefixWord ++ tailWord_131980) baseStart_131980 baseEnd_131980 := by
    simpa [prefixWord, tailWord_131980, baseEnd_131980] using wordTrace_append hprefix tailTrace_131980
  have hstable : (prefixWord ++ tailWord_131980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131980).length < 2 ^ (prefixWord ++ tailWord_131980).sum := by decide
  have hdescent : baseEnd_131980 < baseStart_131980 := by decide
  rcases family_descends (prefixWord ++ tailWord_131980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_131986 : List Nat := [3, 2, 3, 2, 2, 1, 3, 1, 4]
def baseStart_131986 : Nat := 118140960795 + 131986 * 2 ^ 59
def prefixEnd_131986 : Nat := 4983230072969 + 3 ^ 40 * 131986 * 2
def baseEnd_131986 : Nat := 30121003406411483496895

theorem tailTrace_131986 : CollatzResearch.WordTrace tailWord_131986 prefixEnd_131986 30121003406411483496895 := by
  unfold tailWord_131986
  simp only [CollatzResearch.WordTrace]
  refine ⟨1203481224961184564823953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3209283266563158839530541 1203481224961184564823953)
  ·
    refine ⟨902610918720888423617965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1203481224961184564823953 902610918720888423617965)
    ·
      refine ⟨338479094520333158856737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 902610918720888423617965 338479094520333158856737)
      ·
        refine ⟨253859320890249869142553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 338479094520333158856737 253859320890249869142553)
        ·
          refine ⟨190394490667687401856915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 253859320890249869142553 190394490667687401856915)
          ·
            refine ⟨285591736001531102785373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190394490667687401856915 285591736001531102785373)
            ·
              refine ⟨107096901000574163544515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 285591736001531102785373 107096901000574163544515)
              ·
                refine ⟨160645351500861245316773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107096901000574163544515 160645351500861245316773)
                ·
                  refine ⟨30121003406411483496895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160645351500861245316773 30121003406411483496895)
                  ·
                    rfl

theorem cell21_131986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_131986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_131986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_131986 prefixEnd_131986 := by exact prefixLift 131986
  have htrace : WordTrace (prefixWord ++ tailWord_131986) baseStart_131986 baseEnd_131986 := by
    simpa [prefixWord, tailWord_131986, baseEnd_131986] using wordTrace_append hprefix tailTrace_131986
  have hstable : (prefixWord ++ tailWord_131986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_131986).length < 2 ^ (prefixWord ++ tailWord_131986).sum := by decide
  have hdescent : baseEnd_131986 < baseStart_131986 := by decide
  rcases family_descends (prefixWord ++ tailWord_131986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132025 : List Nat := [1, 2, 1, 4, 2, 2, 9]
def baseStart_132025 : Nat := 118140960795 + 132025 * 2 ^ 59
def prefixEnd_132025 : Nat := 4983230072969 + 3 ^ 40 * 132025 * 2
def baseEnd_132025 : Nat := 3347767081972898038535

theorem tailTrace_132025 : CollatzResearch.WordTrace tailWord_132025 prefixEnd_132025 3347767081972898038535 := by
  unfold tailWord_132025
  simp only [CollatzResearch.WordTrace]
  refine ⟨4815347346703447919965529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3210231564468965279977019 4815347346703447919965529)
  ·
    refine ⟨3611510510027585939974147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4815347346703447919965529 3611510510027585939974147)
    ·
      refine ⟨5417265765041378909961221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3611510510027585939974147 5417265765041378909961221)
      ·
        refine ⟨1015737330945258545617729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5417265765041378909961221 1015737330945258545617729)
        ·
          refine ⟨761802998208943909213297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1015737330945258545617729 761802998208943909213297)
          ·
            refine ⟨571352248656707931909973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 761802998208943909213297 571352248656707931909973)
            ·
              refine ⟨3347767081972898038535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 571352248656707931909973 3347767081972898038535)
              ·
                rfl

theorem cell21_132025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 9].length) (baseStart_132025 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_132025 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_132025 prefixEnd_132025 := by exact prefixLift 132025
  have htrace : WordTrace (prefixWord ++ tailWord_132025) baseStart_132025 baseEnd_132025 := by
    simpa [prefixWord, tailWord_132025, baseEnd_132025] using wordTrace_append hprefix tailTrace_132025
  have hstable : (prefixWord ++ tailWord_132025).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132025).length < 2 ^ (prefixWord ++ tailWord_132025).sum := by decide
  have hdescent : baseEnd_132025 < baseStart_132025 := by decide
  rcases family_descends (prefixWord ++ tailWord_132025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132138 : List Nat := [3, 1, 4, 1, 4, 1, 1, 2, 4]
def baseStart_132138 : Nat := 118140960795 + 132138 * 2 ^ 59
def prefixEnd_132138 : Nat := 4983230072969 + 3 ^ 40 * 132138 * 2
def baseEnd_132138 : Nat := 30155691877292996963251

theorem tailTrace_132138 : CollatzResearch.WordTrace tailWord_132138 prefixEnd_132138 30155691877292996963251 := by
  unfold tailWord_132138
  simp only [CollatzResearch.WordTrace]
  refine ⟨1204867198823517054707267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3212979196862712145886045 1204867198823517054707267)
  ·
    refine ⟨1807300798235275582060901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1204867198823517054707267 1807300798235275582060901)
    ·
      refine ⟨338868899669114171636419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1807300798235275582060901 338868899669114171636419)
      ·
        refine ⟨508303349503671257454629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338868899669114171636419 508303349503671257454629)
        ·
          refine ⟨95306878031938360772743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 508303349503671257454629 95306878031938360772743)
          ·
            refine ⟨142960317047907541159115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95306878031938360772743 142960317047907541159115)
            ·
              refine ⟨214440475571861311738673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 142960317047907541159115 214440475571861311738673)
              ·
                refine ⟨160830356678895983804005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 214440475571861311738673 160830356678895983804005)
                ·
                  refine ⟨30155691877292996963251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 160830356678895983804005 30155691877292996963251)
                  ·
                    rfl

theorem cell21_132138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 4].length) (baseStart_132138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_132138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_132138 prefixEnd_132138 := by exact prefixLift 132138
  have htrace : WordTrace (prefixWord ++ tailWord_132138) baseStart_132138 baseEnd_132138 := by
    simpa [prefixWord, tailWord_132138, baseEnd_132138] using wordTrace_append hprefix tailTrace_132138
  have hstable : (prefixWord ++ tailWord_132138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132138).length < 2 ^ (prefixWord ++ tailWord_132138).sum := by decide
  have hdescent : baseEnd_132138 < baseStart_132138 := by decide
  rcases family_descends (prefixWord ++ tailWord_132138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132166 : List Nat := [6, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_132166 : Nat := 118140960795 + 132166 * 2 ^ 59
def prefixEnd_132166 : Nat := 4983230072969 + 3 ^ 40 * 132166 * 2
def baseEnd_132166 : Nat := 30162081858771170496527

theorem tailTrace_132166 : CollatzResearch.WordTrace tailWord_132166 prefixEnd_132166 30162081858771170496527 := by
  unfold tailWord_132166
  simp only [CollatzResearch.WordTrace]
  refine ⟨150640313724769656276511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3213660026128419333898901 150640313724769656276511)
  ·
    refine ⟨225960470587154484414767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 150640313724769656276511 225960470587154484414767)
    ·
      refine ⟨338940705880731726622151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 225960470587154484414767 338940705880731726622151)
      ·
        refine ⟨508411058821097589933227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 338940705880731726622151 508411058821097589933227)
        ·
          refine ⟨762616588231646384899841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 508411058821097589933227 762616588231646384899841)
          ·
            refine ⟨571962441173734788674881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 762616588231646384899841 571962441173734788674881)
            ·
              refine ⟨428971830880301091506161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 571962441173734788674881 428971830880301091506161)
              ·
                refine ⟨321728873160225818629621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 428971830880301091506161 321728873160225818629621)
                ·
                  refine ⟨30162081858771170496527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 321728873160225818629621 30162081858771170496527)
                  ·
                    rfl

theorem cell21_132166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_132166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_132166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_132166 prefixEnd_132166 := by exact prefixLift 132166
  have htrace : WordTrace (prefixWord ++ tailWord_132166) baseStart_132166 baseEnd_132166 := by
    simpa [prefixWord, tailWord_132166, baseEnd_132166] using wordTrace_append hprefix tailTrace_132166
  have hstable : (prefixWord ++ tailWord_132166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132166).length < 2 ^ (prefixWord ++ tailWord_132166).sum := by decide
  have hdescent : baseEnd_132166 < baseStart_132166 := by decide
  rcases family_descends (prefixWord ++ tailWord_132166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132194 : List Nat := [3, 3, 2, 2, 1, 1, 9]
def baseStart_132194 : Nat := 118140960795 + 132194 * 2 ^ 59
def prefixEnd_132194 : Nat := 4983230072969 + 3 ^ 40 * 132194 * 2
def baseEnd_132194 : Nat := 3352052426694371558867

theorem tailTrace_132194 : CollatzResearch.WordTrace tailWord_132194 prefixEnd_132194 3352052426694371558867 := by
  unfold tailWord_132194
  simp only [CollatzResearch.WordTrace]
  refine ⟨1205377820772797445716909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3214340855394126521911757 1205377820772797445716909)
  ·
    refine ⟨452016682789799042143841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1205377820772797445716909 452016682789799042143841)
    ·
      refine ⟨339012512092349281607881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 452016682789799042143841 339012512092349281607881)
      ·
        refine ⟨254259384069261961205911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 339012512092349281607881 254259384069261961205911)
        ·
          refine ⟨381389076103892941808867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 254259384069261961205911 381389076103892941808867)
          ·
            refine ⟨572083614155839412713301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381389076103892941808867 572083614155839412713301)
            ·
              refine ⟨3352052426694371558867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 572083614155839412713301 3352052426694371558867)
              ·
                rfl

theorem cell21_132194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 9].length) (baseStart_132194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_132194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_132194 prefixEnd_132194 := by exact prefixLift 132194
  have htrace : WordTrace (prefixWord ++ tailWord_132194) baseStart_132194 baseEnd_132194 := by
    simpa [prefixWord, tailWord_132194, baseEnd_132194] using wordTrace_append hprefix tailTrace_132194
  have hstable : (prefixWord ++ tailWord_132194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132194).length < 2 ^ (prefixWord ++ tailWord_132194).sum := by decide
  have hdescent : baseEnd_132194 < baseStart_132194 := by decide
  rcases family_descends (prefixWord ++ tailWord_132194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132200 : List Nat := [2, 1, 4, 4, 1, 1, 3, 2, 3]
def baseStart_132200 : Nat := 118140960795 + 132200 * 2 ^ 59
def prefixEnd_132200 : Nat := 4983230072969 + 3 ^ 40 * 132200 * 2
def baseEnd_132200 : Nat := 30169841121994666929791

theorem tailTrace_132200 : CollatzResearch.WordTrace tailWord_132200 prefixEnd_132200 30169841121994666929791 := by
  unfold tailWord_132200
  simp only [CollatzResearch.WordTrace]
  refine ⟨2410865060534726403793027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3214486747379635205057369 2410865060534726403793027)
  ·
    refine ⟨3616297590802089605689541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2410865060534726403793027 3616297590802089605689541)
    ·
      refine ⟨678055798275391801066789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3616297590802089605689541 678055798275391801066789)
      ·
        refine ⟨127135462176635962700023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 678055798275391801066789 127135462176635962700023)
        ·
          refine ⟨190703193264953944050035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127135462176635962700023 190703193264953944050035)
          ·
            refine ⟨286054789897430916075053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 190703193264953944050035 286054789897430916075053)
            ·
              refine ⟨107270546211536593528145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286054789897430916075053 107270546211536593528145)
              ·
                refine ⟨80452909658652445146109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107270546211536593528145 80452909658652445146109)
                ·
                  refine ⟨30169841121994666929791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80452909658652445146109 30169841121994666929791)
                  ·
                    rfl

theorem cell21_132200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 3].length) (baseStart_132200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_132200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_132200 prefixEnd_132200 := by exact prefixLift 132200
  have htrace : WordTrace (prefixWord ++ tailWord_132200) baseStart_132200 baseEnd_132200 := by
    simpa [prefixWord, tailWord_132200, baseEnd_132200] using wordTrace_append hprefix tailTrace_132200
  have hstable : (prefixWord ++ tailWord_132200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132200).length < 2 ^ (prefixWord ++ tailWord_132200).sum := by decide
  have hdescent : baseEnd_132200 < baseStart_132200 := by decide
  rcases family_descends (prefixWord ++ tailWord_132200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132284 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 7]
def baseStart_132284 : Nat := 118140960795 + 132284 * 2 ^ 59
def prefixEnd_132284 : Nat := 4983230072969 + 3 ^ 40 * 132284 * 2
def baseEnd_132284 : Nat := 30189011066429187529619

theorem tailTrace_132284 : CollatzResearch.WordTrace tailWord_132284 prefixEnd_132284 30189011066429187529619 := by
  unfold tailWord_132284
  simp only [CollatzResearch.WordTrace]
  refine ⟨2412396926382567576821953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3216529235176756769095937 2412396926382567576821953)
  ·
    refine ⟨1809297694786925682616465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2412396926382567576821953 1809297694786925682616465)
    ·
      refine ⟨1356973271090194261962349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1809297694786925682616465 1356973271090194261962349)
      ·
        refine ⟨508864976658822848235881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1356973271090194261962349 508864976658822848235881)
        ·
          refine ⟨381648732494117136176911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 508864976658822848235881 381648732494117136176911)
          ·
            refine ⟨572473098741175704265367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 381648732494117136176911 572473098741175704265367)
            ·
              refine ⟨858709648111763556398051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 572473098741175704265367 858709648111763556398051)
              ·
                refine ⟨1288064472167645334597077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 858709648111763556398051 1288064472167645334597077)
                ·
                  refine ⟨30189011066429187529619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1288064472167645334597077 30189011066429187529619)
                  ·
                    rfl

theorem cell21_132284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_132284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_132284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_132284 prefixEnd_132284 := by exact prefixLift 132284
  have htrace : WordTrace (prefixWord ++ tailWord_132284) baseStart_132284 baseEnd_132284 := by
    simpa [prefixWord, tailWord_132284, baseEnd_132284] using wordTrace_append hprefix tailTrace_132284
  have hstable : (prefixWord ++ tailWord_132284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132284).length < 2 ^ (prefixWord ++ tailWord_132284).sum := by decide
  have hdescent : baseEnd_132284 < baseStart_132284 := by decide
  rcases family_descends (prefixWord ++ tailWord_132284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132332 : List Nat := [2, 2, 1, 1, 2, 5, 3, 1, 4]
def baseStart_132332 : Nat := 118140960795 + 132332 * 2 ^ 59
def prefixEnd_132332 : Nat := 4983230072969 + 3 ^ 40 * 132332 * 2
def baseEnd_132332 : Nat := 30199965320391770729521

theorem tailTrace_132332 : CollatzResearch.WordTrace tailWord_132332 prefixEnd_132332 30199965320391770729521 := by
  unfold tailWord_132332
  simp only [CollatzResearch.WordTrace]
  refine ⟨2413272278295619675695625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3217696371060826234260833 2413272278295619675695625)
  ·
    refine ⟨1809954208721714756771719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2413272278295619675695625 1809954208721714756771719)
    ·
      refine ⟨2714931313082572135157579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1809954208721714756771719 2714931313082572135157579)
      ·
        refine ⟨4072396969623858202736369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2714931313082572135157579 4072396969623858202736369)
        ·
          refine ⟨3054297727217893652052277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4072396969623858202736369 3054297727217893652052277)
          ·
            refine ⟨286340411926677529879901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3054297727217893652052277 286340411926677529879901)
            ·
              refine ⟨107377654472504073704963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286340411926677529879901 107377654472504073704963)
              ·
                refine ⟨161066481708756110557445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107377654472504073704963 161066481708756110557445)
                ·
                  refine ⟨30199965320391770729521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161066481708756110557445 30199965320391770729521)
                  ·
                    rfl

theorem cell21_132332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_132332 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_132332 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_132332 prefixEnd_132332 := by exact prefixLift 132332
  have htrace : WordTrace (prefixWord ++ tailWord_132332) baseStart_132332 baseEnd_132332 := by
    simpa [prefixWord, tailWord_132332, baseEnd_132332] using wordTrace_append hprefix tailTrace_132332
  have hstable : (prefixWord ++ tailWord_132332).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132332).length < 2 ^ (prefixWord ++ tailWord_132332).sum := by decide
  have hdescent : baseEnd_132332 < baseStart_132332 := by decide
  rcases family_descends (prefixWord ++ tailWord_132332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132405 : List Nat := [1, 3, 3, 1, 2, 2, 2, 7]
def baseStart_132405 : Nat := 118140960795 + 132405 * 2 ^ 59
def prefixEnd_132405 : Nat := 4983230072969 + 3 ^ 40 * 132405 * 2
def baseEnd_132405 : Nat := 10072208304986622004235

theorem tailTrace_132405 : CollatzResearch.WordTrace tailWord_132405 prefixEnd_132405 10072208304986622004235 := by
  unfold tailWord_132405
  simp only [CollatzResearch.WordTrace]
  refine ⟨4829207085326772818798669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3219471390217848545865779 4829207085326772818798669)
  ·
    refine ⟨1810952656997539807049501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4829207085326772818798669 1810952656997539807049501)
    ·
      refine ⟨679107246374077427643563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1810952656997539807049501 679107246374077427643563)
      ·
        refine ⟨1018660869561116141465345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679107246374077427643563 1018660869561116141465345)
        ·
          refine ⟨763995652170837106099009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1018660869561116141465345 763995652170837106099009)
          ·
            refine ⟨572996739128127829574257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 763995652170837106099009 572996739128127829574257)
            ·
              refine ⟨429747554346095872180693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 572996739128127829574257 429747554346095872180693)
              ·
                refine ⟨10072208304986622004235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 429747554346095872180693 10072208304986622004235)
                ·
                  rfl

theorem cell21_132405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 7].length) (baseStart_132405 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_132405 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_132405 prefixEnd_132405 := by exact prefixLift 132405
  have htrace : WordTrace (prefixWord ++ tailWord_132405) baseStart_132405 baseEnd_132405 := by
    simpa [prefixWord, tailWord_132405, baseEnd_132405] using wordTrace_append hprefix tailTrace_132405
  have hstable : (prefixWord ++ tailWord_132405).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132405).length < 2 ^ (prefixWord ++ tailWord_132405).sum := by decide
  have hdescent : baseEnd_132405 < baseStart_132405 := by decide
  rcases family_descends (prefixWord ++ tailWord_132405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132436 : List Nat := [2, 4, 1, 1, 2, 1, 2, 3, 5]
def baseStart_132436 : Nat := 118140960795 + 132436 * 2 ^ 59
def prefixEnd_132436 : Nat := 4983230072969 + 3 ^ 40 * 132436 * 2
def baseEnd_132436 : Nat := 30223699537310700995975

theorem tailTrace_132436 : CollatzResearch.WordTrace tailWord_132436 prefixEnd_132436 30223699537310700995975 := by
  unfold tailWord_132436
  simp only [CollatzResearch.WordTrace]
  refine ⟨2415168874107232556588581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3220225165476310075451441 2415168874107232556588581)
  ·
    refine ⟨452844163895106104360359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2415168874107232556588581 452844163895106104360359)
    ·
      refine ⟨679266245842659156540539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 452844163895106104360359 679266245842659156540539)
      ·
        refine ⟨1018899368763988734810809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679266245842659156540539 1018899368763988734810809)
        ·
          refine ⟨764174526572991551108107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1018899368763988734810809 764174526572991551108107)
          ·
            refine ⟨1146261789859487326662161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 764174526572991551108107 1146261789859487326662161)
            ·
              refine ⟨859696342394615494996621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1146261789859487326662161 859696342394615494996621)
              ·
                refine ⟨322386128397980810623733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 859696342394615494996621 322386128397980810623733)
                ·
                  refine ⟨30223699537310700995975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 322386128397980810623733 30223699537310700995975)
                  ·
                    rfl

theorem cell21_132436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_132436 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_132436 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_132436 prefixEnd_132436 := by exact prefixLift 132436
  have htrace : WordTrace (prefixWord ++ tailWord_132436) baseStart_132436 baseEnd_132436 := by
    simpa [prefixWord, tailWord_132436, baseEnd_132436] using wordTrace_append hprefix tailTrace_132436
  have hstable : (prefixWord ++ tailWord_132436).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132436).length < 2 ^ (prefixWord ++ tailWord_132436).sum := by decide
  have hdescent : baseEnd_132436 < baseStart_132436 := by decide
  rcases family_descends (prefixWord ++ tailWord_132436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132484 : List Nat := [2, 3, 2, 1, 1, 5, 1, 2, 4]
def baseStart_132484 : Nat := 118140960795 + 132484 * 2 ^ 59
def prefixEnd_132484 : Nat := 4983230072969 + 3 ^ 40 * 132484 * 2
def baseEnd_132484 : Nat := 30234653791273284195877

theorem tailTrace_132484 : CollatzResearch.WordTrace tailWord_132484 prefixEnd_132484 30234653791273284195877 := by
  unfold tailWord_132484
  simp only [CollatzResearch.WordTrace]
  refine ⟨2416044226020284655462253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3221392301360379540616337 2416044226020284655462253)
  ·
    refine ⟨906016584757606745798345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2416044226020284655462253 906016584757606745798345)
    ·
      refine ⟨679512438568205059348759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 906016584757606745798345 679512438568205059348759)
      ·
        refine ⟨1019268657852307589023139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 679512438568205059348759 1019268657852307589023139)
        ·
          refine ⟨1528902986778461383534709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1019268657852307589023139 1528902986778461383534709)
          ·
            refine ⟨143334655010480754706379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1528902986778461383534709 143334655010480754706379)
            ·
              refine ⟨215001982515721132059569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143334655010480754706379 215001982515721132059569)
              ·
                refine ⟨161251486886790849044677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215001982515721132059569 161251486886790849044677)
                ·
                  refine ⟨30234653791273284195877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161251486886790849044677 30234653791273284195877)
                  ·
                    rfl

theorem cell21_132484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_132484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_132484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_132484 prefixEnd_132484 := by exact prefixLift 132484
  have htrace : WordTrace (prefixWord ++ tailWord_132484) baseStart_132484 baseEnd_132484 := by
    simpa [prefixWord, tailWord_132484, baseEnd_132484] using wordTrace_append hprefix tailTrace_132484
  have hstable : (prefixWord ++ tailWord_132484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132484).length < 2 ^ (prefixWord ++ tailWord_132484).sum := by decide
  have hdescent : baseEnd_132484 < baseStart_132484 := by decide
  rcases family_descends (prefixWord ++ tailWord_132484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132605 : List Nat := [1, 4, 1, 1, 1, 5, 1, 4, 3]
def baseStart_132605 : Nat := 118140960795 + 132605 * 2 ^ 59
def prefixEnd_132605 : Nat := 4983230072969 + 3 ^ 40 * 132605 * 2
def baseEnd_132605 : Nat := 30262267639803962678963

theorem tailTrace_132605 : CollatzResearch.WordTrace tailWord_132605 prefixEnd_132605 30262267639803962678963 := by
  unfold tailWord_132605
  simp only [CollatzResearch.WordTrace]
  refine ⟨4836501684602206976079269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3224334456401471317386179 4836501684602206976079269)
  ·
    refine ⟨906844065862913808014863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4836501684602206976079269 906844065862913808014863)
    ·
      refine ⟨1360266098794370712022295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 906844065862913808014863 1360266098794370712022295)
      ·
        refine ⟨2040399148191556068033443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1360266098794370712022295 2040399148191556068033443)
        ·
          refine ⟨3060598722287334102050165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2040399148191556068033443 3060598722287334102050165)
          ·
            refine ⟨286931130214437572067203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3060598722287334102050165 286931130214437572067203)
            ·
              refine ⟨430396695321656358100805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286931130214437572067203 430396695321656358100805)
              ·
                refine ⟨80699380372810567143901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 430396695321656358100805 80699380372810567143901)
                ·
                  refine ⟨30262267639803962678963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80699380372810567143901 30262267639803962678963)
                  ·
                    rfl

theorem cell21_132605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_132605 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_132605 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_132605 prefixEnd_132605 := by exact prefixLift 132605
  have htrace : WordTrace (prefixWord ++ tailWord_132605) baseStart_132605 baseEnd_132605 := by
    simpa [prefixWord, tailWord_132605, baseEnd_132605] using wordTrace_append hprefix tailTrace_132605
  have hstable : (prefixWord ++ tailWord_132605).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132605).length < 2 ^ (prefixWord ++ tailWord_132605).sum := by decide
  have hdescent : baseEnd_132605 < baseStart_132605 := by decide
  rcases family_descends (prefixWord ++ tailWord_132605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132664 : List Nat := [2, 1, 2, 1, 4, 3, 2, 1, 5]
def baseStart_132664 : Nat := 118140960795 + 132664 * 2 ^ 59
def prefixEnd_132664 : Nat := 4983230072969 + 3 ^ 40 * 132664 * 2
def baseEnd_132664 : Nat := 30275732243632971195509

theorem tailTrace_132664 : CollatzResearch.WordTrace tailWord_132664 prefixEnd_132664 30275732243632971195509 := by
  unfold tailWord_132664
  simp only [CollatzResearch.WordTrace]
  refine ⟨2419326795694230026238523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3225769060925640034984697 2419326795694230026238523)
  ·
    refine ⟨3628990193541345039357785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2419326795694230026238523 3628990193541345039357785)
    ·
      refine ⟨2721742645156008779518339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3628990193541345039357785 2721742645156008779518339)
      ·
        refine ⟨4082613967734013169277509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2721742645156008779518339 4082613967734013169277509)
        ·
          refine ⟨765490118950127469239533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4082613967734013169277509 765490118950127469239533)
          ·
            refine ⟨287058794606297800964825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 765490118950127469239533 287058794606297800964825)
            ·
              refine ⟨215294095954723350723619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287058794606297800964825 215294095954723350723619)
              ·
                refine ⟨322941143932085026085429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215294095954723350723619 322941143932085026085429)
                ·
                  refine ⟨30275732243632971195509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 322941143932085026085429 30275732243632971195509)
                  ·
                    rfl

theorem cell21_132664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 2, 1, 5].length) (baseStart_132664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_132664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_132664 prefixEnd_132664 := by exact prefixLift 132664
  have htrace : WordTrace (prefixWord ++ tailWord_132664) baseStart_132664 baseEnd_132664 := by
    simpa [prefixWord, tailWord_132664, baseEnd_132664] using wordTrace_append hprefix tailTrace_132664
  have hstable : (prefixWord ++ tailWord_132664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132664).length < 2 ^ (prefixWord ++ tailWord_132664).sum := by decide
  have hdescent : baseEnd_132664 < baseStart_132664 := by decide
  rcases family_descends (prefixWord ++ tailWord_132664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132709 : List Nat := [1, 3, 1, 3, 3, 3, 7]
def baseStart_132709 : Nat := 118140960795 + 132709 * 2 ^ 59
def prefixEnd_132709 : Nat := 4983230072969 + 3 ^ 40 * 132709 * 2
def baseEnd_132709 : Nat := 3365111317413654771713

theorem tailTrace_132709 : CollatzResearch.WordTrace tailWord_132709 prefixEnd_132709 3365111317413654771713 := by
  unfold tailWord_132709
  simp only [CollatzResearch.WordTrace]
  refine ⟨4840294876225432737865181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3226863250816955158576787 4840294876225432737865181)
  ·
    refine ⟨1815110578584537276699443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4840294876225432737865181 1815110578584537276699443)
    ·
      refine ⟨2722665867876805915049165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1815110578584537276699443 2722665867876805915049165)
      ·
        refine ⟨1020999700453802218143437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2722665867876805915049165 1020999700453802218143437)
        ·
          refine ⟨382874887670175831803789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1020999700453802218143437 382874887670175831803789)
          ·
            refine ⟨143578082876315936926421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382874887670175831803789 143578082876315936926421)
            ·
              refine ⟨3365111317413654771713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 143578082876315936926421 3365111317413654771713)
              ·
                rfl

theorem cell21_132709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 7].length) (baseStart_132709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_132709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_132709 prefixEnd_132709 := by exact prefixLift 132709
  have htrace : WordTrace (prefixWord ++ tailWord_132709) baseStart_132709 baseEnd_132709 := by
    simpa [prefixWord, tailWord_132709, baseEnd_132709] using wordTrace_append hprefix tailTrace_132709
  have hstable : (prefixWord ++ tailWord_132709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132709).length < 2 ^ (prefixWord ++ tailWord_132709).sum := by decide
  have hdescent : baseEnd_132709 < baseStart_132709 := by decide
  rcases family_descends (prefixWord ++ tailWord_132709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132726 : List Nat := [5, 1, 1, 2, 2, 2, 2, 6]
def baseStart_132726 : Nat := 118140960795 + 132726 * 2 ^ 59
def prefixEnd_132726 : Nat := 4983230072969 + 3 ^ 40 * 132726 * 2
def baseEnd_132726 : Nat := 10096627162778213720683

theorem tailTrace_132726 : CollatzResearch.WordTrace tailWord_132726 prefixEnd_132726 10096627162778213720683 := by
  unfold tailWord_132726
  simp only [CollatzResearch.WordTrace]
  refine ⟨302557182322740290077127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3227276611442563094156021 302557182322740290077127)
  ·
    refine ⟨453835773484110435115691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302557182322740290077127 453835773484110435115691)
    ·
      refine ⟨680753660226165652673537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453835773484110435115691 680753660226165652673537)
      ·
        refine ⟨510565245169624239505153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 680753660226165652673537 510565245169624239505153)
        ·
          refine ⟨382923933877218179628865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510565245169624239505153 382923933877218179628865)
          ·
            refine ⟨287192950407913634721649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382923933877218179628865 287192950407913634721649)
            ·
              refine ⟨215394712805935226041237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287192950407913634721649 215394712805935226041237)
              ·
                refine ⟨10096627162778213720683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 215394712805935226041237 10096627162778213720683)
                ·
                  rfl

theorem cell21_132726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 6].length) (baseStart_132726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_132726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_132726 prefixEnd_132726 := by exact prefixLift 132726
  have htrace : WordTrace (prefixWord ++ tailWord_132726) baseStart_132726 baseEnd_132726 := by
    simpa [prefixWord, tailWord_132726, baseEnd_132726] using wordTrace_append hprefix tailTrace_132726
  have hstable : (prefixWord ++ tailWord_132726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132726).length < 2 ^ (prefixWord ++ tailWord_132726).sum := by decide
  have hdescent : baseEnd_132726 < baseStart_132726 := by decide
  rcases family_descends (prefixWord ++ tailWord_132726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132768 : List Nat := [2, 1, 1, 4, 3, 10]
def baseStart_132768 : Nat := 118140960795 + 132768 * 2 ^ 59
def prefixEnd_132768 : Nat := 4983230072969 + 3 ^ 40 * 132768 * 2
def baseEnd_132768 : Nat := 1122202461501922276369

theorem tailTrace_132768 : CollatzResearch.WordTrace tailWord_132768 prefixEnd_132768 1122202461501922276369 := by
  unfold tailWord_132768
  simp only [CollatzResearch.WordTrace]
  refine ⟨2421223391505842907131479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3228297855341123876175305 2421223391505842907131479)
  ·
    refine ⟨3631835087258764360697219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2421223391505842907131479 3631835087258764360697219)
    ·
      refine ⟨5447752630888146541045829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3631835087258764360697219 5447752630888146541045829)
      ·
        refine ⟨1021453618291527476446093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5447752630888146541045829 1021453618291527476446093)
        ·
          refine ⟨383045106859322803667285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1021453618291527476446093 383045106859322803667285)
          ·
            refine ⟨1122202461501922276369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 383045106859322803667285 1122202461501922276369)
            ·
              rfl

theorem cell21_132768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 10].length) (baseStart_132768 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_132768 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_132768 prefixEnd_132768 := by exact prefixLift 132768
  have htrace : WordTrace (prefixWord ++ tailWord_132768) baseStart_132768 baseEnd_132768 := by
    simpa [prefixWord, tailWord_132768, baseEnd_132768] using wordTrace_append hprefix tailTrace_132768
  have hstable : (prefixWord ++ tailWord_132768).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132768).length < 2 ^ (prefixWord ++ tailWord_132768).sum := by decide
  have hdescent : baseEnd_132768 < baseStart_132768 := by decide
  rcases family_descends (prefixWord ++ tailWord_132768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132799 : List Nat := [1, 1, 2, 2, 2, 3, 3, 2, 5]
def baseStart_132799 : Nat := 118140960795 + 132799 * 2 ^ 59
def prefixEnd_132799 : Nat := 4983230072969 + 3 ^ 40 * 132799 * 2
def baseEnd_132799 : Nat := 30306541082902736445233

theorem tailTrace_132799 : CollatzResearch.WordTrace tailWord_132799 prefixEnd_132799 30306541082902736445233 := by
  unfold tailWord_132799
  simp only [CollatzResearch.WordTrace]
  refine ⟨4843577445899378108641451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3229051630599585405760967 4843577445899378108641451)
  ·
    refine ⟨7265366168849067162962177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4843577445899378108641451 7265366168849067162962177)
    ·
      refine ⟨5449024626636800372221633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7265366168849067162962177 5449024626636800372221633)
      ·
        refine ⟨4086768469977600279166225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5449024626636800372221633 4086768469977600279166225)
        ·
          refine ⟨3065076352483200209374669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4086768469977600279166225 3065076352483200209374669)
          ·
            refine ⟨1149403632181200078515501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3065076352483200209374669 1149403632181200078515501)
            ·
              refine ⟨431026362067950029443313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1149403632181200078515501 431026362067950029443313)
              ·
                refine ⟨323269771550962522082485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 431026362067950029443313 323269771550962522082485)
                ·
                  refine ⟨30306541082902736445233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 323269771550962522082485 30306541082902736445233)
                  ·
                    rfl

theorem cell21_132799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 3, 2, 5].length) (baseStart_132799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_132799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_132799 prefixEnd_132799 := by exact prefixLift 132799
  have htrace : WordTrace (prefixWord ++ tailWord_132799) baseStart_132799 baseEnd_132799 := by
    simpa [prefixWord, tailWord_132799, baseEnd_132799] using wordTrace_append hprefix tailTrace_132799
  have hstable : (prefixWord ++ tailWord_132799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132799).length < 2 ^ (prefixWord ++ tailWord_132799).sum := by decide
  have hdescent : baseEnd_132799 < baseStart_132799 := by decide
  rcases family_descends (prefixWord ++ tailWord_132799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132822 : List Nat := [5, 2, 1, 3, 1, 2, 1, 2, 4]
def baseStart_132822 : Nat := 118140960795 + 132822 * 2 ^ 59
def prefixEnd_132822 : Nat := 4983230072969 + 3 ^ 40 * 132822 * 2
def baseEnd_132822 : Nat := 30311789996259807561853

theorem tailTrace_132822 : CollatzResearch.WordTrace tailWord_132822 prefixEnd_132822 30311789996259807561853 := by
  unfold tailWord_132822
  simp only [CollatzResearch.WordTrace]
  refine ⟨302776020301003314795545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3229610883210702024485813 302776020301003314795545)
  ·
    refine ⟨227082015225752486096659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302776020301003314795545 227082015225752486096659)
    ·
      refine ⟨340623022838628729144989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 227082015225752486096659 340623022838628729144989)
      ·
        refine ⟨127733633564485773429371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340623022838628729144989 127733633564485773429371)
        ·
          refine ⟨191600450346728660144057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127733633564485773429371 191600450346728660144057)
          ·
            refine ⟨143700337760046495108043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191600450346728660144057 143700337760046495108043)
            ·
              refine ⟨215550506640069742662065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143700337760046495108043 215550506640069742662065)
              ·
                refine ⟨161662879980052306996549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215550506640069742662065 161662879980052306996549)
                ·
                  refine ⟨30311789996259807561853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161662879980052306996549 30311789996259807561853)
                  ·
                    rfl

theorem cell21_132822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 2, 1, 2, 4].length) (baseStart_132822 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_132822 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_132822 prefixEnd_132822 := by exact prefixLift 132822
  have htrace : WordTrace (prefixWord ++ tailWord_132822) baseStart_132822 baseEnd_132822 := by
    simpa [prefixWord, tailWord_132822, baseEnd_132822] using wordTrace_append hprefix tailTrace_132822
  have hstable : (prefixWord ++ tailWord_132822).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132822).length < 2 ^ (prefixWord ++ tailWord_132822).sum := by decide
  have hdescent : baseEnd_132822 < baseStart_132822 := by decide
  rcases family_descends (prefixWord ++ tailWord_132822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132847 : List Nat := [1, 1, 2, 1, 5, 1, 5, 1, 4]
def baseStart_132847 : Nat := 118140960795 + 132847 * 2 ^ 59
def prefixEnd_132847 : Nat := 4983230072969 + 3 ^ 40 * 132847 * 2
def baseEnd_132847 : Nat := 30317495336865319645135

theorem tailTrace_132847 : CollatzResearch.WordTrace tailWord_132847 prefixEnd_132847 30317495336865319645135 := by
  unfold tailWord_132847
  simp only [CollatzResearch.WordTrace]
  refine ⟨4845328149725482306388795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3230218766483654870925863 4845328149725482306388795)
  ·
    refine ⟨7267992224588223459583193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4845328149725482306388795 7267992224588223459583193)
    ·
      refine ⟨5450994168441167594687395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7267992224588223459583193 5450994168441167594687395)
      ·
        refine ⟨8176491252661751392031093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5450994168441167594687395 8176491252661751392031093)
        ·
          refine ⟨766546054937039193002915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8176491252661751392031093 766546054937039193002915)
          ·
            refine ⟨1149819082405558789504373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 766546054937039193002915 1149819082405558789504373)
            ·
              refine ⟨107795538975521136516035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1149819082405558789504373 107795538975521136516035)
              ·
                refine ⟨161693308463281704774053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107795538975521136516035 161693308463281704774053)
                ·
                  refine ⟨30317495336865319645135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161693308463281704774053 30317495336865319645135)
                  ·
                    rfl

theorem cell21_132847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 5, 1, 4].length) (baseStart_132847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_132847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_132847 prefixEnd_132847 := by exact prefixLift 132847
  have htrace : WordTrace (prefixWord ++ tailWord_132847) baseStart_132847 baseEnd_132847 := by
    simpa [prefixWord, tailWord_132847, baseEnd_132847] using wordTrace_append hprefix tailTrace_132847
  have hstable : (prefixWord ++ tailWord_132847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132847).length < 2 ^ (prefixWord ++ tailWord_132847).sum := by decide
  have hdescent : baseEnd_132847 < baseStart_132847 := by decide
  rcases family_descends (prefixWord ++ tailWord_132847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132870 : List Nat := [6, 2, 2, 1, 2, 1, 7]
def baseStart_132870 : Nat := 118140960795 + 132870 * 2 ^ 59
def prefixEnd_132870 : Nat := 4983230072969 + 3 ^ 40 * 132870 * 2
def baseEnd_132870 : Nat := 3369193805580265640195

theorem tailTrace_132870 : CollatzResearch.WordTrace tailWord_132870 prefixEnd_132870 3369193805580265640195 := by
  unfold tailWord_132870
  simp only [CollatzResearch.WordTrace]
  refine ⟨151442719645067413577377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3230778019094771489650709 151442719645067413577377)
  ·
    refine ⟨113582039733800560183033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151442719645067413577377 113582039733800560183033)
    ·
      refine ⟨85186529800350420137275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113582039733800560183033 85186529800350420137275)
      ·
        refine ⟨127779794700525630205913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85186529800350420137275 127779794700525630205913)
        ·
          refine ⟨95834846025394222654435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127779794700525630205913 95834846025394222654435)
          ·
            refine ⟨143752269038091333981653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95834846025394222654435 143752269038091333981653)
            ·
              refine ⟨3369193805580265640195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 143752269038091333981653 3369193805580265640195)
              ·
                rfl

theorem cell21_132870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 7].length) (baseStart_132870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_132870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_132870 prefixEnd_132870 := by exact prefixLift 132870
  have htrace : WordTrace (prefixWord ++ tailWord_132870) baseStart_132870 baseEnd_132870 := by
    simpa [prefixWord, tailWord_132870, baseEnd_132870] using wordTrace_append hprefix tailTrace_132870
  have hstable : (prefixWord ++ tailWord_132870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132870).length < 2 ^ (prefixWord ++ tailWord_132870).sum := by decide
  have hdescent : baseEnd_132870 < baseStart_132870 := by decide
  rcases family_descends (prefixWord ++ tailWord_132870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132884 : List Nat := [2, 4, 4, 1, 2, 1, 1, 1, 5]
def baseStart_132884 : Nat := 118140960795 + 132884 * 2 ^ 59
def prefixEnd_132884 : Nat := 4983230072969 + 3 ^ 40 * 132884 * 2
def baseEnd_132884 : Nat := 30325939240961477528393

theorem tailTrace_132884 : CollatzResearch.WordTrace tailWord_132884 prefixEnd_132884 30325939240961477528393 := by
  unfold tailWord_132884
  simp only [CollatzResearch.WordTrace]
  refine ⟨2423338825295718812742853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3231118433727625083657137 2423338825295718812742853)
  ·
    refine ⟨454376029742947277389285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2423338825295718812742853 454376029742947277389285)
    ·
      refine ⟨85195505576802614510491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 454376029742947277389285 85195505576802614510491)
      ·
        refine ⟨127793258365203921765737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85195505576802614510491 127793258365203921765737)
        ·
          refine ⟨95844943773902941324303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127793258365203921765737 95844943773902941324303)
          ·
            refine ⟨143767415660854411986455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95844943773902941324303 143767415660854411986455)
            ·
              refine ⟨215651123491281617979683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143767415660854411986455 215651123491281617979683)
              ·
                refine ⟨323476685236922426969525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215651123491281617979683 323476685236922426969525)
                ·
                  refine ⟨30325939240961477528393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 323476685236922426969525 30325939240961477528393)
                  ·
                    rfl

theorem cell21_132884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_132884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_132884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_132884 prefixEnd_132884 := by exact prefixLift 132884
  have htrace : WordTrace (prefixWord ++ tailWord_132884) baseStart_132884 baseEnd_132884 := by
    simpa [prefixWord, tailWord_132884, baseEnd_132884] using wordTrace_append hprefix tailTrace_132884
  have hstable : (prefixWord ++ tailWord_132884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132884).length < 2 ^ (prefixWord ++ tailWord_132884).sum := by decide
  have hdescent : baseEnd_132884 < baseStart_132884 := by decide
  rcases family_descends (prefixWord ++ tailWord_132884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132920 : List Nat := [2, 1, 2, 1, 3, 3, 2, 7]
def baseStart_132920 : Nat := 118140960795 + 132920 * 2 ^ 59
def prefixEnd_132920 : Nat := 4983230072969 + 3 ^ 40 * 132920 * 2
def baseEnd_132920 : Nat := 10111384977144471642773

theorem tailTrace_132920 : CollatzResearch.WordTrace tailWord_132920 prefixEnd_132920 10111384977144471642773 := by
  unfold tailWord_132920
  simp only [CollatzResearch.WordTrace]
  refine ⟨2423995339230507886898107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3231993785640677182530809 2423995339230507886898107)
  ·
    refine ⟨3635993008845761830347161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2423995339230507886898107 3635993008845761830347161)
    ·
      refine ⟨2726994756634321372760371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3635993008845761830347161 2726994756634321372760371)
      ·
        refine ⟨4090492134951482059140557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2726994756634321372760371 4090492134951482059140557)
        ·
          refine ⟨1533934550606805772177709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4090492134951482059140557 1533934550606805772177709)
          ·
            refine ⟨575225456477552164566641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1533934550606805772177709 575225456477552164566641)
            ·
              refine ⟨431419092358164123424981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 575225456477552164566641 431419092358164123424981)
              ·
                refine ⟨10111384977144471642773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 431419092358164123424981 10111384977144471642773)
                ·
                  rfl

theorem cell21_132920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 7].length) (baseStart_132920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_132920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_132920 prefixEnd_132920 := by exact prefixLift 132920
  have htrace : WordTrace (prefixWord ++ tailWord_132920) baseStart_132920 baseEnd_132920 := by
    simpa [prefixWord, tailWord_132920, baseEnd_132920] using wordTrace_append hprefix tailTrace_132920
  have hstable : (prefixWord ++ tailWord_132920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132920).length < 2 ^ (prefixWord ++ tailWord_132920).sum := by decide
  have hdescent : baseEnd_132920 < baseStart_132920 := by decide
  rcases family_descends (prefixWord ++ tailWord_132920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_132965 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 8]
def baseStart_132965 : Nat := 118140960795 + 132965 * 2 ^ 59
def prefixEnd_132965 : Nat := 4983230072969 + 3 ^ 40 * 132965 * 2
def baseEnd_132965 : Nat := 30344424544523336678227

theorem tailTrace_132965 : CollatzResearch.WordTrace tailWord_132965 prefixEnd_132965 30344424544523336678227 := by
  unfold tailWord_132965
  simp only [CollatzResearch.WordTrace]
  refine ⟨4849631963297988459184349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3233087975531992306122899 4849631963297988459184349)
  ·
    refine ⟨1818611986236745672194131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4849631963297988459184349 1818611986236745672194131)
    ·
      refine ⟨2727917979355118508291197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1818611986236745672194131 2727917979355118508291197)
      ·
        refine ⟨1022969242258169440609199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2727917979355118508291197 1022969242258169440609199)
        ·
          refine ⟨1534453863387254160913799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1022969242258169440609199 1534453863387254160913799)
          ·
            refine ⟨2301680795080881241370699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1534453863387254160913799 2301680795080881241370699)
            ·
              refine ⟨3452521192621321862056049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2301680795080881241370699 3452521192621321862056049)
              ·
                refine ⟨2589390894465991396542037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3452521192621321862056049 2589390894465991396542037)
                ·
                  refine ⟨30344424544523336678227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2589390894465991396542037 30344424544523336678227)
                  ·
                    rfl

theorem cell21_132965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_132965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_132965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_132965 prefixEnd_132965 := by exact prefixLift 132965
  have htrace : WordTrace (prefixWord ++ tailWord_132965) baseStart_132965 baseEnd_132965 := by
    simpa [prefixWord, tailWord_132965, baseEnd_132965] using wordTrace_append hprefix tailTrace_132965
  have hstable : (prefixWord ++ tailWord_132965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_132965).length < 2 ^ (prefixWord ++ tailWord_132965).sum := by decide
  have hdescent : baseEnd_132965 < baseStart_132965 := by decide
  rcases family_descends (prefixWord ++ tailWord_132965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133117 : List Nat := [1, 4, 1, 1, 1, 2, 2, 3, 6]
def baseStart_133117 : Nat := 118140960795 + 133117 * 2 ^ 59
def prefixEnd_133117 : Nat := 4983230072969 + 3 ^ 40 * 133117 * 2
def baseEnd_133117 : Nat := 30379113015404850144583

theorem tailTrace_133117 : CollatzResearch.WordTrace tailWord_133117 prefixEnd_133117 30379113015404850144583 := by
  unfold tailWord_133117
  simp only [CollatzResearch.WordTrace]
  refine ⟨4855175858747318418717605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3236783905831545612478403 4855175858747318418717605)
  ·
    refine ⟨910345473515122203509551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4855175858747318418717605 910345473515122203509551)
    ·
      refine ⟨1365518210272683305264327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 910345473515122203509551 1365518210272683305264327)
      ·
        refine ⟨2048277315409024957896491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1365518210272683305264327 2048277315409024957896491)
        ·
          refine ⟨3072415973113537436844737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2048277315409024957896491 3072415973113537436844737)
          ·
            refine ⟨2304311979835153077633553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3072415973113537436844737 2304311979835153077633553)
            ·
              refine ⟨1728233984876364808225165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2304311979835153077633553 1728233984876364808225165)
              ·
                refine ⟨648087744328636803084437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1728233984876364808225165 648087744328636803084437)
                ·
                  refine ⟨30379113015404850144583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 648087744328636803084437 30379113015404850144583)
                  ·
                    rfl

theorem cell21_133117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 3, 6].length) (baseStart_133117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_133117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_133117 prefixEnd_133117 := by exact prefixLift 133117
  have htrace : WordTrace (prefixWord ++ tailWord_133117) baseStart_133117 baseEnd_133117 := by
    simpa [prefixWord, tailWord_133117, baseEnd_133117] using wordTrace_append hprefix tailTrace_133117
  have hstable : (prefixWord ++ tailWord_133117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133117).length < 2 ^ (prefixWord ++ tailWord_133117).sum := by decide
  have hdescent : baseEnd_133117 < baseStart_133117 := by decide
  rcases family_descends (prefixWord ++ tailWord_133117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133134 : List Nat := [4, 1, 1, 2, 2, 1, 1, 5, 4]
def baseStart_133134 : Nat := 118140960795 + 133134 * 2 ^ 59
def prefixEnd_133134 : Nat := 4983230072969 + 3 ^ 40 * 133134 * 2
def baseEnd_133134 : Nat := 30382992647016598361215

theorem tailTrace_133134 : CollatzResearch.WordTrace tailWord_133134 prefixEnd_133134 30382992647016598361215 := by
  unfold tailWord_133134
  simp only [CollatzResearch.WordTrace]
  refine ⟨606974487460716290260807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3237197266457153548057637 606974487460716290260807)
  ·
    refine ⟨910461731191074435391211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 606974487460716290260807 910461731191074435391211)
    ·
      refine ⟨1365692596786611653086817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 910461731191074435391211 1365692596786611653086817)
      ·
        refine ⟨1024269447589958739815113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1365692596786611653086817 1024269447589958739815113)
        ·
          refine ⟨768202085692469054861335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1024269447589958739815113 768202085692469054861335)
          ·
            refine ⟨1152303128538703582292003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 768202085692469054861335 1152303128538703582292003)
            ·
              refine ⟨1728454692808055373438005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1152303128538703582292003 1728454692808055373438005)
              ·
                refine ⟨162042627450755191259813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1728454692808055373438005 162042627450755191259813)
                ·
                  refine ⟨30382992647016598361215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 162042627450755191259813 30382992647016598361215)
                  ·
                    rfl

theorem cell21_133134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 5, 4].length) (baseStart_133134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_133134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_133134 prefixEnd_133134 := by exact prefixLift 133134
  have htrace : WordTrace (prefixWord ++ tailWord_133134) baseStart_133134 baseEnd_133134 := by
    simpa [prefixWord, tailWord_133134, baseEnd_133134] using wordTrace_append hprefix tailTrace_133134
  have hstable : (prefixWord ++ tailWord_133134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133134).length < 2 ^ (prefixWord ++ tailWord_133134).sum := by decide
  have hdescent : baseEnd_133134 < baseStart_133134 := by decide
  rcases family_descends (prefixWord ++ tailWord_133134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133345 : List Nat := [1, 2, 3, 1, 3, 1, 3, 1, 6]
def baseStart_133345 : Nat := 118140960795 + 133345 * 2 ^ 59
def prefixEnd_133345 : Nat := 4983230072969 + 3 ^ 40 * 133345 * 2
def baseEnd_133345 : Nat := 30431145721727120344117

theorem tailTrace_133345 : CollatzResearch.WordTrace tailWord_133345 prefixEnd_133345 30431145721727120344117 := by
  unfold tailWord_133345
  simp only [CollatzResearch.WordTrace]
  refine ⟨4863491701921313358017489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3242327801280875572011659 4863491701921313358017489)
  ·
    refine ⟨3647618776440985018513117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4863491701921313358017489 3647618776440985018513117)
    ·
      refine ⟨1367857041165369381942419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3647618776440985018513117 1367857041165369381942419)
      ·
        refine ⟨2051785561748054072913629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1367857041165369381942419 2051785561748054072913629)
        ·
          refine ⟨769419585655520277342611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2051785561748054072913629 769419585655520277342611)
          ·
            refine ⟨1154129378483280416013917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 769419585655520277342611 1154129378483280416013917)
            ·
              refine ⟨432798516931230156005219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1154129378483280416013917 432798516931230156005219)
              ·
                refine ⟨649197775396845234007829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 432798516931230156005219 649197775396845234007829)
                ·
                  refine ⟨30431145721727120344117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 649197775396845234007829 30431145721727120344117)
                  ·
                    rfl

theorem cell21_133345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_133345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_133345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_133345 prefixEnd_133345 := by exact prefixLift 133345
  have htrace : WordTrace (prefixWord ++ tailWord_133345) baseStart_133345 baseEnd_133345 := by
    simpa [prefixWord, tailWord_133345, baseEnd_133345] using wordTrace_append hprefix tailTrace_133345
  have hstable : (prefixWord ++ tailWord_133345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133345).length < 2 ^ (prefixWord ++ tailWord_133345).sum := by decide
  have hdescent : baseEnd_133345 < baseStart_133345 := by decide
  rcases family_descends (prefixWord ++ tailWord_133345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133376 : List Nat := [2, 1, 1, 2, 1, 1, 8, 5]
def baseStart_133376 : Nat := 118140960795 + 133376 * 2 ^ 59
def prefixEnd_133376 : Nat := 4983230072969 + 3 ^ 40 * 133376 * 2
def baseEnd_133376 : Nat := 10146073448025985109129

theorem tailTrace_133376 : CollatzResearch.WordTrace tailWord_133376 prefixEnd_133376 10146073448025985109129 := by
  unfold tailWord_133376
  simp only [CollatzResearch.WordTrace]
  refine ⟨2432311182404502826197991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3243081576539337101597321 2432311182404502826197991)
  ·
    refine ⟨3648466773606754239296987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2432311182404502826197991 3648466773606754239296987)
    ·
      refine ⟨5472700160410131358945481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3648466773606754239296987 5472700160410131358945481)
      ·
        refine ⟨4104525120307598519209111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5472700160410131358945481 4104525120307598519209111)
        ·
          refine ⟨6156787680461397778813667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4104525120307598519209111 6156787680461397778813667)
          ·
            refine ⟨9235181520692096668220501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6156787680461397778813667 9235181520692096668220501)
            ·
              refine ⟨108224783445610507830709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 9235181520692096668220501 108224783445610507830709)
              ·
                refine ⟨10146073448025985109129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108224783445610507830709 10146073448025985109129)
                ·
                  rfl

theorem cell21_133376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 8, 5].length) (baseStart_133376 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_133376 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_133376 prefixEnd_133376 := by exact prefixLift 133376
  have htrace : WordTrace (prefixWord ++ tailWord_133376) baseStart_133376 baseEnd_133376 := by
    simpa [prefixWord, tailWord_133376, baseEnd_133376] using wordTrace_append hprefix tailTrace_133376
  have hstable : (prefixWord ++ tailWord_133376).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133376).length < 2 ^ (prefixWord ++ tailWord_133376).sum := by decide
  have hdescent : baseEnd_133376 < baseStart_133376 := by decide
  rcases family_descends (prefixWord ++ tailWord_133376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133407 : List Nat := [1, 1, 2, 4, 3, 1, 3, 1, 5]
def baseStart_133407 : Nat := 118140960795 + 133407 * 2 ^ 59
def prefixEnd_133407 : Nat := 4983230072969 + 3 ^ 40 * 133407 * 2
def baseEnd_133407 : Nat := 30445294966428790310657

theorem tailTrace_133407 : CollatzResearch.WordTrace tailWord_133407 prefixEnd_133407 30445294966428790310657 := by
  unfold tailWord_133407
  simp only [CollatzResearch.WordTrace]
  refine ⟨4865753027696697946774475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3243835351797798631182983 4865753027696697946774475)
  ·
    refine ⟨7298629541545046920161713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4865753027696697946774475 7298629541545046920161713)
    ·
      refine ⟨5473972156158785190121285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7298629541545046920161713 5473972156158785190121285)
      ·
        refine ⟨1026369779279772223147741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5473972156158785190121285 1026369779279772223147741)
        ·
          refine ⟨384888667229914583680403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1026369779279772223147741 384888667229914583680403)
          ·
            refine ⟨577333000844871875520605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 384888667229914583680403 577333000844871875520605)
            ·
              refine ⟨216499875316826953320227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 577333000844871875520605 216499875316826953320227)
              ·
                refine ⟨324749812975240429980341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 216499875316826953320227 324749812975240429980341)
                ·
                  refine ⟨30445294966428790310657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 324749812975240429980341 30445294966428790310657)
                  ·
                    rfl

theorem cell21_133407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 3, 1, 5].length) (baseStart_133407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_133407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_133407 prefixEnd_133407 := by exact prefixLift 133407
  have htrace : WordTrace (prefixWord ++ tailWord_133407) baseStart_133407 baseEnd_133407 := by
    simpa [prefixWord, tailWord_133407, baseEnd_133407] using wordTrace_append hprefix tailTrace_133407
  have hstable : (prefixWord ++ tailWord_133407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133407).length < 2 ^ (prefixWord ++ tailWord_133407).sum := by decide
  have hdescent : baseEnd_133407 < baseStart_133407 := by decide
  rcases family_descends (prefixWord ++ tailWord_133407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133466 : List Nat := [3, 1, 1, 2, 1, 2, 1, 5, 5]
def baseStart_133466 : Nat := 118140960795 + 133466 * 2 ^ 59
def prefixEnd_133466 : Nat := 4983230072969 + 3 ^ 40 * 133466 * 2
def baseEnd_133466 : Nat := 30458759570257798827203

theorem tailTrace_133466 : CollatzResearch.WordTrace tailWord_133466 prefixEnd_133466 30458759570257798827203 := by
  unfold tailWord_133466
  simp only [CollatzResearch.WordTrace]
  refine ⟨1216976233620737755793063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3245269956321967348781501 1216976233620737755793063)
  ·
    refine ⟨1825464350431106633689595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1216976233620737755793063 1825464350431106633689595)
    ·
      refine ⟨2738196525646659950534393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1825464350431106633689595 2738196525646659950534393)
      ·
        refine ⟨2053647394234994962900795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2738196525646659950534393 2053647394234994962900795)
        ·
          refine ⟨3080471091352492444351193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2053647394234994962900795 3080471091352492444351193)
          ·
            refine ⟨2310353318514369333263395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3080471091352492444351193 2310353318514369333263395)
            ·
              refine ⟨3465529977771553999895093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2310353318514369333263395 3465529977771553999895093)
              ·
                refine ⟨324893435416083187490165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3465529977771553999895093 324893435416083187490165)
                ·
                  refine ⟨30458759570257798827203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 324893435416083187490165 30458759570257798827203)
                  ·
                    rfl

theorem cell21_133466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_133466 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_133466 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_133466 prefixEnd_133466 := by exact prefixLift 133466
  have htrace : WordTrace (prefixWord ++ tailWord_133466) baseStart_133466 baseEnd_133466 := by
    simpa [prefixWord, tailWord_133466, baseEnd_133466] using wordTrace_append hprefix tailTrace_133466
  have hstable : (prefixWord ++ tailWord_133466).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133466).length < 2 ^ (prefixWord ++ tailWord_133466).sum := by decide
  have hdescent : baseEnd_133466 < baseStart_133466 := by decide
  rcases family_descends (prefixWord ++ tailWord_133466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133511 : List Nat := [1, 1, 4, 2, 2, 1, 10]
def baseStart_133511 : Nat := 118140960795 + 133511 * 2 ^ 59
def prefixEnd_133511 : Nat := 4983230072969 + 3 ^ 40 * 133511 * 2
def baseEnd_133511 : Nat := 3385447687038635619679

theorem tailTrace_133511 : CollatzResearch.WordTrace tailWord_133511 prefixEnd_133511 3385447687038635619679 := by
  unfold tailWord_133511
  simp only [CollatzResearch.WordTrace]
  refine ⟨4869546219319923708560387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3246364146213282472373591 4869546219319923708560387)
  ·
    refine ⟨7304319328979885562840581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4869546219319923708560387 7304319328979885562840581)
    ·
      refine ⟨1369559874183728543032609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7304319328979885562840581 1369559874183728543032609)
      ·
        refine ⟨1027169905637796407274457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1369559874183728543032609 1027169905637796407274457)
        ·
          refine ⟨770377429228347305455843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1027169905637796407274457 770377429228347305455843)
          ·
            refine ⟨1155566143842520958183765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 770377429228347305455843 1155566143842520958183765)
            ·
              refine ⟨3385447687038635619679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1155566143842520958183765 3385447687038635619679)
              ·
                rfl

theorem cell21_133511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 10].length) (baseStart_133511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_133511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_133511 prefixEnd_133511 := by exact prefixLift 133511
  have htrace : WordTrace (prefixWord ++ tailWord_133511) baseStart_133511 baseEnd_133511 := by
    simpa [prefixWord, tailWord_133511, baseEnd_133511] using wordTrace_append hprefix tailTrace_133511
  have hstable : (prefixWord ++ tailWord_133511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133511).length < 2 ^ (prefixWord ++ tailWord_133511).sum := by decide
  have hdescent : baseEnd_133511 < baseStart_133511 := by decide
  rcases family_descends (prefixWord ++ tailWord_133511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133621 : List Nat := [1, 3, 5, 1, 3, 8]
def baseStart_133621 : Nat := 118140960795 + 133621 * 2 ^ 59
def prefixEnd_133621 : Nat := 4983230072969 + 3 ^ 40 * 133621 * 2
def baseEnd_133621 : Nat := 1129412321555999027539

theorem tailTrace_133621 : CollatzResearch.WordTrace tailWord_133621 prefixEnd_133621 1129412321555999027539 := by
  unfold tailWord_133621
  simp only [CollatzResearch.WordTrace]
  refine ⟨4873558248921412495064717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3249038832614274996709811 4873558248921412495064717)
  ·
    refine ⟨1827584343345529685649269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4873558248921412495064717 1827584343345529685649269)
    ·
      refine ⟨171336032188643408029619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1827584343345529685649269 171336032188643408029619)
      ·
        refine ⟨257004048282965112044429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171336032188643408029619 257004048282965112044429)
        ·
          refine ⟨96376518106111917016661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257004048282965112044429 96376518106111917016661)
          ·
            refine ⟨1129412321555999027539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 96376518106111917016661 1129412321555999027539)
            ·
              rfl

theorem cell21_133621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 8].length) (baseStart_133621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_133621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_133621 prefixEnd_133621 := by exact prefixLift 133621
  have htrace : WordTrace (prefixWord ++ tailWord_133621) baseStart_133621 baseEnd_133621 := by
    simpa [prefixWord, tailWord_133621, baseEnd_133621] using wordTrace_append hprefix tailTrace_133621
  have hstable : (prefixWord ++ tailWord_133621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133621).length < 2 ^ (prefixWord ++ tailWord_133621).sum := by decide
  have hdescent : baseEnd_133621 < baseStart_133621 := by decide
  rcases family_descends (prefixWord ++ tailWord_133621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133635 : List Nat := [1, 1, 1, 3, 2, 1, 5, 4, 3]
def baseStart_133635 : Nat := 118140960795 + 133635 * 2 ^ 59
def prefixEnd_133635 : Nat := 4983230072969 + 3 ^ 40 * 133635 * 2
def baseEnd_133635 : Nat := 30497327672751060510191

theorem tailTrace_133635 : CollatzResearch.WordTrace tailWord_133635 prefixEnd_133635 30497327672751060510191 := by
  unfold tailWord_133635
  simp only [CollatzResearch.WordTrace]
  refine ⟨4874068870870692886074359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3249379247247128590716239 4874068870870692886074359)
  ·
    refine ⟨7311103306306039329111539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4874068870870692886074359 7311103306306039329111539)
    ·
      refine ⟨10966654959459058993667309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7311103306306039329111539 10966654959459058993667309)
      ·
        refine ⟨4112495609797147122625241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10966654959459058993667309 4112495609797147122625241)
        ·
          refine ⟨3084371707347860341968931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4112495609797147122625241 3084371707347860341968931)
          ·
            refine ⟨4626557561021790512953397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3084371707347860341968931 4626557561021790512953397)
            ·
              refine ⟨433739771345792860589381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4626557561021790512953397 433739771345792860589381)
              ·
                refine ⟨81326207127336161360509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 433739771345792860589381 81326207127336161360509)
                ·
                  refine ⟨30497327672751060510191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81326207127336161360509 30497327672751060510191)
                  ·
                    rfl

theorem cell21_133635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 4, 3].length) (baseStart_133635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_133635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_133635 prefixEnd_133635 := by exact prefixLift 133635
  have htrace : WordTrace (prefixWord ++ tailWord_133635) baseStart_133635 baseEnd_133635 := by
    simpa [prefixWord, tailWord_133635, baseEnd_133635] using wordTrace_append hprefix tailTrace_133635
  have hstable : (prefixWord ++ tailWord_133635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133635).length < 2 ^ (prefixWord ++ tailWord_133635).sum := by decide
  have hdescent : baseEnd_133635 < baseStart_133635 := by decide
  rcases family_descends (prefixWord ++ tailWord_133635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133652 : List Nat := [2, 4, 3, 1, 1, 2, 1, 2, 5]
def baseStart_133652 : Nat := 118140960795 + 133652 * 2 ^ 59
def prefixEnd_133652 : Nat := 4983230072969 + 3 ^ 40 * 133652 * 2
def baseEnd_133652 : Nat := 30501207304362808726823

theorem tailTrace_133652 : CollatzResearch.WordTrace tailWord_133652 prefixEnd_133652 30501207304362808726823 := by
  unfold tailWord_133652
  simp only [CollatzResearch.WordTrace]
  refine ⟨2437344455904552394721605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3249792607872736526295473 2437344455904552394721605)
  ·
    refine ⟨457002085482103574010301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2437344455904552394721605 457002085482103574010301)
    ·
      refine ⟨171375782055788840253863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 457002085482103574010301 171375782055788840253863)
      ·
        refine ⟨257063673083683260380795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171375782055788840253863 257063673083683260380795)
        ·
          refine ⟨385595509625524890571193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257063673083683260380795 385595509625524890571193)
          ·
            refine ⟨289196632219143667928395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 385595509625524890571193 289196632219143667928395)
            ·
              refine ⟨433794948328715501892593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 289196632219143667928395 433794948328715501892593)
              ·
                refine ⟨325346211246536626419445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 433794948328715501892593 325346211246536626419445)
                ·
                  refine ⟨30501207304362808726823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 325346211246536626419445 30501207304362808726823)
                  ·
                    rfl

theorem cell21_133652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_133652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_133652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_133652 prefixEnd_133652 := by exact prefixLift 133652
  have htrace : WordTrace (prefixWord ++ tailWord_133652) baseStart_133652 baseEnd_133652 := by
    simpa [prefixWord, tailWord_133652, baseEnd_133652] using wordTrace_append hprefix tailTrace_133652
  have hstable : (prefixWord ++ tailWord_133652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133652).length < 2 ^ (prefixWord ++ tailWord_133652).sum := by decide
  have hdescent : baseEnd_133652 < baseStart_133652 := by decide
  rcases family_descends (prefixWord ++ tailWord_133652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133832 : List Nat := [2, 1, 3, 1, 2, 4, 3, 5]
def baseStart_133832 : Nat := 118140960795 + 133832 * 2 ^ 59
def prefixEnd_133832 : Nat := 4983230072969 + 3 ^ 40 * 133832 * 2
def baseEnd_133832 : Nat := 10180761918907498575485

theorem tailTrace_133832 : CollatzResearch.WordTrace tailWord_133832 prefixEnd_133832 10180761918907498575485 := by
  unfold tailWord_133832
  simp only [CollatzResearch.WordTrace]
  refine ⟨2440627025578497765497875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3254169367437997020663833 2440627025578497765497875)
  ·
    refine ⟨3660940538367746648246813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2440627025578497765497875 3660940538367746648246813)
    ·
      refine ⟨1372852701887904993092555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3660940538367746648246813 1372852701887904993092555)
      ·
        refine ⟨2059279052831857489638833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1372852701887904993092555 2059279052831857489638833)
        ·
          refine ⟨1544459289623893117229125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2059279052831857489638833 1544459289623893117229125)
          ·
            refine ⟨289586116804479959480461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1544459289623893117229125 289586116804479959480461)
            ·
              refine ⟨108594793801679984805173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 289586116804479959480461 108594793801679984805173)
              ·
                refine ⟨10180761918907498575485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108594793801679984805173 10180761918907498575485)
                ·
                  rfl

theorem cell21_133832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 3, 5].length) (baseStart_133832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_133832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_133832 prefixEnd_133832 := by exact prefixLift 133832
  have htrace : WordTrace (prefixWord ++ tailWord_133832) baseStart_133832 baseEnd_133832 := by
    simpa [prefixWord, tailWord_133832, baseEnd_133832] using wordTrace_append hprefix tailTrace_133832
  have hstable : (prefixWord ++ tailWord_133832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133832).length < 2 ^ (prefixWord ++ tailWord_133832).sum := by decide
  have hdescent : baseEnd_133832 < baseStart_133832 := by decide
  rcases family_descends (prefixWord ++ tailWord_133832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_133905 : List Nat := [1, 2, 2, 1, 1, 3, 2, 2, 7]
def baseStart_133905 : Nat := 118140960795 + 133905 * 2 ^ 59
def prefixEnd_133905 : Nat := 4983230072969 + 3 ^ 40 * 133905 * 2
def baseEnd_133905 : Nat := 30558945351290591009639

theorem tailTrace_133905 : CollatzResearch.WordTrace tailWord_133905 prefixEnd_133905 30558945351290591009639 := by
  unfold tailWord_133905
  simp only [CollatzResearch.WordTrace]
  refine ⟨4883916579892528998403169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3255944386595019332268779 4883916579892528998403169)
  ·
    refine ⟨3662937434919396748802377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4883916579892528998403169 3662937434919396748802377)
    ·
      refine ⟨2747203076189547561601783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3662937434919396748802377 2747203076189547561601783)
      ·
        refine ⟨4120804614284321342402675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2747203076189547561601783 4120804614284321342402675)
        ·
          refine ⟨6181206921426482013604013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4120804614284321342402675 6181206921426482013604013)
          ·
            refine ⟨2317952595534930755101505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6181206921426482013604013 2317952595534930755101505)
            ·
              refine ⟨1738464446651198066326129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2317952595534930755101505 1738464446651198066326129)
              ·
                refine ⟨1303848334988398549744597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1738464446651198066326129 1303848334988398549744597)
                ·
                  refine ⟨30558945351290591009639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1303848334988398549744597 30558945351290591009639)
                  ·
                    rfl

theorem cell21_133905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 2, 7].length) (baseStart_133905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_133905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_133905 prefixEnd_133905 := by exact prefixLift 133905
  have htrace : WordTrace (prefixWord ++ tailWord_133905) baseStart_133905 baseEnd_133905 := by
    simpa [prefixWord, tailWord_133905, baseEnd_133905] using wordTrace_append hprefix tailTrace_133905
  have hstable : (prefixWord ++ tailWord_133905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_133905).length < 2 ^ (prefixWord ++ tailWord_133905).sum := by decide
  have hdescent : baseEnd_133905 < baseStart_133905 := by decide
  rcases family_descends (prefixWord ++ tailWord_133905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134057 : List Nat := [1, 2, 1, 1, 1, 1, 5, 4, 5]
def baseStart_134057 : Nat := 118140960795 + 134057 * 2 ^ 59
def prefixEnd_134057 : Nat := 4983230072969 + 3 ^ 40 * 134057 * 2
def baseEnd_134057 : Nat := 30593633822172104475995

theorem tailTrace_134057 : CollatzResearch.WordTrace tailWord_134057 prefixEnd_134057 30593633822172104475995 := by
  unfold tailWord_134057
  simp only [CollatzResearch.WordTrace]
  refine ⟨4889460475341858957936425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3259640316894572638624283 4889460475341858957936425)
  ·
    refine ⟨3667095356506394218452319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4889460475341858957936425 3667095356506394218452319)
    ·
      refine ⟨5500643034759591327678479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3667095356506394218452319 5500643034759591327678479)
      ·
        refine ⟨8250964552139386991517719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5500643034759591327678479 8250964552139386991517719)
        ·
          refine ⟨12376446828209080487276579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8250964552139386991517719 12376446828209080487276579)
          ·
            refine ⟨18564670242313620730914869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12376446828209080487276579 18564670242313620730914869)
            ·
              refine ⟨1740437835216901943523269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18564670242313620730914869 1740437835216901943523269)
              ·
                refine ⟨326332094103169114410613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1740437835216901943523269 326332094103169114410613)
                ·
                  refine ⟨30593633822172104475995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 326332094103169114410613 30593633822172104475995)
                  ·
                    rfl

theorem cell21_134057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 5].length) (baseStart_134057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_134057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_134057 prefixEnd_134057 := by exact prefixLift 134057
  have htrace : WordTrace (prefixWord ++ tailWord_134057) baseStart_134057 baseEnd_134057 := by
    simpa [prefixWord, tailWord_134057, baseEnd_134057] using wordTrace_append hprefix tailTrace_134057
  have hstable : (prefixWord ++ tailWord_134057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134057).length < 2 ^ (prefixWord ++ tailWord_134057).sum := by decide
  have hdescent : baseEnd_134057 < baseStart_134057 := by decide
  rcases family_descends (prefixWord ++ tailWord_134057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134105 : List Nat := [1, 2, 1, 2, 5, 2, 1, 3, 4]
def baseStart_134105 : Nat := 118140960795 + 134105 * 2 ^ 59
def prefixEnd_134105 : Nat := 4983230072969 + 3 ^ 40 * 134105 * 2
def baseEnd_134105 : Nat := 30604588076134687675897

theorem tailTrace_134105 : CollatzResearch.WordTrace tailWord_134105 prefixEnd_134105 30604588076134687675897 := by
  unfold tailWord_134105
  simp only [CollatzResearch.WordTrace]
  refine ⟨4891211179167963155683769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3260807452778642103789179 4891211179167963155683769)
  ·
    refine ⟨3668408384375972366762827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4891211179167963155683769 3668408384375972366762827)
    ·
      refine ⟨5502612576563958550144241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3668408384375972366762827 5502612576563958550144241)
      ·
        refine ⟨4126959432422968912608181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5502612576563958550144241 4126959432422968912608181)
        ·
          refine ⟨386902446789653335557017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4126959432422968912608181 386902446789653335557017)
          ·
            refine ⟨290176835092240001667763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386902446789653335557017 290176835092240001667763)
            ·
              refine ⟨435265252638360002501645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290176835092240001667763 435265252638360002501645)
              ·
                refine ⟨163224469739385000938117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 435265252638360002501645 163224469739385000938117)
                ·
                  refine ⟨30604588076134687675897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163224469739385000938117 30604588076134687675897)
                  ·
                    rfl

theorem cell21_134105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 3, 4].length) (baseStart_134105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_134105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_134105 prefixEnd_134105 := by exact prefixLift 134105
  have htrace : WordTrace (prefixWord ++ tailWord_134105) baseStart_134105 baseEnd_134105 := by
    simpa [prefixWord, tailWord_134105, baseEnd_134105] using wordTrace_append hprefix tailTrace_134105
  have hstable : (prefixWord ++ tailWord_134105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134105).length < 2 ^ (prefixWord ++ tailWord_134105).sum := by decide
  have hdescent : baseEnd_134105 < baseStart_134105 := by decide
  rcases family_descends (prefixWord ++ tailWord_134105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134119 : List Nat := [1, 1, 5, 2, 2, 1, 2, 7]
def baseStart_134119 : Nat := 118140960795 + 134119 * 2 ^ 59
def prefixEnd_134119 : Nat := 4983230072969 + 3 ^ 40 * 134119 * 2
def baseEnd_134119 : Nat := 10202594355624591480845

theorem tailTrace_134119 : CollatzResearch.WordTrace tailWord_134119 prefixEnd_134119 10202594355624591480845 := by
  unfold tailWord_134119
  simp only [CollatzResearch.WordTrace]
  refine ⟨4891721801117243546693411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3261147867411495697795607 4891721801117243546693411)
  ·
    refine ⟨7337582701675865320040117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4891721801117243546693411 7337582701675865320040117)
    ·
      refine ⟨687898378282112373753761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7337582701675865320040117 687898378282112373753761)
      ·
        refine ⟨515923783711584280315321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 687898378282112373753761 515923783711584280315321)
        ·
          refine ⟨386942837783688210236491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 515923783711584280315321 386942837783688210236491)
          ·
            refine ⟨580414256675532315354737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386942837783688210236491 580414256675532315354737)
            ·
              refine ⟨435310692506649236516053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 580414256675532315354737 435310692506649236516053)
              ·
                refine ⟨10202594355624591480845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 435310692506649236516053 10202594355624591480845)
                ·
                  rfl

theorem cell21_134119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 2, 7].length) (baseStart_134119 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_134119 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_134119 prefixEnd_134119 := by exact prefixLift 134119
  have htrace : WordTrace (prefixWord ++ tailWord_134119) baseStart_134119 baseEnd_134119 := by
    simpa [prefixWord, tailWord_134119, baseEnd_134119] using wordTrace_append hprefix tailTrace_134119
  have hstable : (prefixWord ++ tailWord_134119).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134119).length < 2 ^ (prefixWord ++ tailWord_134119).sum := by decide
  have hdescent : baseEnd_134119 < baseStart_134119 := by decide
  rcases family_descends (prefixWord ++ tailWord_134119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134142 : List Nat := [4, 2, 2, 2, 2, 2, 2, 2, 3]
def baseStart_134142 : Nat := 118140960795 + 134142 * 2 ^ 59
def prefixEnd_134142 : Nat := 4983230072969 + 3 ^ 40 * 134142 * 2
def baseEnd_134142 : Nat := 30613031980230845559155

theorem tailTrace_134142 : CollatzResearch.WordTrace tailWord_134142 prefixEnd_134142 30613031980230845559155 := by
  unfold tailWord_134142
  simp only [CollatzResearch.WordTrace]
  refine ⟨611570085004239809347585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3261707120022612316520453 611570085004239809347585)
  ·
    refine ⟨458677563753179857010689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 611570085004239809347585 458677563753179857010689)
    ·
      refine ⟨344008172814884892758017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458677563753179857010689 344008172814884892758017)
      ·
        refine ⟨258006129611163669568513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344008172814884892758017 258006129611163669568513)
        ·
          refine ⟨193504597208372752176385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258006129611163669568513 193504597208372752176385)
          ·
            refine ⟨145128447906279564132289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193504597208372752176385 145128447906279564132289)
            ·
              refine ⟨108846335929709673099217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145128447906279564132289 108846335929709673099217)
              ·
                refine ⟨81634751947282254824413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108846335929709673099217 81634751947282254824413)
                ·
                  refine ⟨30613031980230845559155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81634751947282254824413 30613031980230845559155)
                  ·
                    rfl

theorem cell21_134142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 2, 3].length) (baseStart_134142 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_134142 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_134142 prefixEnd_134142 := by exact prefixLift 134142
  have htrace : WordTrace (prefixWord ++ tailWord_134142) baseStart_134142 baseEnd_134142 := by
    simpa [prefixWord, tailWord_134142, baseEnd_134142] using wordTrace_append hprefix tailTrace_134142
  have hstable : (prefixWord ++ tailWord_134142).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134142).length < 2 ^ (prefixWord ++ tailWord_134142).sum := by decide
  have hdescent : baseEnd_134142 < baseStart_134142 := by decide
  rcases family_descends (prefixWord ++ tailWord_134142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134198 : List Nat := [5, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_134198 : Nat := 118140960795 + 134198 * 2 ^ 59
def prefixEnd_134198 : Nat := 4983230072969 + 3 ^ 40 * 134198 * 2
def baseEnd_134198 : Nat := 30625811943187192625707

theorem tailTrace_134198 : CollatzResearch.WordTrace tailWord_134198 prefixEnd_134198 30625811943187192625707 := by
  unfold tailWord_134198
  simp only [CollatzResearch.WordTrace]
  refine ⟨305912697989440002426203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3263068778554026692546165 305912697989440002426203)
  ·
    refine ⟨458869046984160003639305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 305912697989440002426203 458869046984160003639305)
    ·
      refine ⟨344151785238120002729479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 458869046984160003639305 344151785238120002729479)
      ·
        refine ⟨516227677857180004094219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344151785238120002729479 516227677857180004094219)
        ·
          refine ⟨774341516785770006141329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516227677857180004094219 774341516785770006141329)
          ·
            refine ⟨580756137589327504605997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 774341516785770006141329 580756137589327504605997)
            ·
              refine ⟨217783551595997814227249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 580756137589327504605997 217783551595997814227249)
              ·
                refine ⟨163337663696998360670437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217783551595997814227249 163337663696998360670437)
                ·
                  refine ⟨30625811943187192625707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163337663696998360670437 30625811943187192625707)
                  ·
                    rfl

theorem cell21_134198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_134198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_134198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_134198 prefixEnd_134198 := by exact prefixLift 134198
  have htrace : WordTrace (prefixWord ++ tailWord_134198) baseStart_134198 baseEnd_134198 := by
    simpa [prefixWord, tailWord_134198, baseEnd_134198] using wordTrace_append hprefix tailTrace_134198
  have hstable : (prefixWord ++ tailWord_134198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134198).length < 2 ^ (prefixWord ++ tailWord_134198).sum := by decide
  have hdescent : baseEnd_134198 < baseStart_134198 := by decide
  rcases family_descends (prefixWord ++ tailWord_134198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134223 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 10]
def baseStart_134223 : Nat := 118140960795 + 134223 * 2 ^ 59
def prefixEnd_134223 : Nat := 4983230072969 + 3 ^ 40 * 134223 * 2
def baseEnd_134223 : Nat := 30631517283792704708989

theorem tailTrace_134223 : CollatzResearch.WordTrace tailWord_134223 prefixEnd_134223 30631517283792704708989 := by
  unfold tailWord_134223
  simp only [CollatzResearch.WordTrace]
  refine ⟨4895514992740469308479323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3263676661826979538986215 4895514992740469308479323)
  ·
    refine ⟨7343272489110703962718985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4895514992740469308479323 7343272489110703962718985)
    ·
      refine ⟨5507454366833027972039239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7343272489110703962718985 5507454366833027972039239)
      ·
        refine ⟨8261181550249541958058859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5507454366833027972039239 8261181550249541958058859)
        ·
          refine ⟨12391772325374312937088289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8261181550249541958058859 12391772325374312937088289)
          ·
            refine ⟨9293829244030734702816217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12391772325374312937088289 9293829244030734702816217)
            ·
              refine ⟨6970371933023051027112163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9293829244030734702816217 6970371933023051027112163)
              ·
                refine ⟨10455557899534576540668245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6970371933023051027112163 10455557899534576540668245)
                ·
                  refine ⟨30631517283792704708989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 10455557899534576540668245 30631517283792704708989)
                  ·
                    rfl

theorem cell21_134223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 10].length) (baseStart_134223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_134223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_134223 prefixEnd_134223 := by exact prefixLift 134223
  have htrace : WordTrace (prefixWord ++ tailWord_134223) baseStart_134223 baseEnd_134223 := by
    simpa [prefixWord, tailWord_134223, baseEnd_134223] using wordTrace_append hprefix tailTrace_134223
  have hstable : (prefixWord ++ tailWord_134223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134223).length < 2 ^ (prefixWord ++ tailWord_134223).sum := by decide
  have hdescent : baseEnd_134223 < baseStart_134223 := by decide
  rcases family_descends (prefixWord ++ tailWord_134223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134226 : List Nat := [3, 2, 2, 1, 3, 1, 2, 2, 5]
def baseStart_134226 : Nat := 118140960795 + 134226 * 2 ^ 59
def prefixEnd_134226 : Nat := 4983230072969 + 3 ^ 40 * 134226 * 2
def baseEnd_134226 : Nat := 30632201924665366158983

theorem tailTrace_134226 : CollatzResearch.WordTrace tailWord_134226 prefixEnd_134226 30632201924665366158983 := by
  unfold tailWord_134226
  simp only [CollatzResearch.WordTrace]
  refine ⟨1223906102932400205209633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3263749607819733880559021 1223906102932400205209633)
  ·
    refine ⟨917929577199300153907225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1223906102932400205209633 917929577199300153907225)
    ·
      refine ⟨688447182899475115430419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 917929577199300153907225 688447182899475115430419)
      ·
        refine ⟨1032670774349212673145629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 688447182899475115430419 1032670774349212673145629)
        ·
          refine ⟨387251540380954752429611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1032670774349212673145629 387251540380954752429611)
          ·
            refine ⟨580877310571432128644417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387251540380954752429611 580877310571432128644417)
            ·
              refine ⟨435657982928574096483313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 580877310571432128644417 435657982928574096483313)
              ·
                refine ⟨326743487196430572362485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 435657982928574096483313 326743487196430572362485)
                ·
                  refine ⟨30632201924665366158983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 326743487196430572362485 30632201924665366158983)
                  ·
                    rfl

theorem cell21_134226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_134226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_134226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_134226 prefixEnd_134226 := by exact prefixLift 134226
  have htrace : WordTrace (prefixWord ++ tailWord_134226) baseStart_134226 baseEnd_134226 := by
    simpa [prefixWord, tailWord_134226, baseEnd_134226] using wordTrace_append hprefix tailTrace_134226
  have hstable : (prefixWord ++ tailWord_134226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134226).length < 2 ^ (prefixWord ++ tailWord_134226).sum := by decide
  have hdescent : baseEnd_134226 < baseStart_134226 := by decide
  rcases family_descends (prefixWord ++ tailWord_134226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134319 : List Nat := [1, 1, 2, 1, 2, 3, 6, 2, 3]
def baseStart_134319 : Nat := 118140960795 + 134319 * 2 ^ 59
def prefixEnd_134319 : Nat := 4983230072969 + 3 ^ 40 * 134319 * 2
def baseEnd_134319 : Nat := 30653425791717871108793

theorem tailTrace_134319 : CollatzResearch.WordTrace tailWord_134319 prefixEnd_134319 30653425791717871108793 := by
  unfold tailWord_134319
  simp only [CollatzResearch.WordTrace]
  refine ⟨4899016400392677703974011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3266010933595118469316007 4899016400392677703974011)
  ·
    refine ⟨7348524600589016555961017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4899016400392677703974011 7348524600589016555961017)
    ·
      refine ⟨5511393450441762416970763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7348524600589016555961017 5511393450441762416970763)
      ·
        refine ⟨8267090175662643625456145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5511393450441762416970763 8267090175662643625456145)
        ·
          refine ⟨6200317631746982719092109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8267090175662643625456145 6200317631746982719092109)
          ·
            refine ⟨2325119111905118519659541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6200317631746982719092109 2325119111905118519659541)
            ·
              refine ⟨108989958370552430609041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2325119111905118519659541 108989958370552430609041)
              ·
                refine ⟨81742468777914322956781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108989958370552430609041 81742468777914322956781)
                ·
                  refine ⟨30653425791717871108793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81742468777914322956781 30653425791717871108793)
                  ·
                    rfl

theorem cell21_134319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 6, 2, 3].length) (baseStart_134319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_134319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_134319 prefixEnd_134319 := by exact prefixLift 134319
  have htrace : WordTrace (prefixWord ++ tailWord_134319) baseStart_134319 baseEnd_134319 := by
    simpa [prefixWord, tailWord_134319, baseEnd_134319] using wordTrace_append hprefix tailTrace_134319
  have hstable : (prefixWord ++ tailWord_134319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134319).length < 2 ^ (prefixWord ++ tailWord_134319).sum := by decide
  have hdescent : baseEnd_134319 < baseStart_134319 := by decide
  rcases family_descends (prefixWord ++ tailWord_134319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134378 : List Nat := [3, 1, 3, 1, 1, 4, 2, 1, 5]
def baseStart_134378 : Nat := 118140960795 + 134378 * 2 ^ 59
def prefixEnd_134378 : Nat := 4983230072969 + 3 ^ 40 * 134378 * 2
def baseEnd_134378 : Nat := 30666890395546879625339

theorem tailTrace_134378 : CollatzResearch.WordTrace tailWord_134378 prefixEnd_134378 30666890395546879625339 := by
  unfold tailWord_134378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1225292076794732695092947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3267445538119287186914525 1225292076794732695092947)
  ·
    refine ⟨1837938115192099042639421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1225292076794732695092947 1837938115192099042639421)
    ·
      refine ⟨689226793197037140989783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1837938115192099042639421 689226793197037140989783)
      ·
        refine ⟨1033840189795555711484675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 689226793197037140989783 1033840189795555711484675)
        ·
          refine ⟨1550760284693333567227013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1033840189795555711484675 1550760284693333567227013)
          ·
            refine ⟨290767553380000043855065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1550760284693333567227013 290767553380000043855065)
            ·
              refine ⟨218075665035000032891299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290767553380000043855065 218075665035000032891299)
              ·
                refine ⟨327113497552500049336949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 218075665035000032891299 327113497552500049336949)
                ·
                  refine ⟨30666890395546879625339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 327113497552500049336949 30666890395546879625339)
                  ·
                    rfl

theorem cell21_134378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_134378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_134378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_134378 prefixEnd_134378 := by exact prefixLift 134378
  have htrace : WordTrace (prefixWord ++ tailWord_134378) baseStart_134378 baseEnd_134378 := by
    simpa [prefixWord, tailWord_134378, baseEnd_134378] using wordTrace_append hprefix tailTrace_134378
  have hstable : (prefixWord ++ tailWord_134378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134378).length < 2 ^ (prefixWord ++ tailWord_134378).sum := by decide
  have hdescent : baseEnd_134378 < baseStart_134378 := by decide
  rcases family_descends (prefixWord ++ tailWord_134378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134485 : List Nat := [1, 3, 2, 2, 3, 2, 2, 2, 4]
def baseStart_134485 : Nat := 118140960795 + 134485 * 2 ^ 59
def prefixEnd_134485 : Nat := 4983230072969 + 3 ^ 40 * 134485 * 2
def baseEnd_134485 : Nat := 30691309253338471341787

theorem tailTrace_134485 : CollatzResearch.WordTrace tailWord_134485 prefixEnd_134485 30691309253338471341787 := by
  unfold tailWord_134485
  simp only [CollatzResearch.WordTrace]
  refine ⟨4905070917791288054516909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3270047278527525369677939 4905070917791288054516909)
  ·
    refine ⟨1839401594171733020443841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4905070917791288054516909 1839401594171733020443841)
    ·
      refine ⟨1379551195628799765332881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1839401594171733020443841 1379551195628799765332881)
      ·
        refine ⟨1034663396721599823999661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1379551195628799765332881 1034663396721599823999661)
        ·
          refine ⟨387998773770599933999873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1034663396721599823999661 387998773770599933999873)
          ·
            refine ⟨290999080327949950499905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387998773770599933999873 290999080327949950499905)
            ·
              refine ⟨218249310245962462874929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290999080327949950499905 218249310245962462874929)
              ·
                refine ⟨163686982684471847156197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218249310245962462874929 163686982684471847156197)
                ·
                  refine ⟨30691309253338471341787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163686982684471847156197 30691309253338471341787)
                  ·
                    rfl

theorem cell21_134485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 2, 2, 4].length) (baseStart_134485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_134485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_134485 prefixEnd_134485 := by exact prefixLift 134485
  have htrace : WordTrace (prefixWord ++ tailWord_134485) baseStart_134485 baseEnd_134485 := by
    simpa [prefixWord, tailWord_134485, baseEnd_134485] using wordTrace_append hprefix tailTrace_134485
  have hstable : (prefixWord ++ tailWord_134485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134485).length < 2 ^ (prefixWord ++ tailWord_134485).sum := by decide
  have hdescent : baseEnd_134485 < baseStart_134485 := by decide
  rcases family_descends (prefixWord ++ tailWord_134485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134499 : List Nat := [1, 1, 1, 5, 2, 4, 1, 6]
def baseStart_134499 : Nat := 118140960795 + 134499 * 2 ^ 59
def prefixEnd_134499 : Nat := 4983230072969 + 3 ^ 40 * 134499 * 2
def baseEnd_134499 : Nat := 10231501414692519369475

theorem tailTrace_134499 : CollatzResearch.WordTrace tailWord_134499 prefixEnd_134499 10231501414692519369475 := by
  unfold tailWord_134499
  simp only [CollatzResearch.WordTrace]
  refine ⟨4905581539740568445526551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3270387693160378963684367 4905581539740568445526551)
  ·
    refine ⟨7358372309610852668289827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4905581539740568445526551 7358372309610852668289827)
    ·
      refine ⟨11037558464416279002434741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7358372309610852668289827 11037558464416279002434741)
      ·
        refine ⟨1034771106039026156478257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11037558464416279002434741 1034771106039026156478257)
        ·
          refine ⟨776078329529269617358693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1034771106039026156478257 776078329529269617358693)
          ·
            refine ⟨145514686786738053254755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 776078329529269617358693 145514686786738053254755)
            ·
              refine ⟨218272030180107079882133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145514686786738053254755 218272030180107079882133)
              ·
                refine ⟨10231501414692519369475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 218272030180107079882133 10231501414692519369475)
                ·
                  rfl

theorem cell21_134499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 6].length) (baseStart_134499 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_134499 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_134499 prefixEnd_134499 := by exact prefixLift 134499
  have htrace : WordTrace (prefixWord ++ tailWord_134499) baseStart_134499 baseEnd_134499 := by
    simpa [prefixWord, tailWord_134499, baseEnd_134499] using wordTrace_append hprefix tailTrace_134499
  have hstable : (prefixWord ++ tailWord_134499).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134499).length < 2 ^ (prefixWord ++ tailWord_134499).sum := by decide
  have hdescent : baseEnd_134499 < baseStart_134499 := by decide
  rcases family_descends (prefixWord ++ tailWord_134499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134603 : List Nat := [1, 1, 1, 1, 3, 3, 4, 1, 6]
def baseStart_134603 : Nat := 118140960795 + 134603 * 2 ^ 59
def prefixEnd_134603 : Nat := 4983230072969 + 3 ^ 40 * 134603 * 2
def baseEnd_134603 : Nat := 30718238460996488374879

theorem tailTrace_134603 : CollatzResearch.WordTrace tailWord_134603 prefixEnd_134603 30718238460996488374879 := by
  unfold tailWord_134603
  simp only [CollatzResearch.WordTrace]
  refine ⟨4909374731363794207312463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3272916487575862804874975 4909374731363794207312463)
  ·
    refine ⟨7364062097045691310968695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4909374731363794207312463 7364062097045691310968695)
    ·
      refine ⟨11046093145568536966453043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7364062097045691310968695 11046093145568536966453043)
      ·
        refine ⟨16569139718352805449679565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11046093145568536966453043 16569139718352805449679565)
        ·
          refine ⟨6213427394382302043629837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16569139718352805449679565 6213427394382302043629837)
          ·
            refine ⟨2330035272893363266361189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6213427394382302043629837 2330035272893363266361189)
            ·
              refine ⟨436881613667505612442723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2330035272893363266361189 436881613667505612442723)
              ·
                refine ⟨655322420501258418664085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 436881613667505612442723 655322420501258418664085)
                ·
                  refine ⟨30718238460996488374879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 655322420501258418664085 30718238460996488374879)
                  ·
                    rfl

theorem cell21_134603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 6].length) (baseStart_134603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_134603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_134603 prefixEnd_134603 := by exact prefixLift 134603
  have htrace : WordTrace (prefixWord ++ tailWord_134603) baseStart_134603 baseEnd_134603 := by
    simpa [prefixWord, tailWord_134603, baseEnd_134603] using wordTrace_append hprefix tailTrace_134603
  have hstable : (prefixWord ++ tailWord_134603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134603).length < 2 ^ (prefixWord ++ tailWord_134603).sum := by decide
  have hdescent : baseEnd_134603 < baseStart_134603 := by decide
  rcases family_descends (prefixWord ++ tailWord_134603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134606 : List Nat := [4, 1, 1, 1, 2, 1, 2, 6, 3]
def baseStart_134606 : Nat := 118140960795 + 134606 * 2 ^ 59
def prefixEnd_134606 : Nat := 4983230072969 + 3 ^ 40 * 134606 * 2
def baseEnd_134606 : Nat := 30718923101869149824873

theorem tailTrace_134606 : CollatzResearch.WordTrace tailWord_134606 prefixEnd_134606 30718923101869149824873 := by
  unfold tailWord_134606
  simp only [CollatzResearch.WordTrace]
  refine ⟨613685518794115714958959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3272989433568617146447781 613685518794115714958959)
  ·
    refine ⟨920528278191173572438439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 613685518794115714958959 920528278191173572438439)
    ·
      refine ⟨1380792417286760358657659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 920528278191173572438439 1380792417286760358657659)
      ·
        refine ⟨2071188625930140537986489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1380792417286760358657659 2071188625930140537986489)
        ·
          refine ⟨1553391469447605403489867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2071188625930140537986489 1553391469447605403489867)
          ·
            refine ⟨2330087204171408105234801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1553391469447605403489867 2330087204171408105234801)
            ·
              refine ⟨1747565403128556078926101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2330087204171408105234801 1747565403128556078926101)
              ·
                refine ⟨81917128271651066199661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1747565403128556078926101 81917128271651066199661)
                ·
                  refine ⟨30718923101869149824873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81917128271651066199661 30718923101869149824873)
                  ·
                    rfl

theorem cell21_134606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 6, 3].length) (baseStart_134606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_134606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_134606 prefixEnd_134606 := by exact prefixLift 134606
  have htrace : WordTrace (prefixWord ++ tailWord_134606) baseStart_134606 baseEnd_134606 := by
    simpa [prefixWord, tailWord_134606, baseEnd_134606] using wordTrace_append hprefix tailTrace_134606
  have hstable : (prefixWord ++ tailWord_134606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134606).length < 2 ^ (prefixWord ++ tailWord_134606).sum := by decide
  have hdescent : baseEnd_134606 < baseStart_134606 := by decide
  rcases family_descends (prefixWord ++ tailWord_134606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134657 : List Nat := [1, 2, 4, 1, 5, 1, 2, 2, 3]
def baseStart_134657 : Nat := 118140960795 + 134657 * 2 ^ 59
def prefixEnd_134657 : Nat := 4983230072969 + 3 ^ 40 * 134657 * 2
def baseEnd_134657 : Nat := 30730561996704394474769

theorem tailTrace_134657 : CollatzResearch.WordTrace tailWord_134657 prefixEnd_134657 30730561996704394474769 := by
  unfold tailWord_134657
  simp only [CollatzResearch.WordTrace]
  refine ⟨4911344273168161429778225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3274229515445440953185483 4911344273168161429778225)
  ·
    refine ⟨3683508204876121072333669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4911344273168161429778225 3683508204876121072333669)
    ·
      refine ⟨690657788414272701062563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3683508204876121072333669 690657788414272701062563)
      ·
        refine ⟨1035986682621409051593845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 690657788414272701062563 1035986682621409051593845)
        ·
          refine ⟨97123751495757098586923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1035986682621409051593845 97123751495757098586923)
          ·
            refine ⟨145685627243635647880385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97123751495757098586923 145685627243635647880385)
            ·
              refine ⟨109264220432726735910289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145685627243635647880385 109264220432726735910289)
              ·
                refine ⟨81948165324545051932717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 109264220432726735910289 81948165324545051932717)
                ·
                  refine ⟨30730561996704394474769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81948165324545051932717 30730561996704394474769)
                  ·
                    rfl

theorem cell21_134657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 3].length) (baseStart_134657 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_134657 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_134657 prefixEnd_134657 := by exact prefixLift 134657
  have htrace : WordTrace (prefixWord ++ tailWord_134657) baseStart_134657 baseEnd_134657 := by
    simpa [prefixWord, tailWord_134657, baseEnd_134657] using wordTrace_append hprefix tailTrace_134657
  have hstable : (prefixWord ++ tailWord_134657).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134657).length < 2 ^ (prefixWord ++ tailWord_134657).sum := by decide
  have hdescent : baseEnd_134657 < baseStart_134657 := by decide
  rcases family_descends (prefixWord ++ tailWord_134657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134668 : List Nat := [2, 2, 1, 2, 6, 1, 1, 6]
def baseStart_134668 : Nat := 118140960795 + 134668 * 2 ^ 59
def prefixEnd_134668 : Nat := 4983230072969 + 3 ^ 40 * 134668 * 2
def baseEnd_134668 : Nat := 10244357448856939930471

theorem tailTrace_134668 : CollatzResearch.WordTrace tailWord_134668 prefixEnd_134668 10244357448856939930471 := by
  unfold tailWord_134668
  simp only [CollatzResearch.WordTrace]
  refine ⟨2455872738064155154214329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3274496984085540205619105 2455872738064155154214329)
  ·
    refine ⟨1841904553548116365660747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2455872738064155154214329 1841904553548116365660747)
    ·
      refine ⟨2762856830322174548491121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1841904553548116365660747 2762856830322174548491121)
      ·
        refine ⟨2072142622741630911368341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2762856830322174548491121 2072142622741630911368341)
        ·
          refine ⟨97131685441013948970391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2072142622741630911368341 97131685441013948970391)
          ·
            refine ⟨145697528161520923455587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97131685441013948970391 145697528161520923455587)
            ·
              refine ⟨218546292242281385183381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145697528161520923455587 218546292242281385183381)
              ·
                refine ⟨10244357448856939930471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 218546292242281385183381 10244357448856939930471)
                ·
                  rfl

theorem cell21_134668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 6, 1, 1, 6].length) (baseStart_134668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_134668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_134668 prefixEnd_134668 := by exact prefixLift 134668
  have htrace : WordTrace (prefixWord ++ tailWord_134668) baseStart_134668 baseEnd_134668 := by
    simpa [prefixWord, tailWord_134668, baseEnd_134668] using wordTrace_append hprefix tailTrace_134668
  have hstable : (prefixWord ++ tailWord_134668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134668).length < 2 ^ (prefixWord ++ tailWord_134668).sum := by decide
  have hdescent : baseEnd_134668 < baseStart_134668 := by decide
  rcases family_descends (prefixWord ++ tailWord_134668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134713 : List Nat := [1, 2, 1, 5, 1, 4, 1, 2, 4]
def baseStart_134713 : Nat := 118140960795 + 134713 * 2 ^ 59
def prefixEnd_134713 : Nat := 4983230072969 + 3 ^ 40 * 134713 * 2
def baseEnd_134713 : Nat := 30743341959660741541321

theorem tailTrace_134713 : CollatzResearch.WordTrace tailWord_134713 prefixEnd_134713 30743341959660741541321 := by
  unfold tailWord_134713
  simp only [CollatzResearch.WordTrace]
  refine ⟨4913386760965282993816793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3275591173976855329211195 4913386760965282993816793)
  ·
    refine ⟨3685040070723962245362595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4913386760965282993816793 3685040070723962245362595)
    ·
      refine ⟨5527560106085943368043893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3685040070723962245362595 5527560106085943368043893)
      ·
        refine ⟨518208759945557190754115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5527560106085943368043893 518208759945557190754115)
        ·
          refine ⟨777313139918335786131173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518208759945557190754115 777313139918335786131173)
          ·
            refine ⟨145746213734687959899595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 777313139918335786131173 145746213734687959899595)
            ·
              refine ⟨218619320602031939849393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145746213734687959899595 218619320602031939849393)
              ·
                refine ⟨163964490451523954887045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 218619320602031939849393 163964490451523954887045)
                ·
                  refine ⟨30743341959660741541321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163964490451523954887045 30743341959660741541321)
                  ·
                    rfl

theorem cell21_134713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 4].length) (baseStart_134713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_134713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_134713 prefixEnd_134713 := by exact prefixLift 134713
  have htrace : WordTrace (prefixWord ++ tailWord_134713) baseStart_134713 baseEnd_134713 := by
    simpa [prefixWord, tailWord_134713, baseEnd_134713] using wordTrace_append hprefix tailTrace_134713
  have hstable : (prefixWord ++ tailWord_134713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134713).length < 2 ^ (prefixWord ++ tailWord_134713).sum := by decide
  have hdescent : baseEnd_134713 < baseStart_134713 := by decide
  rcases family_descends (prefixWord ++ tailWord_134713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134755 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 6]
def baseStart_134755 : Nat := 118140960795 + 134755 * 2 ^ 59
def prefixEnd_134755 : Nat := 4983230072969 + 3 ^ 40 * 134755 * 2
def baseEnd_134755 : Nat := 30752926931878001841235

theorem tailTrace_134755 : CollatzResearch.WordTrace tailWord_134755 prefixEnd_134755 30752926931878001841235 := by
  unfold tailWord_134755
  simp only [CollatzResearch.WordTrace]
  refine ⟨4914918626813124166845719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3276612417875416111230479 4914918626813124166845719)
  ·
    refine ⟨7372377940219686250268579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4914918626813124166845719 7372377940219686250268579)
    ·
      refine ⟨11058566910329529375402869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7372377940219686250268579 11058566910329529375402869)
      ·
        refine ⟨1036740647843393378944019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11058566910329529375402869 1036740647843393378944019)
        ·
          refine ⟨1555110971765090068416029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1036740647843393378944019 1555110971765090068416029)
          ·
            refine ⟨583166614411908775656011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1555110971765090068416029 583166614411908775656011)
            ·
              refine ⟨874749921617863163484017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 583166614411908775656011 874749921617863163484017)
              ·
                refine ⟨656062441213397372613013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 874749921617863163484017 656062441213397372613013)
                ·
                  refine ⟨30752926931878001841235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 656062441213397372613013 30752926931878001841235)
                  ·
                    rfl

theorem cell21_134755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 6].length) (baseStart_134755 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_134755 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_134755 prefixEnd_134755 := by exact prefixLift 134755
  have htrace : WordTrace (prefixWord ++ tailWord_134755) baseStart_134755 baseEnd_134755 := by
    simpa [prefixWord, tailWord_134755, baseEnd_134755] using wordTrace_append hprefix tailTrace_134755
  have hstable : (prefixWord ++ tailWord_134755).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134755).length < 2 ^ (prefixWord ++ tailWord_134755).sum := by decide
  have hdescent : baseEnd_134755 < baseStart_134755 := by decide
  rcases family_descends (prefixWord ++ tailWord_134755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134800 : List Nat := [2, 1, 1, 1, 1, 1, 3, 6, 5]
def baseStart_134800 : Nat := 118140960795 + 134800 * 2 ^ 59
def prefixEnd_134800 : Nat := 4983230072969 + 3 ^ 40 * 134800 * 2
def baseEnd_134800 : Nat := 30763196544967923591143

theorem tailTrace_134800 : CollatzResearch.WordTrace tailWord_134800 prefixEnd_134800 30763196544967923591143 := by
  unfold tailWord_134800
  simp only [CollatzResearch.WordTrace]
  refine ⟨2458279955825048426116927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3277706607766731234822569 2458279955825048426116927)
  ·
    refine ⟨3687419933737572639175391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2458279955825048426116927 3687419933737572639175391)
    ·
      refine ⟨5531129900606358958763087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3687419933737572639175391 5531129900606358958763087)
      ·
        refine ⟨8296694850909538438144631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5531129900606358958763087 8296694850909538438144631)
        ·
          refine ⟨12445042276364307657216947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8296694850909538438144631 12445042276364307657216947)
          ·
            refine ⟨18667563414546461485825421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12445042276364307657216947 18667563414546461485825421)
            ·
              refine ⟨7000336280454923057184533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18667563414546461485825421 7000336280454923057184533)
              ·
                refine ⟨328140763146324518305525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7000336280454923057184533 328140763146324518305525)
                ·
                  refine ⟨30763196544967923591143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 328140763146324518305525 30763196544967923591143)
                  ·
                    rfl

theorem cell21_134800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 6, 5].length) (baseStart_134800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_134800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_134800 prefixEnd_134800 := by exact prefixLift 134800
  have htrace : WordTrace (prefixWord ++ tailWord_134800) baseStart_134800 baseEnd_134800 := by
    simpa [prefixWord, tailWord_134800, baseEnd_134800] using wordTrace_append hprefix tailTrace_134800
  have hstable : (prefixWord ++ tailWord_134800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134800).length < 2 ^ (prefixWord ++ tailWord_134800).sum := by decide
  have hdescent : baseEnd_134800 < baseStart_134800 := by decide
  rcases family_descends (prefixWord ++ tailWord_134800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134893 : List Nat := [1, 5, 1, 2, 1, 2, 1, 3, 5]
def baseStart_134893 : Nat := 118140960795 + 134893 * 2 ^ 59
def prefixEnd_134893 : Nat := 4983230072969 + 3 ^ 40 * 134893 * 2
def baseEnd_134893 : Nat := 30784420412020428540953

theorem tailTrace_134893 : CollatzResearch.WordTrace tailWord_134893 prefixEnd_134893 30784420412020428540953 := by
  unfold tailWord_134893
  simp only [CollatzResearch.WordTrace]
  refine ⟨4919951900313173735369333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3279967933542115823579555 4919951900313173735369333)
  ·
    refine ⟨461245490654360037690875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4919951900313173735369333 461245490654360037690875)
    ·
      refine ⟨691868235981540056536313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 461245490654360037690875 691868235981540056536313)
      ·
        refine ⟨518901176986155042402235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 691868235981540056536313 518901176986155042402235)
        ·
          refine ⟨778351765479232563603353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 518901176986155042402235 778351765479232563603353)
          ·
            refine ⟨583763824109424422702515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 778351765479232563603353 583763824109424422702515)
            ·
              refine ⟨875645736164136634053773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 583763824109424422702515 875645736164136634053773)
              ·
                refine ⟨328367151061551237770165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 875645736164136634053773 328367151061551237770165)
                ·
                  refine ⟨30784420412020428540953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 328367151061551237770165 30784420412020428540953)
                  ·
                    rfl

theorem cell21_134893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_134893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_134893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_134893 prefixEnd_134893 := by exact prefixLift 134893
  have htrace : WordTrace (prefixWord ++ tailWord_134893) baseStart_134893 baseEnd_134893 := by
    simpa [prefixWord, tailWord_134893, baseEnd_134893] using wordTrace_append hprefix tailTrace_134893
  have hstable : (prefixWord ++ tailWord_134893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134893).length < 2 ^ (prefixWord ++ tailWord_134893).sum := by decide
  have hdescent : baseEnd_134893 < baseStart_134893 := by decide
  rcases family_descends (prefixWord ++ tailWord_134893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134938 : List Nat := [3, 1, 1, 3, 2, 4, 7]
def baseStart_134938 : Nat := 118140960795 + 134938 * 2 ^ 59
def prefixEnd_134938 : Nat := 4983230072969 + 3 ^ 40 * 134938 * 2
def baseEnd_134938 : Nat := 3421632225012261143429

theorem tailTrace_134938 : CollatzResearch.WordTrace tailWord_134938 prefixEnd_134938 3421632225012261143429 := by
  unfold tailWord_134938
  simp only [CollatzResearch.WordTrace]
  refine ⟨1230398296287536605189367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3281062123433430947171645 1230398296287536605189367)
  ·
    refine ⟨1845597444431304907784051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1230398296287536605189367 1845597444431304907784051)
    ·
      refine ⟨2768396166646957361676077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1845597444431304907784051 2768396166646957361676077)
      ·
        refine ⟨1038148562492609010628529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2768396166646957361676077 1038148562492609010628529)
        ·
          refine ⟨778611421869456757971397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1038148562492609010628529 778611421869456757971397)
          ·
            refine ⟨145989641600523142119637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 778611421869456757971397 145989641600523142119637)
            ·
              refine ⟨3421632225012261143429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 145989641600523142119637 3421632225012261143429)
              ·
                rfl

theorem cell21_134938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 4, 7].length) (baseStart_134938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_134938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_134938 prefixEnd_134938 := by exact prefixLift 134938
  have htrace : WordTrace (prefixWord ++ tailWord_134938) baseStart_134938 baseEnd_134938 := by
    simpa [prefixWord, tailWord_134938, baseEnd_134938] using wordTrace_append hprefix tailTrace_134938
  have hstable : (prefixWord ++ tailWord_134938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134938).length < 2 ^ (prefixWord ++ tailWord_134938).sum := by decide
  have hdescent : baseEnd_134938 < baseStart_134938 := by decide
  rcases family_descends (prefixWord ++ tailWord_134938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_134997 : List Nat := [1, 3, 2, 2, 2, 11]
def baseStart_134997 : Nat := 118140960795 + 134997 * 2 ^ 59
def prefixEnd_134997 : Nat := 4983230072969 + 3 ^ 40 * 134997 * 2
def baseEnd_134997 : Nat := 1141042764034791066941

theorem tailTrace_134997 : CollatzResearch.WordTrace tailWord_134997 prefixEnd_134997 1141042764034791066941 := by
  unfold tailWord_134997
  simp only [CollatzResearch.WordTrace]
  refine ⟨4923745091936399497155245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3282496727957599664770163 4923745091936399497155245)
  ·
    refine ⟨1846404409476149811433217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4923745091936399497155245 1846404409476149811433217)
    ·
      refine ⟨1384803307107112358574913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1846404409476149811433217 1384803307107112358574913)
      ·
        refine ⟨1038602480330334268931185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1384803307107112358574913 1038602480330334268931185)
        ·
          refine ⟨778951860247750701698389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1038602480330334268931185 778951860247750701698389)
          ·
            refine ⟨1141042764034791066941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 778951860247750701698389 1141042764034791066941)
            ·
              rfl

theorem cell21_134997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 11].length) (baseStart_134997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_134997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_134997 prefixEnd_134997 := by exact prefixLift 134997
  have htrace : WordTrace (prefixWord ++ tailWord_134997) baseStart_134997 baseEnd_134997 := by
    simpa [prefixWord, tailWord_134997, baseEnd_134997] using wordTrace_append hprefix tailTrace_134997
  have hstable : (prefixWord ++ tailWord_134997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_134997).length < 2 ^ (prefixWord ++ tailWord_134997).sum := by decide
  have hdescent : baseEnd_134997 < baseStart_134997 := by decide
  rcases family_descends (prefixWord ++ tailWord_134997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135166 : List Nat := [4, 2, 2, 2, 1, 10]
def baseStart_135166 : Nat := 118140960795 + 135166 * 2 ^ 59
def prefixEnd_135166 : Nat := 4983230072969 + 3 ^ 40 * 135166 * 2
def baseEnd_135166 : Nat := 1142471212275282240385

theorem tailTrace_135166 : CollatzResearch.WordTrace tailWord_135166 prefixEnd_135166 1142471212275282240385 := by
  unfold tailWord_135166
  simp only [CollatzResearch.WordTrace]
  refine ⟨616238628540517670007169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3286606018882760906704901 616238628540517670007169)
  ·
    refine ⟨462178971405388252505377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 616238628540517670007169 462178971405388252505377)
    ·
      refine ⟨346634228554041189379033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 462178971405388252505377 346634228554041189379033)
      ·
        refine ⟨259975671415530892034275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 346634228554041189379033 259975671415530892034275)
        ·
          refine ⟨389963507123296338051413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 259975671415530892034275 389963507123296338051413)
          ·
            refine ⟨1142471212275282240385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 389963507123296338051413 1142471212275282240385)
            ·
              rfl

theorem cell21_135166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 10].length) (baseStart_135166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_135166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_135166 prefixEnd_135166 := by exact prefixLift 135166
  have htrace : WordTrace (prefixWord ++ tailWord_135166) baseStart_135166 baseEnd_135166 := by
    simpa [prefixWord, tailWord_135166, baseEnd_135166] using wordTrace_append hprefix tailTrace_135166
  have hstable : (prefixWord ++ tailWord_135166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135166).length < 2 ^ (prefixWord ++ tailWord_135166).sum := by decide
  have hdescent : baseEnd_135166 < baseStart_135166 := by decide
  rcases family_descends (prefixWord ++ tailWord_135166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135180 : List Nat := [2, 2, 1, 2, 3, 1, 2, 3, 5]
def baseStart_135180 : Nat := 118140960795 + 135180 * 2 ^ 59
def prefixEnd_135180 : Nat := 4983230072969 + 3 ^ 40 * 135180 * 2
def baseEnd_135180 : Nat := 30849917722171707257033

theorem tailTrace_135180 : CollatzResearch.WordTrace tailWord_135180 prefixEnd_135180 30849917722171707257033 := by
  unfold tailWord_135180
  simp only [CollatzResearch.WordTrace]
  refine ⟨2465209825136710875533497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3286946433515614500711329 2465209825136710875533497)
  ·
    refine ⟨1848907368852533156650123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2465209825136710875533497 1848907368852533156650123)
    ·
      refine ⟨2773361053278799734975185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1848907368852533156650123 2773361053278799734975185)
      ·
        refine ⟨2080020789959099801231389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2773361053278799734975185 2080020789959099801231389)
        ·
          refine ⟨780007796234662425461771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2080020789959099801231389 780007796234662425461771)
          ·
            refine ⟨1170011694351993638192657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 780007796234662425461771 1170011694351993638192657)
            ·
              refine ⟨877508770763995228644493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1170011694351993638192657 877508770763995228644493)
              ·
                refine ⟨329065789036498210741685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 877508770763995228644493 329065789036498210741685)
                ·
                  refine ⟨30849917722171707257033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 329065789036498210741685 30849917722171707257033)
                  ·
                    rfl

theorem cell21_135180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_135180 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_135180 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_135180 prefixEnd_135180 := by exact prefixLift 135180
  have htrace : WordTrace (prefixWord ++ tailWord_135180) baseStart_135180 baseEnd_135180 := by
    simpa [prefixWord, tailWord_135180, baseEnd_135180] using wordTrace_append hprefix tailTrace_135180
  have hstable : (prefixWord ++ tailWord_135180).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135180).length < 2 ^ (prefixWord ++ tailWord_135180).sum := by decide
  have hdescent : baseEnd_135180 < baseStart_135180 := by decide
  rcases family_descends (prefixWord ++ tailWord_135180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135197 : List Nat := [1, 4, 2, 2, 2, 2, 1, 2, 5]
def baseStart_135197 : Nat := 118140960795 + 135197 * 2 ^ 59
def prefixEnd_135197 : Nat := 4983230072969 + 3 ^ 40 * 135197 * 2
def baseEnd_135197 : Nat := 30853797353783455473665

theorem tailTrace_135197 : CollatzResearch.WordTrace tailWord_135197 prefixEnd_135197 30853797353783455473665 := by
  unfold tailWord_135197
  simp only [CollatzResearch.WordTrace]
  refine ⟨4931039691211833654435845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3287359794141222436290563 4931039691211833654435845)
  ·
    refine ⟨924569942102218810206721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4931039691211833654435845 924569942102218810206721)
    ·
      refine ⟨693427456576664107655041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 924569942102218810206721 693427456576664107655041)
      ·
        refine ⟨520070592432498080741281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 693427456576664107655041 520070592432498080741281)
        ·
          refine ⟨390052944324373560555961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 520070592432498080741281 390052944324373560555961)
          ·
            refine ⟨292539708243280170416971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 390052944324373560555961 292539708243280170416971)
            ·
              refine ⟨438809562364920255625457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292539708243280170416971 438809562364920255625457)
              ·
                refine ⟨329107171773690191719093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 438809562364920255625457 329107171773690191719093)
                ·
                  refine ⟨30853797353783455473665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 329107171773690191719093 30853797353783455473665)
                  ·
                    rfl

theorem cell21_135197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_135197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_135197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_135197 prefixEnd_135197 := by exact prefixLift 135197
  have htrace : WordTrace (prefixWord ++ tailWord_135197) baseStart_135197 baseEnd_135197 := by
    simpa [prefixWord, tailWord_135197, baseEnd_135197] using wordTrace_append hprefix tailTrace_135197
  have hstable : (prefixWord ++ tailWord_135197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135197).length < 2 ^ (prefixWord ++ tailWord_135197).sum := by decide
  have hdescent : baseEnd_135197 < baseStart_135197 := by decide
  rcases family_descends (prefixWord ++ tailWord_135197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135214 : List Nat := [4, 1, 3, 1, 1, 2, 1, 5, 3]
def baseStart_135214 : Nat := 118140960795 + 135214 * 2 ^ 59
def prefixEnd_135214 : Nat := 4983230072969 + 3 ^ 40 * 135214 * 2
def baseEnd_135214 : Nat := 30857676985395203690297

theorem tailTrace_135214 : CollatzResearch.WordTrace tailWord_135214 prefixEnd_135214 30857676985395203690297 := by
  unfold tailWord_135214
  simp only [CollatzResearch.WordTrace]
  refine ⟨616457466518780694725587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3287773154766830371869797 616457466518780694725587)
  ·
    refine ⟨924686199778171042088381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 616457466518780694725587 924686199778171042088381)
    ·
      refine ⟨346757324916814140783143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 924686199778171042088381 346757324916814140783143)
      ·
        refine ⟨520135987375221211174715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346757324916814140783143 520135987375221211174715)
        ·
          refine ⟨780203981062831816762073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520135987375221211174715 780203981062831816762073)
          ·
            refine ⟨585152985797123862571555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 780203981062831816762073 585152985797123862571555)
            ·
              refine ⟨877729478695685793857333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 585152985797123862571555 877729478695685793857333)
              ·
                refine ⟨82287138627720543174125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 877729478695685793857333 82287138627720543174125)
                ·
                  refine ⟨30857676985395203690297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82287138627720543174125 30857676985395203690297)
                  ·
                    rfl

theorem cell21_135214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 1, 5, 3].length) (baseStart_135214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_135214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_135214 prefixEnd_135214 := by exact prefixLift 135214
  have htrace : WordTrace (prefixWord ++ tailWord_135214) baseStart_135214 baseEnd_135214 := by
    simpa [prefixWord, tailWord_135214, baseEnd_135214] using wordTrace_append hprefix tailTrace_135214
  have hstable : (prefixWord ++ tailWord_135214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135214).length < 2 ^ (prefixWord ++ tailWord_135214).sum := by decide
  have hdescent : baseEnd_135214 < baseStart_135214 := by decide
  rcases family_descends (prefixWord ++ tailWord_135214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135245 : List Nat := [1, 6, 1, 1, 1, 1, 5, 1, 4]
def baseStart_135245 : Nat := 118140960795 + 135245 * 2 ^ 59
def prefixEnd_135245 : Nat := 4983230072969 + 3 ^ 40 * 135245 * 2
def baseEnd_135245 : Nat := 30864751607746038673567

theorem tailTrace_135245 : CollatzResearch.WordTrace tailWord_135245 prefixEnd_135245 30864751607746038673567 := by
  unfold tailWord_135245
  simp only [CollatzResearch.WordTrace]
  refine ⟨4932790395037937852183189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3288526930025291901455459 4932790395037937852183189)
  ·
    refine ⟨231224549767403336821087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4932790395037937852183189 231224549767403336821087)
    ·
      refine ⟨346836824651105005231631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 231224549767403336821087 346836824651105005231631)
      ·
        refine ⟨520255236976657507847447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 346836824651105005231631 520255236976657507847447)
        ·
          refine ⟨780382855464986261771171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 520255236976657507847447 780382855464986261771171)
          ·
            refine ⟨1170574283197479392656757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 780382855464986261771171 1170574283197479392656757)
            ·
              refine ⟨109741339049763693061571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1170574283197479392656757 109741339049763693061571)
              ·
                refine ⟨164612008574645539592357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109741339049763693061571 164612008574645539592357)
                ·
                  refine ⟨30864751607746038673567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164612008574645539592357 30864751607746038673567)
                  ·
                    rfl

theorem cell21_135245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 5, 1, 4].length) (baseStart_135245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_135245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_135245 prefixEnd_135245 := by exact prefixLift 135245
  have htrace : WordTrace (prefixWord ++ tailWord_135245) baseStart_135245 baseEnd_135245 := by
    simpa [prefixWord, tailWord_135245, baseEnd_135245] using wordTrace_append hprefix tailTrace_135245
  have hstable : (prefixWord ++ tailWord_135245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135245).length < 2 ^ (prefixWord ++ tailWord_135245).sum := by decide
  have hdescent : baseEnd_135245 < baseStart_135245 := by decide
  rcases family_descends (prefixWord ++ tailWord_135245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135256 : List Nat := [2, 1, 2, 2, 1, 4, 2, 2, 5]
def baseStart_135256 : Nat := 118140960795 + 135256 * 2 ^ 59
def prefixEnd_135256 : Nat := 4983230072969 + 3 ^ 40 * 135256 * 2
def baseEnd_135256 : Nat := 30867261957612463990211

theorem tailTrace_135256 : CollatzResearch.WordTrace tailWord_135256 prefixEnd_135256 30867261957612463990211 := by
  unfold tailWord_135256
  simp only [CollatzResearch.WordTrace]
  refine ⟨2466595798999043365416811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3288794398665391153889081 2466595798999043365416811)
  ·
    refine ⟨3699893698498565048125217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2466595798999043365416811 3699893698498565048125217)
    ·
      refine ⟨2774920273873923786093913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3699893698498565048125217 2774920273873923786093913)
      ·
        refine ⟨2081190205405442839570435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2774920273873923786093913 2081190205405442839570435)
        ·
          refine ⟨3121785308108164259355653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2081190205405442839570435 3121785308108164259355653)
          ·
            refine ⟨585334745270280798629185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3121785308108164259355653 585334745270280798629185)
            ·
              refine ⟨439001058952710598971889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 585334745270280798629185 439001058952710598971889)
              ·
                refine ⟨329250794214532949228917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 439001058952710598971889 329250794214532949228917)
                ·
                  refine ⟨30867261957612463990211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 329250794214532949228917 30867261957612463990211)
                  ·
                    rfl

theorem cell21_135256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 5].length) (baseStart_135256 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_135256 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_135256 prefixEnd_135256 := by exact prefixLift 135256
  have htrace : WordTrace (prefixWord ++ tailWord_135256) baseStart_135256 baseEnd_135256 := by
    simpa [prefixWord, tailWord_135256, baseEnd_135256] using wordTrace_append hprefix tailTrace_135256
  have hstable : (prefixWord ++ tailWord_135256).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135256).length < 2 ^ (prefixWord ++ tailWord_135256).sum := by decide
  have hdescent : baseEnd_135256 < baseStart_135256 := by decide
  rcases family_descends (prefixWord ++ tailWord_135256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135301 : List Nat := [1, 3, 1, 1, 5, 1, 1, 8]
def baseStart_135301 : Nat := 118140960795 + 135301 * 2 ^ 59
def prefixEnd_135301 : Nat := 4983230072969 + 3 ^ 40 * 135301 * 2
def baseEnd_135301 : Nat := 10292510523567461913373

theorem tailTrace_135301 : CollatzResearch.WordTrace tailWord_135301 prefixEnd_135301 10292510523567461913373 := by
  unfold tailWord_135301
  simp only [CollatzResearch.WordTrace]
  refine ⟨4934832882835059416221757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3289888588556706277481171 4934832882835059416221757)
  ·
    refine ⟨1850562331063147281083159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4934832882835059416221757 1850562331063147281083159)
    ·
      refine ⟨2775843496594720921624739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1850562331063147281083159 2775843496594720921624739)
      ·
        refine ⟨4163765244892081382437109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2775843496594720921624739 4163765244892081382437109)
        ·
          refine ⟨390352991708632629603479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4163765244892081382437109 390352991708632629603479)
          ·
            refine ⟨585529487562948944405219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 390352991708632629603479 585529487562948944405219)
            ·
              refine ⟨878294231344423416607829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 585529487562948944405219 878294231344423416607829)
              ·
                refine ⟨10292510523567461913373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 878294231344423416607829 10292510523567461913373)
                ·
                  rfl

theorem cell21_135301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 1, 8].length) (baseStart_135301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_135301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_135301 prefixEnd_135301 := by exact prefixLift 135301
  have htrace : WordTrace (prefixWord ++ tailWord_135301) baseStart_135301 baseEnd_135301 := by
    simpa [prefixWord, tailWord_135301, baseEnd_135301] using wordTrace_append hprefix tailTrace_135301
  have hstable : (prefixWord ++ tailWord_135301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135301).length < 2 ^ (prefixWord ++ tailWord_135301).sum := by decide
  have hdescent : baseEnd_135301 < baseStart_135301 := by decide
  rcases family_descends (prefixWord ++ tailWord_135301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135304 : List Nat := [2, 1, 3, 4, 1, 2, 1, 3, 4]
def baseStart_135304 : Nat := 118140960795 + 135304 * 2 ^ 59
def prefixEnd_135304 : Nat := 4983230072969 + 3 ^ 40 * 135304 * 2
def baseEnd_135304 : Nat := 30878216211575047190113

theorem tailTrace_135304 : CollatzResearch.WordTrace tailWord_135304 prefixEnd_135304 30878216211575047190113 := by
  unfold tailWord_135304
  simp only [CollatzResearch.WordTrace]
  refine ⟨2467471150912095464290483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3289961534549460619053977 2467471150912095464290483)
  ·
    refine ⟨3701206726368143196435725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2467471150912095464290483 3701206726368143196435725)
    ·
      refine ⟨1387952522388053698663397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3701206726368143196435725 1387952522388053698663397)
      ·
        refine ⟨260241097947760068499387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1387952522388053698663397 260241097947760068499387)
        ·
          refine ⟨390361646921640102749081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260241097947760068499387 390361646921640102749081)
          ·
            refine ⟨292771235191230077061811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 390361646921640102749081 292771235191230077061811)
            ·
              refine ⟨439156852786845115592717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 292771235191230077061811 439156852786845115592717)
              ·
                refine ⟨164683819795066918347269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 439156852786845115592717 164683819795066918347269)
                ·
                  refine ⟨30878216211575047190113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164683819795066918347269 30878216211575047190113)
                  ·
                    rfl

theorem cell21_135304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 3, 4].length) (baseStart_135304 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_135304 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_135304 prefixEnd_135304 := by exact prefixLift 135304
  have htrace : WordTrace (prefixWord ++ tailWord_135304) baseStart_135304 baseEnd_135304 := by
    simpa [prefixWord, tailWord_135304, baseEnd_135304] using wordTrace_append hprefix tailTrace_135304
  have hstable : (prefixWord ++ tailWord_135304).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135304).length < 2 ^ (prefixWord ++ tailWord_135304).sum := by decide
  have hdescent : baseEnd_135304 < baseStart_135304 := by decide
  rcases family_descends (prefixWord ++ tailWord_135304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135315 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 7]
def baseStart_135315 : Nat := 118140960795 + 135315 * 2 ^ 59
def prefixEnd_135315 : Nat := 4983230072969 + 3 ^ 40 * 135315 * 2
def baseEnd_135315 : Nat := 30880726561441472506757

theorem tailTrace_135315 : CollatzResearch.WordTrace tailWord_135315 prefixEnd_135315 30880726561441472506757 := by
  unfold tailWord_135315
  simp only [CollatzResearch.WordTrace]
  refine ⟨4935343504784339807231399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3290229003189559871487599 4935343504784339807231399)
  ·
    refine ⟨7403015257176509710847099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4935343504784339807231399 7403015257176509710847099)
    ·
      refine ⟨11104522885764764566270649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7403015257176509710847099 11104522885764764566270649)
      ·
        refine ⟨8328392164323573424702987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11104522885764764566270649 8328392164323573424702987)
        ·
          refine ⟨12492588246485360137054481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8328392164323573424702987 12492588246485360137054481)
          ·
            refine ⟨9369441184864020102790861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12492588246485360137054481 9369441184864020102790861)
            ·
              refine ⟨3513540444324007538546573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9369441184864020102790861 3513540444324007538546573)
              ·
                refine ⟨1317577666621502826954965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3513540444324007538546573 1317577666621502826954965)
                ·
                  refine ⟨30880726561441472506757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1317577666621502826954965 30880726561441472506757)
                  ·
                    rfl

theorem cell21_135315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 7].length) (baseStart_135315 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_135315 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_135315 prefixEnd_135315 := by exact prefixLift 135315
  have htrace : WordTrace (prefixWord ++ tailWord_135315) baseStart_135315 baseEnd_135315 := by
    simpa [prefixWord, tailWord_135315, baseEnd_135315] using wordTrace_append hprefix tailTrace_135315
  have hstable : (prefixWord ++ tailWord_135315).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135315).length < 2 ^ (prefixWord ++ tailWord_135315).sum := by decide
  have hdescent : baseEnd_135315 < baseStart_135315 := by decide
  rcases family_descends (prefixWord ++ tailWord_135315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135391 : List Nat := [1, 1, 2, 3, 2, 1, 1, 1, 9]
def baseStart_135391 : Nat := 118140960795 + 135391 * 2 ^ 59
def prefixEnd_135391 : Nat := 4983230072969 + 3 ^ 40 * 135391 * 2
def baseEnd_135391 : Nat := 30898070796882229239935

theorem tailTrace_135391 : CollatzResearch.WordTrace tailWord_135391 prefixEnd_135391 30898070796882229239935 := by
  unfold tailWord_135391
  simp only [CollatzResearch.WordTrace]
  refine ⟨4938115452509004786998027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3292076968339336524665351 4938115452509004786998027)
  ·
    refine ⟨7407173178763507180497041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4938115452509004786998027 7407173178763507180497041)
    ·
      refine ⟨5555379884072630385372781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7407173178763507180497041 5555379884072630385372781)
      ·
        refine ⟨2083267456527236394514793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5555379884072630385372781 2083267456527236394514793)
        ·
          refine ⟨1562450592395427295886095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2083267456527236394514793 1562450592395427295886095)
          ·
            refine ⟨2343675888593140943829143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1562450592395427295886095 2343675888593140943829143)
            ·
              refine ⟨3515513832889711415743715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2343675888593140943829143 3515513832889711415743715)
              ·
                refine ⟨5273270749334567123615573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3515513832889711415743715 5273270749334567123615573)
                ·
                  refine ⟨30898070796882229239935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5273270749334567123615573 30898070796882229239935)
                  ·
                    rfl

theorem cell21_135391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 1, 9].length) (baseStart_135391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_135391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_135391 prefixEnd_135391 := by exact prefixLift 135391
  have htrace : WordTrace (prefixWord ++ tailWord_135391) baseStart_135391 baseEnd_135391 := by
    simpa [prefixWord, tailWord_135391, baseEnd_135391] using wordTrace_append hprefix tailTrace_135391
  have hstable : (prefixWord ++ tailWord_135391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135391).length < 2 ^ (prefixWord ++ tailWord_135391).sum := by decide
  have hdescent : baseEnd_135391 < baseStart_135391 := by decide
  rcases family_descends (prefixWord ++ tailWord_135391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135428 : List Nat := [2, 3, 2, 2, 4, 1, 2, 5]
def baseStart_135428 : Nat := 118140960795 + 135428 * 2 ^ 59
def prefixEnd_135428 : Nat := 4983230072969 + 3 ^ 40 * 135428 * 2
def baseEnd_135428 : Nat := 10302171566992795707731

theorem tailTrace_135428 : CollatzResearch.WordTrace tailWord_135428 prefixEnd_135428 10302171566992795707731 := by
  unfold tailWord_135428
  simp only [CollatzResearch.WordTrace]
  refine ⟨2469732476687480053047469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3292976635583306737396625 2469732476687480053047469)
  ·
    refine ⟨926149678757805019892801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2469732476687480053047469 926149678757805019892801)
    ·
      refine ⟨694612259068353764919601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 926149678757805019892801 694612259068353764919601)
      ·
        refine ⟨520959194301265323689701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 694612259068353764919601 520959194301265323689701)
        ·
          refine ⟨97679848931487248191819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 520959194301265323689701 97679848931487248191819)
          ·
            refine ⟨146519773397230872287729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97679848931487248191819 146519773397230872287729)
            ·
              refine ⟨109889830047923154215797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146519773397230872287729 109889830047923154215797)
              ·
                refine ⟨10302171566992795707731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 109889830047923154215797 10302171566992795707731)
                ·
                  rfl

theorem cell21_135428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 5].length) (baseStart_135428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_135428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_135428 prefixEnd_135428 := by exact prefixLift 135428
  have htrace : WordTrace (prefixWord ++ tailWord_135428) baseStart_135428 baseEnd_135428 := by
    simpa [prefixWord, tailWord_135428, baseEnd_135428] using wordTrace_append hprefix tailTrace_135428
  have hstable : (prefixWord ++ tailWord_135428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135428).length < 2 ^ (prefixWord ++ tailWord_135428).sum := by decide
  have hdescent : baseEnd_135428 < baseStart_135428 := by decide
  rcases family_descends (prefixWord ++ tailWord_135428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135473 : List Nat := [1, 2, 2, 3, 4, 2, 2, 1, 4]
def baseStart_135473 : Nat := 118140960795 + 135473 * 2 ^ 59
def prefixEnd_135473 : Nat := 4983230072969 + 3 ^ 40 * 135473 * 2
def baseEnd_135473 : Nat := 30916784314068308873101

theorem tailTrace_135473 : CollatzResearch.WordTrace tailWord_135473 prefixEnd_135473 30916784314068308873101 := by
  unfold tailWord_135473
  simp only [CollatzResearch.WordTrace]
  refine ⟨4941106238211932791483073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3294070825474621860988715 4941106238211932791483073)
  ·
    refine ⟨3705829678658949593612305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4941106238211932791483073 3705829678658949593612305)
    ·
      refine ⟨2779372258994212195209229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3705829678658949593612305 2779372258994212195209229)
      ·
        refine ⟨1042264597122829573203461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2779372258994212195209229 1042264597122829573203461)
        ·
          refine ⟨195424611960530544975649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1042264597122829573203461 195424611960530544975649)
          ·
            refine ⟨146568458970397908731737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195424611960530544975649 146568458970397908731737)
            ·
              refine ⟨109926344227798431548803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146568458970397908731737 109926344227798431548803)
              ·
                refine ⟨164889516341697647323205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 109926344227798431548803 164889516341697647323205)
                ·
                  refine ⟨30916784314068308873101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 164889516341697647323205 30916784314068308873101)
                  ·
                    rfl

theorem cell21_135473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 4].length) (baseStart_135473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_135473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_135473 prefixEnd_135473 := by exact prefixLift 135473
  have htrace : WordTrace (prefixWord ++ tailWord_135473) baseStart_135473 baseEnd_135473 := by
    simpa [prefixWord, tailWord_135473, baseEnd_135473] using wordTrace_append hprefix tailTrace_135473
  have hstable : (prefixWord ++ tailWord_135473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135473).length < 2 ^ (prefixWord ++ tailWord_135473).sum := by decide
  have hdescent : baseEnd_135473 < baseStart_135473 := by decide
  rcases family_descends (prefixWord ++ tailWord_135473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135664 : List Nat := [2, 1, 1, 1, 3, 3, 1, 9]
def baseStart_135664 : Nat := 118140960795 + 135664 * 2 ^ 59
def prefixEnd_135664 : Nat := 4983230072969 + 3 ^ 40 * 135664 * 2
def baseEnd_135664 : Nat := 10320124372098140396459

theorem tailTrace_135664 : CollatzResearch.WordTrace tailWord_135664 prefixEnd_135664 10320124372098140396459 := by
  unfold tailWord_135664
  simp only [CollatzResearch.WordTrace]
  refine ⟨2474036290259986205843023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3298715053679981607790697 2474036290259986205843023)
  ·
    refine ⟨3711054435389979308764535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2474036290259986205843023 3711054435389979308764535)
    ·
      refine ⟨5566581653084968963146803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3711054435389979308764535 5566581653084968963146803)
      ·
        refine ⟨8349872479627453444720205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5566581653084968963146803 8349872479627453444720205)
        ·
          refine ⟨3131202179860295041770077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8349872479627453444720205 3131202179860295041770077)
          ·
            refine ⟨1174200817447610640663779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3131202179860295041770077 1174200817447610640663779)
            ·
              refine ⟨1761301226171415960995669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1174200817447610640663779 1761301226171415960995669)
              ·
                refine ⟨10320124372098140396459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1761301226171415960995669 10320124372098140396459)
                ·
                  rfl

theorem cell21_135664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 9].length) (baseStart_135664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_135664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_135664 prefixEnd_135664 := by exact prefixLift 135664
  have htrace : WordTrace (prefixWord ++ tailWord_135664) baseStart_135664 baseEnd_135664 := by
    simpa [prefixWord, tailWord_135664, baseEnd_135664] using wordTrace_append hprefix tailTrace_135664
  have hstable : (prefixWord ++ tailWord_135664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135664).length < 2 ^ (prefixWord ++ tailWord_135664).sum := by decide
  have hdescent : baseEnd_135664 < baseStart_135664 := by decide
  rcases family_descends (prefixWord ++ tailWord_135664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135684 : List Nat := [2, 3, 2, 3, 1, 2, 2, 2, 4]
def baseStart_135684 : Nat := 118140960795 + 135684 * 2 ^ 59
def prefixEnd_135684 : Nat := 4983230072969 + 3 ^ 40 * 135684 * 2
def baseEnd_135684 : Nat := 30964937388778830856003

theorem tailTrace_135684 : CollatzResearch.WordTrace tailWord_135684 prefixEnd_135684 30964937388778830856003 := by
  unfold tailWord_135684
  simp only [CollatzResearch.WordTrace]
  refine ⟨2474401020223757913707053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3299201360298343884942737 2474401020223757913707053)
  ·
    refine ⟨927900382583909217640145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2474401020223757913707053 927900382583909217640145)
    ·
      refine ⟨695925286937931913230109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 927900382583909217640145 695925286937931913230109)
      ·
        refine ⟨260971982601724467461291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 695925286937931913230109 260971982601724467461291)
        ·
          refine ⟨391457973902586701191937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 260971982601724467461291 391457973902586701191937)
          ·
            refine ⟨293593480426940025893953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 391457973902586701191937 293593480426940025893953)
            ·
              refine ⟨220195110320205019420465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 293593480426940025893953 220195110320205019420465)
              ·
                refine ⟨165146332740153764565349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220195110320205019420465 165146332740153764565349)
                ·
                  refine ⟨30964937388778830856003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 165146332740153764565349 30964937388778830856003)
                  ·
                    rfl

theorem cell21_135684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_135684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_135684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_135684 prefixEnd_135684 := by exact prefixLift 135684
  have htrace : WordTrace (prefixWord ++ tailWord_135684) baseStart_135684 baseEnd_135684 := by
    simpa [prefixWord, tailWord_135684, baseEnd_135684] using wordTrace_append hprefix tailTrace_135684
  have hstable : (prefixWord ++ tailWord_135684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135684).length < 2 ^ (prefixWord ++ tailWord_135684).sum := by decide
  have hdescent : baseEnd_135684 < baseStart_135684 := by decide
  rcases family_descends (prefixWord ++ tailWord_135684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135687 : List Nat := [1, 1, 4, 3, 3, 2, 2, 2, 3]
def baseStart_135687 : Nat := 118140960795 + 135687 * 2 ^ 59
def prefixEnd_135687 : Nat := 4983230072969 + 3 ^ 40 * 135687 * 2
def baseEnd_135687 : Nat := 30965622029651492305997

theorem tailTrace_135687 : CollatzResearch.WordTrace tailWord_135687 prefixEnd_135687 30965622029651492305997 := by
  unfold tailWord_135687
  simp only [CollatzResearch.WordTrace]
  refine ⟨4948911459436647339773315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3299274306291098226515543 4948911459436647339773315)
  ·
    refine ⟨7423367189154971009659973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4948911459436647339773315 7423367189154971009659973)
    ·
      refine ⟨1391881347966557064311245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7423367189154971009659973 1391881347966557064311245)
      ·
        refine ⟨521955505487458899116717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1391881347966557064311245 521955505487458899116717)
        ·
          refine ⟨195733314557797087168769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 521955505487458899116717 195733314557797087168769)
          ·
            refine ⟨146799985918347815376577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195733314557797087168769 146799985918347815376577)
            ·
              refine ⟨110099989438760861532433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 146799985918347815376577 110099989438760861532433)
              ·
                refine ⟨82574992079070646149325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110099989438760861532433 82574992079070646149325)
                ·
                  refine ⟨30965622029651492305997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82574992079070646149325 30965622029651492305997)
                  ·
                    rfl

theorem cell21_135687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 2, 3].length) (baseStart_135687 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_135687 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_135687 prefixEnd_135687 := by exact prefixLift 135687
  have htrace : WordTrace (prefixWord ++ tailWord_135687) baseStart_135687 baseEnd_135687 := by
    simpa [prefixWord, tailWord_135687, baseEnd_135687] using wordTrace_append hprefix tailTrace_135687
  have hstable : (prefixWord ++ tailWord_135687).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135687).length < 2 ^ (prefixWord ++ tailWord_135687).sum := by decide
  have hdescent : baseEnd_135687 < baseStart_135687 := by decide
  rcases family_descends (prefixWord ++ tailWord_135687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135805 : List Nat := [1, 4, 1, 1, 5, 2, 1, 1, 5]
def baseStart_135805 : Nat := 118140960795 + 135805 * 2 ^ 59
def prefixEnd_135805 : Nat := 4983230072969 + 3 ^ 40 * 135805 * 2
def baseEnd_135805 : Nat := 30992551237309509339089

theorem tailTrace_135805 : CollatzResearch.WordTrace tailWord_135805 prefixEnd_135805 30992551237309509339089 := by
  unfold tailWord_135805
  simp only [CollatzResearch.WordTrace]
  refine ⟨4953215273009153492568869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3302143515339435661712579 4953215273009153492568869)
  ·
    refine ⟨928727863689216279856663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4953215273009153492568869 928727863689216279856663)
    ·
      refine ⟨1393091795533824419784995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 928727863689216279856663 1393091795533824419784995)
      ·
        refine ⟨2089637693300736629677493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1393091795533824419784995 2089637693300736629677493)
        ·
          refine ⟨195903533746944059032265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2089637693300736629677493 195903533746944059032265)
          ·
            refine ⟨146927650310208044274199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 195903533746944059032265 146927650310208044274199)
            ·
              refine ⟨220391475465312066411299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146927650310208044274199 220391475465312066411299)
              ·
                refine ⟨330587213197968099616949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 220391475465312066411299 330587213197968099616949)
                ·
                  refine ⟨30992551237309509339089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 330587213197968099616949 30992551237309509339089)
                  ·
                    rfl

theorem cell21_135805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_135805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_135805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_135805 prefixEnd_135805 := by exact prefixLift 135805
  have htrace : WordTrace (prefixWord ++ tailWord_135805) baseStart_135805 baseEnd_135805 := by
    simpa [prefixWord, tailWord_135805, baseEnd_135805] using wordTrace_append hprefix tailTrace_135805
  have hstable : (prefixWord ++ tailWord_135805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135805).length < 2 ^ (prefixWord ++ tailWord_135805).sum := by decide
  have hdescent : baseEnd_135805 < baseStart_135805 := by decide
  rcases family_descends (prefixWord ++ tailWord_135805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135850 : List Nat := [3, 1, 5, 2, 1, 9]
def baseStart_135850 : Nat := 118140960795 + 135850 * 2 ^ 59
def prefixEnd_135850 : Nat := 4983230072969 + 3 ^ 40 * 135850 * 2
def baseEnd_135850 : Nat := 1148252624088867818111

theorem tailTrace_135850 : CollatzResearch.WordTrace tailWord_135850 prefixEnd_135850 1148252624088867818111 := by
  unfold tailWord_135850
  simp only [CollatzResearch.WordTrace]
  refine ⟨1238714139461531544489251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3303237705230750785304669 1238714139461531544489251)
  ·
    refine ⟨1858071209192297316733877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1238714139461531544489251 1858071209192297316733877)
    ·
      refine ⟨174194175861777873443801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1858071209192297316733877 174194175861777873443801)
      ·
        refine ⟨130645631896333405082851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 174194175861777873443801 130645631896333405082851)
        ·
          refine ⟨195968447844500107624277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 130645631896333405082851 195968447844500107624277)
          ·
            refine ⟨1148252624088867818111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 195968447844500107624277 1148252624088867818111)
            ·
              rfl

theorem cell21_135850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 9].length) (baseStart_135850 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_135850 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_135850 prefixEnd_135850 := by exact prefixLift 135850
  have htrace : WordTrace (prefixWord ++ tailWord_135850) baseStart_135850 baseEnd_135850 := by
    simpa [prefixWord, tailWord_135850, baseEnd_135850] using wordTrace_append hprefix tailTrace_135850
  have hstable : (prefixWord ++ tailWord_135850).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135850).length < 2 ^ (prefixWord ++ tailWord_135850).sum := by decide
  have hdescent : baseEnd_135850 < baseStart_135850 := by decide
  rcases family_descends (prefixWord ++ tailWord_135850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135912 : List Nat := [2, 1, 4, 1, 4, 2, 1, 2, 4]
def baseStart_135912 : Nat := 118140960795 + 135912 * 2 ^ 59
def prefixEnd_135912 : Nat := 4983230072969 + 3 ^ 40 * 135912 * 2
def baseEnd_135912 : Nat := 31016970095101101055537

theorem tailTrace_135912 : CollatzResearch.WordTrace tailWord_135912 prefixEnd_135912 31016970095101101055537 := by
  unfold tailWord_135912
  simp only [CollatzResearch.WordTrace]
  refine ⟨2478558941810755383356995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3304745255747673844475993 2478558941810755383356995)
  ·
    refine ⟨3717838412716133075035493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2478558941810755383356995 3717838412716133075035493)
    ·
      refine ⟨697094702384274951569155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3717838412716133075035493 697094702384274951569155)
      ·
        refine ⟨1045642053576412427353733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 697094702384274951569155 1045642053576412427353733)
        ·
          refine ⟨196057885045577330128825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1045642053576412427353733 196057885045577330128825)
          ·
            refine ⟨147043413784182997596619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 196057885045577330128825 147043413784182997596619)
            ·
              refine ⟨220565120676274496394929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147043413784182997596619 220565120676274496394929)
              ·
                refine ⟨165423840507205872296197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 220565120676274496394929 165423840507205872296197)
                ·
                  refine ⟨31016970095101101055537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 165423840507205872296197 31016970095101101055537)
                  ·
                    rfl

theorem cell21_135912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 2, 4].length) (baseStart_135912 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_135912 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_135912 prefixEnd_135912 := by exact prefixLift 135912
  have htrace : WordTrace (prefixWord ++ tailWord_135912) baseStart_135912 baseEnd_135912 := by
    simpa [prefixWord, tailWord_135912, baseEnd_135912] using wordTrace_append hprefix tailTrace_135912
  have hstable : (prefixWord ++ tailWord_135912).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135912).length < 2 ^ (prefixWord ++ tailWord_135912).sum := by decide
  have hdescent : baseEnd_135912 < baseStart_135912 := by decide
  rcases family_descends (prefixWord ++ tailWord_135912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135968 : List Nat := [2, 1, 1, 5, 1, 2, 9]
def baseStart_135968 : Nat := 118140960795 + 135968 * 2 ^ 59
def prefixEnd_135968 : Nat := 4983230072969 + 3 ^ 40 * 135968 * 2
def baseEnd_135968 : Nat := 3447750006450827569121

theorem tailTrace_135968 : CollatzResearch.WordTrace tailWord_135968 prefixEnd_135968 3447750006450827569121 := by
  unfold tailWord_135968
  simp only [CollatzResearch.WordTrace]
  refine ⟨2479580185709316165376279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3306106914279088220501705 2479580185709316165376279)
  ·
    refine ⟨3719370278563974248064419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2479580185709316165376279 3719370278563974248064419)
    ·
      refine ⟨5579055417845961372096629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3719370278563974248064419 5579055417845961372096629)
      ·
        refine ⟨523036445423058878634059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5579055417845961372096629 523036445423058878634059)
        ·
          refine ⟨784554668134588317951089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 523036445423058878634059 784554668134588317951089)
          ·
            refine ⟨588416001100941238463317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 784554668134588317951089 588416001100941238463317)
            ·
              refine ⟨3447750006450827569121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 588416001100941238463317 3447750006450827569121)
              ·
                rfl

theorem cell21_135968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 9].length) (baseStart_135968 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_135968 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_135968 prefixEnd_135968 := by exact prefixLift 135968
  have htrace : WordTrace (prefixWord ++ tailWord_135968) baseStart_135968 baseEnd_135968 := by
    simpa [prefixWord, tailWord_135968, baseEnd_135968] using wordTrace_append hprefix tailTrace_135968
  have hstable : (prefixWord ++ tailWord_135968).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135968).length < 2 ^ (prefixWord ++ tailWord_135968).sum := by decide
  have hdescent : baseEnd_135968 < baseStart_135968 := by decide
  rcases family_descends (prefixWord ++ tailWord_135968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_135988 : List Nat := [2, 5, 1, 1, 3, 1, 1, 3, 4]
def baseStart_135988 : Nat := 118140960795 + 135988 * 2 ^ 59
def prefixEnd_135988 : Nat := 4983230072969 + 3 ^ 40 * 135988 * 2
def baseEnd_135988 : Nat := 31034314330541857788715

theorem tailTrace_135988 : CollatzResearch.WordTrace tailWord_135988 prefixEnd_135988 31034314330541857788715 := by
  unfold tailWord_135988
  simp only [CollatzResearch.WordTrace]
  refine ⟨2479944915673087873240309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3306593220897450497653745 2479944915673087873240309)
  ·
    refine ⟨232494835844351988116279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2479944915673087873240309 232494835844351988116279)
    ·
      refine ⟨348742253766527982174419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 232494835844351988116279 348742253766527982174419)
      ·
        refine ⟨523113380649791973261629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 348742253766527982174419 523113380649791973261629)
        ·
          refine ⟨196167517743671989973111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 523113380649791973261629 196167517743671989973111)
          ·
            refine ⟨294251276615507984959667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196167517743671989973111 294251276615507984959667)
            ·
              refine ⟨441376914923261977439501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294251276615507984959667 441376914923261977439501)
              ·
                refine ⟨165516343096223241539813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 441376914923261977439501 165516343096223241539813)
                ·
                  refine ⟨31034314330541857788715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 165516343096223241539813 31034314330541857788715)
                  ·
                    rfl

theorem cell21_135988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_135988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_135988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_135988 prefixEnd_135988 := by exact prefixLift 135988
  have htrace : WordTrace (prefixWord ++ tailWord_135988) baseStart_135988 baseEnd_135988 := by
    simpa [prefixWord, tailWord_135988, baseEnd_135988] using wordTrace_append hprefix tailTrace_135988
  have hstable : (prefixWord ++ tailWord_135988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_135988).length < 2 ^ (prefixWord ++ tailWord_135988).sum := by decide
  have hdescent : baseEnd_135988 < baseStart_135988 := by decide
  rcases family_descends (prefixWord ++ tailWord_135988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136120 : List Nat := [2, 1, 2, 1, 2, 5, 1, 7]
def baseStart_136120 : Nat := 118140960795 + 136120 * 2 ^ 59
def prefixEnd_136120 : Nat := 4983230072969 + 3 ^ 40 * 136120 * 2
def baseEnd_136120 : Nat := 10354812842979653862815

theorem tailTrace_136120 : CollatzResearch.WordTrace tailWord_136120 prefixEnd_136120 10354812842979653862815 := by
  unfold tailWord_136120
  simp only [CollatzResearch.WordTrace]
  refine ⟨2482352133433981145142907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3309802844578641526857209 2482352133433981145142907)
  ·
    refine ⟨3723528200150971717714361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2482352133433981145142907 3723528200150971717714361)
    ·
      refine ⟨2792646150113228788285771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3723528200150971717714361 2792646150113228788285771)
      ·
        refine ⟨4188969225169843182428657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2792646150113228788285771 4188969225169843182428657)
        ·
          refine ⟨3141726918877382386821493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4188969225169843182428657 3141726918877382386821493)
          ·
            refine ⟨294536898644754598764515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3141726918877382386821493 294536898644754598764515)
            ·
              refine ⟨441805347967131898146773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294536898644754598764515 441805347967131898146773)
              ·
                refine ⟨10354812842979653862815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 441805347967131898146773 10354812842979653862815)
                ·
                  rfl

theorem cell21_136120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 5, 1, 7].length) (baseStart_136120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136120 prefixEnd_136120 := by exact prefixLift 136120
  have htrace : WordTrace (prefixWord ++ tailWord_136120) baseStart_136120 baseEnd_136120 := by
    simpa [prefixWord, tailWord_136120, baseEnd_136120] using wordTrace_append hprefix tailTrace_136120
  have hstable : (prefixWord ++ tailWord_136120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136120).length < 2 ^ (prefixWord ++ tailWord_136120).sum := by decide
  have hdescent : baseEnd_136120 < baseStart_136120 := by decide
  rcases family_descends (prefixWord ++ tailWord_136120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136202 : List Nat := [3, 1, 2, 2, 3, 3, 2, 2, 3]
def baseStart_136202 : Nat := 118140960795 + 136202 * 2 ^ 59
def prefixEnd_136202 : Nat := 4983230072969 + 3 ^ 40 * 136202 * 2
def baseEnd_136202 : Nat := 31083152046125041221611

theorem tailTrace_136202 : CollatzResearch.WordTrace tailWord_136202 prefixEnd_136202 31083152046125041221611 := by
  unfold tailWord_136202
  simp only [CollatzResearch.WordTrace]
  refine ⟨1241923763142722573692715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3311796701713926863180573 1241923763142722573692715)
  ·
    refine ⟨1862885644714083860539073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1241923763142722573692715 1862885644714083860539073)
    ·
      refine ⟨1397164233535562895404305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1862885644714083860539073 1397164233535562895404305)
      ·
        refine ⟨1047873175151672171553229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1397164233535562895404305 1047873175151672171553229)
        ·
          refine ⟨392952440681877064332461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1047873175151672171553229 392952440681877064332461)
          ·
            refine ⟨147357165255703899124673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 392952440681877064332461 147357165255703899124673)
            ·
              refine ⟨110517873941777924343505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 147357165255703899124673 110517873941777924343505)
              ·
                refine ⟨82888405456333443257629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 110517873941777924343505 82888405456333443257629)
                ·
                  refine ⟨31083152046125041221611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 82888405456333443257629 31083152046125041221611)
                  ·
                    rfl

theorem cell21_136202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 2, 3].length) (baseStart_136202 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136202 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136202 prefixEnd_136202 := by exact prefixLift 136202
  have htrace : WordTrace (prefixWord ++ tailWord_136202) baseStart_136202 baseEnd_136202 := by
    simpa [prefixWord, tailWord_136202, baseEnd_136202] using wordTrace_append hprefix tailTrace_136202
  have hstable : (prefixWord ++ tailWord_136202).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136202).length < 2 ^ (prefixWord ++ tailWord_136202).sum := by decide
  have hdescent : baseEnd_136202 < baseStart_136202 := by decide
  rcases family_descends (prefixWord ++ tailWord_136202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136213 : List Nat := [1, 3, 2, 1, 4, 3, 1, 6]
def baseStart_136213 : Nat := 118140960795 + 136213 * 2 ^ 59
def prefixEnd_136213 : Nat := 4983230072969 + 3 ^ 40 * 136213 * 2
def baseEnd_136213 : Nat := 10361887465330488846085

theorem tailTrace_136213 : CollatzResearch.WordTrace tailWord_136213 prefixEnd_136213 10361887465330488846085 := by
  unfold tailWord_136213
  simp only [CollatzResearch.WordTrace]
  refine ⟨4968096255531039173421293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3312064170354026115614195 4968096255531039173421293)
  ·
    refine ⟨1863036095824139690032985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4968096255531039173421293 1863036095824139690032985)
    ·
      refine ⟨1397277071868104767524739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1863036095824139690032985 1397277071868104767524739)
      ·
        refine ⟨2095915607802157151287109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1397277071868104767524739 2095915607802157151287109)
        ·
          refine ⟨392984176462904465866333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2095915607802157151287109 392984176462904465866333)
          ·
            refine ⟨147369066173589174699875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 392984176462904465866333 147369066173589174699875)
            ·
              refine ⟨221053599260383762049813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147369066173589174699875 221053599260383762049813)
              ·
                refine ⟨10361887465330488846085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 221053599260383762049813 10361887465330488846085)
                ·
                  rfl

theorem cell21_136213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 3, 1, 6].length) (baseStart_136213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136213 prefixEnd_136213 := by exact prefixLift 136213
  have htrace : WordTrace (prefixWord ++ tailWord_136213) baseStart_136213 baseEnd_136213 := by
    simpa [prefixWord, tailWord_136213, baseEnd_136213] using wordTrace_append hprefix tailTrace_136213
  have hstable : (prefixWord ++ tailWord_136213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136213).length < 2 ^ (prefixWord ++ tailWord_136213).sum := by decide
  have hdescent : baseEnd_136213 < baseStart_136213 := by decide
  rcases family_descends (prefixWord ++ tailWord_136213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136227 : List Nat := [1, 1, 1, 4, 3, 3, 1, 2, 5]
def baseStart_136227 : Nat := 118140960795 + 136227 * 2 ^ 59
def prefixEnd_136227 : Nat := 4983230072969 + 3 ^ 40 * 136227 * 2
def baseEnd_136227 : Nat := 31088857386730553304893

theorem tailTrace_136227 : CollatzResearch.WordTrace tailWord_136227 prefixEnd_136227 31088857386730553304893 := by
  unfold tailWord_136227
  simp only [CollatzResearch.WordTrace]
  refine ⟨4968606877480319564430935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3312404584986879709620623 4968606877480319564430935)
  ·
    refine ⟨7452910316220479346646403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4968606877480319564430935 7452910316220479346646403)
    ·
      refine ⟨11179365474330719019969605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7452910316220479346646403 11179365474330719019969605)
      ·
        refine ⟨2096131026437009816244301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11179365474330719019969605 2096131026437009816244301)
        ·
          refine ⟨786049134913878681091613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2096131026437009816244301 786049134913878681091613)
          ·
            refine ⟨294768425592704505409355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 786049134913878681091613 294768425592704505409355)
            ·
              refine ⟨442152638389056758114033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 294768425592704505409355 442152638389056758114033)
              ·
                refine ⟨331614478791792568585525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 442152638389056758114033 331614478791792568585525)
                ·
                  refine ⟨31088857386730553304893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 331614478791792568585525 31088857386730553304893)
                  ·
                    rfl

theorem cell21_136227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 5].length) (baseStart_136227 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136227 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136227 prefixEnd_136227 := by exact prefixLift 136227
  have htrace : WordTrace (prefixWord ++ tailWord_136227) baseStart_136227 baseEnd_136227 := by
    simpa [prefixWord, tailWord_136227, baseEnd_136227] using wordTrace_append hprefix tailTrace_136227
  have hstable : (prefixWord ++ tailWord_136227).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136227).length < 2 ^ (prefixWord ++ tailWord_136227).sum := by decide
  have hdescent : baseEnd_136227 < baseStart_136227 := by decide
  rcases family_descends (prefixWord ++ tailWord_136227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136241 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 6]
def baseStart_136241 : Nat := 118140960795 + 136241 * 2 ^ 59
def prefixEnd_136241 : Nat := 4983230072969 + 3 ^ 40 * 136241 * 2
def baseEnd_136241 : Nat := 31092052377469640071531

theorem tailTrace_136241 : CollatzResearch.WordTrace tailWord_136241 prefixEnd_136241 31092052377469640071531 := by
  unfold tailWord_136241
  simp only [CollatzResearch.WordTrace]
  refine ⟨4969117499429599955440577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3312744999619733303627051 4969117499429599955440577)
  ·
    refine ⟨3726838124572199966580433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4969117499429599955440577 3726838124572199966580433)
    ·
      refine ⟨2795128593429149974935325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3726838124572199966580433 2795128593429149974935325)
      ·
        refine ⟨1048173222535931240600747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2795128593429149974935325 1048173222535931240600747)
        ·
          refine ⟨1572259833803896860901121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1048173222535931240600747 1572259833803896860901121)
          ·
            refine ⟨1179194875352922645675841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1572259833803896860901121 1179194875352922645675841)
            ·
              refine ⟨884396156514691984256881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1179194875352922645675841 884396156514691984256881)
              ·
                refine ⟨663297117386018988192661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 884396156514691984256881 663297117386018988192661)
                ·
                  refine ⟨31092052377469640071531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 663297117386018988192661 31092052377469640071531)
                  ·
                    rfl

theorem cell21_136241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_136241 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136241 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136241 prefixEnd_136241 := by exact prefixLift 136241
  have htrace : WordTrace (prefixWord ++ tailWord_136241) baseStart_136241 baseEnd_136241 := by
    simpa [prefixWord, tailWord_136241, baseEnd_136241] using wordTrace_append hprefix tailTrace_136241
  have hstable : (prefixWord ++ tailWord_136241).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136241).length < 2 ^ (prefixWord ++ tailWord_136241).sum := by decide
  have hdescent : baseEnd_136241 < baseStart_136241 := by decide
  rcases family_descends (prefixWord ++ tailWord_136241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136317 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 6]
def baseStart_136317 : Nat := 118140960795 + 136317 * 2 ^ 59
def prefixEnd_136317 : Nat := 4983230072969 + 3 ^ 40 * 136317 * 2
def baseEnd_136317 : Nat := 31109396612910396804709

theorem tailTrace_136317 : CollatzResearch.WordTrace tailWord_136317 prefixEnd_136317 31109396612910396804709 := by
  unfold tailWord_136317
  simp only [CollatzResearch.WordTrace]
  refine ⟨4971889447154264935207205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3314592964769509956804803 4971889447154264935207205)
  ·
    refine ⟨932229271341424675351351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4971889447154264935207205 932229271341424675351351)
    ·
      refine ⟨1398343907012137013027027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 932229271341424675351351 1398343907012137013027027)
      ·
        refine ⟨2097515860518205519540541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1398343907012137013027027 2097515860518205519540541)
        ·
          refine ⟨786568447694327069827703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2097515860518205519540541 786568447694327069827703)
          ·
            refine ⟨1179852671541490604741555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 786568447694327069827703 1179852671541490604741555)
            ·
              refine ⟨1769779007312235907112333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1179852671541490604741555 1769779007312235907112333)
              ·
                refine ⟨663667127742088465167125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1769779007312235907112333 663667127742088465167125)
                ·
                  refine ⟨31109396612910396804709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 663667127742088465167125 31109396612910396804709)
                  ·
                    rfl

theorem cell21_136317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 6].length) (baseStart_136317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136317 prefixEnd_136317 := by exact prefixLift 136317
  have htrace : WordTrace (prefixWord ++ tailWord_136317) baseStart_136317 baseEnd_136317 := by
    simpa [prefixWord, tailWord_136317, baseEnd_136317] using wordTrace_append hprefix tailTrace_136317
  have hstable : (prefixWord ++ tailWord_136317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136317).length < 2 ^ (prefixWord ++ tailWord_136317).sum := by decide
  have hdescent : baseEnd_136317 < baseStart_136317 := by decide
  rcases family_descends (prefixWord ++ tailWord_136317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136348 : List Nat := [2, 2, 3, 2, 1, 2, 2, 7]
def baseStart_136348 : Nat := 118140960795 + 136348 * 2 ^ 59
def prefixEnd_136348 : Nat := 4983230072969 + 3 ^ 40 * 136348 * 2
def baseEnd_136348 : Nat := 10372157078420410595993

theorem tailTrace_136348 : CollatzResearch.WordTrace tailWord_136348 prefixEnd_136348 10372157078420410595993 := by
  unfold tailWord_136348
  simp only [CollatzResearch.WordTrace]
  refine ⟨2486510055020978614792849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3315346740027971486390465 2486510055020978614792849)
  ·
    refine ⟨1864882541265733961094637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2486510055020978614792849 1864882541265733961094637)
    ·
      refine ⟨699330952974650235410489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1864882541265733961094637 699330952974650235410489)
      ·
        refine ⟨524498214730987676557867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 699330952974650235410489 524498214730987676557867)
        ·
          refine ⟨786747322096481514836801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 524498214730987676557867 786747322096481514836801)
          ·
            refine ⟨590060491572361136127601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 786747322096481514836801 590060491572361136127601)
            ·
              refine ⟨442545368679270852095701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 590060491572361136127601 442545368679270852095701)
              ·
                refine ⟨10372157078420410595993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 442545368679270852095701 10372157078420410595993)
                ·
                  rfl

theorem cell21_136348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 7].length) (baseStart_136348 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136348 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136348 prefixEnd_136348 := by exact prefixLift 136348
  have htrace : WordTrace (prefixWord ++ tailWord_136348) baseStart_136348 baseEnd_136348 := by
    simpa [prefixWord, tailWord_136348, baseEnd_136348] using wordTrace_append hprefix tailTrace_136348
  have hstable : (prefixWord ++ tailWord_136348).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136348).length < 2 ^ (prefixWord ++ tailWord_136348).sum := by decide
  have hdescent : baseEnd_136348 < baseStart_136348 := by decide
  rcases family_descends (prefixWord ++ tailWord_136348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136365 : List Nat := [1, 5, 2, 1, 4, 8]
def baseStart_136365 : Nat := 118140960795 + 136365 * 2 ^ 59
def prefixEnd_136365 : Nat := 4983230072969 + 3 ^ 40 * 136365 * 2
def baseEnd_136365 : Nat := 1152605587661962222393

theorem tailTrace_136365 : CollatzResearch.WordTrace tailWord_136365 prefixEnd_136365 1152605587661962222393 := by
  unfold tailWord_136365
  simp only [CollatzResearch.WordTrace]
  refine ⟨4973640150980369132954549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3315760100653579421969699 4973640150980369132954549)
  ·
    refine ⟨466278764154409606214489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4973640150980369132954549 466278764154409606214489)
    ·
      refine ⟨349709073115807204660867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 466278764154409606214489 349709073115807204660867)
      ·
        refine ⟨524563609673710806991301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 349709073115807204660867 524563609673710806991301)
        ·
          refine ⟨98355676813820776310869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 524563609673710806991301 98355676813820776310869)
          ·
            refine ⟨1152605587661962222393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 98355676813820776310869 1152605587661962222393)
            ·
              rfl

theorem cell21_136365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 8].length) (baseStart_136365 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136365 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136365 prefixEnd_136365 := by exact prefixLift 136365
  have htrace : WordTrace (prefixWord ++ tailWord_136365) baseStart_136365 baseEnd_136365 := by
    simpa [prefixWord, tailWord_136365, baseEnd_136365] using wordTrace_append hprefix tailTrace_136365
  have hstable : (prefixWord ++ tailWord_136365).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136365).length < 2 ^ (prefixWord ++ tailWord_136365).sum := by decide
  have hdescent : baseEnd_136365 < baseStart_136365 := by decide
  rcases family_descends (prefixWord ++ tailWord_136365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136407 : List Nat := [1, 1, 3, 2, 1, 2, 2, 9]
def baseStart_136407 : Nat := 118140960795 + 136407 * 2 ^ 59
def prefixEnd_136407 : Nat := 4983230072969 + 3 ^ 40 * 136407 * 2
def baseEnd_136407 : Nat := 10376645279696746768175

theorem tailTrace_136407 : CollatzResearch.WordTrace tailWord_136407 prefixEnd_136407 10376645279696746768175 := by
  unfold tailWord_136407
  simp only [CollatzResearch.WordTrace]
  refine ⟨4975172016828210305983475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3316781344552140203988983 4975172016828210305983475)
  ·
    refine ⟨7462758025242315458975213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4975172016828210305983475 7462758025242315458975213)
    ·
      refine ⟨2798534259465868297115705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7462758025242315458975213 2798534259465868297115705)
      ·
        refine ⟨2098900694599401222836779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2798534259465868297115705 2098900694599401222836779)
        ·
          refine ⟨3148351041899101834255169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2098900694599401222836779 3148351041899101834255169)
          ·
            refine ⟨2361263281424326375691377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3148351041899101834255169 2361263281424326375691377)
            ·
              refine ⟨1770947461068244781768533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2361263281424326375691377 1770947461068244781768533)
              ·
                refine ⟨10376645279696746768175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1770947461068244781768533 10376645279696746768175)
                ·
                  rfl

theorem cell21_136407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 2, 9].length) (baseStart_136407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136407 prefixEnd_136407 := by exact prefixLift 136407
  have htrace : WordTrace (prefixWord ++ tailWord_136407) baseStart_136407 baseEnd_136407 := by
    simpa [prefixWord, tailWord_136407, baseEnd_136407] using wordTrace_append hprefix tailTrace_136407
  have hstable : (prefixWord ++ tailWord_136407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136407).length < 2 ^ (prefixWord ++ tailWord_136407).sum := by decide
  have hdescent : baseEnd_136407 < baseStart_136407 := by decide
  rcases family_descends (prefixWord ++ tailWord_136407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136472 : List Nat := [2, 1, 2, 3, 1, 3, 3, 3, 3]
def baseStart_136472 : Nat := 118140960795 + 136472 * 2 ^ 59
def prefixEnd_136472 : Nat := 4983230072969 + 3 ^ 40 * 136472 * 2
def baseEnd_136472 : Nat := 31144769724664571721059

theorem tailTrace_136472 : CollatzResearch.WordTrace tailWord_136472 prefixEnd_136472 31144769724664571721059 := by
  unfold tailWord_136472
  simp only [CollatzResearch.WordTrace]
  refine ⟨2488771380796363203549835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3318361841061817604733113 2488771380796363203549835)
  ·
    refine ⟨3733157071194544805324753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2488771380796363203549835 3733157071194544805324753)
    ·
      refine ⟨2799867803395908603993565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3733157071194544805324753 2799867803395908603993565)
      ·
        refine ⟨1049950426273465726497587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2799867803395908603993565 1049950426273465726497587)
        ·
          refine ⟨1574925639410198589746381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1049950426273465726497587 1574925639410198589746381)
          ·
            refine ⟨590597114778824471154893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1574925639410198589746381 590597114778824471154893)
            ·
              refine ⟨221473918042059176683085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 590597114778824471154893 221473918042059176683085)
              ·
                refine ⟨83052719265772191256157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 221473918042059176683085 83052719265772191256157)
                ·
                  refine ⟨31144769724664571721059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83052719265772191256157 31144769724664571721059)
                  ·
                    rfl

theorem cell21_136472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 3, 3].length) (baseStart_136472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136472 prefixEnd_136472 := by exact prefixLift 136472
  have htrace : WordTrace (prefixWord ++ tailWord_136472) baseStart_136472 baseEnd_136472 := by
    simpa [prefixWord, tailWord_136472, baseEnd_136472] using wordTrace_append hprefix tailTrace_136472
  have hstable : (prefixWord ++ tailWord_136472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136472).length < 2 ^ (prefixWord ++ tailWord_136472).sum := by decide
  have hdescent : baseEnd_136472 < baseStart_136472 := by decide
  rcases family_descends (prefixWord ++ tailWord_136472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136483 : List Nat := [1, 1, 1, 4, 2, 3, 9]
def baseStart_136483 : Nat := 118140960795 + 136483 * 2 ^ 59
def prefixEnd_136483 : Nat := 4983230072969 + 3 ^ 40 * 136483 * 2
def baseEnd_136483 : Nat := 3460808897170110781967

theorem tailTrace_136483 : CollatzResearch.WordTrace tailWord_136483 prefixEnd_136483 3460808897170110781967 := by
  unfold tailWord_136483
  simp only [CollatzResearch.WordTrace]
  refine ⟨4977943964552875285750103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3318629309701916857166735 4977943964552875285750103)
  ·
    refine ⟨7466915946829312928625155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4977943964552875285750103 7466915946829312928625155)
    ·
      refine ⟨11200373920243969392937733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7466915946829312928625155 11200373920243969392937733)
      ·
        refine ⟨2100070110045744261175825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11200373920243969392937733 2100070110045744261175825)
        ·
          refine ⟨1575052582534308195881869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2100070110045744261175825 1575052582534308195881869)
          ·
            refine ⟨590644718450365573455701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1575052582534308195881869 590644718450365573455701)
            ·
              refine ⟨3460808897170110781967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 590644718450365573455701 3460808897170110781967)
              ·
                rfl

theorem cell21_136483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 9].length) (baseStart_136483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136483 prefixEnd_136483 := by exact prefixLift 136483
  have htrace : WordTrace (prefixWord ++ tailWord_136483) baseStart_136483 baseEnd_136483 := by
    simpa [prefixWord, tailWord_136483, baseEnd_136483] using wordTrace_append hprefix tailTrace_136483
  have hstable : (prefixWord ++ tailWord_136483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136483).length < 2 ^ (prefixWord ++ tailWord_136483).sum := by decide
  have hdescent : baseEnd_136483 < baseStart_136483 := by decide
  rcases family_descends (prefixWord ++ tailWord_136483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136531 : List Nat := [1, 1, 1, 2, 1, 1, 6, 5, 3]
def baseStart_136531 : Nat := 118140960795 + 136531 * 2 ^ 59
def prefixEnd_136531 : Nat := 4983230072969 + 3 ^ 40 * 136531 * 2
def baseEnd_136531 : Nat := 31158234328493580237605

theorem tailTrace_136531 : CollatzResearch.WordTrace tailWord_136531 prefixEnd_136531 31158234328493580237605 := by
  unfold tailWord_136531
  simp only [CollatzResearch.WordTrace]
  refine ⟨4979694668378979483497447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3319796445585986322331631 4979694668378979483497447)
  ·
    refine ⟨7469542002568469225246171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4979694668378979483497447 7469542002568469225246171)
    ·
      refine ⟨11204313003852703837869257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7469542002568469225246171 11204313003852703837869257)
      ·
        refine ⟨8403234752889527878401943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11204313003852703837869257 8403234752889527878401943)
        ·
          refine ⟨12604852129334291817602915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8403234752889527878401943 12604852129334291817602915)
          ·
            refine ⟨18907278194001437726404373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12604852129334291817602915 18907278194001437726404373)
            ·
              refine ⟨886278665343817393425205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18907278194001437726404373 886278665343817393425205)
              ·
                refine ⟨83088624875982880633613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 886278665343817393425205 83088624875982880633613)
                ·
                  refine ⟨31158234328493580237605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83088624875982880633613 31158234328493580237605)
                  ·
                    rfl

theorem cell21_136531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 3].length) (baseStart_136531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136531 prefixEnd_136531 := by exact prefixLift 136531
  have htrace : WordTrace (prefixWord ++ tailWord_136531) baseStart_136531 baseEnd_136531 := by
    simpa [prefixWord, tailWord_136531, baseEnd_136531] using wordTrace_append hprefix tailTrace_136531
  have hstable : (prefixWord ++ tailWord_136531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136531).length < 2 ^ (prefixWord ++ tailWord_136531).sum := by decide
  have hdescent : baseEnd_136531 < baseStart_136531 := by decide
  rcases family_descends (prefixWord ++ tailWord_136531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136534 : List Nat := [5, 2, 3, 1, 10]
def baseStart_136534 : Nat := 118140960795 + 136534 * 2 ^ 59
def prefixEnd_136534 : Nat := 4983230072969 + 3 ^ 40 * 136534 * 2
def baseEnd_136534 : Nat := 384678011967484465279

theorem tailTrace_136534 : CollatzResearch.WordTrace tailWord_136534 prefixEnd_136534 384678011967484465279 := by
  unfold tailWord_136534
  simp only [CollatzResearch.WordTrace]
  refine ⟨311237755460506937241041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3319869391578740663904437 311237755460506937241041)
  ·
    refine ⟨233428316595380202930781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 311237755460506937241041 233428316595380202930781)
    ·
      refine ⟨87535618723267576099043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233428316595380202930781 87535618723267576099043)
      ·
        refine ⟨131303428084901364148565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87535618723267576099043 131303428084901364148565)
        ·
          refine ⟨384678011967484465279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 131303428084901364148565 384678011967484465279)
          ·
            rfl

theorem cell21_136534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 10].length) (baseStart_136534 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136534 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136534 prefixEnd_136534 := by exact prefixLift 136534
  have htrace : WordTrace (prefixWord ++ tailWord_136534) baseStart_136534 baseEnd_136534 := by
    simpa [prefixWord, tailWord_136534, baseEnd_136534] using wordTrace_append hprefix tailTrace_136534
  have hstable : (prefixWord ++ tailWord_136534).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136534).length < 2 ^ (prefixWord ++ tailWord_136534).sum := by decide
  have hdescent : baseEnd_136534 < baseStart_136534 := by decide
  rcases family_descends (prefixWord ++ tailWord_136534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136548 : List Nat := [2, 3, 1, 1, 3, 3, 1, 4, 3]
def baseStart_136548 : Nat := 118140960795 + 136548 * 2 ^ 59
def prefixEnd_136548 : Nat := 4983230072969 + 3 ^ 40 * 136548 * 2
def baseEnd_136548 : Nat := 31162113960105328454237

theorem tailTrace_136548 : CollatzResearch.WordTrace tailWord_136548 prefixEnd_136548 31162113960105328454237 := by
  unfold tailWord_136548
  simp only [CollatzResearch.WordTrace]
  refine ⟨2490157354658695693433149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3320209806211594257910865 2490157354658695693433149)
  ·
    refine ⟨933809007997010885037431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2490157354658695693433149 933809007997010885037431)
    ·
      refine ⟨1400713511995516327556147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 933809007997010885037431 1400713511995516327556147)
      ·
        refine ⟨2101070267993274491334221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1400713511995516327556147 2101070267993274491334221)
        ·
          refine ⟨787901350497477934250333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2101070267993274491334221 787901350497477934250333)
          ·
            refine ⟨295463006436554225343875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 787901350497477934250333 295463006436554225343875)
            ·
              refine ⟨443194509654831338015813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295463006436554225343875 443194509654831338015813)
              ·
                refine ⟨83098970560280875877965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 443194509654831338015813 83098970560280875877965)
                ·
                  refine ⟨31162113960105328454237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83098970560280875877965 31162113960105328454237)
                  ·
                    rfl

theorem cell21_136548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 4, 3].length) (baseStart_136548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136548 prefixEnd_136548 := by exact prefixLift 136548
  have htrace : WordTrace (prefixWord ++ tailWord_136548) baseStart_136548 baseEnd_136548 := by
    simpa [prefixWord, tailWord_136548, baseEnd_136548] using wordTrace_append hprefix tailTrace_136548
  have hstable : (prefixWord ++ tailWord_136548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136548).length < 2 ^ (prefixWord ++ tailWord_136548).sum := by decide
  have hdescent : baseEnd_136548 < baseStart_136548 := by decide
  rcases family_descends (prefixWord ++ tailWord_136548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136607 : List Nat := [1, 1, 2, 5, 1, 3, 2, 1, 5]
def baseStart_136607 : Nat := 118140960795 + 136607 * 2 ^ 59
def prefixEnd_136607 : Nat := 4983230072969 + 3 ^ 40 * 136607 * 2
def baseEnd_136607 : Nat := 31175578563934336970783

theorem tailTrace_136607 : CollatzResearch.WordTrace tailWord_136607 prefixEnd_136607 31175578563934336970783 := by
  unfold tailWord_136607
  simp only [CollatzResearch.WordTrace]
  refine ⟨4982466616103644463264075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3321644410735762975509383 4982466616103644463264075)
  ·
    refine ⟨7473699924155466694896113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4982466616103644463264075 7473699924155466694896113)
    ·
      refine ⟨5605274943116600021172085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7473699924155466694896113 5605274943116600021172085)
      ·
        refine ⟨525494525917181251984883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5605274943116600021172085 525494525917181251984883)
        ·
          refine ⟨788241788875771877977325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525494525917181251984883 788241788875771877977325)
          ·
            refine ⟨295590670828414454241497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 788241788875771877977325 295590670828414454241497)
            ·
              refine ⟨221693003121310840681123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295590670828414454241497 221693003121310840681123)
              ·
                refine ⟨332539504681966261021685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221693003121310840681123 332539504681966261021685)
                ·
                  refine ⟨31175578563934336970783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 332539504681966261021685 31175578563934336970783)
                  ·
                    rfl

theorem cell21_136607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 1, 5].length) (baseStart_136607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136607 prefixEnd_136607 := by exact prefixLift 136607
  have htrace : WordTrace (prefixWord ++ tailWord_136607) baseStart_136607 baseEnd_136607 := by
    simpa [prefixWord, tailWord_136607, baseEnd_136607] using wordTrace_append hprefix tailTrace_136607
  have hstable : (prefixWord ++ tailWord_136607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136607).length < 2 ^ (prefixWord ++ tailWord_136607).sum := by decide
  have hdescent : baseEnd_136607 < baseStart_136607 := by decide
  rcases family_descends (prefixWord ++ tailWord_136607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136652 : List Nat := [2, 2, 1, 4, 2, 3, 7]
def baseStart_136652 : Nat := 118140960795 + 136652 * 2 ^ 59
def prefixEnd_136652 : Nat := 4983230072969 + 3 ^ 40 * 136652 * 2
def baseEnd_136652 : Nat := 3465094241891584302299

theorem tailTrace_136652 : CollatzResearch.WordTrace tailWord_136652 prefixEnd_136652 3465094241891584302299 := by
  unfold tailWord_136652
  simp only [CollatzResearch.WordTrace]
  refine ⟨2492053950470308574326105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3322738600627078099101473 2492053950470308574326105)
  ·
    refine ⟨1869040462852731430744579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2492053950470308574326105 1869040462852731430744579)
    ·
      refine ⟨2803560694279097146116869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1869040462852731430744579 2803560694279097146116869)
      ·
        refine ⟨525667630177330714896913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2803560694279097146116869 525667630177330714896913)
        ·
          refine ⟨394250722632998036172685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 525667630177330714896913 394250722632998036172685)
          ·
            refine ⟨147844020987374263564757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 394250722632998036172685 147844020987374263564757)
            ·
              refine ⟨3465094241891584302299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 147844020987374263564757 3465094241891584302299)
              ·
                rfl

theorem cell21_136652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 7].length) (baseStart_136652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136652 prefixEnd_136652 := by exact prefixLift 136652
  have htrace : WordTrace (prefixWord ++ tailWord_136652) baseStart_136652 baseEnd_136652 := by
    simpa [prefixWord, tailWord_136652, baseEnd_136652] using wordTrace_append hprefix tailTrace_136652
  have hstable : (prefixWord ++ tailWord_136652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136652).length < 2 ^ (prefixWord ++ tailWord_136652).sum := by decide
  have hdescent : baseEnd_136652 < baseStart_136652 := by decide
  rcases family_descends (prefixWord ++ tailWord_136652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136711 : List Nat := [1, 1, 4, 3, 2, 10]
def baseStart_136711 : Nat := 118140960795 + 136711 * 2 ^ 59
def prefixEnd_136711 : Nat := 4983230072969 + 3 ^ 40 * 136711 * 2
def baseEnd_136711 : Nat := 1155530102994565453231

theorem tailTrace_136711 : CollatzResearch.WordTrace tailWord_136711 prefixEnd_136711 1155530102994565453231 := by
  unfold tailWord_136711
  simp only [CollatzResearch.WordTrace]
  refine ⟨4986259807726870225049987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3324173205151246816699991 4986259807726870225049987)
  ·
    refine ⟨7479389711590305337574981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4986259807726870225049987 7479389711590305337574981)
    ·
      refine ⟨1402385570923182250795309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7479389711590305337574981 1402385570923182250795309)
      ·
        refine ⟨525894589096193344048241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1402385570923182250795309 525894589096193344048241)
        ·
          refine ⟨394420941822145008036181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 525894589096193344048241 394420941822145008036181)
          ·
            refine ⟨1155530102994565453231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 394420941822145008036181 1155530102994565453231)
            ·
              rfl

theorem cell21_136711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 10].length) (baseStart_136711 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136711 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136711 prefixEnd_136711 := by exact prefixLift 136711
  have htrace : WordTrace (prefixWord ++ tailWord_136711) baseStart_136711 baseEnd_136711 := by
    simpa [prefixWord, tailWord_136711, baseEnd_136711] using wordTrace_append hprefix tailTrace_136711
  have hstable : (prefixWord ++ tailWord_136711).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136711).length < 2 ^ (prefixWord ++ tailWord_136711).sum := by decide
  have hdescent : baseEnd_136711 < baseStart_136711 := by decide
  rcases family_descends (prefixWord ++ tailWord_136711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136714 : List Nat := [3, 1, 2, 2, 2, 3, 2, 2, 4]
def baseStart_136714 : Nat := 118140960795 + 136714 * 2 ^ 59
def prefixEnd_136714 : Nat := 4983230072969 + 3 ^ 40 * 136714 * 2
def baseEnd_136714 : Nat := 31199997421725928687231

theorem tailTrace_136714 : CollatzResearch.WordTrace tailWord_136714 prefixEnd_136714 31199997421725928687231 := by
  unfold tailWord_136714
  simp only [CollatzResearch.WordTrace]
  refine ⟨1246592306679000434352299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3324246151144001158272797 1246592306679000434352299)
  ·
    refine ⟨1869888460018500651528449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1246592306679000434352299 1869888460018500651528449)
    ·
      refine ⟨1402416345013875488646337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1869888460018500651528449 1402416345013875488646337)
      ·
        refine ⟨1051812258760406616484753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1402416345013875488646337 1051812258760406616484753)
        ·
          refine ⟨788859194070304962363565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1051812258760406616484753 788859194070304962363565)
          ·
            refine ⟨295822197776364360886337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 788859194070304962363565 295822197776364360886337)
            ·
              refine ⟨221866648332273270664753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 295822197776364360886337 221866648332273270664753)
              ·
                refine ⟨166399986249204952998565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 221866648332273270664753 166399986249204952998565)
                ·
                  refine ⟨31199997421725928687231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 166399986249204952998565 31199997421725928687231)
                  ·
                    rfl

theorem cell21_136714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 3, 2, 2, 4].length) (baseStart_136714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136714 prefixEnd_136714 := by exact prefixLift 136714
  have htrace : WordTrace (prefixWord ++ tailWord_136714) baseStart_136714 baseEnd_136714 := by
    simpa [prefixWord, tailWord_136714, baseEnd_136714] using wordTrace_append hprefix tailTrace_136714
  have hstable : (prefixWord ++ tailWord_136714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136714).length < 2 ^ (prefixWord ++ tailWord_136714).sum := by decide
  have hdescent : baseEnd_136714 < baseStart_136714 := by decide
  rcases family_descends (prefixWord ++ tailWord_136714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136734 : List Nat := [4, 3, 3, 1, 1, 1, 1, 2, 5]
def baseStart_136734 : Nat := 118140960795 + 136734 * 2 ^ 59
def prefixEnd_136734 : Nat := 4983230072969 + 3 ^ 40 * 136734 * 2
def baseEnd_136734 : Nat := 31204561694210338353857

theorem tailTrace_136734 : CollatzResearch.WordTrace tailWord_136734 prefixEnd_136734 31204561694210338353857 := by
  unfold tailWord_136734
  simp only [CollatzResearch.WordTrace]
  refine ⟨623387335830443144142157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3324732457762363435424837 623387335830443144142157)
  ·
    refine ⟨233770250936416179053309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 623387335830443144142157 233770250936416179053309)
    ·
      refine ⟨87663844101156067144991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 233770250936416179053309 87663844101156067144991)
      ·
        refine ⟨131495766151734100717487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87663844101156067144991 131495766151734100717487)
        ·
          refine ⟨197243649227601151076231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131495766151734100717487 197243649227601151076231)
          ·
            refine ⟨295865473841401726614347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197243649227601151076231 295865473841401726614347)
            ·
              refine ⟨443798210762102589921521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295865473841401726614347 443798210762102589921521)
              ·
                refine ⟨332848658071576942441141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443798210762102589921521 332848658071576942441141)
                ·
                  refine ⟨31204561694210338353857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 332848658071576942441141 31204561694210338353857)
                  ·
                    rfl

theorem cell21_136734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 1, 2, 5].length) (baseStart_136734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136734 prefixEnd_136734 := by exact prefixLift 136734
  have htrace : WordTrace (prefixWord ++ tailWord_136734) baseStart_136734 baseEnd_136734 := by
    simpa [prefixWord, tailWord_136734, baseEnd_136734] using wordTrace_append hprefix tailTrace_136734
  have hstable : (prefixWord ++ tailWord_136734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136734).length < 2 ^ (prefixWord ++ tailWord_136734).sum := by decide
  have hdescent : baseEnd_136734 < baseStart_136734 := by decide
  rcases family_descends (prefixWord ++ tailWord_136734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136759 : List Nat := [1, 1, 3, 1, 2, 4, 1, 5, 3]
def baseStart_136759 : Nat := 118140960795 + 136759 * 2 ^ 59
def prefixEnd_136759 : Nat := 4983230072969 + 3 ^ 40 * 136759 * 2
def baseEnd_136759 : Nat := 31210267034815850437139

theorem tailTrace_136759 : CollatzResearch.WordTrace tailWord_136759 prefixEnd_136759 31210267034815850437139 := by
  unfold tailWord_136759
  simp only [CollatzResearch.WordTrace]
  refine ⟨4988010511552974422797331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3325340341035316281864887 4988010511552974422797331)
  ·
    refine ⟨7482015767329461634195997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4988010511552974422797331 7482015767329461634195997)
    ·
      refine ⟨2805755912748548112823499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7482015767329461634195997 2805755912748548112823499)
      ·
        refine ⟨4208633869122822169235249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2805755912748548112823499 4208633869122822169235249)
        ·
          refine ⟨3156475401842116626926437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4208633869122822169235249 3156475401842116626926437)
          ·
            refine ⟨591839137845396867548707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3156475401842116626926437 591839137845396867548707)
            ·
              refine ⟨887758706768095301323061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 591839137845396867548707 887758706768095301323061)
              ·
                refine ⟨83227378759508934499037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 887758706768095301323061 83227378759508934499037)
                ·
                  refine ⟨31210267034815850437139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83227378759508934499037 31210267034815850437139)
                  ·
                    rfl

theorem cell21_136759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 5, 3].length) (baseStart_136759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136759 prefixEnd_136759 := by exact prefixLift 136759
  have htrace : WordTrace (prefixWord ++ tailWord_136759) baseStart_136759 baseEnd_136759 := by
    simpa [prefixWord, tailWord_136759, baseEnd_136759] using wordTrace_append hprefix tailTrace_136759
  have hstable : (prefixWord ++ tailWord_136759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136759).length < 2 ^ (prefixWord ++ tailWord_136759).sum := by decide
  have hdescent : baseEnd_136759 < baseStart_136759 := by decide
  rcases family_descends (prefixWord ++ tailWord_136759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136804 : List Nat := [2, 3, 1, 1, 2, 3, 4, 5]
def baseStart_136804 : Nat := 118140960795 + 136804 * 2 ^ 59
def prefixEnd_136804 : Nat := 4983230072969 + 3 ^ 40 * 136804 * 2
def baseEnd_136804 : Nat := 10406845549301924062349

theorem tailTrace_136804 : CollatzResearch.WordTrace tailWord_136804 prefixEnd_136804 10406845549301924062349 := by
  unfold tailWord_136804
  simp only [CollatzResearch.WordTrace]
  refine ⟨2494825898194973554092733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3326434530926631405456977 2494825898194973554092733)
  ·
    refine ⟨935559711823115082784775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2494825898194973554092733 935559711823115082784775)
    ·
      refine ⟨1403339567734672624177163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 935559711823115082784775 1403339567734672624177163)
      ·
        refine ⟨2105009351602008936265745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1403339567734672624177163 2105009351602008936265745)
        ·
          refine ⟨1578757013701506702199309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2105009351602008936265745 1578757013701506702199309)
          ·
            refine ⟨592033880138065013324741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1578757013701506702199309 592033880138065013324741)
            ·
              refine ⟨111006352525887189998389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 592033880138065013324741 111006352525887189998389)
              ·
                refine ⟨10406845549301924062349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 111006352525887189998389 10406845549301924062349)
                ·
                  rfl

theorem cell21_136804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 4, 5].length) (baseStart_136804 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136804 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136804 prefixEnd_136804 := by exact prefixLift 136804
  have htrace : WordTrace (prefixWord ++ tailWord_136804) baseStart_136804 baseEnd_136804 := by
    simpa [prefixWord, tailWord_136804, baseEnd_136804] using wordTrace_append hprefix tailTrace_136804
  have hstable : (prefixWord ++ tailWord_136804).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136804).length < 2 ^ (prefixWord ++ tailWord_136804).sum := by decide
  have hdescent : baseEnd_136804 < baseStart_136804 := by decide
  rcases family_descends (prefixWord ++ tailWord_136804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136832 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 6]
def baseStart_136832 : Nat := 118140960795 + 136832 * 2 ^ 59
def prefixEnd_136832 : Nat := 4983230072969 + 3 ^ 40 * 136832 * 2
def baseEnd_136832 : Nat := 31226926629383945720323

theorem tailTrace_136832 : CollatzResearch.WordTrace tailWord_136832 prefixEnd_136832 31226926629383945720323 := by
  unfold tailWord_136832
  simp only [CollatzResearch.WordTrace]
  refine ⟨2495336520144253945102375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3327115360192338593469833 2495336520144253945102375)
  ·
    refine ⟨3743004780216380917653563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2495336520144253945102375 3743004780216380917653563)
    ·
      refine ⟨5614507170324571376480345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3743004780216380917653563 5614507170324571376480345)
      ·
        refine ⟨4210880377743428532360259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5614507170324571376480345 4210880377743428532360259)
        ·
          refine ⟨6316320566615142798540389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4210880377743428532360259 6316320566615142798540389)
          ·
            refine ⟨1184310106240339274726323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6316320566615142798540389 1184310106240339274726323)
            ·
              refine ⟨1776465159360508912089485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1184310106240339274726323 1776465159360508912089485)
              ·
                refine ⟨666174434760190842033557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1776465159360508912089485 666174434760190842033557)
                ·
                  refine ⟨31226926629383945720323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 666174434760190842033557 31226926629383945720323)
                  ·
                    rfl

theorem cell21_136832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_136832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136832 prefixEnd_136832 := by exact prefixLift 136832
  have htrace : WordTrace (prefixWord ++ tailWord_136832) baseStart_136832 baseEnd_136832 := by
    simpa [prefixWord, tailWord_136832, baseEnd_136832] using wordTrace_append hprefix tailTrace_136832
  have hstable : (prefixWord ++ tailWord_136832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136832).length < 2 ^ (prefixWord ++ tailWord_136832).sum := by decide
  have hdescent : baseEnd_136832 < baseStart_136832 := by decide
  rcases family_descends (prefixWord ++ tailWord_136832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136886 : List Nat := [5, 1, 3, 1, 1, 1, 4, 2, 3]
def baseStart_136886 : Nat := 118140960795 + 136886 * 2 ^ 59
def prefixEnd_136886 : Nat := 4983230072969 + 3 ^ 40 * 136886 * 2
def baseEnd_136886 : Nat := 31239250165091851820213

theorem tailTrace_136886 : CollatzResearch.WordTrace tailWord_136886 prefixEnd_136886 31239250165091851820213 := by
  unfold tailWord_136886
  simp only [CollatzResearch.WordTrace]
  refine ⟨312040161380804694541907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3328428388061916741780341 312040161380804694541907)
  ·
    refine ⟨468060242071207041812861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 312040161380804694541907 468060242071207041812861)
    ·
      refine ⟨175522590776702640679823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 468060242071207041812861 175522590776702640679823)
      ·
        refine ⟨263283886165053961019735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175522590776702640679823 263283886165053961019735)
        ·
          refine ⟨394925829247580941529603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 263283886165053961019735 394925829247580941529603)
          ·
            refine ⟨592388743871371412294405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 394925829247580941529603 592388743871371412294405)
            ·
              refine ⟨111072889475882139805201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 592388743871371412294405 111072889475882139805201)
              ·
                refine ⟨83304667106911604853901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111072889475882139805201 83304667106911604853901)
                ·
                  refine ⟨31239250165091851820213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83304667106911604853901 31239250165091851820213)
                  ·
                    rfl

theorem cell21_136886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_136886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136886 prefixEnd_136886 := by exact prefixLift 136886
  have htrace : WordTrace (prefixWord ++ tailWord_136886) baseStart_136886 baseEnd_136886 := by
    simpa [prefixWord, tailWord_136886, baseEnd_136886] using wordTrace_append hprefix tailTrace_136886
  have hstable : (prefixWord ++ tailWord_136886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136886).length < 2 ^ (prefixWord ++ tailWord_136886).sum := by decide
  have hdescent : baseEnd_136886 < baseStart_136886 := by decide
  rcases family_descends (prefixWord ++ tailWord_136886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136970 : List Nat := [3, 1, 2, 2, 1, 3, 2, 2, 5]
def baseStart_136970 : Nat := 118140960795 + 136970 * 2 ^ 59
def prefixEnd_136970 : Nat := 4983230072969 + 3 ^ 40 * 136970 * 2
def baseEnd_136970 : Nat := 31258420109526372420041

theorem tailTrace_136970 : CollatzResearch.WordTrace tailWord_136970 prefixEnd_136970 31258420109526372420041 := by
  unfold tailWord_136970
  simp only [CollatzResearch.WordTrace]
  refine ⟨1248926578447139364682091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3330470875859038305818909 1248926578447139364682091)
  ·
    refine ⟨1873389867670709047023137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1248926578447139364682091 1873389867670709047023137)
    ·
      refine ⟨1405042400753031785267353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1873389867670709047023137 1405042400753031785267353)
      ·
        refine ⟨1053781800564773838950515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1405042400753031785267353 1053781800564773838950515)
        ·
          refine ⟨1580672700847160758425773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1053781800564773838950515 1580672700847160758425773)
          ·
            refine ⟨592752262817685284409665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1580672700847160758425773 592752262817685284409665)
            ·
              refine ⟨444564197113263963307249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 592752262817685284409665 444564197113263963307249)
              ·
                refine ⟨333423147834947972480437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 444564197113263963307249 333423147834947972480437)
                ·
                  refine ⟨31258420109526372420041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 333423147834947972480437 31258420109526372420041)
                  ·
                    rfl

theorem cell21_136970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_136970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136970 prefixEnd_136970 := by exact prefixLift 136970
  have htrace : WordTrace (prefixWord ++ tailWord_136970) baseStart_136970 baseEnd_136970 := by
    simpa [prefixWord, tailWord_136970, baseEnd_136970] using wordTrace_append hprefix tailTrace_136970
  have hstable : (prefixWord ++ tailWord_136970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136970).length < 2 ^ (prefixWord ++ tailWord_136970).sum := by decide
  have hdescent : baseEnd_136970 < baseStart_136970 := by decide
  rcases family_descends (prefixWord ++ tailWord_136970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136984 : List Nat := [2, 1, 2, 3, 1, 1, 3, 2, 6]
def baseStart_136984 : Nat := 118140960795 + 136984 * 2 ^ 59
def prefixEnd_136984 : Nat := 4983230072969 + 3 ^ 40 * 136984 * 2
def baseEnd_136984 : Nat := 31261615100265459186679

theorem tailTrace_136984 : CollatzResearch.WordTrace tailWord_136984 prefixEnd_136984 31261615100265459186679 := by
  unfold tailWord_136984
  simp only [CollatzResearch.WordTrace]
  refine ⟨2498108467868918924869003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3330811290491891899825337 2498108467868918924869003)
  ·
    refine ⟨3747162701803378387303505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2498108467868918924869003 3747162701803378387303505)
    ·
      refine ⟨2810372026352533790477629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3747162701803378387303505 2810372026352533790477629)
      ·
        refine ⟨1053889509882200171429111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2810372026352533790477629 1053889509882200171429111)
        ·
          refine ⟨1580834264823300257143667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1053889509882200171429111 1580834264823300257143667)
          ·
            refine ⟨2371251397234950385715501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1580834264823300257143667 2371251397234950385715501)
            ·
              refine ⟨889219273963106394643313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2371251397234950385715501 889219273963106394643313)
              ·
                refine ⟨666914455472329795982485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 889219273963106394643313 666914455472329795982485)
                ·
                  refine ⟨31261615100265459186679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 666914455472329795982485 31261615100265459186679)
                  ·
                    rfl

theorem cell21_136984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_136984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136984 prefixEnd_136984 := by exact prefixLift 136984
  have htrace : WordTrace (prefixWord ++ tailWord_136984) baseStart_136984 baseEnd_136984 := by
    simpa [prefixWord, tailWord_136984, baseEnd_136984] using wordTrace_append hprefix tailTrace_136984
  have hstable : (prefixWord ++ tailWord_136984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136984).length < 2 ^ (prefixWord ++ tailWord_136984).sum := by decide
  have hdescent : baseEnd_136984 < baseStart_136984 := by decide
  rcases family_descends (prefixWord ++ tailWord_136984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136990 : List Nat := [4, 3, 2, 2, 1, 2, 7]
def baseStart_136990 : Nat := 118140960795 + 136990 * 2 ^ 59
def prefixEnd_136990 : Nat := 4983230072969 + 3 ^ 40 * 136990 * 2
def baseEnd_136990 : Nat := 3473664931334531342963

theorem tailTrace_136990 : CollatzResearch.WordTrace tailWord_136990 prefixEnd_136990 3473664931334531342963 := by
  unfold tailWord_136990
  simp only [CollatzResearch.WordTrace]
  refine ⟨624554471714512609307053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3330957182477400582970949 624554471714512609307053)
  ·
    refine ⟨234207926892942228490145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 624554471714512609307053 234207926892942228490145)
    ·
      refine ⟨175655945169706671367609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 234207926892942228490145 175655945169706671367609)
      ·
        refine ⟨131741958877280003525707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175655945169706671367609 131741958877280003525707)
        ·
          refine ⟨197612938315920005288561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131741958877280003525707 197612938315920005288561)
          ·
            refine ⟨148209703736940003966421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197612938315920005288561 148209703736940003966421)
            ·
              refine ⟨3473664931334531342963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 148209703736940003966421 3473664931334531342963)
              ·
                rfl

theorem cell21_136990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 7].length) (baseStart_136990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_136990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_136990 prefixEnd_136990 := by exact prefixLift 136990
  have htrace : WordTrace (prefixWord ++ tailWord_136990) baseStart_136990 baseEnd_136990 := by
    simpa [prefixWord, tailWord_136990, baseEnd_136990] using wordTrace_append hprefix tailTrace_136990
  have hstable : (prefixWord ++ tailWord_136990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136990).length < 2 ^ (prefixWord ++ tailWord_136990).sum := by decide
  have hdescent : baseEnd_136990 < baseStart_136990 := by decide
  rcases family_descends (prefixWord ++ tailWord_136990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137004 : List Nat := [2, 2, 1, 1, 1, 6, 3, 2, 3]
def baseStart_137004 : Nat := 118140960795 + 137004 * 2 ^ 59
def prefixEnd_137004 : Nat := 4983230072969 + 3 ^ 40 * 137004 * 2
def baseEnd_137004 : Nat := 31266179372749868853305

theorem tailTrace_137004 : CollatzResearch.WordTrace tailWord_137004 prefixEnd_137004 31266179372749868853305 := by
  unfold tailWord_137004
  simp only [CollatzResearch.WordTrace]
  refine ⟨2498473197832690632733033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3331297597110254176977377 2498473197832690632733033)
  ·
    refine ⟨1873854898374517974549775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2498473197832690632733033 1873854898374517974549775)
    ·
      refine ⟨2810782347561776961824663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1873854898374517974549775 2810782347561776961824663)
      ·
        refine ⟨4216173521342665442736995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2810782347561776961824663 4216173521342665442736995)
        ·
          refine ⟨6324260282013998164105493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4216173521342665442736995 6324260282013998164105493)
          ·
            refine ⟨296449700719406163942445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6324260282013998164105493 296449700719406163942445)
            ·
              refine ⟨111168637769777311478417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 296449700719406163942445 111168637769777311478417)
              ·
                refine ⟨83376478327332983608813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111168637769777311478417 83376478327332983608813)
                ·
                  refine ⟨31266179372749868853305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83376478327332983608813 31266179372749868853305)
                  ·
                    rfl

theorem cell21_137004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 3, 2, 3].length) (baseStart_137004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_137004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_137004 prefixEnd_137004 := by exact prefixLift 137004
  have htrace : WordTrace (prefixWord ++ tailWord_137004) baseStart_137004 baseEnd_137004 := by
    simpa [prefixWord, tailWord_137004, baseEnd_137004] using wordTrace_append hprefix tailTrace_137004
  have hstable : (prefixWord ++ tailWord_137004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137004).length < 2 ^ (prefixWord ++ tailWord_137004).sum := by decide
  have hdescent : baseEnd_137004 < baseStart_137004 := by decide
  rcases family_descends (prefixWord ++ tailWord_137004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137018 : List Nat := [3, 1, 1, 1, 5, 1, 4, 1, 4]
def baseStart_137018 : Nat := 118140960795 + 137018 * 2 ^ 59
def prefixEnd_137018 : Nat := 4983230072969 + 3 ^ 40 * 137018 * 2
def baseEnd_137018 : Nat := 31269374363488955619943

theorem tailTrace_137018 : CollatzResearch.WordTrace tailWord_137018 prefixEnd_137018 31269374363488955619943 := by
  unfold tailWord_137018
  simp only [CollatzResearch.WordTrace]
  refine ⟨1249364254403665414118927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3331638011743107770983805 1249364254403665414118927)
  ·
    refine ⟨1874046381605498121178391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1249364254403665414118927 1874046381605498121178391)
    ·
      refine ⟨2811069572408247181767587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1874046381605498121178391 2811069572408247181767587)
      ·
        refine ⟨4216604358612370772651381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2811069572408247181767587 4216604358612370772651381)
        ·
          refine ⟨395306658619909759936067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4216604358612370772651381 395306658619909759936067)
          ·
            refine ⟨592959987929864639904101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395306658619909759936067 592959987929864639904101)
            ·
              refine ⟨111179997736849619982019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 592959987929864639904101 111179997736849619982019)
              ·
                refine ⟨166769996605274429973029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111179997736849619982019 166769996605274429973029)
                ·
                  refine ⟨31269374363488955619943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 166769996605274429973029 31269374363488955619943)
                  ·
                    rfl

theorem cell21_137018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 4, 1, 4].length) (baseStart_137018 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_137018 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_137018 prefixEnd_137018 := by exact prefixLift 137018
  have htrace : WordTrace (prefixWord ++ tailWord_137018) baseStart_137018 baseEnd_137018 := by
    simpa [prefixWord, tailWord_137018, baseEnd_137018] using wordTrace_append hprefix tailTrace_137018
  have hstable : (prefixWord ++ tailWord_137018).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137018).length < 2 ^ (prefixWord ++ tailWord_137018).sum := by decide
  have hdescent : baseEnd_137018 < baseStart_137018 := by decide
  rcases family_descends (prefixWord ++ tailWord_137018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137029 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 7]
def baseStart_137029 : Nat := 118140960795 + 137029 * 2 ^ 59
def prefixEnd_137029 : Nat := 4983230072969 + 3 ^ 40 * 137029 * 2
def baseEnd_137029 : Nat := 31271884713355380936587

theorem tailTrace_137029 : CollatzResearch.WordTrace tailWord_137029 prefixEnd_137029 31271884713355380936587 := by
  unfold tailWord_137029
  simp only [CollatzResearch.WordTrace]
  refine ⟨4997858220574810535126141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3331905480383207023417427 4997858220574810535126141)
  ·
    refine ⟨1874196832715553950672303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4997858220574810535126141 1874196832715553950672303)
    ·
      refine ⟨2811295249073330926008455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1874196832715553950672303 2811295249073330926008455)
      ·
        refine ⟨4216942873609996389012683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2811295249073330926008455 4216942873609996389012683)
        ·
          refine ⟨6325414310414994583519025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4216942873609996389012683 6325414310414994583519025)
          ·
            refine ⟨4744060732811245937639269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6325414310414994583519025 4744060732811245937639269)
            ·
              refine ⟨889511387402108613307363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4744060732811245937639269 889511387402108613307363)
              ·
                refine ⟨1334267081103162919961045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 889511387402108613307363 1334267081103162919961045)
                ·
                  refine ⟨31271884713355380936587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1334267081103162919961045 31271884713355380936587)
                  ·
                    rfl

theorem cell21_137029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_137029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_137029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_137029 prefixEnd_137029 := by exact prefixLift 137029
  have htrace : WordTrace (prefixWord ++ tailWord_137029) baseStart_137029 baseEnd_137029 := by
    simpa [prefixWord, tailWord_137029, baseEnd_137029] using wordTrace_append hprefix tailTrace_137029
  have hstable : (prefixWord ++ tailWord_137029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137029).length < 2 ^ (prefixWord ++ tailWord_137029).sum := by decide
  have hdescent : baseEnd_137029 < baseStart_137029 := by decide
  rcases family_descends (prefixWord ++ tailWord_137029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137063 : List Nat := [1, 1, 5, 1, 2, 1, 3, 4, 3]
def baseStart_137063 : Nat := 118140960795 + 137063 * 2 ^ 59
def prefixEnd_137063 : Nat := 4983230072969 + 3 ^ 40 * 137063 * 2
def baseEnd_137063 : Nat := 31279643976578877369851

theorem tailTrace_137063 : CollatzResearch.WordTrace tailWord_137063 prefixEnd_137063 31279643976578877369851 := by
  unfold tailWord_137063
  simp only [CollatzResearch.WordTrace]
  refine ⟨4999098302451634341863843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3332732201634422894575895 4999098302451634341863843)
  ·
    refine ⟨7498647453677451512795765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4999098302451634341863843 7498647453677451512795765)
    ·
      refine ⟨702998198782261079324603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7498647453677451512795765 702998198782261079324603)
      ·
        refine ⟨1054497298173391618986905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 702998198782261079324603 1054497298173391618986905)
        ·
          refine ⟨790872973630043714240179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1054497298173391618986905 790872973630043714240179)
          ·
            refine ⟨1186309460445065571360269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 790872973630043714240179 1186309460445065571360269)
            ·
              refine ⟨444866047666899589260101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1186309460445065571360269 444866047666899589260101)
              ·
                refine ⟨83412383937543672986269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 444866047666899589260101 83412383937543672986269)
                ·
                  refine ⟨31279643976578877369851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83412383937543672986269 31279643976578877369851)
                  ·
                    rfl

theorem cell21_137063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 4, 3].length) (baseStart_137063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_137063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_137063 prefixEnd_137063 := by exact prefixLift 137063
  have htrace : WordTrace (prefixWord ++ tailWord_137063) baseStart_137063 baseEnd_137063 := by
    simpa [prefixWord, tailWord_137063, baseEnd_137063] using wordTrace_append hprefix tailTrace_137063
  have hstable : (prefixWord ++ tailWord_137063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137063).length < 2 ^ (prefixWord ++ tailWord_137063).sum := by decide
  have hdescent : baseEnd_137063 < baseStart_137063 := by decide
  rcases family_descends (prefixWord ++ tailWord_137063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137066 : List Nat := [3, 1, 3, 4, 2, 1, 1, 6]
def baseStart_137066 : Nat := 118140960795 + 137066 * 2 ^ 59
def prefixEnd_137066 : Nat := 4983230072969 + 3 ^ 40 * 137066 * 2
def baseEnd_137066 : Nat := 10426776205817179606615

theorem tailTrace_137066 : CollatzResearch.WordTrace tailWord_137066 prefixEnd_137066 10426776205817179606615 := by
  unfold tailWord_137066
  simp only [CollatzResearch.WordTrace]
  refine ⟨1249801930360191463555763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3332805147627177236148701 1249801930360191463555763)
  ·
    refine ⟨1874702895540287195333645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1249801930360191463555763 1874702895540287195333645)
    ·
      refine ⟨703013585827607698250117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1874702895540287195333645 703013585827607698250117)
      ·
        refine ⟨131815047342676443421897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 703013585827607698250117 131815047342676443421897)
        ·
          refine ⟨98861285507007332566423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 131815047342676443421897 98861285507007332566423)
          ·
            refine ⟨148291928260510998849635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98861285507007332566423 148291928260510998849635)
            ·
              refine ⟨222437892390766498274453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148291928260510998849635 222437892390766498274453)
              ·
                refine ⟨10426776205817179606615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 222437892390766498274453 10426776205817179606615)
                ·
                  rfl

theorem cell21_137066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 4, 2, 1, 1, 6].length) (baseStart_137066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_137066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_137066 prefixEnd_137066 := by exact prefixLift 137066
  have htrace : WordTrace (prefixWord ++ tailWord_137066) baseStart_137066 baseEnd_137066 := by
    simpa [prefixWord, tailWord_137066, baseEnd_137066] using wordTrace_append hprefix tailTrace_137066
  have hstable : (prefixWord ++ tailWord_137066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137066).length < 2 ^ (prefixWord ++ tailWord_137066).sum := by decide
  have hdescent : baseEnd_137066 < baseStart_137066 := by decide
  rcases family_descends (prefixWord ++ tailWord_137066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137077 : List Nat := [1, 3, 4, 1, 1, 1, 1, 5, 4]
def baseStart_137077 : Nat := 118140960795 + 137077 * 2 ^ 59
def prefixEnd_137077 : Nat := 4983230072969 + 3 ^ 40 * 137077 * 2
def baseEnd_137077 : Nat := 31282838967317964136489

theorem tailTrace_137077 : CollatzResearch.WordTrace tailWord_137077 prefixEnd_137077 31282838967317964136489 := by
  unfold tailWord_137077
  simp only [CollatzResearch.WordTrace]
  refine ⟨4999608924400914732873485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3333072616267276488582323 4999608924400914732873485)
  ·
    refine ⟨1874853346650343024827557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4999608924400914732873485 1874853346650343024827557)
    ·
      refine ⟨351535002496939317155167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1874853346650343024827557 351535002496939317155167)
      ·
        refine ⟨527302503745408975732751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351535002496939317155167 527302503745408975732751)
        ·
          refine ⟨790953755618113463599127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 527302503745408975732751 790953755618113463599127)
          ·
            refine ⟨1186430633427170195398691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 790953755618113463599127 1186430633427170195398691)
            ·
              refine ⟨1779645950140755293098037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1186430633427170195398691 1779645950140755293098037)
              ·
                refine ⟨166841807825695808727941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1779645950140755293098037 166841807825695808727941)
                ·
                  refine ⟨31282838967317964136489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 166841807825695808727941 31282838967317964136489)
                  ·
                    rfl

theorem cell21_137077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_137077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_137077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_137077 prefixEnd_137077 := by exact prefixLift 137077
  have htrace : WordTrace (prefixWord ++ tailWord_137077) baseStart_137077 baseEnd_137077 := by
    simpa [prefixWord, tailWord_137077, baseEnd_137077] using wordTrace_append hprefix tailTrace_137077
  have hstable : (prefixWord ++ tailWord_137077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137077).length < 2 ^ (prefixWord ++ tailWord_137077).sum := by decide
  have hdescent : baseEnd_137077 < baseStart_137077 := by decide
  rcases family_descends (prefixWord ++ tailWord_137077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137128 : List Nat := [2, 1, 6, 2, 1, 1, 3, 1, 4]
def baseStart_137128 : Nat := 118140960795 + 137128 * 2 ^ 59
def prefixEnd_137128 : Nat := 4983230072969 + 3 ^ 40 * 137128 * 2
def baseEnd_137128 : Nat := 31294477862153208786385

theorem tailTrace_137128 : CollatzResearch.WordTrace tailWord_137128 prefixEnd_137128 31294477862153208786385 := by
  unfold tailWord_137128
  simp only [CollatzResearch.WordTrace]
  refine ⟨2500734523608075221490019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3334312698144100295320025 2500734523608075221490019)
  ·
    refine ⟨3751101785412112832235029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2500734523608075221490019 3751101785412112832235029)
    ·
      refine ⟨175832896191192789011017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3751101785412112832235029 175832896191192789011017)
      ·
        refine ⟨131874672143394591758263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 175832896191192789011017 131874672143394591758263)
        ·
          refine ⟨197812008215091887637395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131874672143394591758263 197812008215091887637395)
          ·
            refine ⟨296718012322637831456093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197812008215091887637395 296718012322637831456093)
            ·
              refine ⟨111269254620989186796035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 296718012322637831456093 111269254620989186796035)
              ·
                refine ⟨166903881931483780194053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111269254620989186796035 166903881931483780194053)
                ·
                  refine ⟨31294477862153208786385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 166903881931483780194053 31294477862153208786385)
                  ·
                    rfl

theorem cell21_137128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 1, 4].length) (baseStart_137128 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_137128 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_137128 prefixEnd_137128 := by exact prefixLift 137128
  have htrace : WordTrace (prefixWord ++ tailWord_137128) baseStart_137128 baseEnd_137128 := by
    simpa [prefixWord, tailWord_137128, baseEnd_137128] using wordTrace_append hprefix tailTrace_137128
  have hstable : (prefixWord ++ tailWord_137128).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137128).length < 2 ^ (prefixWord ++ tailWord_137128).sum := by decide
  have hdescent : baseEnd_137128 < baseStart_137128 := by decide
  rcases family_descends (prefixWord ++ tailWord_137128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137226 : List Nat := [3, 1, 2, 2, 13]
def baseStart_137226 : Nat := 118140960795 + 137226 * 2 ^ 59
def prefixEnd_137226 : Nat := 4983230072969 + 3 ^ 40 * 137226 * 2
def baseEnd_137226 : Nat := 386627688855886619171

theorem tailTrace_137226 : CollatzResearch.WordTrace tailWord_137226 prefixEnd_137226 386627688855886619171 := by
  unfold tailWord_137226
  simp only [CollatzResearch.WordTrace]
  refine ⟨1251260850215278295011883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3336695600574075453365021 1251260850215278295011883)
  ·
    refine ⟨1876891275322917442517825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1251260850215278295011883 1876891275322917442517825)
    ·
      refine ⟨1407668456492188081888369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1876891275322917442517825 1407668456492188081888369)
      ·
        refine ⟨1055751342369141061416277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1407668456492188081888369 1055751342369141061416277)
        ·
          refine ⟨386627688855886619171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 1055751342369141061416277 386627688855886619171)
          ·
            rfl

theorem cell21_137226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 13].length) (baseStart_137226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_137226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_137226 prefixEnd_137226 := by exact prefixLift 137226
  have htrace : WordTrace (prefixWord ++ tailWord_137226) baseStart_137226 baseEnd_137226 := by
    simpa [prefixWord, tailWord_137226, baseEnd_137226] using wordTrace_append hprefix tailTrace_137226
  have hstable : (prefixWord ++ tailWord_137226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137226).length < 2 ^ (prefixWord ++ tailWord_137226).sum := by decide
  have hdescent : baseEnd_137226 < baseStart_137226 := by decide
  rcases family_descends (prefixWord ++ tailWord_137226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137288 : List Nat := [2, 1, 3, 1, 1, 1, 2, 6, 4]
def baseStart_137288 : Nat := 118140960795 + 137288 * 2 ^ 59
def prefixEnd_137288 : Nat := 4983230072969 + 3 ^ 40 * 137288 * 2
def baseEnd_137288 : Nat := 31330992042028486119391

theorem tailTrace_137288 : CollatzResearch.WordTrace tailWord_137288 prefixEnd_137288 31330992042028486119391 := by
  unfold tailWord_137288
  simp only [CollatzResearch.WordTrace]
  refine ⟨2503652363318248884402259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3338203151090998512536345 2503652363318248884402259)
  ·
    refine ⟨3755478544977373326603389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2503652363318248884402259 3755478544977373326603389)
    ·
      refine ⟨1408304454366514997476271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3755478544977373326603389 1408304454366514997476271)
      ·
        refine ⟨2112456681549772496214407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1408304454366514997476271 2112456681549772496214407)
        ·
          refine ⟨3168685022324658744321611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2112456681549772496214407 3168685022324658744321611)
          ·
            refine ⟨4753027533486988116482417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3168685022324658744321611 4753027533486988116482417)
            ·
              refine ⟨3564770650115241087361813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4753027533486988116482417 3564770650115241087361813)
              ·
                refine ⟨167098624224151925970085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3564770650115241087361813 167098624224151925970085)
                ·
                  refine ⟨31330992042028486119391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 167098624224151925970085 31330992042028486119391)
                  ·
                    rfl

theorem cell21_137288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 6, 4].length) (baseStart_137288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_137288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_137288 prefixEnd_137288 := by exact prefixLift 137288
  have htrace : WordTrace (prefixWord ++ tailWord_137288) baseStart_137288 baseEnd_137288 := by
    simpa [prefixWord, tailWord_137288, baseEnd_137288] using wordTrace_append hprefix tailTrace_137288
  have hstable : (prefixWord ++ tailWord_137288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137288).length < 2 ^ (prefixWord ++ tailWord_137288).sum := by decide
  have hdescent : baseEnd_137288 < baseStart_137288 := by decide
  rcases family_descends (prefixWord ++ tailWord_137288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137305 : List Nat := [1, 2, 1, 2, 2, 1, 7, 1, 4]
def baseStart_137305 : Nat := 118140960795 + 137305 * 2 ^ 59
def prefixEnd_137305 : Nat := 4983230072969 + 3 ^ 40 * 137305 * 2
def baseEnd_137305 : Nat := 31334871673640234336023

theorem tailTrace_137305 : CollatzResearch.WordTrace tailWord_137305 prefixEnd_137305 31334871673640234336023 := by
  unfold tailWord_137305
  simp only [CollatzResearch.WordTrace]
  refine ⟨5007924767574909672173369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3338616511716606448115579 5007924767574909672173369)
  ·
    refine ⟨3755943575681182254130027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5007924767574909672173369 3755943575681182254130027)
    ·
      refine ⟨5633915363521773381195041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3755943575681182254130027 5633915363521773381195041)
      ·
        refine ⟨4225436522641330035896281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5633915363521773381195041 4225436522641330035896281)
        ·
          refine ⟨3169077391980997526922211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4225436522641330035896281 3169077391980997526922211)
          ·
            refine ⟨4753616087971496290383317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3169077391980997526922211 4753616087971496290383317)
            ·
              refine ⟨111412877061831944305859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 4753616087971496290383317 111412877061831944305859)
              ·
                refine ⟨167119315592747916458789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111412877061831944305859 167119315592747916458789)
                ·
                  refine ⟨31334871673640234336023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 167119315592747916458789 31334871673640234336023)
                  ·
                    rfl

theorem cell21_137305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 4].length) (baseStart_137305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_137305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_137305 prefixEnd_137305 := by exact prefixLift 137305
  have htrace : WordTrace (prefixWord ++ tailWord_137305) baseStart_137305 baseEnd_137305 := by
    simpa [prefixWord, tailWord_137305, baseEnd_137305] using wordTrace_append hprefix tailTrace_137305
  have hstable : (prefixWord ++ tailWord_137305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137305).length < 2 ^ (prefixWord ++ tailWord_137305).sum := by decide
  have hdescent : baseEnd_137305 < baseStart_137305 := by decide
  rcases family_descends (prefixWord ++ tailWord_137305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137412 : List Nat := [2, 3, 3, 1, 2, 3, 1, 6]
def baseStart_137412 : Nat := 118140960795 + 137412 * 2 ^ 59
def prefixEnd_137412 : Nat := 4983230072969 + 3 ^ 40 * 137412 * 2
def baseEnd_137412 : Nat := 10453096843810608684157

theorem tailTrace_137412 : CollatzResearch.WordTrace tailWord_137412 prefixEnd_137412 10453096843810608684157 := by
  unfold tailWord_137412
  simp only [CollatzResearch.WordTrace]
  refine ⟨2505913689093633473159245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3341218252124844630878993 2505913689093633473159245)
  ·
    refine ⟨939717633410112552434717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2505913689093633473159245 939717633410112552434717)
    ·
      refine ⟨352394112528792207163019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 939717633410112552434717 352394112528792207163019)
      ·
        refine ⟨528591168793188310744529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352394112528792207163019 528591168793188310744529)
        ·
          refine ⟨396443376594891233058397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 528591168793188310744529 396443376594891233058397)
          ·
            refine ⟨148666266223084212396899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 396443376594891233058397 148666266223084212396899)
            ·
              refine ⟨222999399334626318595349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148666266223084212396899 222999399334626318595349)
              ·
                refine ⟨10453096843810608684157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 222999399334626318595349 10453096843810608684157)
                ·
                  rfl

theorem cell21_137412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 3, 1, 6].length) (baseStart_137412 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_137412 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_137412 prefixEnd_137412 := by exact prefixLift 137412
  have htrace : WordTrace (prefixWord ++ tailWord_137412) baseStart_137412 baseEnd_137412 := by
    simpa [prefixWord, tailWord_137412, baseEnd_137412] using wordTrace_append hprefix tailTrace_137412
  have hstable : (prefixWord ++ tailWord_137412).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137412).length < 2 ^ (prefixWord ++ tailWord_137412).sum := by decide
  have hdescent : baseEnd_137412 < baseStart_137412 := by decide
  rcases family_descends (prefixWord ++ tailWord_137412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137426 : List Nat := [3, 2, 2, 2, 1, 3, 1, 2, 5]
def baseStart_137426 : Nat := 118140960795 + 137426 * 2 ^ 59
def prefixEnd_137426 : Nat := 4983230072969 + 3 ^ 40 * 137426 * 2
def baseEnd_137426 : Nat := 31362485522170912819109

theorem tailTrace_137426 : CollatzResearch.WordTrace tailWord_137426 prefixEnd_137426 31362485522170912819109 := by
  unfold tailWord_137426
  simp only [CollatzResearch.WordTrace]
  refine ⟨1253084500034136834332033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3341558666757698224885421 1253084500034136834332033)
  ·
    refine ⟨939813375025602625749025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1253084500034136834332033 939813375025602625749025)
    ·
      refine ⟨704860031269201969311769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 939813375025602625749025 704860031269201969311769)
      ·
        refine ⟨528645023451901476983827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 704860031269201969311769 528645023451901476983827)
        ·
          refine ⟨792967535177852215475741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528645023451901476983827 792967535177852215475741)
          ·
            refine ⟨297362825691694580803403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 792967535177852215475741 297362825691694580803403)
            ·
              refine ⟨446044238537541871205105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297362825691694580803403 446044238537541871205105)
              ·
                refine ⟨334533178903156403403829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 446044238537541871205105 334533178903156403403829)
                ·
                  refine ⟨31362485522170912819109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 334533178903156403403829 31362485522170912819109)
                  ·
                    rfl

theorem cell21_137426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 5].length) (baseStart_137426 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_137426 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_137426 prefixEnd_137426 := by exact prefixLift 137426
  have htrace : WordTrace (prefixWord ++ tailWord_137426) baseStart_137426 baseEnd_137426 := by
    simpa [prefixWord, tailWord_137426, baseEnd_137426] using wordTrace_append hprefix tailTrace_137426
  have hstable : (prefixWord ++ tailWord_137426).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137426).length < 2 ^ (prefixWord ++ tailWord_137426).sum := by decide
  have hdescent : baseEnd_137426 < baseStart_137426 := by decide
  rcases family_descends (prefixWord ++ tailWord_137426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137499 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 6]
def baseStart_137499 : Nat := 118140960795 + 137499 * 2 ^ 59
def prefixEnd_137499 : Nat := 4983230072969 + 3 ^ 40 * 137499 * 2
def baseEnd_137499 : Nat := 31379145116739008102293

theorem tailTrace_137499 : CollatzResearch.WordTrace tailWord_137499 prefixEnd_137499 31379145116739008102293 := by
  unfold tailWord_137499
  simp only [CollatzResearch.WordTrace]
  refine ⟨5015000528872080804735551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3343333685914720536490367 5015000528872080804735551)
  ·
    refine ⟨7522500793308121207103327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5015000528872080804735551 7522500793308121207103327)
    ·
      refine ⟨11283751189962181810654991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7522500793308121207103327 11283751189962181810654991)
      ·
        refine ⟨16925626784943272715982487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11283751189962181810654991 16925626784943272715982487)
        ·
          refine ⟨25388440177414909073973731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16925626784943272715982487 25388440177414909073973731)
          ·
            refine ⟨38082660266122363610960597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25388440177414909073973731 38082660266122363610960597)
            ·
              refine ⟨892562349987242897131889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 38082660266122363610960597 892562349987242897131889)
              ·
                refine ⟨669421762490432172848917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 892562349987242897131889 669421762490432172848917)
                ·
                  refine ⟨31379145116739008102293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 669421762490432172848917 31379145116739008102293)
                  ·
                    rfl

theorem cell21_137499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 6].length) (baseStart_137499 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_137499 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_137499 prefixEnd_137499 := by exact prefixLift 137499
  have htrace : WordTrace (prefixWord ++ tailWord_137499) baseStart_137499 baseEnd_137499 := by
    simpa [prefixWord, tailWord_137499, baseEnd_137499] using wordTrace_append hprefix tailTrace_137499
  have hstable : (prefixWord ++ tailWord_137499).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137499).length < 2 ^ (prefixWord ++ tailWord_137499).sum := by decide
  have hdescent : baseEnd_137499 < baseStart_137499 := by decide
  rcases family_descends (prefixWord ++ tailWord_137499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137530 : List Nat := [3, 1, 1, 1, 4, 2, 1, 8]
def baseStart_137530 : Nat := 118140960795 + 137530 * 2 ^ 59
def prefixEnd_137530 : Nat := 4983230072969 + 3 ^ 40 * 137530 * 2
def baseEnd_137530 : Nat := 10462073246363281028521

theorem tailTrace_137530 : CollatzResearch.WordTrace tailWord_137530 prefixEnd_137530 10462073246363281028521 := by
  unfold tailWord_137530
  simp only [CollatzResearch.WordTrace]
  refine ⟨1254032797939943274778511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3344087461173182066076029 1254032797939943274778511)
  ·
    refine ⟨1881049196909914912167767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1254032797939943274778511 1881049196909914912167767)
    ·
      refine ⟨2821573795364872368251651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1881049196909914912167767 2821573795364872368251651)
      ·
        refine ⟨4232360693047308552377477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2821573795364872368251651 4232360693047308552377477)
        ·
          refine ⟨793567629946370353570777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4232360693047308552377477 793567629946370353570777)
          ·
            refine ⟨595175722459777765178083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 793567629946370353570777 595175722459777765178083)
            ·
              refine ⟨892763583689666647767125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595175722459777765178083 892763583689666647767125)
              ·
                refine ⟨10462073246363281028521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 892763583689666647767125 10462073246363281028521)
                ·
                  rfl

theorem cell21_137530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_137530 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_137530 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_137530 prefixEnd_137530 := by exact prefixLift 137530
  have htrace : WordTrace (prefixWord ++ tailWord_137530) baseStart_137530 baseEnd_137530 := by
    simpa [prefixWord, tailWord_137530, baseEnd_137530] using wordTrace_append hprefix tailTrace_137530
  have hstable : (prefixWord ++ tailWord_137530).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137530).length < 2 ^ (prefixWord ++ tailWord_137530).sum := by decide
  have hdescent : baseEnd_137530 < baseStart_137530 := by decide
  rcases family_descends (prefixWord ++ tailWord_137530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137564 : List Nat := [2, 2, 4, 3, 2, 8]
def baseStart_137564 : Nat := 118140960795 + 137564 * 2 ^ 59
def prefixEnd_137564 : Nat := 4983230072969 + 3 ^ 40 * 137564 * 2
def baseEnd_137564 : Nat := 1162739963048642204401

theorem tailTrace_137564 : CollatzResearch.WordTrace tailWord_137564 prefixEnd_137564 1162739963048642204401 := by
  unfold tailWord_137564
  simp only [CollatzResearch.WordTrace]
  refine ⟨2508685636818298452925873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3344914182424397937234497 2508685636818298452925873)
  ·
    refine ⟨1881514227613723839694405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2508685636818298452925873 1881514227613723839694405)
    ·
      refine ⟨352783917677573219942701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1881514227613723839694405 352783917677573219942701)
      ·
        refine ⟨132293969129089957478513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 352783917677573219942701 132293969129089957478513)
        ·
          refine ⟨99220476846817468108885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132293969129089957478513 99220476846817468108885)
          ·
            refine ⟨1162739963048642204401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 99220476846817468108885 1162739963048642204401)
            ·
              rfl

theorem cell21_137564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 8].length) (baseStart_137564 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_137564 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_137564 prefixEnd_137564 := by exact prefixLift 137564
  have htrace : WordTrace (prefixWord ++ tailWord_137564) baseStart_137564 baseEnd_137564 := by
    simpa [prefixWord, tailWord_137564, baseEnd_137564] using wordTrace_append hprefix tailTrace_137564
  have hstable : (prefixWord ++ tailWord_137564).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137564).length < 2 ^ (prefixWord ++ tailWord_137564).sum := by decide
  have hdescent : baseEnd_137564 < baseStart_137564 := by decide
  rcases family_descends (prefixWord ++ tailWord_137564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137637 : List Nat := [1, 3, 1, 2, 1, 1, 6, 1, 5]
def baseStart_137637 : Nat := 118140960795 + 137637 * 2 ^ 59
def prefixEnd_137637 : Nat := 4983230072969 + 3 ^ 40 * 137637 * 2
def baseEnd_137637 : Nat := 31410638596881434802011

theorem tailTrace_137637 : CollatzResearch.WordTrace tailWord_137637 prefixEnd_137637 31410638596881434802011 := by
  unfold tailWord_137637
  simp only [CollatzResearch.WordTrace]
  refine ⟨5020033802372130373259165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3346689201581420248839443 5020033802372130373259165)
  ·
    refine ⟨1882512675889548889972187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5020033802372130373259165 1882512675889548889972187)
    ·
      refine ⟨2823769013834323334958281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1882512675889548889972187 2823769013834323334958281)
      ·
        refine ⟨2117826760375742501218711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2823769013834323334958281 2117826760375742501218711)
        ·
          refine ⟨3176740140563613751828067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2117826760375742501218711 3176740140563613751828067)
          ·
            refine ⟨4765110210845420627742101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3176740140563613751828067 4765110210845420627742101)
            ·
              refine ⟨223364541133379091925411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4765110210845420627742101 223364541133379091925411)
              ·
                refine ⟨335046811700068637888117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223364541133379091925411 335046811700068637888117)
                ·
                  refine ⟨31410638596881434802011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 335046811700068637888117 31410638596881434802011)
                  ·
                    rfl

theorem cell21_137637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 5].length) (baseStart_137637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_137637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_137637 prefixEnd_137637 := by exact prefixLift 137637
  have htrace : WordTrace (prefixWord ++ tailWord_137637) baseStart_137637 baseEnd_137637 := by
    simpa [prefixWord, tailWord_137637, baseEnd_137637] using wordTrace_append hprefix tailTrace_137637
  have hstable : (prefixWord ++ tailWord_137637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137637).length < 2 ^ (prefixWord ++ tailWord_137637).sum := by decide
  have hdescent : baseEnd_137637 < baseStart_137637 := by decide
  rcases family_descends (prefixWord ++ tailWord_137637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137671 : List Nat := [1, 1, 4, 1, 1, 6, 1, 3, 3]
def baseStart_137671 : Nat := 118140960795 + 137671 * 2 ^ 59
def prefixEnd_137671 : Nat := 4983230072969 + 3 ^ 40 * 137671 * 2
def baseEnd_137671 : Nat := 31418397860104931235275

theorem tailTrace_137671 : CollatzResearch.WordTrace tailWord_137671 prefixEnd_137671 31418397860104931235275 := by
  unfold tailWord_137671
  simp only [CollatzResearch.WordTrace]
  refine ⟨5021273884248954179996867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3347515922832636119997911 5021273884248954179996867)
  ·
    refine ⟨7531910826373431269995301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5021273884248954179996867 7531910826373431269995301)
    ·
      refine ⟨1412233279945018363124119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7531910826373431269995301 1412233279945018363124119)
      ·
        refine ⟨2118349919917527544686179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1412233279945018363124119 2118349919917527544686179)
        ·
          refine ⟨3177524879876291317029269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2118349919917527544686179 3177524879876291317029269)
          ·
            refine ⟨148946478744201155485747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3177524879876291317029269 148946478744201155485747)
            ·
              refine ⟨223419718116301733228621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148946478744201155485747 223419718116301733228621)
              ·
                refine ⟨83782394293613149960733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 223419718116301733228621 83782394293613149960733)
                ·
                  refine ⟨31418397860104931235275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83782394293613149960733 31418397860104931235275)
                  ·
                    rfl

theorem cell21_137671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 3, 3].length) (baseStart_137671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_137671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_137671 prefixEnd_137671 := by exact prefixLift 137671
  have htrace : WordTrace (prefixWord ++ tailWord_137671) baseStart_137671 baseEnd_137671 := by
    simpa [prefixWord, tailWord_137671, baseEnd_137671] using wordTrace_append hprefix tailTrace_137671
  have hstable : (prefixWord ++ tailWord_137671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137671).length < 2 ^ (prefixWord ++ tailWord_137671).sum := by decide
  have hdescent : baseEnd_137671 < baseStart_137671 := by decide
  rcases family_descends (prefixWord ++ tailWord_137671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137699 : List Nat := [1, 1, 1, 6, 3, 1, 2, 6]
def baseStart_137699 : Nat := 118140960795 + 137699 * 2 ^ 59
def prefixEnd_137699 : Nat := 4983230072969 + 3 ^ 40 * 137699 * 2
def baseEnd_137699 : Nat := 10474929280527701589517

theorem tailTrace_137699 : CollatzResearch.WordTrace tailWord_137699 prefixEnd_137699 10474929280527701589517 := by
  unfold tailWord_137699
  simp only [CollatzResearch.WordTrace]
  refine ⟨5022295128147514962016151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3348196752098343308010767 5022295128147514962016151)
  ·
    refine ⟨7533442692221272443024227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5022295128147514962016151 7533442692221272443024227)
    ·
      refine ⟨11300164038331908664536341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7533442692221272443024227 11300164038331908664536341)
      ·
        refine ⟨529695189296808218650141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11300164038331908664536341 529695189296808218650141)
        ·
          refine ⟨198635695986303081993803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 529695189296808218650141 198635695986303081993803)
          ·
            refine ⟨297953543979454622990705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198635695986303081993803 297953543979454622990705)
            ·
              refine ⟨223465157984590967243029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 297953543979454622990705 223465157984590967243029)
              ·
                refine ⟨10474929280527701589517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 223465157984590967243029 10474929280527701589517)
                ·
                  rfl

theorem cell21_137699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 2, 6].length) (baseStart_137699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_137699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_137699 prefixEnd_137699 := by exact prefixLift 137699
  have htrace : WordTrace (prefixWord ++ tailWord_137699) baseStart_137699 baseEnd_137699 := by
    simpa [prefixWord, tailWord_137699, baseEnd_137699] using wordTrace_append hprefix tailTrace_137699
  have hstable : (prefixWord ++ tailWord_137699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137699).length < 2 ^ (prefixWord ++ tailWord_137699).sum := by decide
  have hdescent : baseEnd_137699 < baseStart_137699 := by decide
  rcases family_descends (prefixWord ++ tailWord_137699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137806 : List Nat := [4, 1, 1, 1, 1, 2, 4, 4, 3]
def baseStart_137806 : Nat := 118140960795 + 137806 * 2 ^ 59
def prefixEnd_137806 : Nat := 4983230072969 + 3 ^ 40 * 137806 * 2
def baseEnd_137806 : Nat := 31449206699374696484999

theorem tailTrace_137806 : CollatzResearch.WordTrace tailWord_137806 prefixEnd_137806 31449206699374696484999 := by
  unfold tailWord_137806
  simp only [CollatzResearch.WordTrace]
  refine ⟨628274717344984029520159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3350798492506581490774181 628274717344984029520159)
  ·
    refine ⟨942412076017476044280239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 628274717344984029520159 942412076017476044280239)
    ·
      refine ⟨1413618114026214066420359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 942412076017476044280239 1413618114026214066420359)
      ·
        refine ⟨2120427171039321099630539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1413618114026214066420359 2120427171039321099630539)
        ·
          refine ⟨3180640756558981649445809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2120427171039321099630539 3180640756558981649445809)
          ·
            refine ⟨2385480567419236237084357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3180640756558981649445809 2385480567419236237084357)
            ·
              refine ⟨447277606391106794453317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2385480567419236237084357 447277606391106794453317)
              ·
                refine ⟨83864551198332523959997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 447277606391106794453317 83864551198332523959997)
                ·
                  refine ⟨31449206699374696484999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83864551198332523959997 31449206699374696484999)
                  ·
                    rfl

theorem cell21_137806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 4, 4, 3].length) (baseStart_137806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_137806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_137806 prefixEnd_137806 := by exact prefixLift 137806
  have htrace : WordTrace (prefixWord ++ tailWord_137806) baseStart_137806 baseEnd_137806 := by
    simpa [prefixWord, tailWord_137806, baseEnd_137806] using wordTrace_append hprefix tailTrace_137806
  have hstable : (prefixWord ++ tailWord_137806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137806).length < 2 ^ (prefixWord ++ tailWord_137806).sum := by decide
  have hdescent : baseEnd_137806 < baseStart_137806 := by decide
  rcases family_descends (prefixWord ++ tailWord_137806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137826 : List Nat := [3, 3, 2, 3, 2, 1, 2, 5]
def baseStart_137826 : Nat := 118140960795 + 137826 * 2 ^ 59
def prefixEnd_137826 : Nat := 4983230072969 + 3 ^ 40 * 137826 * 2
def baseEnd_137826 : Nat := 10484590323953035383875

theorem tailTrace_137826 : CollatzResearch.WordTrace tailWord_137826 prefixEnd_137826 10484590323953035383875 := by
  unfold tailWord_137826
  simp only [CollatzResearch.WordTrace]
  refine ⟨1256731799671853912972333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3351284799124943767926221 1256731799671853912972333)
  ·
    refine ⟨471274424876945217364625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1256731799671853912972333 471274424876945217364625)
    ·
      refine ⟨353455818657708913023469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 471274424876945217364625 353455818657708913023469)
      ·
        refine ⟨132545931996640842383801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 353455818657708913023469 132545931996640842383801)
        ·
          refine ⟨99409448997480631787851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132545931996640842383801 99409448997480631787851)
          ·
            refine ⟨149114173496220947681777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99409448997480631787851 149114173496220947681777)
            ·
              refine ⟨111835630122165710761333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149114173496220947681777 111835630122165710761333)
              ·
                refine ⟨10484590323953035383875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 111835630122165710761333 10484590323953035383875)
                ·
                  rfl

theorem cell21_137826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 5].length) (baseStart_137826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_137826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_137826 prefixEnd_137826 := by exact prefixLift 137826
  have htrace : WordTrace (prefixWord ++ tailWord_137826) baseStart_137826 baseEnd_137826 := by
    simpa [prefixWord, tailWord_137826, baseEnd_137826] using wordTrace_append hprefix tailTrace_137826
  have hstable : (prefixWord ++ tailWord_137826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137826).length < 2 ^ (prefixWord ++ tailWord_137826).sum := by decide
  have hdescent : baseEnd_137826 < baseStart_137826 := by decide
  rcases family_descends (prefixWord ++ tailWord_137826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137834 : List Nat := [3, 1, 3, 2, 1, 1, 3, 7]
def baseStart_137834 : Nat := 118140960795 + 137834 * 2 ^ 59
def prefixEnd_137834 : Nat := 4983230072969 + 3 ^ 40 * 137834 * 2
def baseEnd_137834 : Nat := 10485198893617623339425

theorem tailTrace_137834 : CollatzResearch.WordTrace tailWord_137834 prefixEnd_137834 10485198893617623339425 := by
  unfold tailWord_137834
  simp only [CollatzResearch.WordTrace]
  refine ⟨1256804745664608254545139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3351479321772288678787037 1256804745664608254545139)
  ·
    refine ⟨1885207118496912381817709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1256804745664608254545139 1885207118496912381817709)
    ·
      refine ⟨706952669436342143181641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1885207118496912381817709 706952669436342143181641)
      ·
        refine ⟨530214502077256607386231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 706952669436342143181641 530214502077256607386231)
        ·
          refine ⟨795321753115884911079347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 530214502077256607386231 795321753115884911079347)
          ·
            refine ⟨1192982629673827366619021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 795321753115884911079347 1192982629673827366619021)
            ·
              refine ⟨447368486127685262482133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1192982629673827366619021 447368486127685262482133)
              ·
                refine ⟨10485198893617623339425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 447368486127685262482133 10485198893617623339425)
                ·
                  rfl

theorem cell21_137834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_137834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_137834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_137834 prefixEnd_137834 := by exact prefixLift 137834
  have htrace : WordTrace (prefixWord ++ tailWord_137834) baseStart_137834 baseEnd_137834 := by
    simpa [prefixWord, tailWord_137834, baseEnd_137834] using wordTrace_append hprefix tailTrace_137834
  have hstable : (prefixWord ++ tailWord_137834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137834).length < 2 ^ (prefixWord ++ tailWord_137834).sum := by decide
  have hdescent : baseEnd_137834 < baseStart_137834 := by decide
  rcases family_descends (prefixWord ++ tailWord_137834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137840 : List Nat := [2, 1, 1, 1, 8, 1, 1, 3, 3]
def baseStart_137840 : Nat := 118140960795 + 137840 * 2 ^ 59
def prefixEnd_137840 : Nat := 4983230072969 + 3 ^ 40 * 137840 * 2
def baseEnd_137840 : Nat := 31456965962598192918263

theorem tailTrace_137840 : CollatzResearch.WordTrace tailWord_137840 prefixEnd_137840 31456965962598192918263 := by
  unfold tailWord_137840
  simp only [CollatzResearch.WordTrace]
  refine ⟨2513718910318348021449487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3351625213757797361932649 2513718910318348021449487)
  ·
    refine ⟨3770578365477522032174231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2513718910318348021449487 3770578365477522032174231)
    ·
      refine ⟨5655867548216283048261347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3770578365477522032174231 5655867548216283048261347)
      ·
        refine ⟨8483801322324424572392021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5655867548216283048261347 8483801322324424572392021)
        ·
          refine ⟨99419546745989350457719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 8483801322324424572392021 99419546745989350457719)
          ·
            refine ⟨149129320118984025686579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99419546745989350457719 149129320118984025686579)
            ·
              refine ⟨223693980178476038529869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149129320118984025686579 223693980178476038529869)
              ·
                refine ⟨83885242566928514448701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 223693980178476038529869 83885242566928514448701)
                ·
                  refine ⟨31456965962598192918263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 83885242566928514448701 31456965962598192918263)
                  ·
                    rfl

theorem cell21_137840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 8, 1, 1, 3, 3].length) (baseStart_137840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_137840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_137840 prefixEnd_137840 := by exact prefixLift 137840
  have htrace : WordTrace (prefixWord ++ tailWord_137840) baseStart_137840 baseEnd_137840 := by
    simpa [prefixWord, tailWord_137840, baseEnd_137840] using wordTrace_append hprefix tailTrace_137840
  have hstable : (prefixWord ++ tailWord_137840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137840).length < 2 ^ (prefixWord ++ tailWord_137840).sum := by decide
  have hdescent : baseEnd_137840 < baseStart_137840 := by decide
  rcases family_descends (prefixWord ++ tailWord_137840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137969 : List Nat := [1, 2, 2, 2, 2, 2, 10]
def baseStart_137969 : Nat := 118140960795 + 137969 * 2 ^ 59
def prefixEnd_137969 : Nat := 4983230072969 + 3 ^ 40 * 137969 * 2
def baseEnd_137969 : Nat := 3498489502235848363111

theorem tailTrace_137969 : CollatzResearch.WordTrace tailWord_137969 prefixEnd_137969 3498489502235848363111 := by
  unfold tailWord_137969
  simp only [CollatzResearch.WordTrace]
  refine ⟨5032142837169351074344961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3354761891446234049563307 5032142837169351074344961)
  ·
    refine ⟨3774107127877013305758721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5032142837169351074344961 3774107127877013305758721)
    ·
      refine ⟨2830580345907759979319041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3774107127877013305758721 2830580345907759979319041)
      ·
        refine ⟨2122935259430819984489281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2830580345907759979319041 2122935259430819984489281)
        ·
          refine ⟨1592201444573114988366961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2122935259430819984489281 1592201444573114988366961)
          ·
            refine ⟨1194151083429836241275221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1592201444573114988366961 1194151083429836241275221)
            ·
              refine ⟨3498489502235848363111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1194151083429836241275221 3498489502235848363111)
              ·
                rfl

theorem cell21_137969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 10].length) (baseStart_137969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_137969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_137969 prefixEnd_137969 := by exact prefixLift 137969
  have htrace : WordTrace (prefixWord ++ tailWord_137969) baseStart_137969 baseEnd_137969 := by
    simpa [prefixWord, tailWord_137969, baseEnd_137969] using wordTrace_append hprefix tailTrace_137969
  have hstable : (prefixWord ++ tailWord_137969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137969).length < 2 ^ (prefixWord ++ tailWord_137969).sum := by decide
  have hdescent : baseEnd_137969 < baseStart_137969 := by decide
  rcases family_descends (prefixWord ++ tailWord_137969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138107 : List Nat := [1, 1, 1, 1, 1, 5, 4, 3, 4]
def baseStart_138107 : Nat := 118140960795 + 138107 * 2 ^ 59
def prefixEnd_138107 : Nat := 4983230072969 + 3 ^ 40 * 138107 * 2
def baseEnd_138107 : Nat := 31517899000265061967717

theorem tailTrace_138107 : CollatzResearch.WordTrace tailWord_138107 prefixEnd_138107 31517899000265061967717 := by
  unfold tailWord_138107
  simp only [CollatzResearch.WordTrace]
  refine ⟨5037176110669400642868575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3358117407112933761912383 5037176110669400642868575)
  ·
    refine ⟨7555764166004100964302863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5037176110669400642868575 7555764166004100964302863)
    ·
      refine ⟨11333646249006151446454295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7555764166004100964302863 11333646249006151446454295)
      ·
        refine ⟨17000469373509227169681443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11333646249006151446454295 17000469373509227169681443)
        ·
          refine ⟨25500704060263840754522165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17000469373509227169681443 25500704060263840754522165)
          ·
            refine ⟨2390691005649735070736453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 25500704060263840754522165 2390691005649735070736453)
            ·
              refine ⟨448254563559325325763085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2390691005649735070736453 448254563559325325763085)
              ·
                refine ⟨168095461334746997161157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 448254563559325325763085 168095461334746997161157)
                ·
                  refine ⟨31517899000265061967717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 168095461334746997161157 31517899000265061967717)
                  ·
                    rfl

theorem cell21_138107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 4].length) (baseStart_138107 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138107 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138107 prefixEnd_138107 := by exact prefixLift 138107
  have htrace : WordTrace (prefixWord ++ tailWord_138107) baseStart_138107 baseEnd_138107 := by
    simpa [prefixWord, tailWord_138107, baseEnd_138107] using wordTrace_append hprefix tailTrace_138107
  have hstable : (prefixWord ++ tailWord_138107).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138107).length < 2 ^ (prefixWord ++ tailWord_138107).sum := by decide
  have hdescent : baseEnd_138107 < baseStart_138107 := by decide
  rcases family_descends (prefixWord ++ tailWord_138107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138138 : List Nat := [3, 1, 1, 4, 3, 1, 8]
def baseStart_138138 : Nat := 118140960795 + 138138 * 2 ^ 59
def prefixEnd_138138 : Nat := 4983230072969 + 3 ^ 40 * 138138 * 2
def baseEnd_138138 : Nat := 3502774846957321883443

theorem tailTrace_138138 : CollatzResearch.WordTrace tailWord_138138 prefixEnd_138138 3502774846957321883443 := by
  unfold tailWord_138138
  simp only [CollatzResearch.WordTrace]
  refine ⟨1259576693389273234311767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3358871182371395291498045 1259576693389273234311767)
  ·
    refine ⟨1889365040083909851467651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1259576693389273234311767 1889365040083909851467651)
    ·
      refine ⟨2834047560125864777201477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1889365040083909851467651 2834047560125864777201477)
      ·
        refine ⟨531383917523599645725277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2834047560125864777201477 531383917523599645725277)
        ·
          refine ⟨199268969071349867146979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 531383917523599645725277 199268969071349867146979)
          ·
            refine ⟨298903453607024800720469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199268969071349867146979 298903453607024800720469)
            ·
              refine ⟨3502774846957321883443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 298903453607024800720469 3502774846957321883443)
              ·
                rfl

theorem cell21_138138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 8].length) (baseStart_138138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138138 prefixEnd_138138 := by exact prefixLift 138138
  have htrace : WordTrace (prefixWord ++ tailWord_138138) baseStart_138138 baseEnd_138138 := by
    simpa [prefixWord, tailWord_138138, baseEnd_138138] using wordTrace_append hprefix tailTrace_138138
  have hstable : (prefixWord ++ tailWord_138138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138138).length < 2 ^ (prefixWord ++ tailWord_138138).sum := by decide
  have hdescent : baseEnd_138138 < baseStart_138138 := by decide
  rcases family_descends (prefixWord ++ tailWord_138138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138189 : List Nat := [1, 6, 3, 1, 1, 2, 7]
def baseStart_138189 : Nat := 118140960795 + 138189 * 2 ^ 59
def prefixEnd_138189 : Nat := 4983230072969 + 3 ^ 40 * 138189 * 2
def baseEnd_138189 : Nat := 3504068057494571288987

theorem tailTrace_138189 : CollatzResearch.WordTrace tailWord_138189 prefixEnd_138189 3504068057494571288987 := by
  unfold tailWord_138189
  simp only [CollatzResearch.WordTrace]
  refine ⟨5040166896372328647353621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3360111264248219098235747 5040166896372328647353621)
  ·
    refine ⟨236257823267452905344701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5040166896372328647353621 236257823267452905344701)
    ·
      refine ⟨88596683725294839504263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 236257823267452905344701 88596683725294839504263)
      ·
        refine ⟨132895025587942259256395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 88596683725294839504263 132895025587942259256395)
        ·
          refine ⟨199342538381913388884593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132895025587942259256395 199342538381913388884593)
          ·
            refine ⟨149506903786435041663445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199342538381913388884593 149506903786435041663445)
            ·
              refine ⟨3504068057494571288987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 149506903786435041663445 3504068057494571288987)
              ·
                rfl

theorem cell21_138189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 7].length) (baseStart_138189 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138189 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138189 prefixEnd_138189 := by exact prefixLift 138189
  have htrace : WordTrace (prefixWord ++ tailWord_138189) baseStart_138189 baseEnd_138189 := by
    simpa [prefixWord, tailWord_138189, baseEnd_138189] using wordTrace_append hprefix tailTrace_138189
  have hstable : (prefixWord ++ tailWord_138189).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138189).length < 2 ^ (prefixWord ++ tailWord_138189).sum := by decide
  have hdescent : baseEnd_138189 < baseStart_138189 := by decide
  rcases family_descends (prefixWord ++ tailWord_138189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138245 : List Nat := [1, 3, 1, 1, 2, 3, 2, 5, 3]
def baseStart_138245 : Nat := 118140960795 + 138245 * 2 ^ 59
def prefixEnd_138245 : Nat := 4983230072969 + 3 ^ 40 * 138245 * 2
def baseEnd_138245 : Nat := 31549392480407488667435

theorem tailTrace_138245 : CollatzResearch.WordTrace tailWord_138245 prefixEnd_138245 31549392480407488667435 := by
  unfold tailWord_138245
  simp only [CollatzResearch.WordTrace]
  refine ⟨5042209384169450211392189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3361472922779633474261459 5042209384169450211392189)
  ·
    refine ⟨1890828519063543829272071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5042209384169450211392189 1890828519063543829272071)
    ·
      refine ⟨2836242778595315743908107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1890828519063543829272071 2836242778595315743908107)
      ·
        refine ⟨4254364167892973615862161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2836242778595315743908107 4254364167892973615862161)
        ·
          refine ⟨3190773125919730211896621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4254364167892973615862161 3190773125919730211896621)
          ·
            refine ⟨1196539922219898829461233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3190773125919730211896621 1196539922219898829461233)
            ·
              refine ⟨897404941664924122095925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1196539922219898829461233 897404941664924122095925)
              ·
                refine ⟨84131713281086636446493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 897404941664924122095925 84131713281086636446493)
                ·
                  refine ⟨31549392480407488667435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84131713281086636446493 31549392480407488667435)
                  ·
                    rfl

theorem cell21_138245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 5, 3].length) (baseStart_138245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138245 prefixEnd_138245 := by exact prefixLift 138245
  have htrace : WordTrace (prefixWord ++ tailWord_138245) baseStart_138245 baseEnd_138245 := by
    simpa [prefixWord, tailWord_138245, baseEnd_138245] using wordTrace_append hprefix tailTrace_138245
  have hstable : (prefixWord ++ tailWord_138245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138245).length < 2 ^ (prefixWord ++ tailWord_138245).sum := by decide
  have hdescent : baseEnd_138245 < baseStart_138245 := by decide
  rcases family_descends (prefixWord ++ tailWord_138245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138276 : List Nat := [2, 3, 1, 4, 1, 1, 2, 3, 4]
def baseStart_138276 : Nat := 118140960795 + 138276 * 2 ^ 59
def prefixEnd_138276 : Nat := 4983230072969 + 3 ^ 40 * 138276 * 2
def baseEnd_138276 : Nat := 31556467102758323650705

theorem tailTrace_138276 : CollatzResearch.WordTrace tailWord_138276 prefixEnd_138276 31556467102758323650705 := by
  unfold tailWord_138276
  simp only [CollatzResearch.WordTrace]
  refine ⟨2521670023528571252885341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3362226698038095003847121 2521670023528571252885341)
  ·
    refine ⟨945626258823214219832003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2521670023528571252885341 945626258823214219832003)
    ·
      refine ⟨1418439388234821329748005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 945626258823214219832003 1418439388234821329748005)
      ·
        refine ⟨265957385294028999327751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1418439388234821329748005 265957385294028999327751)
        ·
          refine ⟨398936077941043498991627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265957385294028999327751 398936077941043498991627)
          ·
            refine ⟨598404116911565248487441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 398936077941043498991627 598404116911565248487441)
            ·
              refine ⟨448803087683673936365581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 598404116911565248487441 448803087683673936365581)
              ·
                refine ⟨168301157881377726137093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 448803087683673936365581 168301157881377726137093)
                ·
                  refine ⟨31556467102758323650705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 168301157881377726137093 31556467102758323650705)
                  ·
                    rfl

theorem cell21_138276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_138276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138276 prefixEnd_138276 := by exact prefixLift 138276
  have htrace : WordTrace (prefixWord ++ tailWord_138276) baseStart_138276 baseEnd_138276 := by
    simpa [prefixWord, tailWord_138276, baseEnd_138276] using wordTrace_append hprefix tailTrace_138276
  have hstable : (prefixWord ++ tailWord_138276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138276).length < 2 ^ (prefixWord ++ tailWord_138276).sum := by decide
  have hdescent : baseEnd_138276 < baseStart_138276 := by decide
  rcases family_descends (prefixWord ++ tailWord_138276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138290 : List Nat := [3, 2, 1, 1, 2, 2, 5, 5]
def baseStart_138290 : Nat := 118140960795 + 138290 * 2 ^ 59
def prefixEnd_138290 : Nat := 4983230072969 + 3 ^ 40 * 138290 * 2
def baseEnd_138290 : Nat := 10519887364499136805781

theorem tailTrace_138290 : CollatzResearch.WordTrace tailWord_138290 prefixEnd_138290 10519887364499136805781 := by
  unfold tailWord_138290
  simp only [CollatzResearch.WordTrace]
  refine ⟨1260962667251605724195081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3362567112670948597853549 1260962667251605724195081)
  ·
    refine ⟨945722000438704293146311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1260962667251605724195081 945722000438704293146311)
    ·
      refine ⟨1418583000658056439719467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 945722000438704293146311 1418583000658056439719467)
      ·
        refine ⟨2127874500987084659579201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1418583000658056439719467 2127874500987084659579201)
        ·
          refine ⟨1595905875740313494684401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2127874500987084659579201 1595905875740313494684401)
          ·
            refine ⟨1196929406805235121013301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1595905875740313494684401 1196929406805235121013301)
            ·
              refine ⟨112212131887990792594997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1196929406805235121013301 112212131887990792594997)
              ·
                refine ⟨10519887364499136805781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 112212131887990792594997 10519887364499136805781)
                ·
                  rfl

theorem cell21_138290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_138290 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138290 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138290 prefixEnd_138290 := by exact prefixLift 138290
  have htrace : WordTrace (prefixWord ++ tailWord_138290) baseStart_138290 baseEnd_138290 := by
    simpa [prefixWord, tailWord_138290, baseEnd_138290] using wordTrace_append hprefix tailTrace_138290
  have hstable : (prefixWord ++ tailWord_138290).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138290).length < 2 ^ (prefixWord ++ tailWord_138290).sum := by decide
  have hdescent : baseEnd_138290 < baseStart_138290 := by decide
  rcases family_descends (prefixWord ++ tailWord_138290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138310 : List Nat := [6, 1, 1, 1, 1, 4, 1, 2, 4]
def baseStart_138310 : Nat := 118140960795 + 138310 * 2 ^ 59
def prefixEnd_138310 : Nat := 4983230072969 + 3 ^ 40 * 138310 * 2
def baseEnd_138310 : Nat := 31564226365981820083969

theorem tailTrace_138310 : CollatzResearch.WordTrace tailWord_138310 prefixEnd_138310 31564226365981820083969 := by
  unfold tailWord_138310
  simp only [CollatzResearch.WordTrace]
  refine ⟨157643129029186447265887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3363053419289310875005589 157643129029186447265887)
  ·
    refine ⟨236464693543779670898831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157643129029186447265887 236464693543779670898831)
    ·
      refine ⟨354697040315669506348247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236464693543779670898831 354697040315669506348247)
      ·
        refine ⟨532045560473504259522371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354697040315669506348247 532045560473504259522371)
        ·
          refine ⟨798068340710256389283557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532045560473504259522371 798068340710256389283557)
          ·
            refine ⟨149637813883173072990667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 798068340710256389283557 149637813883173072990667)
            ·
              refine ⟨224456720824759609486001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149637813883173072990667 224456720824759609486001)
              ·
                refine ⟨168342540618569707114501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 224456720824759609486001 168342540618569707114501)
                ·
                  refine ⟨31564226365981820083969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 168342540618569707114501 31564226365981820083969)
                  ·
                    rfl

theorem cell21_138310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_138310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138310 prefixEnd_138310 := by exact prefixLift 138310
  have htrace : WordTrace (prefixWord ++ tailWord_138310) baseStart_138310 baseEnd_138310 := by
    simpa [prefixWord, tailWord_138310, baseEnd_138310] using wordTrace_append hprefix tailTrace_138310
  have hstable : (prefixWord ++ tailWord_138310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138310).length < 2 ^ (prefixWord ++ tailWord_138310).sum := by decide
  have hdescent : baseEnd_138310 < baseStart_138310 := by decide
  rcases family_descends (prefixWord ++ tailWord_138310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138321 : List Nat := [1, 2, 2, 1, 3, 1, 4, 4, 3]
def baseStart_138321 : Nat := 118140960795 + 138321 * 2 ^ 59
def prefixEnd_138321 : Nat := 4983230072969 + 3 ^ 40 * 138321 * 2
def baseEnd_138321 : Nat := 31566736715848245400613

theorem tailTrace_138321 : CollatzResearch.WordTrace tailWord_138321 prefixEnd_138321 31566736715848245400613 := by
  unfold tailWord_138321
  simp only [CollatzResearch.WordTrace]
  refine ⟨5044981331894115191158817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3363320887929410127439211 5044981331894115191158817)
  ·
    refine ⟨3783735998920586393369113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5044981331894115191158817 3783735998920586393369113)
    ·
      refine ⟨2837801999190439795026835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3783735998920586393369113 2837801999190439795026835)
      ·
        refine ⟨4256702998785659692540253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2837801999190439795026835 4256702998785659692540253)
        ·
          refine ⟨1596263624544622384702595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4256702998785659692540253 1596263624544622384702595)
          ·
            refine ⟨2394395436816933577053893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1596263624544622384702595 2394395436816933577053893)
            ·
              refine ⟨448949144403175045697605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2394395436816933577053893 448949144403175045697605)
              ·
                refine ⟨84177964575595321068301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 448949144403175045697605 84177964575595321068301)
                ·
                  refine ⟨31566736715848245400613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84177964575595321068301 31566736715848245400613)
                  ·
                    rfl

theorem cell21_138321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 4, 3].length) (baseStart_138321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138321 prefixEnd_138321 := by exact prefixLift 138321
  have htrace : WordTrace (prefixWord ++ tailWord_138321) baseStart_138321 baseEnd_138321 := by
    simpa [prefixWord, tailWord_138321, baseEnd_138321] using wordTrace_append hprefix tailTrace_138321
  have hstable : (prefixWord ++ tailWord_138321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138321).length < 2 ^ (prefixWord ++ tailWord_138321).sum := by decide
  have hdescent : baseEnd_138321 < baseStart_138321 := by decide
  rcases family_descends (prefixWord ++ tailWord_138321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138363 : List Nat := [1, 1, 1, 1, 1, 4, 1, 4, 7]
def baseStart_138363 : Nat := 118140960795 + 138363 * 2 ^ 59
def prefixEnd_138363 : Nat := 4983230072969 + 3 ^ 40 * 138363 * 2
def baseEnd_138363 : Nat := 31576321688065505700527

theorem tailTrace_138363 : CollatzResearch.WordTrace tailWord_138363 prefixEnd_138363 31576321688065505700527 := by
  unfold tailWord_138363
  simp only [CollatzResearch.WordTrace]
  refine ⟨5046513197741956364187743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3364342131827970909458495 5046513197741956364187743)
  ·
    refine ⟨7569769796612934546281615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5046513197741956364187743 7569769796612934546281615)
    ·
      refine ⟨11354654694919401819422423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7569769796612934546281615 11354654694919401819422423)
      ·
        refine ⟨17031982042379102729133635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11354654694919401819422423 17031982042379102729133635)
        ·
          refine ⟨25547973063568654093700453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17031982042379102729133635 25547973063568654093700453)
          ·
            refine ⟨4790244949419122642568835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25547973063568654093700453 4790244949419122642568835)
            ·
              refine ⟨7185367424128683963853253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4790244949419122642568835 7185367424128683963853253)
              ·
                refine ⟨1347256392024128243222485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7185367424128683963853253 1347256392024128243222485)
                ·
                  refine ⟨31576321688065505700527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1347256392024128243222485 31576321688065505700527)
                  ·
                    rfl

theorem cell21_138363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 4, 7].length) (baseStart_138363 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138363 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138363 prefixEnd_138363 := by exact prefixLift 138363
  have htrace : WordTrace (prefixWord ++ tailWord_138363) baseStart_138363 baseEnd_138363 := by
    simpa [prefixWord, tailWord_138363, baseEnd_138363] using wordTrace_append hprefix tailTrace_138363
  have hstable : (prefixWord ++ tailWord_138363).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138363).length < 2 ^ (prefixWord ++ tailWord_138363).sum := by decide
  have hdescent : baseEnd_138363 < baseStart_138363 := by decide
  rcases family_descends (prefixWord ++ tailWord_138363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138428 : List Nat := [2, 2, 2, 3, 2, 2, 2, 2, 4]
def baseStart_138428 : Nat := 118140960795 + 138428 * 2 ^ 59
def prefixEnd_138428 : Nat := 4983230072969 + 3 ^ 40 * 138428 * 2
def baseEnd_138428 : Nat := 31591155573639837117061

theorem tailTrace_138428 : CollatzResearch.WordTrace tailWord_138428 prefixEnd_138428 31591155573639837117061 := by
  unfold tailWord_138428
  simp only [CollatzResearch.WordTrace]
  refine ⟨2524441971253236232651969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3365922628337648310202625 2524441971253236232651969)
  ·
    refine ⟨1893331478439927174488977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2524441971253236232651969 1893331478439927174488977)
    ·
      refine ⟨1419998608829945380866733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1893331478439927174488977 1419998608829945380866733)
      ·
        refine ⟨532499478311229517825025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1419998608829945380866733 532499478311229517825025)
        ·
          refine ⟨399374608733422138368769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 532499478311229517825025 399374608733422138368769)
          ·
            refine ⟨299530956550066603776577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 399374608733422138368769 299530956550066603776577)
            ·
              refine ⟨224648217412549952832433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 299530956550066603776577 224648217412549952832433)
              ·
                refine ⟨168486163059412464624325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 224648217412549952832433 168486163059412464624325)
                ·
                  refine ⟨31591155573639837117061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 168486163059412464624325 31591155573639837117061)
                  ·
                    rfl

theorem cell21_138428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_138428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138428 prefixEnd_138428 := by exact prefixLift 138428
  have htrace : WordTrace (prefixWord ++ tailWord_138428) baseStart_138428 baseEnd_138428 := by
    simpa [prefixWord, tailWord_138428, baseEnd_138428] using wordTrace_append hprefix tailTrace_138428
  have hstable : (prefixWord ++ tailWord_138428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138428).length < 2 ^ (prefixWord ++ tailWord_138428).sum := by decide
  have hdescent : baseEnd_138428 < baseStart_138428 := by decide
  rcases family_descends (prefixWord ++ tailWord_138428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138439 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 9]
def baseStart_138439 : Nat := 118140960795 + 138439 * 2 ^ 59
def prefixEnd_138439 : Nat := 4983230072969 + 3 ^ 40 * 138439 * 2
def baseEnd_138439 : Nat := 31593665923506262433705

theorem tailTrace_138439 : CollatzResearch.WordTrace tailWord_138439 prefixEnd_138439 31593665923506262433705 := by
  unfold tailWord_138439
  simp only [CollatzResearch.WordTrace]
  refine ⟨5049285145466621343954371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3366190096977747562636247 5049285145466621343954371)
  ·
    refine ⟨7573927718199932015931557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5049285145466621343954371 7573927718199932015931557)
    ·
      refine ⟨1420111447162487252987167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7573927718199932015931557 1420111447162487252987167)
      ·
        refine ⟨2130167170743730879480751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1420111447162487252987167 2130167170743730879480751)
        ·
          refine ⟨3195250756115596319221127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2130167170743730879480751 3195250756115596319221127)
          ·
            refine ⟨4792876134173394478831691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3195250756115596319221127 4792876134173394478831691)
            ·
              refine ⟨7189314201260091718247537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4792876134173394478831691 7189314201260091718247537)
              ·
                refine ⟨5391985650945068788685653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7189314201260091718247537 5391985650945068788685653)
                ·
                  refine ⟨31593665923506262433705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 5391985650945068788685653 31593665923506262433705)
                  ·
                    rfl

theorem cell21_138439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 9].length) (baseStart_138439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138439 prefixEnd_138439 := by exact prefixLift 138439
  have htrace : WordTrace (prefixWord ++ tailWord_138439) baseStart_138439 baseEnd_138439 := by
    simpa [prefixWord, tailWord_138439, baseEnd_138439] using wordTrace_append hprefix tailTrace_138439
  have hstable : (prefixWord ++ tailWord_138439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138439).length < 2 ^ (prefixWord ++ tailWord_138439).sum := by decide
  have hdescent : baseEnd_138439 < baseStart_138439 := by decide
  rcases family_descends (prefixWord ++ tailWord_138439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138442 : List Nat := [3, 1, 2, 1, 3, 4, 1, 6]
def baseStart_138442 : Nat := 118140960795 + 138442 * 2 ^ 59
def prefixEnd_138442 : Nat := 4983230072969 + 3 ^ 40 * 138442 * 2
def baseEnd_138442 : Nat := 10531450188126307961233

theorem tailTrace_138442 : CollatzResearch.WordTrace tailWord_138442 prefixEnd_138442 10531450188126307961233 := by
  unfold tailWord_138442
  simp only [CollatzResearch.WordTrace]
  refine ⟨1262348641113938214078395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3366263042970501904209053 1262348641113938214078395)
  ·
    refine ⟨1893522961670907321117593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1262348641113938214078395 1893522961670907321117593)
    ·
      refine ⟨1420142221253180490838195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1893522961670907321117593 1420142221253180490838195)
      ·
        refine ⟨2130213331879770736257293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1420142221253180490838195 2130213331879770736257293)
        ·
          refine ⟨798829999454914026096485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2130213331879770736257293 798829999454914026096485)
          ·
            refine ⟨149780624897796379893091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 798829999454914026096485 149780624897796379893091)
            ·
              refine ⟨224670937346694569839637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149780624897796379893091 224670937346694569839637)
              ·
                refine ⟨10531450188126307961233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 224670937346694569839637 10531450188126307961233)
                ·
                  rfl

theorem cell21_138442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 6].length) (baseStart_138442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138442 prefixEnd_138442 := by exact prefixLift 138442
  have htrace : WordTrace (prefixWord ++ tailWord_138442) baseStart_138442 baseEnd_138442 := by
    simpa [prefixWord, tailWord_138442, baseEnd_138442] using wordTrace_append hprefix tailTrace_138442
  have hstable : (prefixWord ++ tailWord_138442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138442).length < 2 ^ (prefixWord ++ tailWord_138442).sum := by decide
  have hdescent : baseEnd_138442 < baseStart_138442 := by decide
  rcases family_descends (prefixWord ++ tailWord_138442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138549 : List Nat := [1, 3, 3, 1, 2, 4, 1, 1, 5]
def baseStart_138549 : Nat := 118140960795 + 138549 * 2 ^ 59
def prefixEnd_138549 : Nat := 4983230072969 + 3 ^ 40 * 138549 * 2
def baseEnd_138549 : Nat := 31618769422170515600147

theorem tailTrace_138549 : CollatzResearch.WordTrace tailWord_138549 prefixEnd_138549 31618769422170515600147 := by
  unfold tailWord_138549
  simp only [CollatzResearch.WordTrace]
  refine ⟨5053297175068110130458701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3368864783378740086972467 5053297175068110130458701)
  ·
    refine ⟨1894986440650541298922013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5053297175068110130458701 1894986440650541298922013)
    ·
      refine ⟨710619915243952987095755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1894986440650541298922013 710619915243952987095755)
      ·
        refine ⟨1065929872865929480643633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 710619915243952987095755 1065929872865929480643633)
        ·
          refine ⟨799447404649447110482725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1065929872865929480643633 799447404649447110482725)
          ·
            refine ⟨149896388371771333215511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 799447404649447110482725 149896388371771333215511)
            ·
              refine ⟨224844582557656999823267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149896388371771333215511 224844582557656999823267)
              ·
                refine ⟨337266873836485499734901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224844582557656999823267 337266873836485499734901)
                ·
                  refine ⟨31618769422170515600147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 337266873836485499734901 31618769422170515600147)
                  ·
                    rfl

theorem cell21_138549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 5].length) (baseStart_138549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138549 prefixEnd_138549 := by exact prefixLift 138549
  have htrace : WordTrace (prefixWord ++ tailWord_138549) baseStart_138549 baseEnd_138549 := by
    simpa [prefixWord, tailWord_138549, baseEnd_138549] using wordTrace_append hprefix tailTrace_138549
  have hstable : (prefixWord ++ tailWord_138549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138549).length < 2 ^ (prefixWord ++ tailWord_138549).sum := by decide
  have hdescent : baseEnd_138549 < baseStart_138549 := by decide
  rcases family_descends (prefixWord ++ tailWord_138549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138600 : List Nat := [2, 1, 4, 2, 4, 1, 2, 2, 3]
def baseStart_138600 : Nat := 118140960795 + 138600 * 2 ^ 59
def prefixEnd_138600 : Nat := 4983230072969 + 3 ^ 40 * 138600 * 2
def baseEnd_138600 : Nat := 31630408317005760250043

theorem tailTrace_138600 : CollatzResearch.WordTrace tailWord_138600 prefixEnd_138600 31630408317005760250043 := by
  unfold tailWord_138600
  simp only [CollatzResearch.WordTrace]
  refine ⟨2527578648941672920282627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3370104865255563893710169 2527578648941672920282627)
  ·
    refine ⟨3791367973412509380423941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2527578648941672920282627 3791367973412509380423941)
    ·
      refine ⟨710881495014845508829489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3791367973412509380423941 710881495014845508829489)
      ·
        refine ⟨533161121261134131622117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 710881495014845508829489 533161121261134131622117)
        ·
          refine ⟨99967710236462649679147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 533161121261134131622117 99967710236462649679147)
          ·
            refine ⟨149951565354693974518721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99967710236462649679147 149951565354693974518721)
            ·
              refine ⟨112463674016020480889041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 149951565354693974518721 112463674016020480889041)
              ·
                refine ⟨84347755512015360666781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112463674016020480889041 84347755512015360666781)
                ·
                  refine ⟨31630408317005760250043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84347755512015360666781 31630408317005760250043)
                  ·
                    rfl

theorem cell21_138600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 2, 3].length) (baseStart_138600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138600 prefixEnd_138600 := by exact prefixLift 138600
  have htrace : WordTrace (prefixWord ++ tailWord_138600) baseStart_138600 baseEnd_138600 := by
    simpa [prefixWord, tailWord_138600, baseEnd_138600] using wordTrace_append hprefix tailTrace_138600
  have hstable : (prefixWord ++ tailWord_138600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138600).length < 2 ^ (prefixWord ++ tailWord_138600).sum := by decide
  have hdescent : baseEnd_138600 < baseStart_138600 := by decide
  rcases family_descends (prefixWord ++ tailWord_138600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138625 : List Nat := [1, 2, 4, 3, 2, 1, 1, 2, 5]
def baseStart_138625 : Nat := 118140960795 + 138625 * 2 ^ 59
def prefixEnd_138625 : Nat := 4983230072969 + 3 ^ 40 * 138625 * 2
def baseEnd_138625 : Nat := 31636113657611272333325

theorem tailTrace_138625 : CollatzResearch.WordTrace tailWord_138625 prefixEnd_138625 31636113657611272333325 := by
  unfold tailWord_138625
  simp only [CollatzResearch.WordTrace]
  refine ⟨5056069122792775110225329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3370712748528516740150219 5056069122792775110225329)
  ·
    refine ⟨3792051842094581332668997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5056069122792775110225329 3792051842094581332668997)
    ·
      refine ⟨711009720392733999875437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3792051842094581332668997 711009720392733999875437)
      ·
        refine ⟨266628645147275249953289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 711009720392733999875437 266628645147275249953289)
        ·
          refine ⟨199971483860456437464967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 266628645147275249953289 199971483860456437464967)
          ·
            refine ⟨299957225790684656197451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199971483860456437464967 299957225790684656197451)
            ·
              refine ⟨449935838686026984296177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299957225790684656197451 449935838686026984296177)
              ·
                refine ⟨337451879014520238222133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 449935838686026984296177 337451879014520238222133)
                ·
                  refine ⟨31636113657611272333325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 337451879014520238222133 31636113657611272333325)
                  ·
                    rfl

theorem cell21_138625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 5].length) (baseStart_138625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138625 prefixEnd_138625 := by exact prefixLift 138625
  have htrace : WordTrace (prefixWord ++ tailWord_138625) baseStart_138625 baseEnd_138625 := by
    simpa [prefixWord, tailWord_138625, baseEnd_138625] using wordTrace_append hprefix tailTrace_138625
  have hstable : (prefixWord ++ tailWord_138625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138625).length < 2 ^ (prefixWord ++ tailWord_138625).sum := by decide
  have hdescent : baseEnd_138625 < baseStart_138625 := by decide
  rcases family_descends (prefixWord ++ tailWord_138625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138653 : List Nat := [1, 4, 2, 1, 3, 2, 8]
def baseStart_138653 : Nat := 118140960795 + 138653 * 2 ^ 59
def prefixEnd_138653 : Nat := 4983230072969 + 3 ^ 40 * 138653 * 2
def baseEnd_138653 : Nat := 3515833737676605096289

theorem tailTrace_138653 : CollatzResearch.WordTrace tailWord_138653 prefixEnd_138653 3515833737676605096289 := by
  unfold tailWord_138653
  simp only [CollatzResearch.WordTrace]
  refine ⟨5057090366691335892244613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3371393577794223928163075 5057090366691335892244613)
  ·
    refine ⟨948204443754625479795865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5057090366691335892244613 948204443754625479795865)
    ·
      refine ⟨711153332815969109846899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 948204443754625479795865 711153332815969109846899)
      ·
        refine ⟨1066729999223953664770349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 711153332815969109846899 1066729999223953664770349)
        ·
          refine ⟨400023749708982624288881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1066729999223953664770349 400023749708982624288881)
          ·
            refine ⟨300017812281736968216661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 400023749708982624288881 300017812281736968216661)
            ·
              refine ⟨3515833737676605096289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 300017812281736968216661 3515833737676605096289)
              ·
                rfl

theorem cell21_138653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 8].length) (baseStart_138653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138653 prefixEnd_138653 := by exact prefixLift 138653
  have htrace : WordTrace (prefixWord ++ tailWord_138653) baseStart_138653 baseEnd_138653 := by
    simpa [prefixWord, tailWord_138653, baseEnd_138653] using wordTrace_append hprefix tailTrace_138653
  have hstable : (prefixWord ++ tailWord_138653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138653).length < 2 ^ (prefixWord ++ tailWord_138653).sum := by decide
  have hdescent : baseEnd_138653 < baseStart_138653 := by decide
  rcases family_descends (prefixWord ++ tailWord_138653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138698 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 6]
def baseStart_138698 : Nat := 118140960795 + 138698 * 2 ^ 59
def prefixEnd_138698 : Nat := 4983230072969 + 3 ^ 40 * 138698 * 2
def baseEnd_138698 : Nat := 31652773252179367616509

theorem tailTrace_138698 : CollatzResearch.WordTrace tailWord_138698 prefixEnd_138698 31652773252179367616509 := by
  unfold tailWord_138698
  simp only [CollatzResearch.WordTrace]
  refine ⟨1264682912882077144408187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3372487767685539051755165 1264682912882077144408187)
  ·
    refine ⟨1897024369323115716612281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1264682912882077144408187 1897024369323115716612281)
    ·
      refine ⟨1422768276992336787459211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1897024369323115716612281 1422768276992336787459211)
      ·
        refine ⟨2134152415488505181188817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1422768276992336787459211 2134152415488505181188817)
        ·
          refine ⟨1600614311616378885891613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2134152415488505181188817 1600614311616378885891613)
          ·
            refine ⟨600230366856142082209355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1600614311616378885891613 600230366856142082209355)
            ·
              refine ⟨900345550284213123314033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 600230366856142082209355 900345550284213123314033)
              ·
                refine ⟨675259162713159842485525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 900345550284213123314033 675259162713159842485525)
                ·
                  refine ⟨31652773252179367616509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 675259162713159842485525 31652773252179367616509)
                  ·
                    rfl

theorem cell21_138698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_138698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138698 prefixEnd_138698 := by exact prefixLift 138698
  have htrace : WordTrace (prefixWord ++ tailWord_138698) baseStart_138698 baseEnd_138698 := by
    simpa [prefixWord, tailWord_138698, baseEnd_138698] using wordTrace_append hprefix tailTrace_138698
  have hstable : (prefixWord ++ tailWord_138698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138698).length < 2 ^ (prefixWord ++ tailWord_138698).sum := by decide
  have hdescent : baseEnd_138698 < baseStart_138698 := by decide
  rcases family_descends (prefixWord ++ tailWord_138698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138712 : List Nat := [2, 1, 2, 2, 2, 1, 11]
def baseStart_138712 : Nat := 118140960795 + 138712 * 2 ^ 59
def prefixEnd_138712 : Nat := 4983230072969 + 3 ^ 40 * 138712 * 2
def baseEnd_138712 : Nat := 3517329804768717153683

theorem tailTrace_138712 : CollatzResearch.WordTrace tailWord_138712 prefixEnd_138712 3517329804768717153683 := by
  unfold tailWord_138712
  simp only [CollatzResearch.WordTrace]
  refine ⟨2529621136738794484321195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3372828182318392645761593 2529621136738794484321195)
  ·
    refine ⟨3794431705108191726481793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2529621136738794484321195 3794431705108191726481793)
    ·
      refine ⟨2845823778831143794861345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3794431705108191726481793 2845823778831143794861345)
      ·
        refine ⟨2134367834123357846146009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2845823778831143794861345 2134367834123357846146009)
        ·
          refine ⟨1600775875592518384609507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2134367834123357846146009 1600775875592518384609507)
          ·
            refine ⟨2401163813388777576914261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1600775875592518384609507 2401163813388777576914261)
            ·
              refine ⟨3517329804768717153683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 2401163813388777576914261 3517329804768717153683)
              ·
                rfl

theorem cell21_138712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 11].length) (baseStart_138712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138712 prefixEnd_138712 := by exact prefixLift 138712
  have htrace : WordTrace (prefixWord ++ tailWord_138712) baseStart_138712 baseEnd_138712 := by
    simpa [prefixWord, tailWord_138712, baseEnd_138712] using wordTrace_append hprefix tailTrace_138712
  have hstable : (prefixWord ++ tailWord_138712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138712).length < 2 ^ (prefixWord ++ tailWord_138712).sum := by decide
  have hdescent : baseEnd_138712 < baseStart_138712 := by decide
  rcases family_descends (prefixWord ++ tailWord_138712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138836 : List Nat := [2, 4, 1, 1, 1, 2, 4, 1, 5]
def baseStart_138836 : Nat := 118140960795 + 138836 * 2 ^ 59
def prefixEnd_138836 : Nat := 4983230072969 + 3 ^ 40 * 138836 * 2
def baseEnd_138836 : Nat := 31684266732321794316227

theorem tailTrace_138836 : CollatzResearch.WordTrace tailWord_138836 prefixEnd_138836 31684266732321794316227 := by
  unfold tailWord_138836
  simp only [CollatzResearch.WordTrace]
  refine ⟨2531882462514179073078181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3375843283352238764104241 2531882462514179073078181)
  ·
    refine ⟨474727961721408576202159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2531882462514179073078181 474727961721408576202159)
    ·
      refine ⟨712091942582112864303239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 474727961721408576202159 712091942582112864303239)
      ·
        refine ⟨1068137913873169296454859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 712091942582112864303239 1068137913873169296454859)
        ·
          refine ⟨1602206870809753944682289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1068137913873169296454859 1602206870809753944682289)
          ·
            refine ⟨1201655153107315458511717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1602206870809753944682289 1201655153107315458511717)
            ·
              refine ⟨225310341207621648470947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1201655153107315458511717 225310341207621648470947)
              ·
                refine ⟨337965511811432472706421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225310341207621648470947 337965511811432472706421)
                ·
                  refine ⟨31684266732321794316227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 337965511811432472706421 31684266732321794316227)
                  ·
                    rfl

theorem cell21_138836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_138836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138836 prefixEnd_138836 := by exact prefixLift 138836
  have htrace : WordTrace (prefixWord ++ tailWord_138836) baseStart_138836 baseEnd_138836 := by
    simpa [prefixWord, tailWord_138836, baseEnd_138836] using wordTrace_append hprefix tailTrace_138836
  have hstable : (prefixWord ++ tailWord_138836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138836).length < 2 ^ (prefixWord ++ tailWord_138836).sum := by decide
  have hdescent : baseEnd_138836 < baseStart_138836 := by decide
  rcases family_descends (prefixWord ++ tailWord_138836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138870 : List Nat := [5, 1, 1, 2, 2, 1, 3, 3, 3]
def baseStart_138870 : Nat := 118140960795 + 138870 * 2 ^ 59
def prefixEnd_138870 : Nat := 4983230072969 + 3 ^ 40 * 138870 * 2
def baseEnd_138870 : Nat := 31692025995545290749491

theorem tailTrace_138870 : CollatzResearch.WordTrace tailWord_138870 prefixEnd_138870 31692025995545290749491 := by
  unfold tailWord_138870
  simp only [CollatzResearch.WordTrace]
  refine ⟨316562812931573872055879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3376670004603454635262709 316562812931573872055879)
  ·
    refine ⟨474844219397360808083819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 316562812931573872055879 474844219397360808083819)
    ·
      refine ⟨712266329096041212125729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 474844219397360808083819 712266329096041212125729)
      ·
        refine ⟨534199746822030909094297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 712266329096041212125729 534199746822030909094297)
        ·
          refine ⟨400649810116523181820723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 534199746822030909094297 400649810116523181820723)
          ·
            refine ⟨600974715174784772731085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400649810116523181820723 600974715174784772731085)
            ·
              refine ⟨225365518190544289774157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 600974715174784772731085 225365518190544289774157)
              ·
                refine ⟨84512069321454108665309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 225365518190544289774157 84512069321454108665309)
                ·
                  refine ⟨31692025995545290749491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84512069321454108665309 31692025995545290749491)
                  ·
                    rfl

theorem cell21_138870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 3, 3].length) (baseStart_138870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138870 prefixEnd_138870 := by exact prefixLift 138870
  have htrace : WordTrace (prefixWord ++ tailWord_138870) baseStart_138870 baseEnd_138870 := by
    simpa [prefixWord, tailWord_138870, baseEnd_138870] using wordTrace_append hprefix tailTrace_138870
  have hstable : (prefixWord ++ tailWord_138870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138870).length < 2 ^ (prefixWord ++ tailWord_138870).sum := by decide
  have hdescent : baseEnd_138870 < baseStart_138870 := by decide
  rcases family_descends (prefixWord ++ tailWord_138870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138881 : List Nat := [1, 2, 4, 2, 1, 4, 7]
def baseStart_138881 : Nat := 118140960795 + 138881 * 2 ^ 59
def prefixEnd_138881 : Nat := 4983230072969 + 3 ^ 40 * 138881 * 2
def baseEnd_138881 : Nat := 3521615149490190674015

theorem tailTrace_138881 : CollatzResearch.WordTrace tailWord_138881 prefixEnd_138881 3521615149490190674015 := by
  unfold tailWord_138881
  simp only [CollatzResearch.WordTrace]
  refine ⟨5065406209865330831544497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3376937473243553887696331 5065406209865330831544497)
  ·
    refine ⟨3799054657398998123658373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5065406209865330831544497 3799054657398998123658373)
    ·
      refine ⟨712322748262312148185945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3799054657398998123658373 712322748262312148185945)
      ·
        refine ⟨534242061196734111139459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 712322748262312148185945 534242061196734111139459)
        ·
          refine ⟨801363091795101166709189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534242061196734111139459 801363091795101166709189)
          ·
            refine ⟨150255579711581468757973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 801363091795101166709189 150255579711581468757973)
            ·
              refine ⟨3521615149490190674015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 150255579711581468757973 3521615149490190674015)
              ·
                rfl

theorem cell21_138881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 4, 7].length) (baseStart_138881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138881 prefixEnd_138881 := by exact prefixLift 138881
  have htrace : WordTrace (prefixWord ++ tailWord_138881) baseStart_138881 baseEnd_138881 := by
    simpa [prefixWord, tailWord_138881, baseEnd_138881] using wordTrace_append hprefix tailTrace_138881
  have hstable : (prefixWord ++ tailWord_138881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138881).length < 2 ^ (prefixWord ++ tailWord_138881).sum := by decide
  have hdescent : baseEnd_138881 < baseStart_138881 := by decide
  rcases family_descends (prefixWord ++ tailWord_138881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138898 : List Nat := [3, 2, 3, 1, 3, 1, 2, 6]
def baseStart_138898 : Nat := 118140960795 + 138898 * 2 ^ 59
def prefixEnd_138898 : Nat := 4983230072969 + 3 ^ 40 * 138898 * 2
def baseEnd_138898 : Nat := 10566138659007821427589

theorem tailTrace_138898 : CollatzResearch.WordTrace tailWord_138898 prefixEnd_138898 10566138659007821427589 := by
  unfold tailWord_138898
  simp only [CollatzResearch.WordTrace]
  refine ⟨1266506562700935683728337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3377350833869161823275565 1266506562700935683728337)
  ·
    refine ⟨949879922025701762796253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1266506562700935683728337 949879922025701762796253)
    ·
      refine ⟨356204970759638161048595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 949879922025701762796253 356204970759638161048595)
      ·
        refine ⟨534307456139457241572893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 356204970759638161048595 534307456139457241572893)
        ·
          refine ⟨200365296052296465589835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 534307456139457241572893 200365296052296465589835)
          ·
            refine ⟨300547944078444698384753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200365296052296465589835 300547944078444698384753)
            ·
              refine ⟨225410958058833523788565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300547944078444698384753 225410958058833523788565)
              ·
                refine ⟨10566138659007821427589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 225410958058833523788565 10566138659007821427589)
                ·
                  rfl

theorem cell21_138898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_138898 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138898 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138898 prefixEnd_138898 := by exact prefixLift 138898
  have htrace : WordTrace (prefixWord ++ tailWord_138898) baseStart_138898 baseEnd_138898 := by
    simpa [prefixWord, tailWord_138898, baseEnd_138898] using wordTrace_append hprefix tailTrace_138898
  have hstable : (prefixWord ++ tailWord_138898).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138898).length < 2 ^ (prefixWord ++ tailWord_138898).sum := by decide
  have hdescent : baseEnd_138898 < baseStart_138898 := by decide
  rcases family_descends (prefixWord ++ tailWord_138898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138940 : List Nat := [2, 2, 2, 3, 1, 11]
def baseStart_138940 : Nat := 118140960795 + 138940 * 2 ^ 59
def prefixEnd_138940 : Nat := 4983230072969 + 3 ^ 40 * 138940 * 2
def baseEnd_138940 : Nat := 1174370405527434243803

theorem tailTrace_138940 : CollatzResearch.WordTrace tailWord_138940 prefixEnd_138940 1174370405527434243803 := by
  unfold tailWord_138940
  simp only [CollatzResearch.WordTrace]
  refine ⟨2533779058325791953971137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3378372077767722605294849 2533779058325791953971137)
  ·
    refine ⟨1900334293744343965478353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2533779058325791953971137 1900334293744343965478353)
    ·
      refine ⟨1425250720308257974108765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1900334293744343965478353 1425250720308257974108765)
      ·
        refine ⟨534469020115596740290787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1425250720308257974108765 534469020115596740290787)
        ·
          refine ⟨801703530173395110436181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 534469020115596740290787 801703530173395110436181)
          ·
            refine ⟨1174370405527434243803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 801703530173395110436181 1174370405527434243803)
            ·
              rfl

theorem cell21_138940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 11].length) (baseStart_138940 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138940 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138940 prefixEnd_138940 := by exact prefixLift 138940
  have htrace : WordTrace (prefixWord ++ tailWord_138940) baseStart_138940 baseEnd_138940 := by
    simpa [prefixWord, tailWord_138940, baseEnd_138940] using wordTrace_append hprefix tailTrace_138940
  have hstable : (prefixWord ++ tailWord_138940).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138940).length < 2 ^ (prefixWord ++ tailWord_138940).sum := by decide
  have hdescent : baseEnd_138940 < baseStart_138940 := by decide
  rcases family_descends (prefixWord ++ tailWord_138940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138985 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 6]
def baseStart_138985 : Nat := 118140960795 + 138985 * 2 ^ 59
def prefixEnd_138985 : Nat := 4983230072969 + 3 ^ 40 * 138985 * 2
def baseEnd_138985 : Nat := 31718270562330646332589

theorem tailTrace_138985 : CollatzResearch.WordTrace tailWord_138985 prefixEnd_138985 31718270562330646332589 := by
  unfold tailWord_138985
  simp only [CollatzResearch.WordTrace]
  refine ⟨5069199401488556593330409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3379466267659037728886939 5069199401488556593330409)
  ·
    refine ⟨3801899551116417444997807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5069199401488556593330409 3801899551116417444997807)
    ·
      refine ⟨5702849326674626167496711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3801899551116417444997807 5702849326674626167496711)
      ·
        refine ⟨8554273990011939251245067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5702849326674626167496711 8554273990011939251245067)
        ·
          refine ⟨12831410985017908876867601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8554273990011939251245067 12831410985017908876867601)
          ·
            refine ⟨9623558238763431657650701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12831410985017908876867601 9623558238763431657650701)
            ·
              refine ⟨3608834339536286871619013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9623558238763431657650701 3608834339536286871619013)
              ·
                refine ⟨676656438663053788428565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3608834339536286871619013 676656438663053788428565)
                ·
                  refine ⟨31718270562330646332589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 676656438663053788428565 31718270562330646332589)
                  ·
                    rfl

theorem cell21_138985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 6].length) (baseStart_138985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138985 prefixEnd_138985 := by exact prefixLift 138985
  have htrace : WordTrace (prefixWord ++ tailWord_138985) baseStart_138985 baseEnd_138985 := by
    simpa [prefixWord, tailWord_138985, baseEnd_138985] using wordTrace_append hprefix tailTrace_138985
  have hstable : (prefixWord ++ tailWord_138985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138985).length < 2 ^ (prefixWord ++ tailWord_138985).sum := by decide
  have hdescent : baseEnd_138985 < baseStart_138985 := by decide
  rcases family_descends (prefixWord ++ tailWord_138985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138988 : List Nat := [2, 2, 1, 1, 2, 2, 3, 5, 3]
def baseStart_138988 : Nat := 118140960795 + 138988 * 2 ^ 59
def prefixEnd_138988 : Nat := 4983230072969 + 3 ^ 40 * 138988 * 2
def baseEnd_138988 : Nat := 31718955203203307782583

theorem tailTrace_138988 : CollatzResearch.WordTrace tailWord_138988 prefixEnd_138988 31718955203203307782583 := by
  unfold tailWord_138988
  simp only [CollatzResearch.WordTrace]
  refine ⟨2534654410238844052844809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3379539213651792070459745 2534654410238844052844809)
  ·
    refine ⟨1900990807679133039633607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2534654410238844052844809 1900990807679133039633607)
    ·
      refine ⟨2851486211518699559450411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1900990807679133039633607 2851486211518699559450411)
      ·
        refine ⟨4277229317278049339175617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2851486211518699559450411 4277229317278049339175617)
        ·
          refine ⟨3207921987958537004381713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4277229317278049339175617 3207921987958537004381713)
          ·
            refine ⟨2405941490968902753286285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3207921987958537004381713 2405941490968902753286285)
            ·
              refine ⟨902228059113338532482357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2405941490968902753286285 902228059113338532482357)
              ·
                refine ⟨84583880541875487420221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 902228059113338532482357 84583880541875487420221)
                ·
                  refine ⟨31718955203203307782583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84583880541875487420221 31718955203203307782583)
                  ·
                    rfl

theorem cell21_138988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 3].length) (baseStart_138988 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_138988 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_138988 prefixEnd_138988 := by exact prefixLift 138988
  have htrace : WordTrace (prefixWord ++ tailWord_138988) baseStart_138988 baseEnd_138988 := by
    simpa [prefixWord, tailWord_138988, baseEnd_138988] using wordTrace_append hprefix tailTrace_138988
  have hstable : (prefixWord ++ tailWord_138988).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138988).length < 2 ^ (prefixWord ++ tailWord_138988).sum := by decide
  have hdescent : baseEnd_138988 < baseStart_138988 := by decide
  rcases family_descends (prefixWord ++ tailWord_138988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139016 : List Nat := [2, 1, 3, 2, 2, 1, 2, 8]
def baseStart_139016 : Nat := 118140960795 + 139016 * 2 ^ 59
def prefixEnd_139016 : Nat := 4983230072969 + 3 ^ 40 * 139016 * 2
def baseEnd_139016 : Nat := 10575115061560493771953

theorem tailTrace_139016 : CollatzResearch.WordTrace tailWord_139016 prefixEnd_139016 10575115061560493771953 := by
  unfold tailWord_139016
  simp only [CollatzResearch.WordTrace]
  refine ⟨2535165032188124443854451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3380220042917499258472601 2535165032188124443854451)
  ·
    refine ⟨3802747548282186665781677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2535165032188124443854451 3802747548282186665781677)
    ·
      refine ⟨1426030330605819999668129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3802747548282186665781677 1426030330605819999668129)
      ·
        refine ⟨1069522747954364999751097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1426030330605819999668129 1069522747954364999751097)
        ·
          refine ⟨802142060965773749813323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1069522747954364999751097 802142060965773749813323)
          ·
            refine ⟨1203213091448660624719985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 802142060965773749813323 1203213091448660624719985)
            ·
              refine ⟨902409818586495468539989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1203213091448660624719985 902409818586495468539989)
              ·
                refine ⟨10575115061560493771953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 902409818586495468539989 10575115061560493771953)
                ·
                  rfl

theorem cell21_139016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 8].length) (baseStart_139016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_139016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_139016 prefixEnd_139016 := by exact prefixLift 139016
  have htrace : WordTrace (prefixWord ++ tailWord_139016) baseStart_139016 baseEnd_139016 := by
    simpa [prefixWord, tailWord_139016, baseEnd_139016] using wordTrace_append hprefix tailTrace_139016
  have hstable : (prefixWord ++ tailWord_139016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139016).length < 2 ^ (prefixWord ++ tailWord_139016).sum := by decide
  have hdescent : baseEnd_139016 < baseStart_139016 := by decide
  rcases family_descends (prefixWord ++ tailWord_139016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139064 : List Nat := [2, 1, 2, 1, 3, 5, 1, 1, 5]
def baseStart_139064 : Nat := 118140960795 + 139064 * 2 ^ 59
def prefixEnd_139064 : Nat := 4983230072969 + 3 ^ 40 * 139064 * 2
def baseEnd_139064 : Nat := 31736299438644064515761

theorem tailTrace_139064 : CollatzResearch.WordTrace tailWord_139064 prefixEnd_139064 31736299438644064515761 := by
  unfold tailWord_139064
  simp only [CollatzResearch.WordTrace]
  refine ⟨2536040384101176542728123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3381387178801568723637497 2536040384101176542728123)
  ·
    refine ⟨3804060576151764814092185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2536040384101176542728123 3804060576151764814092185)
    ·
      refine ⟨2853045432113823610569139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3804060576151764814092185 2853045432113823610569139)
      ·
        refine ⟨4279568148170735415853709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2853045432113823610569139 4279568148170735415853709)
        ·
          refine ⟨1604838055564025780945141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4279568148170735415853709 1604838055564025780945141)
          ·
            refine ⟨150453567709127416963607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1604838055564025780945141 150453567709127416963607)
            ·
              refine ⟨225680351563691125445411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150453567709127416963607 225680351563691125445411)
              ·
                refine ⟨338520527345536688168117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225680351563691125445411 338520527345536688168117)
                ·
                  refine ⟨31736299438644064515761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 338520527345536688168117 31736299438644064515761)
                  ·
                    rfl

theorem cell21_139064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 1, 1, 5].length) (baseStart_139064 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_139064 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_139064 prefixEnd_139064 := by exact prefixLift 139064
  have htrace : WordTrace (prefixWord ++ tailWord_139064) baseStart_139064 baseEnd_139064 := by
    simpa [prefixWord, tailWord_139064, baseEnd_139064] using wordTrace_append hprefix tailTrace_139064
  have hstable : (prefixWord ++ tailWord_139064).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139064).length < 2 ^ (prefixWord ++ tailWord_139064).sum := by decide
  have hdescent : baseEnd_139064 < baseStart_139064 := by decide
  rcases family_descends (prefixWord ++ tailWord_139064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139216 : List Nat := [2, 1, 1, 1, 1, 2, 7, 3, 3]
def baseStart_139216 : Nat := 118140960795 + 139216 * 2 ^ 59
def prefixEnd_139216 : Nat := 4983230072969 + 3 ^ 40 * 139216 * 2
def baseEnd_139216 : Nat := 31770987909525577982117

theorem tailTrace_139216 : CollatzResearch.WordTrace tailWord_139216 prefixEnd_139216 31770987909525577982117 := by
  unfold tailWord_139216
  simp only [CollatzResearch.WordTrace]
  refine ⟨2538812331825841522494751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3385083109101122029993001 2538812331825841522494751)
  ·
    refine ⟨3808218497738762283742127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2538812331825841522494751 3808218497738762283742127)
    ·
      refine ⟨5712327746608143425613191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3808218497738762283742127 5712327746608143425613191)
      ·
        refine ⟨8568491619912215138419787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5712327746608143425613191 8568491619912215138419787)
        ·
          refine ⟨12852737429868322707629681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8568491619912215138419787 12852737429868322707629681)
          ·
            refine ⟨9639553072401242030722261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12852737429868322707629681 9639553072401242030722261)
            ·
              refine ⟨225927025134404110095053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 9639553072401242030722261 225927025134404110095053)
              ·
                refine ⟨84722634425401541285645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 225927025134404110095053 84722634425401541285645)
                ·
                  refine ⟨31770987909525577982117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84722634425401541285645 31770987909525577982117)
                  ·
                    rfl

theorem cell21_139216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 3, 3].length) (baseStart_139216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_139216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_139216 prefixEnd_139216 := by exact prefixLift 139216
  have htrace : WordTrace (prefixWord ++ tailWord_139216) baseStart_139216 baseEnd_139216 := by
    simpa [prefixWord, tailWord_139216, baseEnd_139216] using wordTrace_append hprefix tailTrace_139216
  have hstable : (prefixWord ++ tailWord_139216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139216).length < 2 ^ (prefixWord ++ tailWord_139216).sum := by decide
  have hdescent : baseEnd_139216 < baseStart_139216 := by decide
  rcases family_descends (prefixWord ++ tailWord_139216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139284 : List Nat := [2, 4, 3, 2, 1, 2, 2, 2, 3]
def baseStart_139284 : Nat := 118140960795 + 139284 * 2 ^ 59
def prefixEnd_139284 : Nat := 4983230072969 + 3 ^ 40 * 139284 * 2
def baseEnd_139284 : Nat := 31786506435972570848645

theorem tailTrace_139284 : CollatzResearch.WordTrace tailWord_139284 prefixEnd_139284 31786506435972570848645 := by
  unfold tailWord_139284
  simp only [CollatzResearch.WordTrace]
  refine ⟨2540052413702665329232453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3386736551603553772309937 2540052413702665329232453)
  ·
    refine ⟨476259827569249749231085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2540052413702665329232453 476259827569249749231085)
    ·
      refine ⟨178597435338468655961657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 476259827569249749231085 178597435338468655961657)
      ·
        refine ⟨133948076503851491971243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 178597435338468655961657 133948076503851491971243)
        ·
          refine ⟨200922114755777237956865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133948076503851491971243 200922114755777237956865)
          ·
            refine ⟨150691586066832928467649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200922114755777237956865 150691586066832928467649)
            ·
              refine ⟨113018689550124696350737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150691586066832928467649 113018689550124696350737)
              ·
                refine ⟨84764017162593522263053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113018689550124696350737 84764017162593522263053)
                ·
                  refine ⟨31786506435972570848645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84764017162593522263053 31786506435972570848645)
                  ·
                    rfl

theorem cell21_139284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 2, 3].length) (baseStart_139284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_139284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_139284 prefixEnd_139284 := by exact prefixLift 139284
  have htrace : WordTrace (prefixWord ++ tailWord_139284) baseStart_139284 baseEnd_139284 := by
    simpa [prefixWord, tailWord_139284, baseEnd_139284] using wordTrace_append hprefix tailTrace_139284
  have hstable : (prefixWord ++ tailWord_139284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139284).length < 2 ^ (prefixWord ++ tailWord_139284).sum := by decide
  have hdescent : baseEnd_139284 < baseStart_139284 := by decide
  rcases family_descends (prefixWord ++ tailWord_139284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139326 : List Nat := [4, 2, 1, 3, 2, 1, 2, 3, 3]
def baseStart_139326 : Nat := 118140960795 + 139326 * 2 ^ 59
def prefixEnd_139326 : Nat := 4983230072969 + 3 ^ 40 * 139326 * 2
def baseEnd_139326 : Nat := 31796091408189831148559

theorem tailTrace_139326 : CollatzResearch.WordTrace tailWord_139326 prefixEnd_139326 31796091408189831148559 := by
  unfold tailWord_139326
  simp only [CollatzResearch.WordTrace]
  refine ⟨635204586656646478936729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3387757795502114554329221 635204586656646478936729)
  ·
    refine ⟨476403439992484859202547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 635204586656646478936729 476403439992484859202547)
    ·
      refine ⟨714605159988727288803821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 476403439992484859202547 714605159988727288803821)
      ·
        refine ⟨267976934995772733301433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 714605159988727288803821 267976934995772733301433)
        ·
          refine ⟨200982701246829549976075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267976934995772733301433 200982701246829549976075)
          ·
            refine ⟨301474051870244324964113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200982701246829549976075 301474051870244324964113)
            ·
              refine ⟨226105538902683243723085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 301474051870244324964113 226105538902683243723085)
              ·
                refine ⟨84789577088506216396157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 226105538902683243723085 84789577088506216396157)
                ·
                  refine ⟨31796091408189831148559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84789577088506216396157 31796091408189831148559)
                  ·
                    rfl

theorem cell21_139326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 2, 1, 2, 3, 3].length) (baseStart_139326 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_139326 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_139326 prefixEnd_139326 := by exact prefixLift 139326
  have htrace : WordTrace (prefixWord ++ tailWord_139326) baseStart_139326 baseEnd_139326 := by
    simpa [prefixWord, tailWord_139326, baseEnd_139326] using wordTrace_append hprefix tailTrace_139326
  have hstable : (prefixWord ++ tailWord_139326).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139326).length < 2 ^ (prefixWord ++ tailWord_139326).sum := by decide
  have hdescent : baseEnd_139326 < baseStart_139326 := by decide
  rcases family_descends (prefixWord ++ tailWord_139326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139382 : List Nat := [5, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_139382 : Nat := 118140960795 + 139382 * 2 ^ 59
def prefixEnd_139382 : Nat := 4983230072969 + 3 ^ 40 * 139382 * 2
def baseEnd_139382 : Nat := 31808871371146178215111

theorem tailTrace_139382 : CollatzResearch.WordTrace tailWord_139382 prefixEnd_139382 31808871371146178215111 := by
  unfold tailWord_139382
  simp only [CollatzResearch.WordTrace]
  refine ⟨317729948815643337220775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3389119454033528930354933 317729948815643337220775)
  ·
    refine ⟨476594923223465005831163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 317729948815643337220775 476594923223465005831163)
    ·
      refine ⟨714892384835197508746745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 476594923223465005831163 714892384835197508746745)
      ·
        refine ⟨536169288626398131560059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 714892384835197508746745 536169288626398131560059)
        ·
          refine ⟨804253932939597197340089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536169288626398131560059 804253932939597197340089)
          ·
            refine ⟨603190449704697898005067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 804253932939597197340089 603190449704697898005067)
            ·
              refine ⟨904785674557046847007601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 603190449704697898005067 904785674557046847007601)
              ·
                refine ⟨678589255917785135255701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 904785674557046847007601 678589255917785135255701)
                ·
                  refine ⟨31808871371146178215111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 678589255917785135255701 31808871371146178215111)
                  ·
                    rfl

theorem cell21_139382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_139382 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_139382 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_139382 prefixEnd_139382 := by exact prefixLift 139382
  have htrace : WordTrace (prefixWord ++ tailWord_139382) baseStart_139382 baseEnd_139382 := by
    simpa [prefixWord, tailWord_139382, baseEnd_139382] using wordTrace_append hprefix tailTrace_139382
  have hstable : (prefixWord ++ tailWord_139382).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139382).length < 2 ^ (prefixWord ++ tailWord_139382).sum := by decide
  have hdescent : baseEnd_139382 < baseStart_139382 := by decide
  rcases family_descends (prefixWord ++ tailWord_139382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139385 : List Nat := [1, 2, 1, 3, 4, 3, 1, 3, 3]
def baseStart_139385 : Nat := 118140960795 + 139385 * 2 ^ 59
def prefixEnd_139385 : Nat := 4983230072969 + 3 ^ 40 * 139385 * 2
def baseEnd_139385 : Nat := 31809556012018839665105

theorem tailTrace_139385 : CollatzResearch.WordTrace tailWord_139385 prefixEnd_139385 31809556012018839665105 := by
  unfold tailWord_139385
  simp only [CollatzResearch.WordTrace]
  refine ⟨5083788600039424907891609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3389192400026283271927739 5083788600039424907891609)
  ·
    refine ⟨3812841450029568680918707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5083788600039424907891609 3812841450029568680918707)
    ·
      refine ⟨5719262175044353021378061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3812841450029568680918707 5719262175044353021378061)
      ·
        refine ⟨2144723315641632383016773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5719262175044353021378061 2144723315641632383016773)
        ·
          refine ⟨402135621682806071815645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2144723315641632383016773 402135621682806071815645)
          ·
            refine ⟨150800858131052276930867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 402135621682806071815645 150800858131052276930867)
            ·
              refine ⟨226201287196578415396301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150800858131052276930867 226201287196578415396301)
              ·
                refine ⟨84825482698716905773613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 226201287196578415396301 84825482698716905773613)
                ·
                  refine ⟨31809556012018839665105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 84825482698716905773613 31809556012018839665105)
                  ·
                    rfl

theorem cell21_139385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 3, 3].length) (baseStart_139385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_139385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_139385 prefixEnd_139385 := by exact prefixLift 139385
  have htrace : WordTrace (prefixWord ++ tailWord_139385) baseStart_139385 baseEnd_139385 := by
    simpa [prefixWord, tailWord_139385, baseEnd_139385] using wordTrace_append hprefix tailTrace_139385
  have hstable : (prefixWord ++ tailWord_139385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139385).length < 2 ^ (prefixWord ++ tailWord_139385).sum := by decide
  have hdescent : baseEnd_139385 < baseStart_139385 := by decide
  rcases family_descends (prefixWord ++ tailWord_139385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139416 : List Nat := [2, 1, 2, 4, 3, 2, 2, 1, 4]
def baseStart_139416 : Nat := 118140960795 + 139416 * 2 ^ 59
def prefixEnd_139416 : Nat := 4983230072969 + 3 ^ 40 * 139416 * 2
def baseEnd_139416 : Nat := 31816630634369674648375

theorem tailTrace_139416 : CollatzResearch.WordTrace tailWord_139416 prefixEnd_139416 31816630634369674648375 := by
  unfold tailWord_139416
  simp only [CollatzResearch.WordTrace]
  refine ⟨2542459631463558601135051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3389946175284744801513401 2542459631463558601135051)
  ·
    refine ⟨3813689447195337901702577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2542459631463558601135051 3813689447195337901702577)
    ·
      refine ⟨2860267085396503426276933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3813689447195337901702577 2860267085396503426276933)
      ·
        refine ⟨536300078511844392426925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2860267085396503426276933 536300078511844392426925)
        ·
          refine ⟨201112529441941647160097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 536300078511844392426925 201112529441941647160097)
          ·
            refine ⟨150834397081456235370073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201112529441941647160097 150834397081456235370073)
            ·
              refine ⟨113125797811092176527555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150834397081456235370073 113125797811092176527555)
              ·
                refine ⟨169688696716638264791333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113125797811092176527555 169688696716638264791333)
                ·
                  refine ⟨31816630634369674648375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 169688696716638264791333 31816630634369674648375)
                  ·
                    rfl

theorem cell21_139416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 2, 2, 1, 4].length) (baseStart_139416 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_139416 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_139416 prefixEnd_139416 := by exact prefixLift 139416
  have htrace : WordTrace (prefixWord ++ tailWord_139416) baseStart_139416 baseEnd_139416 := by
    simpa [prefixWord, tailWord_139416, baseEnd_139416] using wordTrace_append hprefix tailTrace_139416
  have hstable : (prefixWord ++ tailWord_139416).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139416).length < 2 ^ (prefixWord ++ tailWord_139416).sum := by decide
  have hdescent : baseEnd_139416 < baseStart_139416 := by decide
  rcases family_descends (prefixWord ++ tailWord_139416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139531 : List Nat := [1, 1, 1, 1, 5, 2, 2, 8]
def baseStart_139531 : Nat := 118140960795 + 139531 * 2 ^ 59
def prefixEnd_139531 : Nat := 4983230072969 + 3 ^ 40 * 139531 * 2
def baseEnd_139531 : Nat := 10614291733718343410491

theorem tailTrace_139531 : CollatzResearch.WordTrace tailWord_139531 prefixEnd_139531 10614291733718343410491 := by
  unfold tailWord_139531
  simp only [CollatzResearch.WordTrace]
  refine ⟨5089113657510491842706447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3392742438340327895137631 5089113657510491842706447)
  ·
    refine ⟨7633670486265737764059671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5089113657510491842706447 7633670486265737764059671)
    ·
      refine ⟨11450505729398606646089507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7633670486265737764059671 11450505729398606646089507)
      ·
        refine ⟨17175758594097909969134261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11450505729398606646089507 17175758594097909969134261)
        ·
          refine ⟨1610227368196679059606337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17175758594097909969134261 1610227368196679059606337)
          ·
            refine ⟨1207670526147509294704753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1610227368196679059606337 1207670526147509294704753)
            ·
              refine ⟨905752894610631971028565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1207670526147509294704753 905752894610631971028565)
              ·
                refine ⟨10614291733718343410491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 905752894610631971028565 10614291733718343410491)
                ·
                  rfl

theorem cell21_139531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 8].length) (baseStart_139531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_139531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_139531 prefixEnd_139531 := by exact prefixLift 139531
  have htrace : WordTrace (prefixWord ++ tailWord_139531) baseStart_139531 baseEnd_139531 := by
    simpa [prefixWord, tailWord_139531, baseEnd_139531] using wordTrace_append hprefix tailTrace_139531
  have hstable : (prefixWord ++ tailWord_139531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139531).length < 2 ^ (prefixWord ++ tailWord_139531).sum := by decide
  have hdescent : baseEnd_139531 < baseStart_139531 := by decide
  rcases family_descends (prefixWord ++ tailWord_139531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139585 : List Nat := [1, 2, 5, 2, 3, 1, 2, 1, 4]
def baseStart_139585 : Nat := 118140960795 + 139585 * 2 ^ 59
def prefixEnd_139585 : Nat := 4983230072969 + 3 ^ 40 * 139585 * 2
def baseEnd_139585 : Nat := 31855198736862936331363

theorem tailTrace_139585 : CollatzResearch.WordTrace tailWord_139585 prefixEnd_139585 31855198736862936331363 := by
  unfold tailWord_139585
  simp only [CollatzResearch.WordTrace]
  refine ⟨5091083199314859065172209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3394055466209906043448139 5091083199314859065172209)
  ·
    refine ⟨3818312399486144298879157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5091083199314859065172209 3818312399486144298879157)
    ·
      refine ⟨357966787451826028019921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3818312399486144298879157 357966787451826028019921)
      ·
        refine ⟨268475090588869521014941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 357966787451826028019921 268475090588869521014941)
        ·
          refine ⟨100678158970826070380603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 268475090588869521014941 100678158970826070380603)
          ·
            refine ⟨151017238456239105570905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100678158970826070380603 151017238456239105570905)
            ·
              refine ⟨113262928842179329178179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151017238456239105570905 113262928842179329178179)
              ·
                refine ⟨169894393263268993767269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113262928842179329178179 169894393263268993767269)
                ·
                  refine ⟨31855198736862936331363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 169894393263268993767269 31855198736862936331363)
                  ·
                    rfl

theorem cell21_139585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 1, 4].length) (baseStart_139585 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_139585 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_139585 prefixEnd_139585 := by exact prefixLift 139585
  have htrace : WordTrace (prefixWord ++ tailWord_139585) baseStart_139585 baseEnd_139585 := by
    simpa [prefixWord, tailWord_139585, baseEnd_139585] using wordTrace_append hprefix tailTrace_139585
  have hstable : (prefixWord ++ tailWord_139585).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139585).length < 2 ^ (prefixWord ++ tailWord_139585).sum := by decide
  have hdescent : baseEnd_139585 < baseStart_139585 := by decide
  rcases family_descends (prefixWord ++ tailWord_139585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139607 : List Nat := [1, 1, 3, 2, 3, 1, 1, 9]
def baseStart_139607 : Nat := 118140960795 + 139607 * 2 ^ 59
def prefixEnd_139607 : Nat := 4983230072969 + 3 ^ 40 * 139607 * 2
def baseEnd_139607 : Nat := 10620073145531928988217

theorem tailTrace_139607 : CollatzResearch.WordTrace tailWord_139607 prefixEnd_139607 10620073145531928988217 := by
  unfold tailWord_139607
  simp only [CollatzResearch.WordTrace]
  refine ⟨5091885605235156822473075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3394590403490104548315383 5091885605235156822473075)
  ·
    refine ⟨7637828407852735233709613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5091885605235156822473075 7637828407852735233709613)
    ·
      refine ⟨2864185652944775712641105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7637828407852735233709613 2864185652944775712641105)
      ·
        refine ⟨2148139239708581784480829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2864185652944775712641105 2148139239708581784480829)
        ·
          refine ⟨805552214890718169180311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2148139239708581784480829 805552214890718169180311)
          ·
            refine ⟨1208328322336077253770467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 805552214890718169180311 1208328322336077253770467)
            ·
              refine ⟨1812492483504115880655701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1208328322336077253770467 1812492483504115880655701)
              ·
                refine ⟨10620073145531928988217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1812492483504115880655701 10620073145531928988217)
                ·
                  rfl

theorem cell21_139607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 9].length) (baseStart_139607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_139607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_139607 prefixEnd_139607 := by exact prefixLift 139607
  have htrace : WordTrace (prefixWord ++ tailWord_139607) baseStart_139607 baseEnd_139607 := by
    simpa [prefixWord, tailWord_139607, baseEnd_139607] using wordTrace_append hprefix tailTrace_139607
  have hstable : (prefixWord ++ tailWord_139607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139607).length < 2 ^ (prefixWord ++ tailWord_139607).sum := by decide
  have hdescent : baseEnd_139607 < baseStart_139607 := by decide
  rcases family_descends (prefixWord ++ tailWord_139607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139658 : List Nat := [3, 1, 2, 5, 1, 1, 3, 5]
def baseStart_139658 : Nat := 118140960795 + 139658 * 2 ^ 59
def prefixEnd_139658 : Nat := 4983230072969 + 3 ^ 40 * 139658 * 2
def baseEnd_139658 : Nat := 10623952777143677204849

theorem tailTrace_139658 : CollatzResearch.WordTrace tailWord_139658 prefixEnd_139658 10623952777143677204849 := by
  unfold tailWord_139658
  simp only [CollatzResearch.WordTrace]
  refine ⟨1273436432012598133144907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3395830485366928355053085 1273436432012598133144907)
  ·
    refine ⟨1910154648018897199717361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1273436432012598133144907 1910154648018897199717361)
    ·
      refine ⟨1432615986014172899788021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1910154648018897199717361 1432615986014172899788021)
      ·
        refine ⟨134307748688828709355127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1432615986014172899788021 134307748688828709355127)
        ·
          refine ⟨201461623033243064032691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134307748688828709355127 201461623033243064032691)
          ·
            refine ⟨302192434549864596049037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201461623033243064032691 302192434549864596049037)
            ·
              refine ⟨113322162956199223518389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 302192434549864596049037 113322162956199223518389)
              ·
                refine ⟨10623952777143677204849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 113322162956199223518389 10623952777143677204849)
                ·
                  rfl

theorem cell21_139658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_139658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_139658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_139658 prefixEnd_139658 := by exact prefixLift 139658
  have htrace : WordTrace (prefixWord ++ tailWord_139658) baseStart_139658 baseEnd_139658 := by
    simpa [prefixWord, tailWord_139658, baseEnd_139658] using wordTrace_append hprefix tailTrace_139658
  have hstable : (prefixWord ++ tailWord_139658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139658).length < 2 ^ (prefixWord ++ tailWord_139658).sum := by decide
  have hdescent : baseEnd_139658 < baseStart_139658 := by decide
  rcases family_descends (prefixWord ++ tailWord_139658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139672 : List Nat := [2, 1, 2, 5, 1, 1, 1, 5, 3]
def baseStart_139672 : Nat := 118140960795 + 139672 * 2 ^ 59
def prefixEnd_139672 : Nat := 4983230072969 + 3 ^ 40 * 139672 * 2
def baseEnd_139672 : Nat := 31875053322170118381185

theorem tailTrace_139672 : CollatzResearch.WordTrace tailWord_139672 prefixEnd_139672 31875053322170118381185 := by
  unfold tailWord_139672
  simp only [CollatzResearch.WordTrace]
  refine ⟨2547128174999836461794635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3396170899999781949059513 2547128174999836461794635)
  ·
    refine ⟨3820692262499754692691953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2547128174999836461794635 3820692262499754692691953)
    ·
      refine ⟨2865519196874816019518965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3820692262499754692691953 2865519196874816019518965)
      ·
        refine ⟨268642424707014001829903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2865519196874816019518965 268642424707014001829903)
        ·
          refine ⟨402963637060521002744855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268642424707014001829903 402963637060521002744855)
          ·
            refine ⟨604445455590781504117283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402963637060521002744855 604445455590781504117283)
            ·
              refine ⟨906668183386172256175925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 604445455590781504117283 906668183386172256175925)
              ·
                refine ⟨85000142192453649016493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 906668183386172256175925 85000142192453649016493)
                ·
                  refine ⟨31875053322170118381185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85000142192453649016493 31875053322170118381185)
                  ·
                    rfl

theorem cell21_139672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 3].length) (baseStart_139672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_139672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_139672 prefixEnd_139672 := by exact prefixLift 139672
  have htrace : WordTrace (prefixWord ++ tailWord_139672) baseStart_139672 baseEnd_139672 := by
    simpa [prefixWord, tailWord_139672, baseEnd_139672] using wordTrace_append hprefix tailTrace_139672
  have hstable : (prefixWord ++ tailWord_139672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139672).length < 2 ^ (prefixWord ++ tailWord_139672).sum := by decide
  have hdescent : baseEnd_139672 < baseStart_139672 := by decide
  rcases family_descends (prefixWord ++ tailWord_139672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139683 : List Nat := [1, 1, 1, 4, 1, 5, 8]
def baseStart_139683 : Nat := 118140960795 + 139683 * 2 ^ 59
def prefixEnd_139683 : Nat := 4983230072969 + 3 ^ 40 * 139683 * 2
def baseEnd_139683 : Nat := 3541951519115171521981

theorem tailTrace_139683 : CollatzResearch.WordTrace tailWord_139683 prefixEnd_139683 3541951519115171521981 := by
  unfold tailWord_139683
  simp only [CollatzResearch.WordTrace]
  refine ⟨5094657552959821802239703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3396438368639881201493135 5094657552959821802239703)
  ·
    refine ⟨7641986329439732703359555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5094657552959821802239703 7641986329439732703359555)
    ·
      refine ⟨11462979494159599055039333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7641986329439732703359555 11462979494159599055039333)
      ·
        refine ⟨2149308655154924822819875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11462979494159599055039333 2149308655154924822819875)
        ·
          refine ⟨3223962982732387234229813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2149308655154924822819875 3223962982732387234229813)
          ·
            refine ⟨302246529631161303209045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3223962982732387234229813 302246529631161303209045)
            ·
              refine ⟨3541951519115171521981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 302246529631161303209045 3541951519115171521981)
              ·
                rfl

theorem cell21_139683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 5, 8].length) (baseStart_139683 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_139683 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_139683 prefixEnd_139683 := by exact prefixLift 139683
  have htrace : WordTrace (prefixWord ++ tailWord_139683) baseStart_139683 baseEnd_139683 := by
    simpa [prefixWord, tailWord_139683, baseEnd_139683] using wordTrace_append hprefix tailTrace_139683
  have hstable : (prefixWord ++ tailWord_139683).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139683).length < 2 ^ (prefixWord ++ tailWord_139683).sum := by decide
  have hdescent : baseEnd_139683 < baseStart_139683 := by decide
  rcases family_descends (prefixWord ++ tailWord_139683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139745 : List Nat := [1, 2, 3, 1, 2, 2, 2, 4, 4]
def baseStart_139745 : Nat := 118140960795 + 139745 * 2 ^ 59
def prefixEnd_139745 : Nat := 4983230072969 + 3 ^ 40 * 139745 * 2
def baseEnd_139745 : Nat := 31891712916738213664369

theorem tailTrace_139745 : CollatzResearch.WordTrace tailWord_139745 prefixEnd_139745 31891712916738213664369 := by
  unfold tailWord_139745
  simp only [CollatzResearch.WordTrace]
  refine ⟨5096918878735206390996689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3397945919156804260664459 5096918878735206390996689)
  ·
    refine ⟨3822689159051404793247517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5096918878735206390996689 3822689159051404793247517)
    ·
      refine ⟨1433508434644276797467819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3822689159051404793247517 1433508434644276797467819)
      ·
        refine ⟨2150262651966415196201729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1433508434644276797467819 2150262651966415196201729)
        ·
          refine ⟨1612696988974811397151297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2150262651966415196201729 1612696988974811397151297)
          ·
            refine ⟨1209522741731108547863473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1612696988974811397151297 1209522741731108547863473)
            ·
              refine ⟨907142056298331410897605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1209522741731108547863473 907142056298331410897605)
              ·
                refine ⟨170089135555937139543301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 907142056298331410897605 170089135555937139543301)
                ·
                  refine ⟨31891712916738213664369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 170089135555937139543301 31891712916738213664369)
                  ·
                    rfl

theorem cell21_139745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 4, 4].length) (baseStart_139745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_139745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_139745 prefixEnd_139745 := by exact prefixLift 139745
  have htrace : WordTrace (prefixWord ++ tailWord_139745) baseStart_139745 baseEnd_139745 := by
    simpa [prefixWord, tailWord_139745, baseEnd_139745] using wordTrace_append hprefix tailTrace_139745
  have hstable : (prefixWord ++ tailWord_139745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139745).length < 2 ^ (prefixWord ++ tailWord_139745).sum := by decide
  have hdescent : baseEnd_139745 < baseStart_139745 := by decide
  rcases family_descends (prefixWord ++ tailWord_139745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139799 : List Nat := [1, 1, 3, 6, 2, 1, 2, 2, 3]
def baseStart_139799 : Nat := 118140960795 + 139799 * 2 ^ 59
def prefixEnd_139799 : Nat := 4983230072969 + 3 ^ 40 * 139799 * 2
def baseEnd_139799 : Nat := 31904036452446119764259

theorem tailTrace_139799 : CollatzResearch.WordTrace tailWord_139799 prefixEnd_139799 31904036452446119764259 := by
  unfold tailWord_139799
  simp only [CollatzResearch.WordTrace]
  refine ⟨5098888420539573613462451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3399258947026382408974967 5098888420539573613462451)
  ·
    refine ⟨7648332630809360420193677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5098888420539573613462451 7648332630809360420193677)
    ·
      refine ⟨2868124736553510157572629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7648332630809360420193677 2868124736553510157572629)
      ·
        refine ⟨134443347025945788636217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 2868124736553510157572629 134443347025945788636217)
        ·
          refine ⟨100832510269459341477163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 134443347025945788636217 100832510269459341477163)
          ·
            refine ⟨151248765404189012215745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100832510269459341477163 151248765404189012215745)
            ·
              refine ⟨113436574053141759161809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 151248765404189012215745 113436574053141759161809)
              ·
                refine ⟨85077430539856319371357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113436574053141759161809 85077430539856319371357)
                ·
                  refine ⟨31904036452446119764259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85077430539856319371357 31904036452446119764259)
                  ·
                    rfl

theorem cell21_139799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 2, 3].length) (baseStart_139799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_139799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_139799 prefixEnd_139799 := by exact prefixLift 139799
  have htrace : WordTrace (prefixWord ++ tailWord_139799) baseStart_139799 baseEnd_139799 := by
    simpa [prefixWord, tailWord_139799, baseEnd_139799] using wordTrace_append hprefix tailTrace_139799
  have hstable : (prefixWord ++ tailWord_139799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139799).length < 2 ^ (prefixWord ++ tailWord_139799).sum := by decide
  have hdescent : baseEnd_139799 < baseStart_139799 := by decide
  rcases family_descends (prefixWord ++ tailWord_139799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139976 : List Nat := [2, 1, 3, 1, 2, 3, 4, 2, 3]
def baseStart_139976 : Nat := 118140960795 + 139976 * 2 ^ 59
def prefixEnd_139976 : Nat := 4983230072969 + 3 ^ 40 * 139976 * 2
def baseEnd_139976 : Nat := 31944430263933145313897

theorem tailTrace_139976 : CollatzResearch.WordTrace tailWord_139976 prefixEnd_139976 31944430263933145313897 := by
  unfold tailWord_139976
  simp only [CollatzResearch.WordTrace]
  refine ⟨2552672070449166421327891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3403562760598888561770521 2552672070449166421327891)
  ·
    refine ⟨3829008105673749631991837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2552672070449166421327891 3829008105673749631991837)
    ·
      refine ⟨1435878039627656111996939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3829008105673749631991837 1435878039627656111996939)
      ·
        refine ⟨2153817059441484167995409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1435878039627656111996939 2153817059441484167995409)
        ·
          refine ⟨1615362794581113125996557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2153817059441484167995409 1615362794581113125996557)
          ·
            refine ⟨605761047967917422248709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1615362794581113125996557 605761047967917422248709)
            ·
              refine ⟨113580196493984516671633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 605761047967917422248709 113580196493984516671633)
              ·
                refine ⟨85185147370488387503725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113580196493984516671633 85185147370488387503725)
                ·
                  refine ⟨31944430263933145313897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85185147370488387503725 31944430263933145313897)
                  ·
                    rfl

theorem cell21_139976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 3].length) (baseStart_139976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_139976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_139976 prefixEnd_139976 := by exact prefixLift 139976
  have htrace : WordTrace (prefixWord ++ tailWord_139976) baseStart_139976 baseEnd_139976 := by
    simpa [prefixWord, tailWord_139976, baseEnd_139976] using wordTrace_append hprefix tailTrace_139976
  have hstable : (prefixWord ++ tailWord_139976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139976).length < 2 ^ (prefixWord ++ tailWord_139976).sum := by decide
  have hdescent : baseEnd_139976 < baseStart_139976 := by decide
  rcases family_descends (prefixWord ++ tailWord_139976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140004 : List Nat := [2, 3, 1, 1, 1, 5, 3, 5]
def baseStart_140004 : Nat := 118140960795 + 140004 * 2 ^ 59
def prefixEnd_140004 : Nat := 4983230072969 + 3 ^ 40 * 140004 * 2
def baseEnd_140004 : Nat := 10650273415137106282391

theorem tailTrace_140004 : CollatzResearch.WordTrace tailWord_140004 prefixEnd_140004 10650273415137106282391 := by
  unfold tailWord_140004
  simp only [CollatzResearch.WordTrace]
  refine ⟨2553182692398446812337533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3404243589864595749783377 2553182692398446812337533)
  ·
    refine ⟨957443509649417554626575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2553182692398446812337533 957443509649417554626575)
    ·
      refine ⟨1436165264474126331939863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 957443509649417554626575 1436165264474126331939863)
      ·
        refine ⟨2154247896711189497909795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1436165264474126331939863 2154247896711189497909795)
        ·
          refine ⟨3231371845066784246864693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2154247896711189497909795 3231371845066784246864693)
          ·
            refine ⟨302941110475011023143565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3231371845066784246864693 302941110475011023143565)
            ·
              refine ⟨113602916428129133678837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 302941110475011023143565 113602916428129133678837)
              ·
                refine ⟨10650273415137106282391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 113602916428129133678837 10650273415137106282391)
                ·
                  rfl

theorem cell21_140004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 5, 3, 5].length) (baseStart_140004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_140004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_140004 prefixEnd_140004 := by exact prefixLift 140004
  have htrace : WordTrace (prefixWord ++ tailWord_140004) baseStart_140004 baseEnd_140004 := by
    simpa [prefixWord, tailWord_140004, baseEnd_140004] using wordTrace_append hprefix tailTrace_140004
  have hstable : (prefixWord ++ tailWord_140004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140004).length < 2 ^ (prefixWord ++ tailWord_140004).sum := by decide
  have hdescent : baseEnd_140004 < baseStart_140004 := by decide
  rcases family_descends (prefixWord ++ tailWord_140004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140063 : List Nat := [1, 1, 2, 4, 2, 3, 1, 7]
def baseStart_140063 : Nat := 118140960795 + 140063 * 2 ^ 59
def prefixEnd_140063 : Nat := 4983230072969 + 3 ^ 40 * 140063 * 2
def baseEnd_140063 : Nat := 10654761616413442454573

theorem tailTrace_140063 : CollatzResearch.WordTrace tailWord_140063 prefixEnd_140063 10654761616413442454573 := by
  unfold tailWord_140063
  simp only [CollatzResearch.WordTrace]
  refine ⟨5108517291583146701072843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3405678194388764467381895 5108517291583146701072843)
  ·
    refine ⟨7662775937374720051609265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5108517291583146701072843 7662775937374720051609265)
    ·
      refine ⟨5747081953031040038706949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7662775937374720051609265 5747081953031040038706949)
      ·
        refine ⟨1077577866193320007257553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5747081953031040038706949 1077577866193320007257553)
        ·
          refine ⟨808183399644990005443165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1077577866193320007257553 808183399644990005443165)
          ·
            refine ⟨303068774866871252041187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 808183399644990005443165 303068774866871252041187)
            ·
              refine ⟨454603162300306878061781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303068774866871252041187 454603162300306878061781)
              ·
                refine ⟨10654761616413442454573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 454603162300306878061781 10654761616413442454573)
                ·
                  rfl

theorem cell21_140063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 1, 7].length) (baseStart_140063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_140063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_140063 prefixEnd_140063 := by exact prefixLift 140063
  have htrace : WordTrace (prefixWord ++ tailWord_140063) baseStart_140063 baseEnd_140063 := by
    simpa [prefixWord, tailWord_140063, baseEnd_140063] using wordTrace_append hprefix tailTrace_140063
  have hstable : (prefixWord ++ tailWord_140063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140063).length < 2 ^ (prefixWord ++ tailWord_140063).sum := by decide
  have hdescent : baseEnd_140063 < baseStart_140063 := by decide
  rcases family_descends (prefixWord ++ tailWord_140063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140086 : List Nat := [5, 1, 2, 2, 2, 1, 3, 2, 3]
def baseStart_140086 : Nat := 118140960795 + 140086 * 2 ^ 59
def prefixEnd_140086 : Nat := 4983230072969 + 3 ^ 40 * 140086 * 2
def baseEnd_140086 : Nat := 31969533762597398480339

theorem tailTrace_140086 : CollatzResearch.WordTrace tailWord_140086 prefixEnd_140086 31969533762597398480339 := by
  unfold tailWord_140086
  simp only [CollatzResearch.WordTrace]
  refine ⟨319334760656238851822507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3406237446999881086106741 319334760656238851822507)
  ·
    refine ⟨479002140984358277733761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 319334760656238851822507 479002140984358277733761)
    ·
      refine ⟨359251605738268708300321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 479002140984358277733761 359251605738268708300321)
      ·
        refine ⟨269438704303701531225241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 359251605738268708300321 269438704303701531225241)
        ·
          refine ⟨202079028227776148418931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 269438704303701531225241 202079028227776148418931)
          ·
            refine ⟨303118542341664222628397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202079028227776148418931 303118542341664222628397)
            ·
              refine ⟨113669453378124083485649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 303118542341664222628397 113669453378124083485649)
              ·
                refine ⟨85252090033593062614237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113669453378124083485649 85252090033593062614237)
                ·
                  refine ⟨31969533762597398480339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85252090033593062614237 31969533762597398480339)
                  ·
                    rfl

theorem cell21_140086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_140086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_140086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_140086 prefixEnd_140086 := by exact prefixLift 140086
  have htrace : WordTrace (prefixWord ++ tailWord_140086) baseStart_140086 baseEnd_140086 := by
    simpa [prefixWord, tailWord_140086, baseEnd_140086] using wordTrace_append hprefix tailTrace_140086
  have hstable : (prefixWord ++ tailWord_140086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140086).length < 2 ^ (prefixWord ++ tailWord_140086).sum := by decide
  have hdescent : baseEnd_140086 < baseStart_140086 := by decide
  rcases family_descends (prefixWord ++ tailWord_140086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140097 : List Nat := [1, 2, 5, 3, 1, 1, 2, 6]
def baseStart_140097 : Nat := 118140960795 + 140097 * 2 ^ 59
def prefixEnd_140097 : Nat := 4983230072969 + 3 ^ 40 * 140097 * 2
def baseEnd_140097 : Nat := 10657348037487941265661

theorem tailTrace_140097 : CollatzResearch.WordTrace tailWord_140097 prefixEnd_140097 10657348037487941265661 := by
  unfold tailWord_140097
  simp only [CollatzResearch.WordTrace]
  refine ⟨5109757373459970507810545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3406504915639980338540363 5109757373459970507810545)
  ·
    refine ⟨3832318030094977880857909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5109757373459970507810545 3832318030094977880857909)
    ·
      refine ⟨359279815321404176330429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3832318030094977880857909 359279815321404176330429)
      ·
        refine ⟨134729930745526566123911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 359279815321404176330429 134729930745526566123911)
        ·
          refine ⟨202094896118289849185867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 134729930745526566123911 202094896118289849185867)
          ·
            refine ⟨303142344177434773778801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202094896118289849185867 303142344177434773778801)
            ·
              refine ⟨227356758133076080334101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 303142344177434773778801 227356758133076080334101)
              ·
                refine ⟨10657348037487941265661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 227356758133076080334101 10657348037487941265661)
                ·
                  rfl

theorem cell21_140097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 2, 6].length) (baseStart_140097 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_140097 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_140097 prefixEnd_140097 := by exact prefixLift 140097
  have htrace : WordTrace (prefixWord ++ tailWord_140097) baseStart_140097 baseEnd_140097 := by
    simpa [prefixWord, tailWord_140097, baseEnd_140097] using wordTrace_append hprefix tailTrace_140097
  have hstable : (prefixWord ++ tailWord_140097).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140097).length < 2 ^ (prefixWord ++ tailWord_140097).sum := by decide
  have hdescent : baseEnd_140097 < baseStart_140097 := by decide
  rcases family_descends (prefixWord ++ tailWord_140097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140170 : List Nat := [3, 1, 2, 4, 1, 1, 1, 1, 7]
def baseStart_140170 : Nat := 118140960795 + 140170 * 2 ^ 59
def prefixEnd_140170 : Nat := 4983230072969 + 3 ^ 40 * 140170 * 2
def baseEnd_140170 : Nat := 31988703707031919080167

theorem tailTrace_140170 : CollatzResearch.WordTrace tailWord_140170 prefixEnd_140170 31988703707031919080167 := by
  unfold tailWord_140170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1278104975548875993804491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3408279934797002650145309 1278104975548875993804491)
  ·
    refine ⟨1917157463323313990706737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1278104975548875993804491 1917157463323313990706737)
    ·
      refine ⟨1437868097492485493030053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1917157463323313990706737 1437868097492485493030053)
      ·
        refine ⟨269600268279841029943135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1437868097492485493030053 269600268279841029943135)
        ·
          refine ⟨404400402419761544914703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269600268279841029943135 404400402419761544914703)
          ·
            refine ⟨606600603629642317372055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404400402419761544914703 606600603629642317372055)
            ·
              refine ⟨909900905444463476058083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606600603629642317372055 909900905444463476058083)
              ·
                refine ⟨1364851358166695214087125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 909900905444463476058083 1364851358166695214087125)
                ·
                  refine ⟨31988703707031919080167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1364851358166695214087125 31988703707031919080167)
                  ·
                    rfl

theorem cell21_140170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 1, 7].length) (baseStart_140170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_140170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_140170 prefixEnd_140170 := by exact prefixLift 140170
  have htrace : WordTrace (prefixWord ++ tailWord_140170) baseStart_140170 baseEnd_140170 := by
    simpa [prefixWord, tailWord_140170, baseEnd_140170] using wordTrace_append hprefix tailTrace_140170
  have hstable : (prefixWord ++ tailWord_140170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140170).length < 2 ^ (prefixWord ++ tailWord_140170).sum := by decide
  have hdescent : baseEnd_140170 < baseStart_140170 := by decide
  rcases family_descends (prefixWord ++ tailWord_140170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140263 : List Nat := [1, 1, 5, 2, 2, 3, 1, 1, 5]
def baseStart_140263 : Nat := 118140960795 + 140263 * 2 ^ 59
def prefixEnd_140263 : Nat := 4983230072969 + 3 ^ 40 * 140263 * 2
def baseEnd_140263 : Nat := 32009927574084424029977

theorem tailTrace_140263 : CollatzResearch.WordTrace tailWord_140263 prefixEnd_140263 32009927574084424029977 := by
  unfold tailWord_140263
  simp only [CollatzResearch.WordTrace]
  refine ⟨5115811890858580858353443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3410541260572387238902295 5115811890858580858353443)
  ·
    refine ⟨7673717836287871287530165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5115811890858580858353443 7673717836287871287530165)
    ·
      refine ⟨719411047151987933205953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7673717836287871287530165 719411047151987933205953)
      ·
        refine ⟨539558285363990949904465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 719411047151987933205953 539558285363990949904465)
        ·
          refine ⟨404668714022993212428349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 539558285363990949904465 404668714022993212428349)
          ·
            refine ⟨151750767758622454660631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 404668714022993212428349 151750767758622454660631)
            ·
              refine ⟨227626151637933681990947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151750767758622454660631 227626151637933681990947)
              ·
                refine ⟨341439227456900522986421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227626151637933681990947 341439227456900522986421)
                ·
                  refine ⟨32009927574084424029977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 341439227456900522986421 32009927574084424029977)
                  ·
                    rfl

theorem cell21_140263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 1, 1, 5].length) (baseStart_140263 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_140263 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_140263 prefixEnd_140263 := by exact prefixLift 140263
  have htrace : WordTrace (prefixWord ++ tailWord_140263) baseStart_140263 baseEnd_140263 := by
    simpa [prefixWord, tailWord_140263, baseEnd_140263] using wordTrace_append hprefix tailTrace_140263
  have hstable : (prefixWord ++ tailWord_140263).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140263).length < 2 ^ (prefixWord ++ tailWord_140263).sum := by decide
  have hdescent : baseEnd_140263 < baseStart_140263 := by decide
  rcases family_descends (prefixWord ++ tailWord_140263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140336 : List Nat := [2, 1, 1, 1, 2, 4, 1, 5, 4]
def baseStart_140336 : Nat := 118140960795 + 140336 * 2 ^ 59
def prefixEnd_140336 : Nat := 4983230072969 + 3 ^ 40 * 140336 * 2
def baseEnd_140336 : Nat := 32026587168652519313161

theorem tailTrace_140336 : CollatzResearch.WordTrace tailWord_140336 prefixEnd_140336 32026587168652519313161 := by
  unfold tailWord_140336
  simp only [CollatzResearch.WordTrace]
  refine ⟨2559237209797057162880431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3412316279729409550507241 2559237209797057162880431)
  ·
    refine ⟨3838855814695585744320647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2559237209797057162880431 3838855814695585744320647)
    ·
      refine ⟨5758283722043378616480971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3838855814695585744320647 5758283722043378616480971)
      ·
        refine ⟨8637425583065067924721457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5758283722043378616480971 8637425583065067924721457)
        ·
          refine ⟨6478069187298800943541093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8637425583065067924721457 6478069187298800943541093)
          ·
            refine ⟨1214637972618525176913955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6478069187298800943541093 1214637972618525176913955)
            ·
              refine ⟨1821956958927787765370933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214637972618525176913955 1821956958927787765370933)
              ·
                refine ⟨170808464899480103003525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1821956958927787765370933 170808464899480103003525)
                ·
                  refine ⟨32026587168652519313161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 170808464899480103003525 32026587168652519313161)
                  ·
                    rfl

theorem cell21_140336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 5, 4].length) (baseStart_140336 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_140336 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_140336 prefixEnd_140336 := by exact prefixLift 140336
  have htrace : WordTrace (prefixWord ++ tailWord_140336) baseStart_140336 baseEnd_140336 := by
    simpa [prefixWord, tailWord_140336, baseEnd_140336] using wordTrace_append hprefix tailTrace_140336
  have hstable : (prefixWord ++ tailWord_140336).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140336).length < 2 ^ (prefixWord ++ tailWord_140336).sum := by decide
  have hdescent : baseEnd_140336 < baseStart_140336 := by decide
  rcases family_descends (prefixWord ++ tailWord_140336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140370 : List Nat := [3, 2, 2, 1, 3, 3, 1, 2, 4]
def baseStart_140370 : Nat := 118140960795 + 140370 * 2 ^ 59
def prefixEnd_140370 : Nat := 4983230072969 + 3 ^ 40 * 140370 * 2
def baseEnd_140370 : Nat := 32034346431876015746425

theorem tailTrace_140370 : CollatzResearch.WordTrace tailWord_140370 prefixEnd_140370 32034346431876015746425 := by
  unfold tailWord_140370
  simp only [CollatzResearch.WordTrace]
  refine ⟨1279928625367734533124641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3413143000980625421665709 1279928625367734533124641)
  ·
    refine ⟨959946469025800899843481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1279928625367734533124641 959946469025800899843481)
    ·
      refine ⟨719959851769350674882611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 959946469025800899843481 719959851769350674882611)
      ·
        refine ⟨1079939777654026012323917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 719959851769350674882611 1079939777654026012323917)
        ·
          refine ⟨404977416620259754621469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1079939777654026012323917 404977416620259754621469)
          ·
            refine ⟨151866531232597407983051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 404977416620259754621469 151866531232597407983051)
            ·
              refine ⟨227799796848896111974577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151866531232597407983051 227799796848896111974577)
              ·
                refine ⟨170849847636672083980933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227799796848896111974577 170849847636672083980933)
                ·
                  refine ⟨32034346431876015746425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 170849847636672083980933 32034346431876015746425)
                  ·
                    rfl

theorem cell21_140370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_140370 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_140370 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_140370 prefixEnd_140370 := by exact prefixLift 140370
  have htrace : WordTrace (prefixWord ++ tailWord_140370) baseStart_140370 baseEnd_140370 := by
    simpa [prefixWord, tailWord_140370, baseEnd_140370] using wordTrace_append hprefix tailTrace_140370
  have hstable : (prefixWord ++ tailWord_140370).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140370).length < 2 ^ (prefixWord ++ tailWord_140370).sum := by decide
  have hdescent : baseEnd_140370 < baseStart_140370 := by decide
  rcases family_descends (prefixWord ++ tailWord_140370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140398 : List Nat := [4, 1, 2, 2, 1, 2, 2, 2, 5]
def baseStart_140398 : Nat := 118140960795 + 140398 * 2 ^ 59
def prefixEnd_140398 : Nat := 4983230072969 + 3 ^ 40 * 140398 * 2
def baseEnd_140398 : Nat := 32040736413354189279701

theorem tailTrace_140398 : CollatzResearch.WordTrace tailWord_140398 prefixEnd_140398 32040736413354189279701 := by
  unfold tailWord_140398
  simp only [CollatzResearch.WordTrace]
  refine ⟨640091968171187364314731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3413823830246332609678565 640091968171187364314731)
  ·
    refine ⟨960137952256781046472097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 640091968171187364314731 960137952256781046472097)
    ·
      refine ⟨720103464192585784854073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 960137952256781046472097 720103464192585784854073)
      ·
        refine ⟨540077598144439338640555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 720103464192585784854073 540077598144439338640555)
        ·
          refine ⟨810116397216659007960833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540077598144439338640555 810116397216659007960833)
          ·
            refine ⟨607587297912494255970625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 810116397216659007960833 607587297912494255970625)
            ·
              refine ⟨455690473434370691977969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 607587297912494255970625 455690473434370691977969)
              ·
                refine ⟨341767855075778018983477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 455690473434370691977969 341767855075778018983477)
                ·
                  refine ⟨32040736413354189279701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 341767855075778018983477 32040736413354189279701)
                  ·
                    rfl

theorem cell21_140398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 5].length) (baseStart_140398 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_140398 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_140398 prefixEnd_140398 := by exact prefixLift 140398
  have htrace : WordTrace (prefixWord ++ tailWord_140398) baseStart_140398 baseEnd_140398 := by
    simpa [prefixWord, tailWord_140398, baseEnd_140398] using wordTrace_append hprefix tailTrace_140398
  have hstable : (prefixWord ++ tailWord_140398).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140398).length < 2 ^ (prefixWord ++ tailWord_140398).sum := by decide
  have hdescent : baseEnd_140398 < baseStart_140398 := by decide
  rcases family_descends (prefixWord ++ tailWord_140398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140446 : List Nat := [4, 3, 1, 1, 2, 2, 1, 3, 4]
def baseStart_140446 : Nat := 118140960795 + 140446 * 2 ^ 59
def prefixEnd_140446 : Nat := 4983230072969 + 3 ^ 40 * 140446 * 2
def baseEnd_140446 : Nat := 32051690667316772479603

theorem tailTrace_140446 : CollatzResearch.WordTrace tailWord_140446 prefixEnd_140446 32051690667316772479603 := by
  unfold tailWord_140446
  simp only [CollatzResearch.WordTrace]
  refine ⟨640310806149450389033149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3414990966130402074843461 640310806149450389033149)
  ·
    refine ⟨240116552306043895887431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 640310806149450389033149 240116552306043895887431)
    ·
      refine ⟨360174828459065843831147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 240116552306043895887431 360174828459065843831147)
      ·
        refine ⟨540262242688598765746721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360174828459065843831147 540262242688598765746721)
        ·
          refine ⟨405196682016449074310041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 540262242688598765746721 405196682016449074310041)
          ·
            refine ⟨303897511512336805732531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 405196682016449074310041 303897511512336805732531)
            ·
              refine ⟨455846267268505208598797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303897511512336805732531 455846267268505208598797)
              ·
                refine ⟨170942350225689453224549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 455846267268505208598797 170942350225689453224549)
                ·
                  refine ⟨32051690667316772479603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 170942350225689453224549 32051690667316772479603)
                  ·
                    rfl

theorem cell21_140446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_140446 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_140446 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_140446 prefixEnd_140446 := by exact prefixLift 140446
  have htrace : WordTrace (prefixWord ++ tailWord_140446) baseStart_140446 baseEnd_140446 := by
    simpa [prefixWord, tailWord_140446, baseEnd_140446] using wordTrace_append hprefix tailTrace_140446
  have hstable : (prefixWord ++ tailWord_140446).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140446).length < 2 ^ (prefixWord ++ tailWord_140446).sum := by decide
  have hdescent : baseEnd_140446 < baseStart_140446 := by decide
  rcases family_descends (prefixWord ++ tailWord_140446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140474 : List Nat := [3, 1, 1, 1, 2, 2, 1, 7, 3]
def baseStart_140474 : Nat := 118140960795 + 140474 * 2 ^ 59
def prefixEnd_140474 : Nat := 4983230072969 + 3 ^ 40 * 140474 * 2
def baseEnd_140474 : Nat := 32058080648794946012879

theorem tailTrace_140474 : CollatzResearch.WordTrace tailWord_140474 prefixEnd_140474 32058080648794946012879 := by
  unfold tailWord_140474
  simp only [CollatzResearch.WordTrace]
  refine ⟨1280876923273540973571119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3415671795396109262856317 1280876923273540973571119)
  ·
    refine ⟨1921315384910311460356679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1280876923273540973571119 1921315384910311460356679)
    ·
      refine ⟨2881973077365467190535019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1921315384910311460356679 2881973077365467190535019)
      ·
        refine ⟨4322959616048200785802529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2881973077365467190535019 4322959616048200785802529)
        ·
          refine ⟨3242219712036150589351897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4322959616048200785802529 3242219712036150589351897)
          ·
            refine ⟨2431664784027112942013923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3242219712036150589351897 2431664784027112942013923)
            ·
              refine ⟨3647497176040669413020885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2431664784027112942013923 3647497176040669413020885)
              ·
                refine ⟨85488215063453189367677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3647497176040669413020885 85488215063453189367677)
                ·
                  refine ⟨32058080648794946012879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85488215063453189367677 32058080648794946012879)
                  ·
                    rfl

theorem cell21_140474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 7, 3].length) (baseStart_140474 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_140474 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_140474 prefixEnd_140474 := by exact prefixLift 140474
  have htrace : WordTrace (prefixWord ++ tailWord_140474) baseStart_140474 baseEnd_140474 := by
    simpa [prefixWord, tailWord_140474, baseEnd_140474] using wordTrace_append hprefix tailTrace_140474
  have hstable : (prefixWord ++ tailWord_140474).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140474).length < 2 ^ (prefixWord ++ tailWord_140474).sum := by decide
  have hdescent : baseEnd_140474 < baseStart_140474 := by decide
  rcases family_descends (prefixWord ++ tailWord_140474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140488 : List Nat := [2, 1, 3, 1, 2, 1, 3, 4, 4]
def baseStart_140488 : Nat := 118140960795 + 140488 * 2 ^ 59
def prefixEnd_140488 : Nat := 4983230072969 + 3 ^ 40 * 140488 * 2
def baseEnd_140488 : Nat := 32061275639534032779517

theorem tailTrace_140488 : CollatzResearch.WordTrace tailWord_140488 prefixEnd_140488 32061275639534032779517 := by
  unfold tailWord_140488
  simp only [CollatzResearch.WordTrace]
  refine ⟨2562009157521722142647059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3416012210028962856862745 2562009157521722142647059)
  ·
    refine ⟨3843013736282583213970589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2562009157521722142647059 3843013736282583213970589)
    ·
      refine ⟨1441130151105968705238971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3843013736282583213970589 1441130151105968705238971)
      ·
        refine ⟨2161695226658953057858457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1441130151105968705238971 2161695226658953057858457)
        ·
          refine ⟨1621271419994214793393843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2161695226658953057858457 1621271419994214793393843)
          ·
            refine ⟨2431907129991322190090765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1621271419994214793393843 2431907129991322190090765)
            ·
              refine ⟨911965173746745821284037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2431907129991322190090765 911965173746745821284037)
              ·
                refine ⟨170993470077514841490757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 911965173746745821284037 170993470077514841490757)
                ·
                  refine ⟨32061275639534032779517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 170993470077514841490757 32061275639534032779517)
                  ·
                    rfl

theorem cell21_140488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 4].length) (baseStart_140488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_140488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_140488 prefixEnd_140488 := by exact prefixLift 140488
  have htrace : WordTrace (prefixWord ++ tailWord_140488) baseStart_140488 baseEnd_140488 := by
    simpa [prefixWord, tailWord_140488, baseEnd_140488] using wordTrace_append hprefix tailTrace_140488
  have hstable : (prefixWord ++ tailWord_140488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140488).length < 2 ^ (prefixWord ++ tailWord_140488).sum := by decide
  have hdescent : baseEnd_140488 < baseStart_140488 := by decide
  rcases family_descends (prefixWord ++ tailWord_140488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140584 : List Nat := [2, 1, 5, 1, 2, 3, 1, 3, 3]
def baseStart_140584 : Nat := 118140960795 + 140584 * 2 ^ 59
def prefixEnd_140584 : Nat := 4983230072969 + 3 ^ 40 * 140584 * 2
def baseEnd_140584 : Nat := 32083184147459199179321

theorem tailTrace_140584 : CollatzResearch.WordTrace tailWord_140584 prefixEnd_140584 32083184147459199179321 := by
  unfold tailWord_140584
  simp only [CollatzResearch.WordTrace]
  refine ⟨2563759861347826340394403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3418346481797101787192537 2563759861347826340394403)
  ·
    refine ⟨3845639792021739510591605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2563759861347826340394403 3845639792021739510591605)
    ·
      refine ⟨360528730502038079117963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3845639792021739510591605 360528730502038079117963)
      ·
        refine ⟨540793095753057118676945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 360528730502038079117963 540793095753057118676945)
        ·
          refine ⟨405594821814792839007709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 540793095753057118676945 405594821814792839007709)
          ·
            refine ⟨152098058180547314627891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 405594821814792839007709 152098058180547314627891)
            ·
              refine ⟨228147087270820971941837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152098058180547314627891 228147087270820971941837)
              ·
                refine ⟨85555157726557864478189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 228147087270820971941837 85555157726557864478189)
                ·
                  refine ⟨32083184147459199179321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85555157726557864478189 32083184147459199179321)
                  ·
                    rfl

theorem cell21_140584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 3, 3].length) (baseStart_140584 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_140584 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_140584 prefixEnd_140584 := by exact prefixLift 140584
  have htrace : WordTrace (prefixWord ++ tailWord_140584) baseStart_140584 baseEnd_140584 := by
    simpa [prefixWord, tailWord_140584, baseEnd_140584] using wordTrace_append hprefix tailTrace_140584
  have hstable : (prefixWord ++ tailWord_140584).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140584).length < 2 ^ (prefixWord ++ tailWord_140584).sum := by decide
  have hdescent : baseEnd_140584 < baseStart_140584 := by decide
  rcases family_descends (prefixWord ++ tailWord_140584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140612 : List Nat := [2, 3, 4, 1, 1, 2, 2, 6]
def baseStart_140612 : Nat := 118140960795 + 140612 * 2 ^ 59
def prefixEnd_140612 : Nat := 4983230072969 + 3 ^ 40 * 140612 * 2
def baseEnd_140612 : Nat := 10696524709645790904199

theorem tailTrace_140612 : CollatzResearch.WordTrace tailWord_140612 prefixEnd_140612 10696524709645790904199 := by
  unfold tailWord_140612
  simp only [CollatzResearch.WordTrace]
  refine ⟨2564270483297106731404045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3419027311062808975205393 2564270483297106731404045)
  ·
    refine ⟨961601431236415024276517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2564270483297106731404045 961601431236415024276517)
    ·
      refine ⟨180300268356827817051847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 961601431236415024276517 180300268356827817051847)
      ·
        refine ⟨270450402535241725577771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180300268356827817051847 270450402535241725577771)
        ·
          refine ⟨405675603802862588366657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270450402535241725577771 405675603802862588366657)
          ·
            refine ⟨304256702852146941274993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 405675603802862588366657 304256702852146941274993)
            ·
              refine ⟨228192527139110205956245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304256702852146941274993 228192527139110205956245)
              ·
                refine ⟨10696524709645790904199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 228192527139110205956245 10696524709645790904199)
                ·
                  rfl

theorem cell21_140612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 2, 2, 6].length) (baseStart_140612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_140612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_140612 prefixEnd_140612 := by exact prefixLift 140612
  have htrace : WordTrace (prefixWord ++ tailWord_140612) baseStart_140612 baseEnd_140612 := by
    simpa [prefixWord, tailWord_140612, baseEnd_140612] using wordTrace_append hprefix tailTrace_140612
  have hstable : (prefixWord ++ tailWord_140612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140612).length < 2 ^ (prefixWord ++ tailWord_140612).sum := by decide
  have hdescent : baseEnd_140612 < baseStart_140612 := by decide
  rcases family_descends (prefixWord ++ tailWord_140612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140674 : List Nat := [3, 4, 2, 1, 1, 1, 2, 3, 4]
def baseStart_140674 : Nat := 118140960795 + 140674 * 2 ^ 59
def prefixEnd_140674 : Nat := 4983230072969 + 3 ^ 40 * 140674 * 2
def baseEnd_140674 : Nat := 32103723373639042679137

theorem tailTrace_140674 : CollatzResearch.WordTrace tailWord_140674 prefixEnd_140674 32103723373639042679137 := by
  unfold tailWord_140674
  simp only [CollatzResearch.WordTrace]
  refine ⟨1282700573092399512891269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3420534861579732034376717 1282700573092399512891269)
  ·
    refine ⟨240506357454824908667113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1282700573092399512891269 240506357454824908667113)
    ·
      refine ⟨180379768091118681500335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 240506357454824908667113 180379768091118681500335)
      ·
        refine ⟨270569652136678022250503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180379768091118681500335 270569652136678022250503)
        ·
          refine ⟨405854478205017033375755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 270569652136678022250503 405854478205017033375755)
          ·
            refine ⟨608781717307525550063633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 405854478205017033375755 608781717307525550063633)
            ·
              refine ⟨456586287980644162547725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 608781717307525550063633 456586287980644162547725)
              ·
                refine ⟨171219857992741560955397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 456586287980644162547725 171219857992741560955397)
                ·
                  refine ⟨32103723373639042679137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171219857992741560955397 32103723373639042679137)
                  ·
                    rfl

theorem cell21_140674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 2, 3, 4].length) (baseStart_140674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_140674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_140674 prefixEnd_140674 := by exact prefixLift 140674
  have htrace : WordTrace (prefixWord ++ tailWord_140674) baseStart_140674 baseEnd_140674 := by
    simpa [prefixWord, tailWord_140674, baseEnd_140674] using wordTrace_append hprefix tailTrace_140674
  have hstable : (prefixWord ++ tailWord_140674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140674).length < 2 ^ (prefixWord ++ tailWord_140674).sum := by decide
  have hdescent : baseEnd_140674 < baseStart_140674 := by decide
  rcases family_descends (prefixWord ++ tailWord_140674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140716 : List Nat := [2, 2, 1, 1, 1, 1, 7, 2, 4]
def baseStart_140716 : Nat := 118140960795 + 140716 * 2 ^ 59
def prefixEnd_140716 : Nat := 4983230072969 + 3 ^ 40 * 140716 * 2
def baseEnd_140716 : Nat := 32113308345856302979051

theorem tailTrace_140716 : CollatzResearch.WordTrace tailWord_140716 prefixEnd_140716 32113308345856302979051 := by
  unfold tailWord_140716
  simp only [CollatzResearch.WordTrace]
  refine ⟨2566167079108719612297001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3421556105478292816396001 2566167079108719612297001)
  ·
    refine ⟨1924625309331539709222751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2566167079108719612297001 1924625309331539709222751)
    ·
      refine ⟨2886937963997309563834127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1924625309331539709222751 2886937963997309563834127)
      ·
        refine ⟨4330406945995964345751191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2886937963997309563834127 4330406945995964345751191)
        ·
          refine ⟨6495610418993946518626787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4330406945995964345751191 6495610418993946518626787)
          ·
            refine ⟨9743415628490919777940181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6495610418993946518626787 9743415628490919777940181)
            ·
              refine ⟨228361303792755932295473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 9743415628490919777940181 228361303792755932295473)
              ·
                refine ⟨171270977844566949221605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228361303792755932295473 171270977844566949221605)
                ·
                  refine ⟨32113308345856302979051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171270977844566949221605 32113308345856302979051)
                  ·
                    rfl

theorem cell21_140716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_140716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_140716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_140716 prefixEnd_140716 := by exact prefixLift 140716
  have htrace : WordTrace (prefixWord ++ tailWord_140716) baseStart_140716 baseEnd_140716 := by
    simpa [prefixWord, tailWord_140716, baseEnd_140716] using wordTrace_append hprefix tailTrace_140716
  have hstable : (prefixWord ++ tailWord_140716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140716).length < 2 ^ (prefixWord ++ tailWord_140716).sum := by decide
  have hdescent : baseEnd_140716 < baseStart_140716 := by decide
  rcases family_descends (prefixWord ++ tailWord_140716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140733 : List Nat := [1, 4, 1, 2, 2, 1, 5, 1, 4]
def baseStart_140733 : Nat := 118140960795 + 140733 * 2 ^ 59
def prefixEnd_140733 : Nat := 4983230072969 + 3 ^ 40 * 140733 * 2
def baseEnd_140733 : Nat := 32117187977468051195683

theorem tailTrace_140733 : CollatzResearch.WordTrace tailWord_140733 prefixEnd_140733 32117187977468051195683 := by
  unfold tailWord_140733
  simp only [CollatzResearch.WordTrace]
  refine ⟨5132954199155851127962853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3421969466103900751975235 5132954199155851127962853)
  ·
    refine ⟨962428912341722086493035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5132954199155851127962853 962428912341722086493035)
    ·
      refine ⟨1443643368512583129739553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 962428912341722086493035 1443643368512583129739553)
      ·
        refine ⟨1082732526384437347304665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1443643368512583129739553 1082732526384437347304665)
        ·
          refine ⟨812049394788328010478499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1082732526384437347304665 812049394788328010478499)
          ·
            refine ⟨1218074092182492015717749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 812049394788328010478499 1218074092182492015717749)
            ·
              refine ⟨114194446142108626473539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1218074092182492015717749 114194446142108626473539)
              ·
                refine ⟨171291669213162939710309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114194446142108626473539 171291669213162939710309)
                ·
                  refine ⟨32117187977468051195683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171291669213162939710309 32117187977468051195683)
                  ·
                    rfl

theorem cell21_140733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 1, 4].length) (baseStart_140733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_140733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_140733 prefixEnd_140733 := by exact prefixLift 140733
  have htrace : WordTrace (prefixWord ++ tailWord_140733) baseStart_140733 baseEnd_140733 := by
    simpa [prefixWord, tailWord_140733, baseEnd_140733] using wordTrace_append hprefix tailTrace_140733
  have hstable : (prefixWord ++ tailWord_140733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140733).length < 2 ^ (prefixWord ++ tailWord_140733).sum := by decide
  have hdescent : baseEnd_140733 < baseStart_140733 := by decide
  rcases family_descends (prefixWord ++ tailWord_140733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140792 : List Nat := [2, 1, 2, 1, 1, 6, 1, 3, 4]
def baseStart_140792 : Nat := 118140960795 + 140792 * 2 ^ 59
def prefixEnd_140792 : Nat := 4983230072969 + 3 ^ 40 * 140792 * 2
def baseEnd_140792 : Nat := 32130652581297059712229

theorem tailTrace_140792 : CollatzResearch.WordTrace tailWord_140792 prefixEnd_140792 32130652581297059712229 := by
  unfold tailWord_140792
  simp only [CollatzResearch.WordTrace]
  refine ⟨2567553052971052102180315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3423404070628069469573753 2567553052971052102180315)
  ·
    refine ⟨3851329579456578153270473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2567553052971052102180315 3851329579456578153270473)
    ·
      refine ⟨2888497184592433614952855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3851329579456578153270473 2888497184592433614952855)
      ·
        refine ⟨4332745776888650422429283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2888497184592433614952855 4332745776888650422429283)
        ·
          refine ⟨6499118665332975633643925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4332745776888650422429283 6499118665332975633643925)
          ·
            refine ⟨304646187437483232827059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6499118665332975633643925 304646187437483232827059)
            ·
              refine ⟨456969281156224849240589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 304646187437483232827059 456969281156224849240589)
              ·
                refine ⟨171363480433584318465221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 456969281156224849240589 171363480433584318465221)
                ·
                  refine ⟨32130652581297059712229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171363480433584318465221 32130652581297059712229)
                  ·
                    rfl

theorem cell21_140792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 4].length) (baseStart_140792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_140792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_140792 prefixEnd_140792 := by exact prefixLift 140792
  have htrace : WordTrace (prefixWord ++ tailWord_140792) baseStart_140792 baseEnd_140792 := by
    simpa [prefixWord, tailWord_140792, baseEnd_140792] using wordTrace_append hprefix tailTrace_140792
  have hstable : (prefixWord ++ tailWord_140792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140792).length < 2 ^ (prefixWord ++ tailWord_140792).sum := by decide
  have hdescent : baseEnd_140792 < baseStart_140792 := by decide
  rcases family_descends (prefixWord ++ tailWord_140792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140840 : List Nat := [2, 1, 5, 2, 2, 2, 1, 6]
def baseStart_140840 : Nat := 118140960795 + 140840 * 2 ^ 59
def prefixEnd_140840 : Nat := 4983230072969 + 3 ^ 40 * 140840 * 2
def baseEnd_140840 : Nat := 10713868945086547637377

theorem tailTrace_140840 : CollatzResearch.WordTrace tailWord_140840 prefixEnd_140840 10713868945086547637377 := by
  unfold tailWord_140840
  simp only [CollatzResearch.WordTrace]
  refine ⟨2568428404884104201053987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3424571206512138934738649 2568428404884104201053987)
  ·
    refine ⟨3852642607326156301580981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2568428404884104201053987 3852642607326156301580981)
    ·
      refine ⟨361185244436827153273217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3852642607326156301580981 361185244436827153273217)
      ·
        refine ⟨270888933327620364954913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 361185244436827153273217 270888933327620364954913)
        ·
          refine ⟨203166699995715273716185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 270888933327620364954913 203166699995715273716185)
          ·
            refine ⟨152375024996786455287139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203166699995715273716185 152375024996786455287139)
            ·
              refine ⟨228562537495179682930709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152375024996786455287139 228562537495179682930709)
              ·
                refine ⟨10713868945086547637377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 228562537495179682930709 10713868945086547637377)
                ·
                  rfl

theorem cell21_140840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 6].length) (baseStart_140840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_140840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_140840 prefixEnd_140840 := by exact prefixLift 140840
  have htrace : WordTrace (prefixWord ++ tailWord_140840) baseStart_140840 baseEnd_140840 := by
    simpa [prefixWord, tailWord_140840, baseEnd_140840] using wordTrace_append hprefix tailTrace_140840
  have hstable : (prefixWord ++ tailWord_140840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140840).length < 2 ^ (prefixWord ++ tailWord_140840).sum := by decide
  have hdescent : baseEnd_140840 < baseStart_140840 := by decide
  rcases family_descends (prefixWord ++ tailWord_140840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140871 : List Nat := [1, 1, 4, 1, 5, 1, 2, 3, 3]
def baseStart_140871 : Nat := 118140960795 + 140871 * 2 ^ 59
def prefixEnd_140871 : Nat := 4983230072969 + 3 ^ 40 * 140871 * 2
def baseEnd_140871 : Nat := 32148681457610477895401

theorem tailTrace_140871 : CollatzResearch.WordTrace tailWord_140871 prefixEnd_140871 32148681457610477895401 := by
  unfold tailWord_140871
  simp only [CollatzResearch.WordTrace]
  refine ⟨5137987472655900696486467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3425324981770600464324311 5137987472655900696486467)
  ·
    refine ⟨7706981208983851044729701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5137987472655900696486467 7706981208983851044729701)
    ·
      refine ⟨1445058976684472070886819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7706981208983851044729701 1445058976684472070886819)
      ·
        refine ⟨2167588465026708106330229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1445058976684472070886819 2167588465026708106330229)
        ·
          refine ⟨203211418596253884968459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2167588465026708106330229 203211418596253884968459)
          ·
            refine ⟨304817127894380827452689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203211418596253884968459 304817127894380827452689)
            ·
              refine ⟨228612845920785620589517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304817127894380827452689 228612845920785620589517)
              ·
                refine ⟨85729817220294607721069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 228612845920785620589517 85729817220294607721069)
                ·
                  refine ⟨32148681457610477895401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85729817220294607721069 32148681457610477895401)
                  ·
                    rfl

theorem cell21_140871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 3, 3].length) (baseStart_140871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_140871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_140871 prefixEnd_140871 := by exact prefixLift 140871
  have htrace : WordTrace (prefixWord ++ tailWord_140871) baseStart_140871 baseEnd_140871 := by
    simpa [prefixWord, tailWord_140871, baseEnd_140871] using wordTrace_append hprefix tailTrace_140871
  have hstable : (prefixWord ++ tailWord_140871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140871).length < 2 ^ (prefixWord ++ tailWord_140871).sum := by decide
  have hdescent : baseEnd_140871 < baseStart_140871 := by decide
  rcases family_descends (prefixWord ++ tailWord_140871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140882 : List Nat := [3, 2, 2, 1, 2, 3, 8]
def baseStart_140882 : Nat := 118140960795 + 140882 * 2 ^ 59
def prefixEnd_140882 : Nat := 4983230072969 + 3 ^ 40 * 140882 * 2
def baseEnd_140882 : Nat := 3572354645275211468005

theorem tailTrace_140882 : CollatzResearch.WordTrace tailWord_140882 prefixEnd_140882 3572354645275211468005 := by
  unfold tailWord_140882
  simp only [CollatzResearch.WordTrace]
  refine ⟨1284597168904012393784225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3425592450410699716757933 1284597168904012393784225)
  ·
    refine ⟨963447876678009295338169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1284597168904012393784225 963447876678009295338169)
    ·
      refine ⟨722585907508506971503627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 963447876678009295338169 722585907508506971503627)
      ·
        refine ⟨1083878861262760457255441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 722585907508506971503627 1083878861262760457255441)
        ·
          refine ⟨812909145947070342941581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1083878861262760457255441 812909145947070342941581)
          ·
            refine ⟨304840929730151378603093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 812909145947070342941581 304840929730151378603093)
            ·
              refine ⟨3572354645275211468005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 304840929730151378603093 3572354645275211468005)
              ·
                rfl

theorem cell21_140882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 3, 8].length) (baseStart_140882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_140882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_140882 prefixEnd_140882 := by exact prefixLift 140882
  have htrace : WordTrace (prefixWord ++ tailWord_140882) baseStart_140882 baseEnd_140882 := by
    simpa [prefixWord, tailWord_140882, baseEnd_140882] using wordTrace_append hprefix tailTrace_140882
  have hstable : (prefixWord ++ tailWord_140882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140882).length < 2 ^ (prefixWord ++ tailWord_140882).sum := by decide
  have hdescent : baseEnd_140882 < baseStart_140882 := by decide
  rcases family_descends (prefixWord ++ tailWord_140882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140961 : List Nat := [1, 2, 3, 3, 2, 1, 4, 1, 4]
def baseStart_140961 : Nat := 118140960795 + 140961 * 2 ^ 59
def prefixEnd_140961 : Nat := 4983230072969 + 3 ^ 40 * 140961 * 2
def baseEnd_140961 : Nat := 32169220683790321395217

theorem tailTrace_140961 : CollatzResearch.WordTrace tailWord_140961 prefixEnd_140961 32169220683790321395217 := by
  unfold tailWord_140961
  simp only [CollatzResearch.WordTrace]
  refine ⟨5141270042329846067262737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3427513361553230711508491 5141270042329846067262737)
  ·
    refine ⟨3855952531747384550447053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5141270042329846067262737 3855952531747384550447053)
    ·
      refine ⟨1445982199405269206417645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3855952531747384550447053 1445982199405269206417645)
      ·
        refine ⟨542243324776975952406617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1445982199405269206417645 542243324776975952406617)
        ·
          refine ⟨406682493582731964304963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 542243324776975952406617 406682493582731964304963)
          ·
            refine ⟨610023740374097946457445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 406682493582731964304963 610023740374097946457445)
            ·
              refine ⟨114379451320143364960771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 610023740374097946457445 114379451320143364960771)
              ·
                refine ⟨171569176980215047441157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114379451320143364960771 171569176980215047441157)
                ·
                  refine ⟨32169220683790321395217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171569176980215047441157 32169220683790321395217)
                  ·
                    rfl

theorem cell21_140961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 4, 1, 4].length) (baseStart_140961 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_140961 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_140961 prefixEnd_140961 := by exact prefixLift 140961
  have htrace : WordTrace (prefixWord ++ tailWord_140961) baseStart_140961 baseEnd_140961 := by
    simpa [prefixWord, tailWord_140961, baseEnd_140961] using wordTrace_append hprefix tailTrace_140961
  have hstable : (prefixWord ++ tailWord_140961).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140961).length < 2 ^ (prefixWord ++ tailWord_140961).sum := by decide
  have hdescent : baseEnd_140961 < baseStart_140961 := by decide
  rcases family_descends (prefixWord ++ tailWord_140961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140998 : List Nat := [6, 1, 2, 1, 1, 3, 2, 2, 3]
def baseStart_140998 : Nat := 118140960795 + 140998 * 2 ^ 59
def prefixEnd_140998 : Nat := 4983230072969 + 3 ^ 40 * 140998 * 2
def baseEnd_140998 : Nat := 32177664587886479278475

theorem tailTrace_140998 : CollatzResearch.WordTrace tailWord_140998 prefixEnd_140998 32177664587886479278475 := by
  unfold tailWord_140998
  simp only [CollatzResearch.WordTrace]
  refine ⟨160706860724868793323739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3428413028797200924239765 160706860724868793323739)
  ·
    refine ⟨241060291087303189985609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160706860724868793323739 241060291087303189985609)
    ·
      refine ⟨180795218315477392489207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241060291087303189985609 180795218315477392489207)
      ·
        refine ⟨271192827473216088733811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180795218315477392489207 271192827473216088733811)
        ·
          refine ⟨406789241209824133100717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271192827473216088733811 406789241209824133100717)
          ·
            refine ⟨152545965453684049912769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 406789241209824133100717 152545965453684049912769)
            ·
              refine ⟨114409474090263037434577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152545965453684049912769 114409474090263037434577)
              ·
                refine ⟨85807105567697278075933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114409474090263037434577 85807105567697278075933)
                ·
                  refine ⟨32177664587886479278475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85807105567697278075933 32177664587886479278475)
                  ·
                    rfl

theorem cell21_140998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_140998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_140998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_140998 prefixEnd_140998 := by exact prefixLift 140998
  have htrace : WordTrace (prefixWord ++ tailWord_140998) baseStart_140998 baseEnd_140998 := by
    simpa [prefixWord, tailWord_140998, baseEnd_140998] using wordTrace_append hprefix tailTrace_140998
  have hstable : (prefixWord ++ tailWord_140998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140998).length < 2 ^ (prefixWord ++ tailWord_140998).sum := by decide
  have hdescent : baseEnd_140998 < baseStart_140998 := by decide
  rcases family_descends (prefixWord ++ tailWord_140998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141006 : List Nat := [4, 1, 1, 1, 3, 1, 3, 4, 3]
def baseStart_141006 : Nat := 118140960795 + 141006 * 2 ^ 59
def prefixEnd_141006 : Nat := 4983230072969 + 3 ^ 40 * 141006 * 2
def baseEnd_141006 : Nat := 32179490296880243145125

theorem tailTrace_141006 : CollatzResearch.WordTrace tailWord_141006 prefixEnd_141006 32179490296880243145125 := by
  unfold tailWord_141006
  simp only [CollatzResearch.WordTrace]
  refine ⟨642863915895852344081359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3428607551444545835100581 642863915895852344081359)
  ·
    refine ⟨964295873843778516122039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 642863915895852344081359 964295873843778516122039)
    ·
      refine ⟨1446443810765667774183059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 964295873843778516122039 1446443810765667774183059)
      ·
        refine ⟨2169665716148501661274589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1446443810765667774183059 2169665716148501661274589)
        ·
          refine ⟨813624643555688122977971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2169665716148501661274589 813624643555688122977971)
          ·
            refine ⟨1220436965333532184466957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813624643555688122977971 1220436965333532184466957)
            ·
              refine ⟨457663862000074569175109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1220436965333532184466957 457663862000074569175109)
              ·
                refine ⟨85811974125013981720333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 457663862000074569175109 85811974125013981720333)
                ·
                  refine ⟨32179490296880243145125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85811974125013981720333 32179490296880243145125)
                  ·
                    rfl

theorem cell21_141006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_141006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_141006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_141006 prefixEnd_141006 := by exact prefixLift 141006
  have htrace : WordTrace (prefixWord ++ tailWord_141006) baseStart_141006 baseEnd_141006 := by
    simpa [prefixWord, tailWord_141006, baseEnd_141006] using wordTrace_append hprefix tailTrace_141006
  have hstable : (prefixWord ++ tailWord_141006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141006).length < 2 ^ (prefixWord ++ tailWord_141006).sum := by decide
  have hdescent : baseEnd_141006 < baseStart_141006 := by decide
  rcases family_descends (prefixWord ++ tailWord_141006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141054 : List Nat := [4, 2, 2, 1, 3, 2, 1, 2, 4]
def baseStart_141054 : Nat := 118140960795 + 141054 * 2 ^ 59
def prefixEnd_141054 : Nat := 4983230072969 + 3 ^ 40 * 141054 * 2
def baseEnd_141054 : Nat := 32190444550842826345027

theorem tailTrace_141054 : CollatzResearch.WordTrace tailWord_141054 prefixEnd_141054 32190444550842826345027 := by
  unfold tailWord_141054
  simp only [CollatzResearch.WordTrace]
  refine ⟨643082753874115368799777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3429774687328615300265477 643082753874115368799777)
  ·
    refine ⟨482312065405586526599833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 643082753874115368799777 482312065405586526599833)
    ·
      refine ⟨361734049054189894949875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 482312065405586526599833 361734049054189894949875)
      ·
        refine ⟨542601073581284842424813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361734049054189894949875 542601073581284842424813)
        ·
          refine ⟨203475402592981815909305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 542601073581284842424813 203475402592981815909305)
          ·
            refine ⟨152606551944736361931979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203475402592981815909305 152606551944736361931979)
            ·
              refine ⟨228909827917104542897969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152606551944736361931979 228909827917104542897969)
              ·
                refine ⟨171682370937828407173477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228909827917104542897969 171682370937828407173477)
                ·
                  refine ⟨32190444550842826345027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171682370937828407173477 32190444550842826345027)
                  ·
                    rfl

theorem cell21_141054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 3, 2, 1, 2, 4].length) (baseStart_141054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_141054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_141054 prefixEnd_141054 := by exact prefixLift 141054
  have htrace : WordTrace (prefixWord ++ tailWord_141054) baseStart_141054 baseEnd_141054 := by
    simpa [prefixWord, tailWord_141054, baseEnd_141054] using wordTrace_append hprefix tailTrace_141054
  have hstable : (prefixWord ++ tailWord_141054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141054).length < 2 ^ (prefixWord ++ tailWord_141054).sum := by decide
  have hdescent : baseEnd_141054 < baseStart_141054 := by decide
  rcases family_descends (prefixWord ++ tailWord_141054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141248 : List Nat := [2, 1, 1, 2, 3, 2, 5, 1, 4]
def baseStart_141248 : Nat := 118140960795 + 141248 * 2 ^ 59
def prefixEnd_141248 : Nat := 4983230072969 + 3 ^ 40 * 141248 * 2
def baseEnd_141248 : Nat := 32234717993941600111297

theorem tailTrace_141248 : CollatzResearch.WordTrace tailWord_141248 prefixEnd_141248 32234717993941600111297 := by
  unfold tailWord_141248
  simp only [CollatzResearch.WordTrace]
  refine ⟨2575868896145047041480199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3434491861526729388640265 2575868896145047041480199)
  ·
    refine ⟨3863803344217570562220299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2575868896145047041480199 3863803344217570562220299)
    ·
      refine ⟨5795705016326355843330449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3863803344217570562220299 5795705016326355843330449)
      ·
        refine ⟨4346778762244766882497837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5795705016326355843330449 4346778762244766882497837)
        ·
          refine ⟨1630042035841787580936689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4346778762244766882497837 1630042035841787580936689)
          ·
            refine ⟨1222531526881340685702517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1630042035841787580936689 1222531526881340685702517)
            ·
              refine ⟨114612330645125689284611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1222531526881340685702517 114612330645125689284611)
              ·
                refine ⟨171918495967688533926917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114612330645125689284611 171918495967688533926917)
                ·
                  refine ⟨32234717993941600111297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171918495967688533926917 32234717993941600111297)
                  ·
                    rfl

theorem cell21_141248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 5, 1, 4].length) (baseStart_141248 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_141248 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_141248 prefixEnd_141248 := by exact prefixLift 141248
  have htrace : WordTrace (prefixWord ++ tailWord_141248) baseStart_141248 baseEnd_141248 := by
    simpa [prefixWord, tailWord_141248, baseEnd_141248] using wordTrace_append hprefix tailTrace_141248
  have hstable : (prefixWord ++ tailWord_141248).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141248).length < 2 ^ (prefixWord ++ tailWord_141248).sum := by decide
  have hdescent : baseEnd_141248 < baseStart_141248 := by decide
  rcases family_descends (prefixWord ++ tailWord_141248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141369 : List Nat := [1, 2, 1, 5, 3, 1, 1, 2, 5]
def baseStart_141369 : Nat := 118140960795 + 141369 * 2 ^ 59
def prefixEnd_141369 : Nat := 4983230072969 + 3 ^ 40 * 141369 * 2
def baseEnd_141369 : Nat := 32262331842472278594383

theorem tailTrace_141369 : CollatzResearch.WordTrace tailWord_141369 prefixEnd_141369 32262331842472278594383 := by
  unfold tailWord_141369
  simp only [CollatzResearch.WordTrace]
  refine ⟨5156151024851731748115161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3437434016567821165410107 5156151024851731748115161)
  ·
    refine ⟨3867113268638798811086371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5156151024851731748115161 3867113268638798811086371)
    ·
      refine ⟨5800669902958198216629557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3867113268638798811086371 5800669902958198216629557)
      ·
        refine ⟨543812803402331082809021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5800669902958198216629557 543812803402331082809021)
        ·
          refine ⟨203929801275874156053383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 543812803402331082809021 203929801275874156053383)
          ·
            refine ⟨305894701913811234080075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203929801275874156053383 305894701913811234080075)
            ·
              refine ⟨458842052870716851120113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305894701913811234080075 458842052870716851120113)
              ·
                refine ⟨344131539653037638340085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 458842052870716851120113 344131539653037638340085)
                ·
                  refine ⟨32262331842472278594383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 344131539653037638340085 32262331842472278594383)
                  ·
                    rfl

theorem cell21_141369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 1, 2, 5].length) (baseStart_141369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_141369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_141369 prefixEnd_141369 := by exact prefixLift 141369
  have htrace : WordTrace (prefixWord ++ tailWord_141369) baseStart_141369 baseEnd_141369 := by
    simpa [prefixWord, tailWord_141369, baseEnd_141369] using wordTrace_append hprefix tailTrace_141369
  have hstable : (prefixWord ++ tailWord_141369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141369).length < 2 ^ (prefixWord ++ tailWord_141369).sum := by decide
  have hdescent : baseEnd_141369 < baseStart_141369 := by decide
  rcases family_descends (prefixWord ++ tailWord_141369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141397 : List Nat := [1, 3, 2, 2, 1, 4, 8]
def baseStart_141397 : Nat := 118140960795 + 141397 * 2 ^ 59
def prefixEnd_141397 : Nat := 4983230072969 + 3 ^ 40 * 141397 * 2
def baseEnd_141397 : Nat := 3585413535994494680851

theorem tailTrace_141397 : CollatzResearch.WordTrace tailWord_141397 prefixEnd_141397 3585413535994494680851 := by
  unfold tailWord_141397
  simp only [CollatzResearch.WordTrace]
  refine ⟨5157172268750292530134445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3438114845833528353422963 5157172268750292530134445)
  ·
    refine ⟨1933939600781359698800417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5157172268750292530134445 1933939600781359698800417)
    ·
      refine ⟨1450454700586019774100313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1933939600781359698800417 1450454700586019774100313)
      ·
        refine ⟨1087841025439514830575235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1450454700586019774100313 1087841025439514830575235)
        ·
          refine ⟨1631761538159272245862853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1087841025439514830575235 1631761538159272245862853)
          ·
            refine ⟨305955288404863546099285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1631761538159272245862853 305955288404863546099285)
            ·
              refine ⟨3585413535994494680851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 305955288404863546099285 3585413535994494680851)
              ·
                rfl

theorem cell21_141397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 8].length) (baseStart_141397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_141397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_141397 prefixEnd_141397 := by exact prefixLift 141397
  have htrace : WordTrace (prefixWord ++ tailWord_141397) baseStart_141397 baseEnd_141397 := by
    simpa [prefixWord, tailWord_141397, baseEnd_141397] using wordTrace_append hprefix tailTrace_141397
  have hstable : (prefixWord ++ tailWord_141397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141397).length < 2 ^ (prefixWord ++ tailWord_141397).sum := by decide
  have hdescent : baseEnd_141397 < baseStart_141397 := by decide
  rcases family_descends (prefixWord ++ tailWord_141397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141400 : List Nat := [2, 1, 2, 2, 1, 6, 1, 2, 4]
def baseStart_141400 : Nat := 118140960795 + 141400 * 2 ^ 59
def prefixEnd_141400 : Nat := 4983230072969 + 3 ^ 40 * 141400 * 2
def baseEnd_141400 : Nat := 32269406464823113577653

theorem tailTrace_141400 : CollatzResearch.WordTrace tailWord_141400 prefixEnd_141400 32269406464823113577653 := by
  unfold tailWord_141400
  simp only [CollatzResearch.WordTrace]
  refine ⟨2578640843869712021246827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3438187791826282694995769 2578640843869712021246827)
  ·
    refine ⟨3867961265804568031870241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2578640843869712021246827 3867961265804568031870241)
    ·
      refine ⟨2900970949353426023902681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3867961265804568031870241 2900970949353426023902681)
      ·
        refine ⟨2175728212015069517927011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2900970949353426023902681 2175728212015069517927011)
        ·
          refine ⟨3263592318022604276890517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2175728212015069517927011 3263592318022604276890517)
          ·
            refine ⟨152980889907309575479243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 3263592318022604276890517 152980889907309575479243)
            ·
              refine ⟨229471334860964363218865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152980889907309575479243 229471334860964363218865)
              ·
                refine ⟨172103501145723272414149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 229471334860964363218865 172103501145723272414149)
                ·
                  refine ⟨32269406464823113577653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 172103501145723272414149 32269406464823113577653)
                  ·
                    rfl

theorem cell21_141400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 4].length) (baseStart_141400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_141400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_141400 prefixEnd_141400 := by exact prefixLift 141400
  have htrace : WordTrace (prefixWord ++ tailWord_141400) baseStart_141400 baseEnd_141400 := by
    simpa [prefixWord, tailWord_141400, baseEnd_141400] using wordTrace_append hprefix tailTrace_141400
  have hstable : (prefixWord ++ tailWord_141400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141400).length < 2 ^ (prefixWord ++ tailWord_141400).sum := by decide
  have hdescent : baseEnd_141400 < baseStart_141400 := by decide
  rcases family_descends (prefixWord ++ tailWord_141400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141473 : List Nat := [1, 2, 3, 3, 1, 2, 1, 8]
def baseStart_141473 : Nat := 118140960795 + 141473 * 2 ^ 59
def prefixEnd_141473 : Nat := 4983230072969 + 3 ^ 40 * 141473 * 2
def baseEnd_141473 : Nat := 10762022019797069620279

theorem tailTrace_141473 : CollatzResearch.WordTrace tailWord_141473 prefixEnd_141473 10762022019797069620279 := by
  unfold tailWord_141473
  simp only [CollatzResearch.WordTrace]
  refine ⟨5159944216474957509901073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3439962810983305006600715 5159944216474957509901073)
  ·
    refine ⟨3869958162356218132425805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5159944216474957509901073 3869958162356218132425805)
    ·
      refine ⟨1451234310883581799659677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3869958162356218132425805 1451234310883581799659677)
      ·
        refine ⟨544212866581343174872379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1451234310883581799659677 544212866581343174872379)
        ·
          refine ⟨816319299872014762308569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544212866581343174872379 816319299872014762308569)
          ·
            refine ⟨612239474904011071731427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 816319299872014762308569 612239474904011071731427)
            ·
              refine ⟨918359212356016607597141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612239474904011071731427 918359212356016607597141)
              ·
                refine ⟨10762022019797069620279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 918359212356016607597141 10762022019797069620279)
                ·
                  rfl

theorem cell21_141473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 1, 8].length) (baseStart_141473 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_141473 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_141473 prefixEnd_141473 := by exact prefixLift 141473
  have htrace : WordTrace (prefixWord ++ tailWord_141473) baseStart_141473 baseEnd_141473 := by
    simpa [prefixWord, tailWord_141473, baseEnd_141473] using wordTrace_append hprefix tailTrace_141473
  have hstable : (prefixWord ++ tailWord_141473).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141473).length < 2 ^ (prefixWord ++ tailWord_141473).sum := by decide
  have hdescent : baseEnd_141473 < baseStart_141473 := by decide
  rcases family_descends (prefixWord ++ tailWord_141473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141476 : List Nat := [2, 3, 1, 2, 4, 1, 1, 3, 4]
def baseStart_141476 : Nat := 118140960795 + 141476 * 2 ^ 59
def prefixEnd_141476 : Nat := 4983230072969 + 3 ^ 40 * 141476 * 2
def baseEnd_141476 : Nat := 32286750700263870310831

theorem tailTrace_141476 : CollatzResearch.WordTrace tailWord_141476 prefixEnd_141476 32286750700263870310831 := by
  unfold tailWord_141476
  simp only [CollatzResearch.WordTrace]
  refine ⟨2580026817732044511130141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3440035756976059348173521 2580026817732044511130141)
  ·
    refine ⟨967510056649516691673803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2580026817732044511130141 967510056649516691673803)
    ·
      refine ⟨1451265084974275037510705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 967510056649516691673803 1451265084974275037510705)
      ·
        refine ⟨1088448813730706278133029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1451265084974275037510705 1088448813730706278133029)
        ·
          refine ⟨204084152574507427149943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1088448813730706278133029 204084152574507427149943)
          ·
            refine ⟨306126228861761140724915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204084152574507427149943 306126228861761140724915)
            ·
              refine ⟨459189343292641711087373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306126228861761140724915 459189343292641711087373)
              ·
                refine ⟨172196003734740641657765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 459189343292641711087373 172196003734740641657765)
                ·
                  refine ⟨32286750700263870310831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 172196003734740641657765 32286750700263870310831)
                  ·
                    rfl

theorem cell21_141476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_141476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_141476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_141476 prefixEnd_141476 := by exact prefixLift 141476
  have htrace : WordTrace (prefixWord ++ tailWord_141476) baseStart_141476 baseEnd_141476 := by
    simpa [prefixWord, tailWord_141476, baseEnd_141476] using wordTrace_append hprefix tailTrace_141476
  have hstable : (prefixWord ++ tailWord_141476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141476).length < 2 ^ (prefixWord ++ tailWord_141476).sum := by decide
  have hdescent : baseEnd_141476 < baseStart_141476 := by decide
  rcases family_descends (prefixWord ++ tailWord_141476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141487 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 7]
def baseStart_141487 : Nat := 118140960795 + 141487 * 2 ^ 59
def prefixEnd_141487 : Nat := 4983230072969 + 3 ^ 40 * 141487 * 2
def baseEnd_141487 : Nat := 32289261050130295627475

theorem tailTrace_141487 : CollatzResearch.WordTrace tailWord_141487 prefixEnd_141487 32289261050130295627475 := by
  unfold tailWord_141487
  simp only [CollatzResearch.WordTrace]
  refine ⟨5160454838424237900910715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3440303225616158600607143 5160454838424237900910715)
  ·
    refine ⟨7740682257636356851366073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5160454838424237900910715 7740682257636356851366073)
    ·
      refine ⟨5805511693227267638524555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7740682257636356851366073 5805511693227267638524555)
      ·
        refine ⟨8708267539840901457786833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5805511693227267638524555 8708267539840901457786833)
        ·
          refine ⟨6531200654880676093340125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8708267539840901457786833 6531200654880676093340125)
          ·
            refine ⟨2449200245580253535002547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6531200654880676093340125 2449200245580253535002547)
            ·
              refine ⟨3673800368370380302503821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2449200245580253535002547 3673800368370380302503821)
              ·
                refine ⟨1377675138138892613438933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3673800368370380302503821 1377675138138892613438933)
                ·
                  refine ⟨32289261050130295627475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1377675138138892613438933 32289261050130295627475)
                  ·
                    rfl

theorem cell21_141487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 7].length) (baseStart_141487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_141487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_141487 prefixEnd_141487 := by exact prefixLift 141487
  have htrace : WordTrace (prefixWord ++ tailWord_141487) baseStart_141487 baseEnd_141487 := by
    simpa [prefixWord, tailWord_141487, baseEnd_141487] using wordTrace_append hprefix tailTrace_141487
  have hstable : (prefixWord ++ tailWord_141487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141487).length < 2 ^ (prefixWord ++ tailWord_141487).sum := by decide
  have hdescent : baseEnd_141487 < baseStart_141487 := by decide
  rcases family_descends (prefixWord ++ tailWord_141487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141580 : List Nat := [2, 2, 1, 2, 2, 2, 4, 1, 5]
def baseStart_141580 : Nat := 118140960795 + 141580 * 2 ^ 59
def prefixEnd_141580 : Nat := 4983230072969 + 3 ^ 40 * 141580 * 2
def baseEnd_141580 : Nat := 32310484917182800577285

theorem tailTrace_141580 : CollatzResearch.WordTrace tailWord_141580 prefixEnd_141580 32310484917182800577285 := by
  unfold tailWord_141580
  simp only [CollatzResearch.WordTrace]
  refine ⟨2581923413543657392023097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3442564551391543189364129 2581923413543657392023097)
  ·
    refine ⟨1936442560157743044017323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2581923413543657392023097 1936442560157743044017323)
    ·
      refine ⟨2904663840236614566025985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1936442560157743044017323 2904663840236614566025985)
      ·
        refine ⟨2178497880177460924519489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2904663840236614566025985 2178497880177460924519489)
        ·
          refine ⟨1633873410133095693389617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2178497880177460924519489 1633873410133095693389617)
          ·
            refine ⟨1225405057599821770042213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1633873410133095693389617 1225405057599821770042213)
            ·
              refine ⟨229763448299966581882915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1225405057599821770042213 229763448299966581882915)
              ·
                refine ⟨344645172449949872824373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229763448299966581882915 344645172449949872824373)
                ·
                  refine ⟨32310484917182800577285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 344645172449949872824373 32310484917182800577285)
                  ·
                    rfl

theorem cell21_141580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 5].length) (baseStart_141580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_141580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_141580 prefixEnd_141580 := by exact prefixLift 141580
  have htrace : WordTrace (prefixWord ++ tailWord_141580) baseStart_141580 baseEnd_141580 := by
    simpa [prefixWord, tailWord_141580, baseEnd_141580] using wordTrace_append hprefix tailTrace_141580
  have hstable : (prefixWord ++ tailWord_141580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141580).length < 2 ^ (prefixWord ++ tailWord_141580).sum := by decide
  have hdescent : baseEnd_141580 < baseStart_141580 := by decide
  rcases family_descends (prefixWord ++ tailWord_141580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141625 : List Nat := [1, 2, 1, 6, 1, 1, 9]
def baseStart_141625 : Nat := 118140960795 + 141625 * 2 ^ 59
def prefixEnd_141625 : Nat := 4983230072969 + 3 ^ 40 * 141625 * 2
def baseEnd_141625 : Nat := 3591194947808080258577

theorem tailTrace_141625 : CollatzResearch.WordTrace tailWord_141625 prefixEnd_141625 3591194947808080258577 := by
  unfold tailWord_141625
  simp only [CollatzResearch.WordTrace]
  refine ⟨5165488111924287469434329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3443658741282858312956219 5165488111924287469434329)
  ·
    refine ⟨3874116083943215602075747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5165488111924287469434329 3874116083943215602075747)
    ·
      refine ⟨5811174125914823403113621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3874116083943215602075747 5811174125914823403113621)
      ·
        refine ⟨272398787152257347020951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5811174125914823403113621 272398787152257347020951)
        ·
          refine ⟨408598180728386020531427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272398787152257347020951 408598180728386020531427)
          ·
            refine ⟨612897271092579030797141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408598180728386020531427 612897271092579030797141)
            ·
              refine ⟨3591194947808080258577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 612897271092579030797141 3591194947808080258577)
              ·
                rfl

theorem cell21_141625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 9].length) (baseStart_141625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_141625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_141625 prefixEnd_141625 := by exact prefixLift 141625
  have htrace : WordTrace (prefixWord ++ tailWord_141625) baseStart_141625 baseEnd_141625 := by
    simpa [prefixWord, tailWord_141625, baseEnd_141625] using wordTrace_append hprefix tailTrace_141625
  have hstable : (prefixWord ++ tailWord_141625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141625).length < 2 ^ (prefixWord ++ tailWord_141625).sum := by decide
  have hdescent : baseEnd_141625 < baseStart_141625 := by decide
  rcases family_descends (prefixWord ++ tailWord_141625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141746 : List Nat := [3, 2, 1, 1, 1, 1, 5, 1, 6]
def baseStart_141746 : Nat := 118140960795 + 141746 * 2 ^ 59
def prefixEnd_141746 : Nat := 4983230072969 + 3 ^ 40 * 141746 * 2
def baseEnd_141746 : Nat := 32348368378803400810279

theorem tailTrace_141746 : CollatzResearch.WordTrace tailWord_141746 prefixEnd_141746 32348368378803400810279 := by
  unfold tailWord_141746
  simp only [CollatzResearch.WordTrace]
  refine ⟨1292475336121481283647273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3446600896323950089726061 1292475336121481283647273)
  ·
    refine ⟨969356502091110962735455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1292475336121481283647273 969356502091110962735455)
    ·
      refine ⟨1454034753136666444103183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 969356502091110962735455 1454034753136666444103183)
      ·
        refine ⟨2181052129704999666154775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1454034753136666444103183 2181052129704999666154775)
        ·
          refine ⟨3271578194557499499232163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2181052129704999666154775 3271578194557499499232163)
          ·
            refine ⟨4907367291836249248848245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3271578194557499499232163 4907367291836249248848245)
            ·
              refine ⟨460065683609648367079523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4907367291836249248848245 460065683609648367079523)
              ·
                refine ⟨690098525414472550619285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460065683609648367079523 690098525414472550619285)
                ·
                  refine ⟨32348368378803400810279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 690098525414472550619285 32348368378803400810279)
                  ·
                    rfl

theorem cell21_141746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 5, 1, 6].length) (baseStart_141746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_141746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_141746 prefixEnd_141746 := by exact prefixLift 141746
  have htrace : WordTrace (prefixWord ++ tailWord_141746) baseStart_141746 baseEnd_141746 := by
    simpa [prefixWord, tailWord_141746, baseEnd_141746] using wordTrace_append hprefix tailTrace_141746
  have hstable : (prefixWord ++ tailWord_141746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141746).length < 2 ^ (prefixWord ++ tailWord_141746).sum := by decide
  have hdescent : baseEnd_141746 < baseStart_141746 := by decide
  rcases family_descends (prefixWord ++ tailWord_141746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141749 : List Nat := [1, 3, 3, 2, 3, 1, 2, 1, 5]
def baseStart_141749 : Nat := 118140960795 + 141749 * 2 ^ 59
def prefixEnd_141749 : Nat := 4983230072969 + 3 ^ 40 * 141749 * 2
def baseEnd_141749 : Nat := 32349053019676062260273

theorem tailTrace_141749 : CollatzResearch.WordTrace tailWord_141749 prefixEnd_141749 32349053019676062260273 := by
  unfold tailWord_141749
  simp only [CollatzResearch.WordTrace]
  refine ⟨5170010763475056646948301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3446673842316704431298867 5170010763475056646948301)
  ·
    refine ⟨1938754036303146242605613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5170010763475056646948301 1938754036303146242605613)
    ·
      refine ⟨727032763613679840977105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1938754036303146242605613 727032763613679840977105)
      ·
        refine ⟨545274572710259880732829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 727032763613679840977105 545274572710259880732829)
        ·
          refine ⟨204477964766347455274811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 545274572710259880732829 204477964766347455274811)
          ·
            refine ⟨306716947149521182912217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204477964766347455274811 306716947149521182912217)
            ·
              refine ⟨230037710362140887184163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 306716947149521182912217 230037710362140887184163)
              ·
                refine ⟨345056565543211330776245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230037710362140887184163 345056565543211330776245)
                ·
                  refine ⟨32349053019676062260273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 345056565543211330776245 32349053019676062260273)
                  ·
                    rfl

theorem cell21_141749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_141749 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_141749 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_141749 prefixEnd_141749 := by exact prefixLift 141749
  have htrace : WordTrace (prefixWord ++ tailWord_141749) baseStart_141749 baseEnd_141749 := by
    simpa [prefixWord, tailWord_141749, baseEnd_141749] using wordTrace_append hprefix tailTrace_141749
  have hstable : (prefixWord ++ tailWord_141749).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141749).length < 2 ^ (prefixWord ++ tailWord_141749).sum := by decide
  have hdescent : baseEnd_141749 < baseStart_141749 := by decide
  rcases family_descends (prefixWord ++ tailWord_141749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141760 : List Nat := [2, 1, 1, 2, 3, 1, 1, 10]
def baseStart_141760 : Nat := 118140960795 + 141760 * 2 ^ 59
def prefixEnd_141760 : Nat := 4983230072969 + 3 ^ 40 * 141760 * 2
def baseEnd_141760 : Nat := 10783854456514162525639

theorem tailTrace_141760 : CollatzResearch.WordTrace tailWord_141760 prefixEnd_141760 10783854456514162525639 := by
  unfold tailWord_141760
  simp only [CollatzResearch.WordTrace]
  refine ⟨2585205983217602762799367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3446941310956803683732489 2585205983217602762799367)
  ·
    refine ⟨3877808974826404144199051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2585205983217602762799367 3877808974826404144199051)
    ·
      refine ⟨5816713462239606216298577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3877808974826404144199051 5816713462239606216298577)
      ·
        refine ⟨4362535096679704662223933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5816713462239606216298577 4362535096679704662223933)
        ·
          refine ⟨1635950661254889248333975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4362535096679704662223933 1635950661254889248333975)
          ·
            refine ⟨2453925991882333872500963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1635950661254889248333975 2453925991882333872500963)
            ·
              refine ⟨3680888987823500808751445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453925991882333872500963 3680888987823500808751445)
              ·
                refine ⟨10783854456514162525639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 3680888987823500808751445 10783854456514162525639)
                ·
                  rfl

theorem cell21_141760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 1, 10].length) (baseStart_141760 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_141760 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_141760 prefixEnd_141760 := by exact prefixLift 141760
  have htrace : WordTrace (prefixWord ++ tailWord_141760) baseStart_141760 baseEnd_141760 := by
    simpa [prefixWord, tailWord_141760, baseEnd_141760] using wordTrace_append hprefix tailTrace_141760
  have hstable : (prefixWord ++ tailWord_141760).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141760).length < 2 ^ (prefixWord ++ tailWord_141760).sum := by decide
  have hdescent : baseEnd_141760 < baseStart_141760 := by decide
  rcases family_descends (prefixWord ++ tailWord_141760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141856 : List Nat := [2, 1, 1, 6, 2, 1, 2, 2, 4]
def baseStart_141856 : Nat := 118140960795 + 141856 * 2 ^ 59
def prefixEnd_141856 : Nat := 4983230072969 + 3 ^ 40 * 141856 * 2
def baseEnd_141856 : Nat := 32373471877467653976721

theorem tailTrace_141856 : CollatzResearch.WordTrace tailWord_141856 prefixEnd_141856 32373471877467653976721 := by
  unfold tailWord_141856
  simp only [CollatzResearch.WordTrace]
  refine ⟨2586956687043706960546711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3449275582724942614062281 2586956687043706960546711)
  ·
    refine ⟨3880435030565560440820067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2586956687043706960546711 3880435030565560440820067)
    ·
      refine ⟨5820652545848340661230101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3880435030565560440820067 5820652545848340661230101)
      ·
        refine ⟨272843088086640968495161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5820652545848340661230101 272843088086640968495161)
        ·
          refine ⟨204632316064980726371371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272843088086640968495161 204632316064980726371371)
          ·
            refine ⟨306948474097471089557057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204632316064980726371371 306948474097471089557057)
            ·
              refine ⟨230211355573103317167793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 306948474097471089557057 230211355573103317167793)
              ·
                refine ⟨172658516679827487875845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230211355573103317167793 172658516679827487875845)
                ·
                  refine ⟨32373471877467653976721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 172658516679827487875845 32373471877467653976721)
                  ·
                    rfl

theorem cell21_141856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 2, 2, 4].length) (baseStart_141856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_141856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_141856 prefixEnd_141856 := by exact prefixLift 141856
  have htrace : WordTrace (prefixWord ++ tailWord_141856) baseStart_141856 baseEnd_141856 := by
    simpa [prefixWord, tailWord_141856, baseEnd_141856] using wordTrace_append hprefix tailTrace_141856
  have hstable : (prefixWord ++ tailWord_141856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141856).length < 2 ^ (prefixWord ++ tailWord_141856).sum := by decide
  have hdescent : baseEnd_141856 < baseStart_141856 := by decide
  rcases family_descends (prefixWord ++ tailWord_141856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141884 : List Nat := [2, 2, 2, 2, 3, 2, 1, 2, 5]
def baseStart_141884 : Nat := 118140960795 + 141884 * 2 ^ 59
def prefixEnd_141884 : Nat := 4983230072969 + 3 ^ 40 * 141884 * 2
def baseEnd_141884 : Nat := 32379861858945827509997

theorem tailTrace_141884 : CollatzResearch.WordTrace tailWord_141884 prefixEnd_141884 32379861858945827509997 := by
  unfold tailWord_141884
  simp only [CollatzResearch.WordTrace]
  refine ⟨2587467308992987351556353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3449956411990649802075137 2587467308992987351556353)
  ·
    refine ⟨1940600481744740513667265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2587467308992987351556353 1940600481744740513667265)
    ·
      refine ⟨1455450361308555385250449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1940600481744740513667265 1455450361308555385250449)
      ·
        refine ⟨1091587770981416538937837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1455450361308555385250449 1091587770981416538937837)
        ·
          refine ⟨409345414118031202101689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1091587770981416538937837 409345414118031202101689)
          ·
            refine ⟨307009060588523401576267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 409345414118031202101689 307009060588523401576267)
            ·
              refine ⟨460513590882785102364401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 307009060588523401576267 460513590882785102364401)
              ·
                refine ⟨345385193162088826773301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 460513590882785102364401 345385193162088826773301)
                ·
                  refine ⟨32379861858945827509997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 345385193162088826773301 32379861858945827509997)
                  ·
                    rfl

theorem cell21_141884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 5].length) (baseStart_141884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_141884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_141884 prefixEnd_141884 := by exact prefixLift 141884
  have htrace : WordTrace (prefixWord ++ tailWord_141884) baseStart_141884 baseEnd_141884 := by
    simpa [prefixWord, tailWord_141884, baseEnd_141884] using wordTrace_append hprefix tailTrace_141884
  have hstable : (prefixWord ++ tailWord_141884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141884).length < 2 ^ (prefixWord ++ tailWord_141884).sum := by decide
  have hdescent : baseEnd_141884 < baseStart_141884 := by decide
  rcases family_descends (prefixWord ++ tailWord_141884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141943 : List Nat := [1, 1, 3, 1, 1, 3, 4, 2, 5]
def baseStart_141943 : Nat := 118140960795 + 141943 * 2 ^ 59
def prefixEnd_141943 : Nat := 4983230072969 + 3 ^ 40 * 141943 * 2
def baseEnd_141943 : Nat := 32393326462774836026543

theorem tailTrace_141943 : CollatzResearch.WordTrace tailWord_141943 prefixEnd_141943 32393326462774836026543 := by
  unfold tailWord_141943
  simp only [CollatzResearch.WordTrace]
  refine ⟨5177086524772227779510483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3451391016514818519673655 5177086524772227779510483)
  ·
    refine ⟨7765629787158341669265725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5177086524772227779510483 7765629787158341669265725)
    ·
      refine ⟨2912111170184378125974647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7765629787158341669265725 2912111170184378125974647)
      ·
        refine ⟨4368166755276567188961971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2912111170184378125974647 4368166755276567188961971)
        ·
          refine ⟨6552250132914850783442957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4368166755276567188961971 6552250132914850783442957)
          ·
            refine ⟨2457093799843069043791109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6552250132914850783442957 2457093799843069043791109)
            ·
              refine ⟨460705087470575445710833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2457093799843069043791109 460705087470575445710833)
              ·
                refine ⟨345528815602931584283125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 460705087470575445710833 345528815602931584283125)
                ·
                  refine ⟨32393326462774836026543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 345528815602931584283125 32393326462774836026543)
                  ·
                    rfl

theorem cell21_141943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 4, 2, 5].length) (baseStart_141943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_141943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_141943 prefixEnd_141943 := by exact prefixLift 141943
  have htrace : WordTrace (prefixWord ++ tailWord_141943) baseStart_141943 baseEnd_141943 := by
    simpa [prefixWord, tailWord_141943, baseEnd_141943] using wordTrace_append hprefix tailTrace_141943
  have hstable : (prefixWord ++ tailWord_141943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141943).length < 2 ^ (prefixWord ++ tailWord_141943).sum := by decide
  have hdescent : baseEnd_141943 < baseStart_141943 := by decide
  rcases family_descends (prefixWord ++ tailWord_141943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141977 : List Nat := [1, 2, 1, 2, 1, 2, 7, 2, 3]
def baseStart_141977 : Nat := 118140960795 + 141977 * 2 ^ 59
def prefixEnd_141977 : Nat := 4983230072969 + 3 ^ 40 * 141977 * 2
def baseEnd_141977 : Nat := 32401085725998332459807

theorem tailTrace_141977 : CollatzResearch.WordTrace tailWord_141977 prefixEnd_141977 32401085725998332459807 := by
  unfold tailWord_141977
  simp only [CollatzResearch.WordTrace]
  refine ⟨5178326606649051586248185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3452217737766034390832123 5178326606649051586248185)
  ·
    refine ⟨3883744954986788689686139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5178326606649051586248185 3883744954986788689686139)
    ·
      refine ⟨5825617432480183034529209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3883744954986788689686139 5825617432480183034529209)
      ·
        refine ⟨4369213074360137275896907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5825617432480183034529209 4369213074360137275896907)
        ·
          refine ⟨6553819611540205913845361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4369213074360137275896907 6553819611540205913845361)
          ·
            refine ⟨4915364708655154435384021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6553819611540205913845361 4915364708655154435384021)
            ·
              refine ⟨115203860359105182079313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 4915364708655154435384021 115203860359105182079313)
              ·
                refine ⟨86402895269328886559485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115203860359105182079313 86402895269328886559485)
                ·
                  refine ⟨32401085725998332459807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86402895269328886559485 32401085725998332459807)
                  ·
                    rfl

theorem cell21_141977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 7, 2, 3].length) (baseStart_141977 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_141977 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_141977 prefixEnd_141977 := by exact prefixLift 141977
  have htrace : WordTrace (prefixWord ++ tailWord_141977) baseStart_141977 baseEnd_141977 := by
    simpa [prefixWord, tailWord_141977, baseEnd_141977] using wordTrace_append hprefix tailTrace_141977
  have hstable : (prefixWord ++ tailWord_141977).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141977).length < 2 ^ (prefixWord ++ tailWord_141977).sum := by decide
  have hdescent : baseEnd_141977 < baseStart_141977 := by decide
  rcases family_descends (prefixWord ++ tailWord_141977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142005 : List Nat := [1, 3, 3, 3, 1, 1, 2, 7]
def baseStart_142005 : Nat := 118140960795 + 142005 * 2 ^ 59
def prefixEnd_142005 : Nat := 4983230072969 + 3 ^ 40 * 142005 * 2
def baseEnd_142005 : Nat := 10802491902492168664361

theorem tailTrace_142005 : CollatzResearch.WordTrace tailWord_142005 prefixEnd_142005 10802491902492168664361 := by
  unfold tailWord_142005
  simp only [CollatzResearch.WordTrace]
  refine ⟨5179347850547612368267469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3452898567031741578844979 5179347850547612368267469)
  ·
    refine ⟨1942255443955354638100301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5179347850547612368267469 1942255443955354638100301)
    ·
      refine ⟨728345791483257989287613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1942255443955354638100301 728345791483257989287613)
      ·
        refine ⟨273129671806221745982855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 728345791483257989287613 273129671806221745982855)
        ·
          refine ⟨409694507709332618974283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 273129671806221745982855 409694507709332618974283)
          ·
            refine ⟨614541761563998928461425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409694507709332618974283 614541761563998928461425)
            ·
              refine ⟨460906321172999196346069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 614541761563998928461425 460906321172999196346069)
              ·
                refine ⟨10802491902492168664361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 460906321172999196346069 10802491902492168664361)
                ·
                  rfl

theorem cell21_142005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 7].length) (baseStart_142005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_142005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_142005 prefixEnd_142005 := by exact prefixLift 142005
  have htrace : WordTrace (prefixWord ++ tailWord_142005) baseStart_142005 baseEnd_142005 := by
    simpa [prefixWord, tailWord_142005, baseEnd_142005] using wordTrace_append hprefix tailTrace_142005
  have hstable : (prefixWord ++ tailWord_142005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142005).length < 2 ^ (prefixWord ++ tailWord_142005).sum := by decide
  have hdescent : baseEnd_142005 < baseStart_142005 := by decide
  rcases family_descends (prefixWord ++ tailWord_142005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142022 : List Nat := [6, 1, 2, 1, 11]
def baseStart_142022 : Nat := 118140960795 + 142022 * 2 ^ 59
def prefixEnd_142022 : Nat := 4983230072969 + 3 ^ 40 * 142022 * 2
def baseEnd_142022 : Nat := 400140189371459928515

theorem tailTrace_142022 : CollatzResearch.WordTrace tailWord_142022 prefixEnd_142022 400140189371459928515 := by
  unfold tailWord_142022
  simp only [CollatzResearch.WordTrace]
  refine ⟨161873996608938258488635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3453311927657349514424213 161873996608938258488635)
  ·
    refine ⟨242810994913407387732953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161873996608938258488635 242810994913407387732953)
    ·
      refine ⟨182108246185055540799715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242810994913407387732953 182108246185055540799715)
      ·
        refine ⟨273162369277583311199573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182108246185055540799715 273162369277583311199573)
        ·
          refine ⟨400140189371459928515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 273162369277583311199573 400140189371459928515)
          ·
            rfl

theorem cell21_142022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 11].length) (baseStart_142022 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_142022 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_142022 prefixEnd_142022 := by exact prefixLift 142022
  have htrace : WordTrace (prefixWord ++ tailWord_142022) baseStart_142022 baseEnd_142022 := by
    simpa [prefixWord, tailWord_142022, baseEnd_142022] using wordTrace_append hprefix tailTrace_142022
  have hstable : (prefixWord ++ tailWord_142022).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142022).length < 2 ^ (prefixWord ++ tailWord_142022).sum := by decide
  have hdescent : baseEnd_142022 < baseStart_142022 := by decide
  rcases family_descends (prefixWord ++ tailWord_142022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142095 : List Nat := [1, 1, 2, 1, 1, 1, 8, 1, 5]
def baseStart_142095 : Nat := 118140960795 + 142095 * 2 ^ 59
def prefixEnd_142095 : Nat := 4983230072969 + 3 ^ 40 * 142095 * 2
def baseEnd_142095 : Nat := 32428014933656349492899

theorem tailTrace_142095 : CollatzResearch.WordTrace tailWord_142095 prefixEnd_142095 32428014933656349492899 := by
  unfold tailWord_142095
  simp only [CollatzResearch.WordTrace]
  refine ⟨5182630420221557739043739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3455086946814371826029159 5182630420221557739043739)
  ·
    refine ⟨7773945630332336608565609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5182630420221557739043739 7773945630332336608565609)
    ·
      refine ⟨5830459222749252456424207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7773945630332336608565609 5830459222749252456424207)
      ·
        refine ⟨8745688834123878684636311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5830459222749252456424207 8745688834123878684636311)
        ·
          refine ⟨13118533251185818026954467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8745688834123878684636311 13118533251185818026954467)
          ·
            refine ⟨19677799876778727040431701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13118533251185818026954467 19677799876778727040431701)
            ·
              refine ⟨230599217306000707505059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 19677799876778727040431701 230599217306000707505059)
              ·
                refine ⟨345898825959001061257589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230599217306000707505059 345898825959001061257589)
                ·
                  refine ⟨32428014933656349492899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 345898825959001061257589 32428014933656349492899)
                  ·
                    rfl

theorem cell21_142095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 8, 1, 5].length) (baseStart_142095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_142095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_142095 prefixEnd_142095 := by exact prefixLift 142095
  have htrace : WordTrace (prefixWord ++ tailWord_142095) baseStart_142095 baseEnd_142095 := by
    simpa [prefixWord, tailWord_142095, baseEnd_142095] using wordTrace_append hprefix tailTrace_142095
  have hstable : (prefixWord ++ tailWord_142095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142095).length < 2 ^ (prefixWord ++ tailWord_142095).sum := by decide
  have hdescent : baseEnd_142095 < baseStart_142095 := by decide
  rcases family_descends (prefixWord ++ tailWord_142095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142188 : List Nat := [2, 2, 1, 1, 4, 1, 2, 5, 3]
def baseStart_142188 : Nat := 118140960795 + 142188 * 2 ^ 59
def prefixEnd_142188 : Nat := 4983230072969 + 3 ^ 40 * 142188 * 2
def baseEnd_142188 : Nat := 32449238800708854442709

theorem tailTrace_142188 : CollatzResearch.WordTrace tailWord_142188 prefixEnd_142188 32449238800708854442709 := by
  unfold tailWord_142188
  simp only [CollatzResearch.WordTrace]
  refine ⟨2593011204442317311089609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3457348272589756414786145 2593011204442317311089609)
  ·
    refine ⟨1944758403331737983317207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2593011204442317311089609 1944758403331737983317207)
    ·
      refine ⟨2917137604997606974975811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1944758403331737983317207 2917137604997606974975811)
      ·
        refine ⟨4375706407496410462463717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2917137604997606974975811 4375706407496410462463717)
        ·
          refine ⟨820444951405576961711947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4375706407496410462463717 820444951405576961711947)
          ·
            refine ⟨1230667427108365442567921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 820444951405576961711947 1230667427108365442567921)
            ·
              refine ⟨923000570331274081925941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1230667427108365442567921 923000570331274081925941)
              ·
                refine ⟨86531303468556945180557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 923000570331274081925941 86531303468556945180557)
                ·
                  refine ⟨32449238800708854442709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86531303468556945180557 32449238800708854442709)
                  ·
                    rfl

theorem cell21_142188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 2, 5, 3].length) (baseStart_142188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_142188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_142188 prefixEnd_142188 := by exact prefixLift 142188
  have htrace : WordTrace (prefixWord ++ tailWord_142188) baseStart_142188 baseEnd_142188 := by
    simpa [prefixWord, tailWord_142188, baseEnd_142188] using wordTrace_append hprefix tailTrace_142188
  have hstable : (prefixWord ++ tailWord_142188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142188).length < 2 ^ (prefixWord ++ tailWord_142188).sum := by decide
  have hdescent : baseEnd_142188 < baseStart_142188 := by decide
  rcases family_descends (prefixWord ++ tailWord_142188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142205 : List Nat := [1, 4, 1, 1, 2, 1, 6, 2, 3]
def baseStart_142205 : Nat := 118140960795 + 142205 * 2 ^ 59
def prefixEnd_142205 : Nat := 4983230072969 + 3 ^ 40 * 142205 * 2
def baseEnd_142205 : Nat := 32453118432320602659341

theorem tailTrace_142205 : CollatzResearch.WordTrace tailWord_142205 prefixEnd_142205 32453118432320602659341 := by
  unfold tailWord_142205
  simp only [CollatzResearch.WordTrace]
  refine ⟨5186642449823046525548069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3457761633215364350365379 5186642449823046525548069)
  ·
    refine ⟨972495459341821223540263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5186642449823046525548069 972495459341821223540263)
    ·
      refine ⟨1458743189012731835310395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 972495459341821223540263 1458743189012731835310395)
      ·
        refine ⟨2188114783519097752965593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1458743189012731835310395 2188114783519097752965593)
        ·
          refine ⟨1641086087639323314724195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2188114783519097752965593 1641086087639323314724195)
          ·
            refine ⟨2461629131458984972086293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1641086087639323314724195 2461629131458984972086293)
            ·
              refine ⟨115388865537139920566545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2461629131458984972086293 115388865537139920566545)
              ·
                refine ⟨86541649152854940424909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 115388865537139920566545 86541649152854940424909)
                ·
                  refine ⟨32453118432320602659341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86541649152854940424909 32453118432320602659341)
                  ·
                    rfl

theorem cell21_142205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 6, 2, 3].length) (baseStart_142205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_142205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_142205 prefixEnd_142205 := by exact prefixLift 142205
  have htrace : WordTrace (prefixWord ++ tailWord_142205) baseStart_142205 baseEnd_142205 := by
    simpa [prefixWord, tailWord_142205, baseEnd_142205] using wordTrace_append hprefix tailTrace_142205
  have hstable : (prefixWord ++ tailWord_142205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142205).length < 2 ^ (prefixWord ++ tailWord_142205).sum := by decide
  have hdescent : baseEnd_142205 < baseStart_142205 := by decide
  rcases family_descends (prefixWord ++ tailWord_142205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142253 : List Nat := [1, 5, 2, 3, 1, 2, 1, 2, 4]
def baseStart_142253 : Nat := 118140960795 + 142253 * 2 ^ 59
def prefixEnd_142253 : Nat := 4983230072969 + 3 ^ 40 * 142253 * 2
def baseEnd_142253 : Nat := 32464072686283185859243

theorem tailTrace_142253 : CollatzResearch.WordTrace tailWord_142253 prefixEnd_142253 32464072686283185859243 := by
  unfold tailWord_142253
  simp only [CollatzResearch.WordTrace]
  refine ⟨5188393153649150723295413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3458928769099433815530275 5188393153649150723295413)
  ·
    refine ⟨486411858154607880308945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5188393153649150723295413 486411858154607880308945)
    ·
      refine ⟨364808893615955910231709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 486411858154607880308945 364808893615955910231709)
      ·
        refine ⟨136803335105983466336891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 364808893615955910231709 136803335105983466336891)
        ·
          refine ⟨205205002658975199505337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136803335105983466336891 205205002658975199505337)
          ·
            refine ⟨153903751994231399629003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 205205002658975199505337 153903751994231399629003)
            ·
              refine ⟨230855627991347099443505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153903751994231399629003 230855627991347099443505)
              ·
                refine ⟨173141720993510324582629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 230855627991347099443505 173141720993510324582629)
                ·
                  refine ⟨32464072686283185859243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 173141720993510324582629 32464072686283185859243)
                  ·
                    rfl

theorem cell21_142253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_142253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_142253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_142253 prefixEnd_142253 := by exact prefixLift 142253
  have htrace : WordTrace (prefixWord ++ tailWord_142253) baseStart_142253 baseEnd_142253 := by
    simpa [prefixWord, tailWord_142253, baseEnd_142253] using wordTrace_append hprefix tailTrace_142253
  have hstable : (prefixWord ++ tailWord_142253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142253).length < 2 ^ (prefixWord ++ tailWord_142253).sum := by decide
  have hdescent : baseEnd_142253 < baseStart_142253 := by decide
  rcases family_descends (prefixWord ++ tailWord_142253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142264 : List Nat := [2, 1, 2, 1, 2, 4, 2, 4, 3]
def baseStart_142264 : Nat := 118140960795 + 142264 * 2 ^ 59
def prefixEnd_142264 : Nat := 4983230072969 + 3 ^ 40 * 142264 * 2
def baseEnd_142264 : Nat := 32466583036149611175887

theorem tailTrace_142264 : CollatzResearch.WordTrace tailWord_142264 prefixEnd_142264 32466583036149611175887 := by
  unfold tailWord_142264
  simp only [CollatzResearch.WordTrace]
  refine ⟨2594397178304649800972923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3459196237739533067963897 2594397178304649800972923)
  ·
    refine ⟨3891595767456974701459385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2594397178304649800972923 3891595767456974701459385)
    ·
      refine ⟨2918696825592731026094539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3891595767456974701459385 2918696825592731026094539)
      ·
        refine ⟨4378045238389096539141809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2918696825592731026094539 4378045238389096539141809)
        ·
          refine ⟨3283533928791822404356357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4378045238389096539141809 3283533928791822404356357)
          ·
            refine ⟨615662611648466700816817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3283533928791822404356357 615662611648466700816817)
            ·
              refine ⟨461746958736350025612613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 615662611648466700816817 461746958736350025612613)
              ·
                refine ⟨86577554763065629802365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 461746958736350025612613 86577554763065629802365)
                ·
                  refine ⟨32466583036149611175887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86577554763065629802365 32466583036149611175887)
                  ·
                    rfl

theorem cell21_142264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 2, 4, 3].length) (baseStart_142264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_142264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_142264 prefixEnd_142264 := by exact prefixLift 142264
  have htrace : WordTrace (prefixWord ++ tailWord_142264) baseStart_142264 baseEnd_142264 := by
    simpa [prefixWord, tailWord_142264, baseEnd_142264] using wordTrace_append hprefix tailTrace_142264
  have hstable : (prefixWord ++ tailWord_142264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142264).length < 2 ^ (prefixWord ++ tailWord_142264).sum := by decide
  have hdescent : baseEnd_142264 < baseStart_142264 := by decide
  rcases family_descends (prefixWord ++ tailWord_142264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142368 : List Nat := [2, 1, 1, 7, 10]
def baseStart_142368 : Nat := 118140960795 + 142368 * 2 ^ 59
def prefixEnd_142368 : Nat := 4983230072969 + 3 ^ 40 * 142368 * 2
def baseEnd_142368 : Nat := 401115027815661005461

theorem tailTrace_142368 : CollatzResearch.WordTrace tailWord_142368 prefixEnd_142368 401115027815661005461 := by
  unfold tailWord_142368
  simp only [CollatzResearch.WordTrace]
  refine ⟨2596293774116262681865879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3461725032155016909154505 2596293774116262681865879)
  ·
    refine ⟨3894440661174394022798819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2596293774116262681865879 3894440661174394022798819)
    ·
      refine ⟨5841660991761591034198229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3894440661174394022798819 5841660991761591034198229)
      ·
        refine ⟨136913929494412289864021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 5841660991761591034198229 136913929494412289864021)
        ·
          refine ⟨401115027815661005461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 136913929494412289864021 401115027815661005461)
          ·
            rfl

theorem cell21_142368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 10].length) (baseStart_142368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_142368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_142368 prefixEnd_142368 := by exact prefixLift 142368
  have htrace : WordTrace (prefixWord ++ tailWord_142368) baseStart_142368 baseEnd_142368 := by
    simpa [prefixWord, tailWord_142368, baseEnd_142368] using wordTrace_append hprefix tailTrace_142368
  have hstable : (prefixWord ++ tailWord_142368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142368).length < 2 ^ (prefixWord ++ tailWord_142368).sum := by decide
  have hdescent : baseEnd_142368 < baseStart_142368 := by decide
  rcases family_descends (prefixWord ++ tailWord_142368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142422 : List Nat := [5, 2, 2, 1, 3, 1, 1, 2, 4]
def baseStart_142422 : Nat := 118140960795 + 142422 * 2 ^ 59
def prefixEnd_142422 : Nat := 4983230072969 + 3 ^ 40 * 142422 * 2
def baseEnd_142422 : Nat := 32502640788776447542231

theorem tailTrace_142422 : CollatzResearch.WordTrace tailWord_142422 prefixEnd_142422 32502640788776447542231 := by
  unfold tailWord_142422
  simp only [CollatzResearch.WordTrace]
  refine ⟨324659818127305786637345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3463038060024595057465013 324659818127305786637345)
  ·
    refine ⟨243494863595479339978009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 324659818127305786637345 243494863595479339978009)
    ·
      refine ⟨182621147696609504983507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 243494863595479339978009 182621147696609504983507)
      ·
        refine ⟨273931721544914257475261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 182621147696609504983507 273931721544914257475261)
        ·
          refine ⟨102724395579342846553223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 273931721544914257475261 102724395579342846553223)
          ·
            refine ⟨154086593369014269829835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102724395579342846553223 154086593369014269829835)
            ·
              refine ⟨231129890053521404744753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154086593369014269829835 231129890053521404744753)
              ·
                refine ⟨173347417540141053558565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 231129890053521404744753 173347417540141053558565)
                ·
                  refine ⟨32502640788776447542231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 173347417540141053558565 32502640788776447542231)
                  ·
                    rfl

theorem cell21_142422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_142422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_142422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_142422 prefixEnd_142422 := by exact prefixLift 142422
  have htrace : WordTrace (prefixWord ++ tailWord_142422) baseStart_142422 baseEnd_142422 := by
    simpa [prefixWord, tailWord_142422, baseEnd_142422] using wordTrace_append hprefix tailTrace_142422
  have hstable : (prefixWord ++ tailWord_142422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142422).length < 2 ^ (prefixWord ++ tailWord_142422).sum := by decide
  have hdescent : baseEnd_142422 < baseStart_142422 := by decide
  rcases family_descends (prefixWord ++ tailWord_142422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142492 : List Nat := [2, 2, 3, 2, 1, 4, 1, 1, 5]
def baseStart_142492 : Nat := 118140960795 + 142492 * 2 ^ 59
def prefixEnd_142492 : Nat := 4983230072969 + 3 ^ 40 * 142492 * 2
def baseEnd_142492 : Nat := 32518615742471881375421

theorem tailTrace_142492 : CollatzResearch.WordTrace tailWord_142492 prefixEnd_142492 32518615742471881375421 := by
  unfold tailWord_142492
  simp only [CollatzResearch.WordTrace]
  refine ⟨2598555099891647270622865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3464740133188863027497153 2598555099891647270622865)
  ·
    refine ⟨1948916324918735452967149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2598555099891647270622865 1948916324918735452967149)
    ·
      refine ⟨730843621844525794862681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1948916324918735452967149 730843621844525794862681)
      ·
        refine ⟨548132716383394346147011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 730843621844525794862681 548132716383394346147011)
        ·
          refine ⟨822199074575091519220517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 548132716383394346147011 822199074575091519220517)
          ·
            refine ⟨154162326482829659853847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 822199074575091519220517 154162326482829659853847)
            ·
              refine ⟨231243489724244489780771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154162326482829659853847 231243489724244489780771)
              ·
                refine ⟨346865234586366734671157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 231243489724244489780771 346865234586366734671157)
                ·
                  refine ⟨32518615742471881375421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 346865234586366734671157 32518615742471881375421)
                  ·
                    rfl

theorem cell21_142492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_142492 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_142492 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_142492 prefixEnd_142492 := by exact prefixLift 142492
  have htrace : WordTrace (prefixWord ++ tailWord_142492) baseStart_142492 baseEnd_142492 := by
    simpa [prefixWord, tailWord_142492, baseEnd_142492] using wordTrace_append hprefix tailTrace_142492
  have hstable : (prefixWord ++ tailWord_142492).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142492).length < 2 ^ (prefixWord ++ tailWord_142492).sum := by decide
  have hdescent : baseEnd_142492 < baseStart_142492 := by decide
  rcases family_descends (prefixWord ++ tailWord_142492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142596 : List Nat := [2, 3, 2, 2, 2, 2, 8]
def baseStart_142596 : Nat := 118140960795 + 142596 * 2 ^ 59
def prefixEnd_142596 : Nat := 4983230072969 + 3 ^ 40 * 142596 * 2
def baseEnd_142596 : Nat := 3615816662154534626875

theorem tailTrace_142596 : CollatzResearch.WordTrace tailWord_142596 prefixEnd_142596 3615816662154534626875 := by
  unfold tailWord_142596
  simp only [CollatzResearch.WordTrace]
  refine ⟨2600451695703260151515821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3467268927604346868687761 2600451695703260151515821)
  ·
    refine ⟨975169385888722556818433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2600451695703260151515821 975169385888722556818433)
    ·
      refine ⟨731377039416541917613825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 975169385888722556818433 731377039416541917613825)
      ·
        refine ⟨548532779562406438210369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 731377039416541917613825 548532779562406438210369)
        ·
          refine ⟨411399584671804828657777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 548532779562406438210369 411399584671804828657777)
          ·
            refine ⟨308549688503853621493333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 411399584671804828657777 308549688503853621493333)
            ·
              refine ⟨3615816662154534626875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 308549688503853621493333 3615816662154534626875)
              ·
                rfl

theorem cell21_142596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 8].length) (baseStart_142596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_142596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_142596 prefixEnd_142596 := by exact prefixLift 142596
  have htrace : WordTrace (prefixWord ++ tailWord_142596) baseStart_142596 baseEnd_142596 := by
    simpa [prefixWord, tailWord_142596, baseEnd_142596] using wordTrace_append hprefix tailTrace_142596
  have hstable : (prefixWord ++ tailWord_142596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142596).length < 2 ^ (prefixWord ++ tailWord_142596).sum := by decide
  have hdescent : baseEnd_142596 < baseStart_142596 := by decide
  rcases family_descends (prefixWord ++ tailWord_142596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142641 : List Nat := [1, 2, 2, 3, 3, 1, 1, 2, 6]
def baseStart_142641 : Nat := 118140960795 + 142641 * 2 ^ 59
def prefixEnd_142641 : Nat := 4983230072969 + 3 ^ 40 * 142641 * 2
def baseEnd_142641 : Nat := 32552619572480733391783

theorem tailTrace_142641 : CollatzResearch.WordTrace tailWord_142641 prefixEnd_142641 32552619572480733391783 := by
  unfold tailWord_142641
  simp only [CollatzResearch.WordTrace]
  refine ⟨5202544676243492988419777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3468363117495661992279851 5202544676243492988419777)
  ·
    refine ⟨3901908507182619741314833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5202544676243492988419777 3901908507182619741314833)
    ·
      refine ⟨2926431380386964805986125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3901908507182619741314833 2926431380386964805986125)
      ·
        refine ⟨1097411767645111802244797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2926431380386964805986125 1097411767645111802244797)
        ·
          refine ⟨411529412866916925841799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1097411767645111802244797 411529412866916925841799)
          ·
            refine ⟨617294119300375388762699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 411529412866916925841799 617294119300375388762699)
            ·
              refine ⟨925941178950563083144049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 617294119300375388762699 925941178950563083144049)
              ·
                refine ⟨694455884212922312358037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 925941178950563083144049 694455884212922312358037)
                ·
                  refine ⟨32552619572480733391783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 694455884212922312358037 32552619572480733391783)
                  ·
                    rfl

theorem cell21_142641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 1, 2, 6].length) (baseStart_142641 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_142641 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_142641 prefixEnd_142641 := by exact prefixLift 142641
  have htrace : WordTrace (prefixWord ++ tailWord_142641) baseStart_142641 baseEnd_142641 := by
    simpa [prefixWord, tailWord_142641, baseEnd_142641] using wordTrace_append hprefix tailTrace_142641
  have hstable : (prefixWord ++ tailWord_142641).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142641).length < 2 ^ (prefixWord ++ tailWord_142641).sum := by decide
  have hdescent : baseEnd_142641 < baseStart_142641 := by decide
  rcases family_descends (prefixWord ++ tailWord_142641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142655 : List Nat := [1, 1, 2, 2, 4, 2, 9]
def baseStart_142655 : Nat := 118140960795 + 142655 * 2 ^ 59
def prefixEnd_142655 : Nat := 4983230072969 + 3 ^ 40 * 142655 * 2
def baseEnd_142655 : Nat := 3617312729246646684269

theorem tailTrace_142655 : CollatzResearch.WordTrace tailWord_142655 prefixEnd_142655 3617312729246646684269 := by
  unfold tailWord_142655
  simp only [CollatzResearch.WordTrace]
  refine ⟨5203055298192773379429419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3468703532128515586286279 5203055298192773379429419)
  ·
    refine ⟨7804582947289160069144129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5203055298192773379429419 7804582947289160069144129)
    ·
      refine ⟨5853437210466870051858097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7804582947289160069144129 5853437210466870051858097)
      ·
        refine ⟨4390077907850152538893573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5853437210466870051858097 4390077907850152538893573)
        ·
          refine ⟨823139607721903601042545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4390077907850152538893573 823139607721903601042545)
          ·
            refine ⟨617354705791427700781909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 823139607721903601042545 617354705791427700781909)
            ·
              refine ⟨3617312729246646684269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 617354705791427700781909 3617312729246646684269)
              ·
                rfl

theorem cell21_142655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 9].length) (baseStart_142655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_142655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_142655 prefixEnd_142655 := by exact prefixLift 142655
  have htrace : WordTrace (prefixWord ++ tailWord_142655) baseStart_142655 baseEnd_142655 := by
    simpa [prefixWord, tailWord_142655, baseEnd_142655] using wordTrace_append hprefix tailTrace_142655
  have hstable : (prefixWord ++ tailWord_142655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142655).length < 2 ^ (prefixWord ++ tailWord_142655).sum := by decide
  have hdescent : baseEnd_142655 < baseStart_142655 := by decide
  rcases family_descends (prefixWord ++ tailWord_142655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142703 : List Nat := [1, 1, 2, 1, 3, 1, 4, 5, 3]
def baseStart_142703 : Nat := 118140960795 + 142703 * 2 ^ 59
def prefixEnd_142703 : Nat := 4983230072969 + 3 ^ 40 * 142703 * 2
def baseEnd_142703 : Nat := 32566768817182403358323

theorem tailTrace_142703 : CollatzResearch.WordTrace tailWord_142703 prefixEnd_142703 32566768817182403358323 := by
  unfold tailWord_142703
  simp only [CollatzResearch.WordTrace]
  refine ⟨5204806002018877577176763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3469870668012585051451175 5204806002018877577176763)
  ·
    refine ⟨7807209003028316365765145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5204806002018877577176763 7807209003028316365765145)
    ·
      refine ⟨5855406752271237274323859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7807209003028316365765145 5855406752271237274323859)
      ·
        refine ⟨8783110128406855911485789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5855406752271237274323859 8783110128406855911485789)
        ·
          refine ⟨3293666298152570966807171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8783110128406855911485789 3293666298152570966807171)
          ·
            refine ⟨4940499447228856450210757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3293666298152570966807171 4940499447228856450210757)
            ·
              refine ⟨926343646355410584414517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4940499447228856450210757 926343646355410584414517)
              ·
                refine ⟨86844716845819742288861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 926343646355410584414517 86844716845819742288861)
                ·
                  refine ⟨32566768817182403358323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86844716845819742288861 32566768817182403358323)
                  ·
                    rfl

theorem cell21_142703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 5, 3].length) (baseStart_142703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_142703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_142703 prefixEnd_142703 := by exact prefixLift 142703
  have htrace : WordTrace (prefixWord ++ tailWord_142703) baseStart_142703 baseEnd_142703 := by
    simpa [prefixWord, tailWord_142703, baseEnd_142703] using wordTrace_append hprefix tailTrace_142703
  have hstable : (prefixWord ++ tailWord_142703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142703).length < 2 ^ (prefixWord ++ tailWord_142703).sum := by decide
  have hdescent : baseEnd_142703 < baseStart_142703 := by decide
  rcases family_descends (prefixWord ++ tailWord_142703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142813 : List Nat := [1, 4, 3, 1, 1, 4, 1, 3, 3]
def baseStart_142813 : Nat := 118140960795 + 142813 * 2 ^ 59
def prefixEnd_142813 : Nat := 4983230072969 + 3 ^ 40 * 142813 * 2
def baseEnd_142813 : Nat := 32591872315846656524765

theorem tailTrace_142813 : CollatzResearch.WordTrace tailWord_142813 prefixEnd_142813 32591872315846656524765 := by
  unfold tailWord_142813
  simp only [CollatzResearch.WordTrace]
  refine ⟨5208818031620366363681093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3472545354413577575787395 5208818031620366363681093)
  ·
    refine ⟨976653380928818693190205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5208818031620366363681093 976653380928818693190205)
    ·
      refine ⟨366245017848307009946327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 976653380928818693190205 366245017848307009946327)
      ·
        refine ⟨549367526772460514919491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 366245017848307009946327 549367526772460514919491)
        ·
          refine ⟨824051290158690772379237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 549367526772460514919491 824051290158690772379237)
          ·
            refine ⟨154509616904754519821107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 824051290158690772379237 154509616904754519821107)
            ·
              refine ⟨231764425357131779731661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 154509616904754519821107 231764425357131779731661)
              ·
                refine ⟨86911659508924417399373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 231764425357131779731661 86911659508924417399373)
                ·
                  refine ⟨32591872315846656524765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86911659508924417399373 32591872315846656524765)
                  ·
                    rfl

theorem cell21_142813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_142813 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_142813 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_142813 prefixEnd_142813 := by exact prefixLift 142813
  have htrace : WordTrace (prefixWord ++ tailWord_142813) baseStart_142813 baseEnd_142813 := by
    simpa [prefixWord, tailWord_142813, baseEnd_142813] using wordTrace_append hprefix tailTrace_142813
  have hstable : (prefixWord ++ tailWord_142813).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142813).length < 2 ^ (prefixWord ++ tailWord_142813).sum := by decide
  have hdescent : baseEnd_142813 < baseStart_142813 := by decide
  rcases family_descends (prefixWord ++ tailWord_142813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142883 : List Nat := [1, 1, 1, 4, 5, 9]
def baseStart_142883 : Nat := 118140960795 + 142883 * 2 ^ 59
def prefixEnd_142883 : Nat := 4983230072969 + 3 ^ 40 * 142883 * 2
def baseEnd_142883 : Nat := 1207698047020077420665

theorem tailTrace_142883 : CollatzResearch.WordTrace tailWord_142883 prefixEnd_142883 1207698047020077420665 := by
  unfold tailWord_142883
  simp only [CollatzResearch.WordTrace]
  refine ⟨5211371141366768318729303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3474247427577845545819535 5211371141366768318729303)
  ·
    refine ⟨7817056712050152478093955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5211371141366768318729303 7817056712050152478093955)
    ·
      refine ⟨11725585068075228717140933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7817056712050152478093955 11725585068075228717140933)
      ·
        refine ⟨2198547200264105384463925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11725585068075228717140933 2198547200264105384463925)
        ·
          refine ⟨206113800024759879793493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2198547200264105384463925 206113800024759879793493)
          ·
            refine ⟨1207698047020077420665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 206113800024759879793493 1207698047020077420665)
            ·
              rfl

theorem cell21_142883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 9].length) (baseStart_142883 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_142883 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_142883 prefixEnd_142883 := by exact prefixLift 142883
  have htrace : WordTrace (prefixWord ++ tailWord_142883) baseStart_142883 baseEnd_142883 := by
    simpa [prefixWord, tailWord_142883, baseEnd_142883] using wordTrace_append hprefix tailTrace_142883
  have hstable : (prefixWord ++ tailWord_142883).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142883).length < 2 ^ (prefixWord ++ tailWord_142883).sum := by decide
  have hdescent : baseEnd_142883 < baseStart_142883 := by decide
  rcases family_descends (prefixWord ++ tailWord_142883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
