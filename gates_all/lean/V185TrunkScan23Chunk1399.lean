import V185TrunkScan23Chunk1398

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_8286475 : List Nat := [1, 1, 1, 1, 5, 2, 4, 1, 2, 5]
def baseStart_8286475 : Nat := 118140960795 + 8286475 * 2 ^ 59
def prefixEnd_8286475 : Nat := 4983230072969 + 3 ^ 40 * 8286475 * 2
def baseEnd_8286475 : Nat := 1418314868821857287384567

theorem tailTrace_8286475 : CollatzResearch.WordTrace tailWord_8286475 prefixEnd_8286475 1418314868821857287384567 := by
  unfold tailWord_8286475
  simp only [CollatzResearch.WordTrace]
  refine ⟨302232572654523767103908879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201488381769682511402605919 302232572654523767103908879)
  ·
    refine ⟨453348858981785650655863319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302232572654523767103908879 453348858981785650655863319)
    ·
      refine ⟨680023288472678475983794979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453348858981785650655863319 680023288472678475983794979)
      ·
        refine ⟨1020034932709017713975692469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680023288472678475983794979 1020034932709017713975692469)
        ·
          refine ⟨95628274941470410685221169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1020034932709017713975692469 95628274941470410685221169)
          ·
            refine ⟨71721206206102808013915877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95628274941470410685221169 71721206206102808013915877)
            ·
              refine ⟨13447726163644276502609227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71721206206102808013915877 13447726163644276502609227)
              ·
                refine ⟨20171589245466414753913841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13447726163644276502609227 20171589245466414753913841)
                ·
                  refine ⟨15128691934099811065435381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20171589245466414753913841 15128691934099811065435381)
                  ·
                    refine ⟨1418314868821857287384567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15128691934099811065435381 1418314868821857287384567)
                    ·
                      rfl

theorem cell23_8286475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 5].length) (baseStart_8286475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286475 prefixEnd_8286475 := by exact prefixLift 8286475
  have htrace : WordTrace (prefixWord ++ tailWord_8286475) baseStart_8286475 baseEnd_8286475 := by
    simpa [prefixWord, tailWord_8286475, baseEnd_8286475] using wordTrace_append hprefix tailTrace_8286475
  have hstable : (prefixWord ++ tailWord_8286475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286475).length < 2 ^ (prefixWord ++ tailWord_8286475).sum := by decide
  have hdescent : baseEnd_8286475 < baseStart_8286475 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286515 : List Nat := [1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 3]
def baseStart_8286515 : Nat := 118140960795 + 8286515 * 2 ^ 59
def prefixEnd_8286515 : Nat := 4983230072969 + 3 ^ 40 * 8286515 * 2
def baseEnd_8286515 : Nat := 4254965145691751705653517

theorem tailTrace_8286515 : CollatzResearch.WordTrace tailWord_8286515 prefixEnd_8286515 4254965145691751705653517 := by
  unfold tailWord_8286515
  simp only [CollatzResearch.WordTrace]
  refine ⟨302234031574378853935364999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201489354382919235956909999 302234031574378853935364999)
  ·
    refine ⟨453351047361568280903047499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302234031574378853935364999 453351047361568280903047499)
    ·
      refine ⟨680026571042352421354571249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453351047361568280903047499 680026571042352421354571249)
      ·
        refine ⟨510019928281764316015928437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 680026571042352421354571249 510019928281764316015928437)
        ·
          refine ⟨47814368276415404626493291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 510019928281764316015928437 47814368276415404626493291)
          ·
            refine ⟨71721552414623106939739937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47814368276415404626493291 71721552414623106939739937)
            ·
              refine ⟨53791164310967330204804953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71721552414623106939739937 53791164310967330204804953)
              ·
                refine ⟨40343373233225497653603715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53791164310967330204804953 40343373233225497653603715)
                ·
                  refine ⟨60515059849838246480405573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40343373233225497653603715 60515059849838246480405573)
                  ·
                    refine ⟨11346573721844671215076045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60515059849838246480405573 11346573721844671215076045)
                    ·
                      refine ⟨4254965145691751705653517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11346573721844671215076045 4254965145691751705653517)
                      ·
                        rfl

theorem cell23_8286515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 3].length) (baseStart_8286515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286515 prefixEnd_8286515 := by exact prefixLift 8286515
  have htrace : WordTrace (prefixWord ++ tailWord_8286515) baseStart_8286515 baseEnd_8286515 := by
    simpa [prefixWord, tailWord_8286515, baseEnd_8286515] using wordTrace_append hprefix tailTrace_8286515
  have hstable : (prefixWord ++ tailWord_8286515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286515).length < 2 ^ (prefixWord ++ tailWord_8286515).sum := by decide
  have hdescent : baseEnd_8286515 < baseStart_8286515 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286522 : List Nat := [3, 1, 1, 1, 4, 3, 1, 2, 3, 4]
def baseStart_8286522 : Nat := 118140960795 + 8286522 * 2 ^ 59
def prefixEnd_8286522 : Nat := 4983230072969 + 3 ^ 40 * 8286522 * 2
def baseEnd_8286522 : Nat := 1418322913352111059421995

theorem tailTrace_8286522 : CollatzResearch.WordTrace tailWord_8286522 prefixEnd_8286522 1418322913352111059421995 := by
  unfold tailWord_8286522
  simp only [CollatzResearch.WordTrace]
  refine ⟨75558571721338373532717455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201489524590235662753913213 75558571721338373532717455)
  ·
    refine ⟨113337857582007560299076183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75558571721338373532717455 113337857582007560299076183)
    ·
      refine ⟨170006786373011340448614275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113337857582007560299076183 170006786373011340448614275)
      ·
        refine ⟨255010179559517010672921413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170006786373011340448614275 255010179559517010672921413)
        ·
          refine ⟨47814408667409439501172765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255010179559517010672921413 47814408667409439501172765)
          ·
            refine ⟨17930403250278539812939787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47814408667409439501172765 17930403250278539812939787)
            ·
              refine ⟨26895604875417809719409681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17930403250278539812939787 26895604875417809719409681)
              ·
                refine ⟨20171703656563357289557261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26895604875417809719409681 20171703656563357289557261)
                ·
                  refine ⟨7564388871211258983583973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20171703656563357289557261 7564388871211258983583973)
                  ·
                    refine ⟨1418322913352111059421995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7564388871211258983583973 1418322913352111059421995)
                    ·
                      rfl

theorem cell23_8286522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 1, 2, 3, 4].length) (baseStart_8286522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286522 prefixEnd_8286522 := by exact prefixLift 8286522
  have htrace : WordTrace (prefixWord ++ tailWord_8286522) baseStart_8286522 baseEnd_8286522 := by
    simpa [prefixWord, tailWord_8286522, baseEnd_8286522] using wordTrace_append hprefix tailTrace_8286522
  have hstable : (prefixWord ++ tailWord_8286522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286522).length < 2 ^ (prefixWord ++ tailWord_8286522).sum := by decide
  have hdescent : baseEnd_8286522 < baseStart_8286522 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286556 : List Nat := [2, 2, 4, 3, 1, 1, 2, 1, 3, 4]
def baseStart_8286556 : Nat := 118140960795 + 8286556 * 2 ^ 59
def prefixEnd_8286556 : Nat := 4983230072969 + 3 ^ 40 * 8286556 * 2
def baseEnd_8286556 : Nat := 1418328732799528681746943

theorem tailTrace_8286556 : CollatzResearch.WordTrace tailWord_8286556 prefixEnd_8286556 1418328732799528681746943 := by
  unfold tailWord_8286556
  simp only [CollatzResearch.WordTrace]
  refine ⟨151117763483615158968803761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201490351311486878625071681 151117763483615158968803761)
  ·
    refine ⟨113338322612711369226602821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151117763483615158968803761 113338322612711369226602821)
    ·
      refine ⟨21250935489883381729988029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113338322612711369226602821 21250935489883381729988029)
      ·
        refine ⟨7969100808706268148745511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21250935489883381729988029 7969100808706268148745511)
        ·
          refine ⟨11953651213059402223118267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7969100808706268148745511 11953651213059402223118267)
          ·
            refine ⟨17930476819589103334677401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11953651213059402223118267 17930476819589103334677401)
            ·
              refine ⟨13447857614691827501008051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17930476819589103334677401 13447857614691827501008051)
              ·
                refine ⟨20171786422037741251512077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13447857614691827501008051 20171786422037741251512077)
                ·
                  refine ⟨7564419908264152969317029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20171786422037741251512077 7564419908264152969317029)
                  ·
                    refine ⟨1418328732799528681746943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7564419908264152969317029 1418328732799528681746943)
                    ·
                      rfl

theorem cell23_8286556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 1, 1, 2, 1, 3, 4].length) (baseStart_8286556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286556 prefixEnd_8286556 := by exact prefixLift 8286556
  have htrace : WordTrace (prefixWord ++ tailWord_8286556) baseStart_8286556 baseEnd_8286556 := by
    simpa [prefixWord, tailWord_8286556, baseEnd_8286556] using wordTrace_append hprefix tailTrace_8286556
  have hstable : (prefixWord ++ tailWord_8286556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286556).length < 2 ^ (prefixWord ++ tailWord_8286556).sum := by decide
  have hdescent : baseEnd_8286556 < baseStart_8286556 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286606 : List Nat := [4, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2]
def baseStart_8286606 : Nat := 118140960795 + 8286606 * 2 ^ 59
def prefixEnd_8286606 : Nat := 4983230072969 + 3 ^ 40 * 8286606 * 2
def baseEnd_8286606 : Nat := 4255011872431310849615599

theorem tailTrace_8286606 : CollatzResearch.WordTrace tailWord_8286606 prefixEnd_8286606 4255011872431310849615599 := by
  unfold tailWord_8286606
  simp only [CollatzResearch.WordTrace]
  refine ⟨37779668827131147059615959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201491567078032784317951781 37779668827131147059615959)
  ·
    refine ⟨56669503240696720589423939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37779668827131147059615959 56669503240696720589423939)
    ·
      refine ⟨85004254861045080884135909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56669503240696720589423939 85004254861045080884135909)
      ·
        refine ⟨15938297786445952665775483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85004254861045080884135909 15938297786445952665775483)
        ·
          refine ⟨23907446679668928998663225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15938297786445952665775483 23907446679668928998663225)
          ·
            refine ⟨17930585009751696748997419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23907446679668928998663225 17930585009751696748997419)
            ·
              refine ⟨26895877514627545123496129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17930585009751696748997419 26895877514627545123496129)
              ·
                refine ⟨20171908135970658842622097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26895877514627545123496129 20171908135970658842622097)
                ·
                  refine ⟨15128931101977994131966573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20171908135970658842622097 15128931101977994131966573)
                  ·
                    refine ⟨5673349163241747799487465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15128931101977994131966573 5673349163241747799487465)
                    ·
                      refine ⟨4255011872431310849615599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5673349163241747799487465 4255011872431310849615599)
                      ·
                        rfl

theorem cell23_8286606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 2, 2, 3, 2].length) (baseStart_8286606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286606 prefixEnd_8286606 := by exact prefixLift 8286606
  have htrace : WordTrace (prefixWord ++ tailWord_8286606) baseStart_8286606 baseEnd_8286606 := by
    simpa [prefixWord, tailWord_8286606, baseEnd_8286606] using wordTrace_append hprefix tailTrace_8286606
  have hstable : (prefixWord ++ tailWord_8286606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286606).length < 2 ^ (prefixWord ++ tailWord_8286606).sum := by decide
  have hdescent : baseEnd_8286606 < baseStart_8286606 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286615 : List Nat := [1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 6]
def baseStart_8286615 : Nat := 118140960795 + 8286615 * 2 ^ 59
def prefixEnd_8286615 : Nat := 4983230072969 + 3 ^ 40 * 8286615 * 2
def baseEnd_8286615 : Nat := 4255016493757201314403057

theorem tailTrace_8286615 : CollatzResearch.WordTrace tailWord_8286615 prefixEnd_8286615 4255016493757201314403057 := by
  unfold tailWord_8286615
  simp only [CollatzResearch.WordTrace]
  refine ⟨302237678874016571014005299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201491785916011047342670199 302237678874016571014005299)
  ·
    refine ⟨453356518311024856521007949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302237678874016571014005299 453356518311024856521007949)
    ·
      refine ⟨170008694366634321195377981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 453356518311024856521007949 170008694366634321195377981)
      ·
        refine ⟨63753260387487870448266743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170008694366634321195377981 63753260387487870448266743)
        ·
          refine ⟨95629890581231805672400115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63753260387487870448266743 95629890581231805672400115)
          ·
            refine ⟨143444835871847708508600173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95629890581231805672400115 143444835871847708508600173)
            ·
              refine ⟨53791813451942890690725065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143444835871847708508600173 53791813451942890690725065)
              ·
                refine ⟨40343860088957168018043799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53791813451942890690725065 40343860088957168018043799)
                ·
                  refine ⟨60515790133435752027065699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40343860088957168018043799 60515790133435752027065699)
                  ·
                    refine ⟨90773685200153628040598549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60515790133435752027065699 90773685200153628040598549)
                    ·
                      refine ⟨4255016493757201314403057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90773685200153628040598549 4255016493757201314403057)
                      ·
                        rfl

theorem cell23_8286615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 2, 1, 1, 6].length) (baseStart_8286615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286615 prefixEnd_8286615 := by exact prefixLift 8286615
  have htrace : WordTrace (prefixWord ++ tailWord_8286615) baseStart_8286615 baseEnd_8286615 := by
    simpa [prefixWord, tailWord_8286615, baseEnd_8286615] using wordTrace_append hprefix tailTrace_8286615
  have hstable : (prefixWord ++ tailWord_8286615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286615).length < 2 ^ (prefixWord ++ tailWord_8286615).sum := by decide
  have hdescent : baseEnd_8286615 < baseStart_8286615 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286635 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 3]
def baseStart_8286635 : Nat := 118140960795 + 8286635 * 2 ^ 59
def prefixEnd_8286635 : Nat := 4983230072969 + 3 ^ 40 * 8286635 * 2
def baseEnd_8286635 : Nat := 4255026763370291236152965

theorem tailTrace_8286635 : CollatzResearch.WordTrace tailWord_8286635 prefixEnd_8286635 4255026763370291236152965 := by
  unfold tailWord_8286635
  simp only [CollatzResearch.WordTrace]
  refine ⟨302238408333944114429733359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201492272222629409619822239 302238408333944114429733359)
  ·
    refine ⟨453357612500916171644600039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302238408333944114429733359 453357612500916171644600039)
    ·
      refine ⟨680036418751374257466900059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453357612500916171644600039 680036418751374257466900059)
      ·
        refine ⟨1020054628127061386200350089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680036418751374257466900059 1020054628127061386200350089)
        ·
          refine ⟨765040971095296039650262567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1020054628127061386200350089 765040971095296039650262567)
          ·
            refine ⟨1147561456642944059475393851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765040971095296039650262567 1147561456642944059475393851)
            ·
              refine ⟨1721342184964416089213090777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1147561456642944059475393851 1721342184964416089213090777)
              ·
                refine ⟨1291006638723312066909818083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1721342184964416089213090777 1291006638723312066909818083)
                ·
                  refine ⟨1936509958084968100364727125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1291006638723312066909818083 1936509958084968100364727125)
                  ·
                    refine ⟨11346738035654109963074573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1936509958084968100364727125 11346738035654109963074573)
                    ·
                      refine ⟨4255026763370291236152965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11346738035654109963074573 4255026763370291236152965)
                      ·
                        rfl

theorem cell23_8286635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 3].length) (baseStart_8286635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286635 prefixEnd_8286635 := by exact prefixLift 8286635
  have htrace : WordTrace (prefixWord ++ tailWord_8286635) baseStart_8286635 baseEnd_8286635 := by
    simpa [prefixWord, tailWord_8286635, baseEnd_8286635] using wordTrace_append hprefix tailTrace_8286635
  have hstable : (prefixWord ++ tailWord_8286635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286635).length < 2 ^ (prefixWord ++ tailWord_8286635).sum := by decide
  have hdescent : baseEnd_8286635 < baseStart_8286635 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286665 : List Nat := [1, 2, 1, 1, 2, 1, 4, 2, 2, 2, 5]
def baseStart_8286665 : Nat := 118140960795 + 8286665 * 2 ^ 59
def prefixEnd_8286665 : Nat := 4983230072969 + 3 ^ 40 * 8286665 * 2
def baseEnd_8286665 : Nat := 4255042167789926118777827

theorem tailTrace_8286665 : CollatzResearch.WordTrace tailWord_8286665 prefixEnd_8286665 4255042167789926118777827 := by
  unfold tailWord_8286665
  simp only [CollatzResearch.WordTrace]
  refine ⟨302239502523835429553325449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201493001682556953035550299 302239502523835429553325449)
  ·
    refine ⟨226679626892876572164994087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302239502523835429553325449 226679626892876572164994087)
    ·
      refine ⟨340019440339314858247491131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226679626892876572164994087 340019440339314858247491131)
      ·
        refine ⟨510029160508972287371236697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340019440339314858247491131 510029160508972287371236697)
        ·
          refine ⟨382521870381729215528427523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510029160508972287371236697 382521870381729215528427523)
          ·
            refine ⟨573782805572593823292641285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382521870381729215528427523 573782805572593823292641285)
            ·
              refine ⟨107584276044861341867370241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 573782805572593823292641285 107584276044861341867370241)
              ·
                refine ⟨80688207033646006400527681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107584276044861341867370241 80688207033646006400527681)
                ·
                  refine ⟨60516155275234504800395761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80688207033646006400527681 60516155275234504800395761)
                  ·
                    refine ⟨45387116456425878600296821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60516155275234504800395761 45387116456425878600296821)
                    ·
                      refine ⟨4255042167789926118777827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45387116456425878600296821 4255042167789926118777827)
                      ·
                        rfl

theorem cell23_8286665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_8286665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286665 prefixEnd_8286665 := by exact prefixLift 8286665
  have htrace : WordTrace (prefixWord ++ tailWord_8286665) baseStart_8286665 baseEnd_8286665 := by
    simpa [prefixWord, tailWord_8286665, baseEnd_8286665] using wordTrace_append hprefix tailTrace_8286665
  have hstable : (prefixWord ++ tailWord_8286665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286665).length < 2 ^ (prefixWord ++ tailWord_8286665).sum := by decide
  have hdescent : baseEnd_8286665 < baseStart_8286665 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286732 : List Nat := [2, 2, 1, 2, 4, 1, 1, 3, 7]
def baseStart_8286732 : Nat := 118140960795 + 8286732 * 2 ^ 59
def prefixEnd_8286732 : Nat := 4983230072969 + 3 ^ 40 * 8286732 * 2
def baseEnd_8286732 : Nat := 472786285665975261848891

theorem tailTrace_8286732 : CollatzResearch.WordTrace tailWord_8286732 prefixEnd_8286732 472786285665975261848891 := by
  unfold tailWord_8286732
  simp only [CollatzResearch.WordTrace]
  refine ⟨151120973107296349998007225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201494630809728466664009633 151120973107296349998007225)
  ·
    refine ⟨113340729830472262498505419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151120973107296349998007225 113340729830472262498505419)
    ·
      refine ⟨170011094745708393747758129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113340729830472262498505419 170011094745708393747758129)
      ·
        refine ⟨127508321059281295310818597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170011094745708393747758129 127508321059281295310818597)
        ·
          refine ⟨23907810198615242870778487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127508321059281295310818597 23907810198615242870778487)
          ·
            refine ⟨35861715297922864306167731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23907810198615242870778487 35861715297922864306167731)
            ·
              refine ⟨53792572946884296459251597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35861715297922864306167731 53792572946884296459251597)
              ·
                refine ⟨20172214855081611172219349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53792572946884296459251597 20172214855081611172219349)
                ·
                  refine ⟨472786285665975261848891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20172214855081611172219349 472786285665975261848891)
                  ·
                    rfl

theorem cell23_8286732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 3, 7].length) (baseStart_8286732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286732 prefixEnd_8286732 := by exact prefixLift 8286732
  have htrace : WordTrace (prefixWord ++ tailWord_8286732) baseStart_8286732 baseEnd_8286732 := by
    simpa [prefixWord, tailWord_8286732, baseEnd_8286732] using wordTrace_append hprefix tailTrace_8286732
  have hstable : (prefixWord ++ tailWord_8286732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286732).length < 2 ^ (prefixWord ++ tailWord_8286732).sum := by decide
  have hdescent : baseEnd_8286732 < baseStart_8286732 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286735 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 8]
def baseStart_8286735 : Nat := 118140960795 + 8286735 * 2 ^ 59
def prefixEnd_8286735 : Nat := 4983230072969 + 3 ^ 40 * 8286735 * 2
def baseEnd_8286735 : Nat := 4255078111435740844902505

theorem tailTrace_8286735 : CollatzResearch.WordTrace tailWord_8286735 prefixEnd_8286735 4255078111435740844902505 := by
  unfold tailWord_8286735
  simp only [CollatzResearch.WordTrace]
  refine ⟨302242055633581831508373659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201494703755721221005582439 302242055633581831508373659)
  ·
    refine ⟨453363083450372747262560489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302242055633581831508373659 453363083450372747262560489)
    ·
      refine ⟨340022312587779560446920367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453363083450372747262560489 340022312587779560446920367)
      ·
        refine ⟨510033468881669340670380551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340022312587779560446920367 510033468881669340670380551)
        ·
          refine ⟨765050203322504011005570827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510033468881669340670380551 765050203322504011005570827)
          ·
            refine ⟨1147575304983756016508356241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765050203322504011005570827 1147575304983756016508356241)
            ·
              refine ⟨860681478737817012381267181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1147575304983756016508356241 860681478737817012381267181)
              ·
                refine ⟨322755554526681379642975193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 860681478737817012381267181 322755554526681379642975193)
                ·
                  refine ⟨242066665895011034732231395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 322755554526681379642975193 242066665895011034732231395)
                  ·
                    refine ⟨363099998842516552098347093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 242066665895011034732231395 363099998842516552098347093)
                    ·
                      refine ⟨4255078111435740844902505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 363099998842516552098347093 4255078111435740844902505)
                      ·
                        rfl

theorem cell23_8286735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 1, 8].length) (baseStart_8286735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286735 prefixEnd_8286735 := by exact prefixLift 8286735
  have htrace : WordTrace (prefixWord ++ tailWord_8286735) baseStart_8286735 baseEnd_8286735 := by
    simpa [prefixWord, tailWord_8286735, baseEnd_8286735] using wordTrace_append hprefix tailTrace_8286735
  have hstable : (prefixWord ++ tailWord_8286735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286735).length < 2 ^ (prefixWord ++ tailWord_8286735).sum := by decide
  have hdescent : baseEnd_8286735 < baseStart_8286735 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286799 : List Nat := [1, 1, 2, 1, 1, 2, 4, 3, 2, 4, 2]
def baseStart_8286799 : Nat := 118140960795 + 8286799 * 2 ^ 59
def prefixEnd_8286799 : Nat := 4983230072969 + 3 ^ 40 * 8286799 * 2
def baseEnd_8286799 : Nat := 4255110974197628594502211

theorem tailTrace_8286799 : CollatzResearch.WordTrace tailWord_8286799 prefixEnd_8286799 4255110974197628594502211 := by
  unfold tailWord_8286799
  simp only [CollatzResearch.WordTrace]
  refine ⟨302244389905349970438703451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201496259936899980292468967 302244389905349970438703451)
  ·
    refine ⟨453366584858024955658055177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302244389905349970438703451 453366584858024955658055177)
    ·
      refine ⟨340024938643518716743541383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453366584858024955658055177 340024938643518716743541383)
      ·
        refine ⟨510037407965278075115312075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340024938643518716743541383 510037407965278075115312075)
        ·
          refine ⟨765056111947917112672968113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510037407965278075115312075 765056111947917112672968113)
          ·
            refine ⟨573792083960937834504726085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765056111947917112672968113 573792083960937834504726085)
            ·
              refine ⟨107586015742675843969636141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 573792083960937834504726085 107586015742675843969636141)
              ·
                refine ⟨40344755903503441488613553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107586015742675843969636141 40344755903503441488613553)
                ·
                  refine ⟨30258566927627581116460165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40344755903503441488613553 30258566927627581116460165)
                  ·
                    refine ⟨5673481298930171459336281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30258566927627581116460165 5673481298930171459336281)
                    ·
                      refine ⟨4255110974197628594502211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5673481298930171459336281 4255110974197628594502211)
                      ·
                        rfl

theorem cell23_8286799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 3, 2, 4, 2].length) (baseStart_8286799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286799 prefixEnd_8286799 := by exact prefixLift 8286799
  have htrace : WordTrace (prefixWord ++ tailWord_8286799) baseStart_8286799 baseEnd_8286799 := by
    simpa [prefixWord, tailWord_8286799, baseEnd_8286799] using wordTrace_append hprefix tailTrace_8286799
  have hstable : (prefixWord ++ tailWord_8286799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286799).length < 2 ^ (prefixWord ++ tailWord_8286799).sum := by decide
  have hdescent : baseEnd_8286799 < baseStart_8286799 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286890 : List Nat := [3, 1, 5, 2, 1, 2, 1, 2, 6]
def baseStart_8286890 : Nat := 118140960795 + 8286890 * 2 ^ 59
def prefixEnd_8286890 : Nat := 4983230072969 + 3 ^ 40 * 8286890 * 2
def baseEnd_8286890 : Nat := 472795300104131970940477

theorem tailTrace_8286890 : CollatzResearch.WordTrace tailWord_8286890 prefixEnd_8286890 472795300104131970940477 := by
  unfold tailWord_8286890
  simp only [CollatzResearch.WordTrace]
  refine ⟨75561927237005073245066531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201498472632013528653510749 75561927237005073245066531)
  ·
    refine ⟨113342890855507609867599797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75561927237005073245066531 113342890855507609867599797)
    ·
      refine ⟨10625896017703838425087481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113342890855507609867599797 10625896017703838425087481)
      ·
        refine ⟨7969422013277878818815611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10625896017703838425087481 7969422013277878818815611)
        ·
          refine ⟨11954133019916818228223417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7969422013277878818815611 11954133019916818228223417)
          ·
            refine ⟨8965599764937613671167563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11954133019916818228223417 8965599764937613671167563)
            ·
              refine ⟨13448399647406420506751345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8965599764937613671167563 13448399647406420506751345)
              ·
                refine ⟨10086299735554815380063509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13448399647406420506751345 10086299735554815380063509)
                ·
                  refine ⟨472795300104131970940477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10086299735554815380063509 472795300104131970940477)
                  ·
                    rfl

theorem cell23_8286890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 2, 1, 2, 6].length) (baseStart_8286890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286890 prefixEnd_8286890 := by exact prefixLift 8286890
  have htrace : WordTrace (prefixWord ++ tailWord_8286890) baseStart_8286890 baseEnd_8286890 := by
    simpa [prefixWord, tailWord_8286890, baseEnd_8286890] using wordTrace_append hprefix tailTrace_8286890
  have hstable : (prefixWord ++ tailWord_8286890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286890).length < 2 ^ (prefixWord ++ tailWord_8286890).sum := by decide
  have hdescent : baseEnd_8286890 < baseStart_8286890 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286909 : List Nat := [1, 4, 1, 2, 1, 3, 1, 1, 3, 1, 5]
def baseStart_8286909 : Nat := 118140960795 + 8286909 * 2 ^ 59
def prefixEnd_8286909 : Nat := 4983230072969 + 3 ^ 40 * 8286909 * 2
def baseEnd_8286909 : Nat := 4255167457069623164126705

theorem tailTrace_8286909 : CollatzResearch.WordTrace tailWord_8286909 prefixEnd_8286909 4255167457069623164126705 := by
  unfold tailWord_8286909
  simp only [CollatzResearch.WordTrace]
  refine ⟨302248401934951459225207781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201498934623300972816805187 302248401934951459225207781)
  ·
    refine ⟨56671575362803398604726459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302248401934951459225207781 56671575362803398604726459)
    ·
      refine ⟨85007363044205097907089689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56671575362803398604726459 85007363044205097907089689)
      ·
        refine ⟨63755522283153823430317267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85007363044205097907089689 63755522283153823430317267)
        ·
          refine ⟨95633283424730735145475901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63755522283153823430317267 95633283424730735145475901)
          ·
            refine ⟨35862481284274025679553463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95633283424730735145475901 35862481284274025679553463)
            ·
              refine ⟨53793721926411038519330195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35862481284274025679553463 53793721926411038519330195)
              ·
                refine ⟨80690582889616557778995293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53793721926411038519330195 80690582889616557778995293)
                ·
                  refine ⟨30258968583606209167123235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80690582889616557778995293 30258968583606209167123235)
                  ·
                    refine ⟨45388452875409313750684853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30258968583606209167123235 45388452875409313750684853)
                    ·
                      refine ⟨4255167457069623164126705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45388452875409313750684853 4255167457069623164126705)
                      ·
                        rfl

theorem cell23_8286909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_8286909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286909 prefixEnd_8286909 := by exact prefixLift 8286909
  have htrace : WordTrace (prefixWord ++ tailWord_8286909) baseStart_8286909 baseEnd_8286909 := by
    simpa [prefixWord, tailWord_8286909, baseEnd_8286909] using wordTrace_append hprefix tailTrace_8286909
  have hstable : (prefixWord ++ tailWord_8286909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286909).length < 2 ^ (prefixWord ++ tailWord_8286909).sum := by decide
  have hdescent : baseEnd_8286909 < baseStart_8286909 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286916 : List Nat := [2, 3, 3, 1, 1, 2, 3, 1, 1, 6]
def baseStart_8286916 : Nat := 118140960795 + 8286916 * 2 ^ 59
def prefixEnd_8286916 : Nat := 4983230072969 + 3 ^ 40 * 8286916 * 2
def baseEnd_8286916 : Nat := 1418390350478068212246391

theorem tailTrace_8286916 : CollatzResearch.WordTrace tailWord_8286916 prefixEnd_8286916 1418390350478068212246391 := by
  unfold tailWord_8286916
  simp only [CollatzResearch.WordTrace]
  refine ⟨151124328622963049710356301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201499104830617399613808401 151124328622963049710356301)
  ·
    refine ⟨56671623233611143641383613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151124328622963049710356301 56671623233611143641383613)
    ·
      refine ⟨21251858712604178865518855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56671623233611143641383613 21251858712604178865518855)
      ·
        refine ⟨31877788068906268298278283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21251858712604178865518855 31877788068906268298278283)
        ·
          refine ⟨47816682103359402447417425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31877788068906268298278283 47816682103359402447417425)
          ·
            refine ⟨35862511577519551835563069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47816682103359402447417425 35862511577519551835563069)
            ·
              refine ⟨13448441841569831938336151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35862511577519551835563069 13448441841569831938336151)
              ·
                refine ⟨20172662762354747907504227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13448441841569831938336151 20172662762354747907504227)
                ·
                  refine ⟨30258994143532121861256341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20172662762354747907504227 30258994143532121861256341)
                  ·
                    refine ⟨1418390350478068212246391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30258994143532121861256341 1418390350478068212246391)
                    ·
                      rfl

theorem cell23_8286916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_8286916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286916 prefixEnd_8286916 := by exact prefixLift 8286916
  have htrace : WordTrace (prefixWord ++ tailWord_8286916) baseStart_8286916 baseEnd_8286916 := by
    simpa [prefixWord, tailWord_8286916, baseEnd_8286916] using wordTrace_append hprefix tailTrace_8286916
  have hstable : (prefixWord ++ tailWord_8286916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286916).length < 2 ^ (prefixWord ++ tailWord_8286916).sum := by decide
  have hdescent : baseEnd_8286916 < baseStart_8286916 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286919 : List Nat := [1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 4]
def baseStart_8286919 : Nat := 118140960795 + 8286919 * 2 ^ 59
def prefixEnd_8286919 : Nat := 4983230072969 + 3 ^ 40 * 8286919 * 2
def baseEnd_8286919 : Nat := 4255172591876168125001659

theorem tailTrace_8286919 : CollatzResearch.WordTrace tailWord_8286919 prefixEnd_8286919 4255172591876168125001659 := by
  unfold tailWord_8286919
  simp only [CollatzResearch.WordTrace]
  refine ⟨302248766664915230933071811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201499177776610153955381207 302248766664915230933071811)
  ·
    refine ⟨453373149997372846399607717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302248766664915230933071811 453373149997372846399607717)
    ·
      refine ⟨85007465624507408699926447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 453373149997372846399607717 85007465624507408699926447)
      ·
        refine ⟨127511198436761113049889671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85007465624507408699926447 127511198436761113049889671)
        ·
          refine ⟨191266797655141669574834507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127511198436761113049889671 191266797655141669574834507)
          ·
            refine ⟨286900196482712504362251761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191266797655141669574834507 286900196482712504362251761)
            ·
              refine ⟨215175147362034378271688821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286900196482712504362251761 215175147362034378271688821)
              ·
                refine ⟨20172670065190722962970827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215175147362034378271688821 20172670065190722962970827)
                ·
                  refine ⟨30259005097786084444456241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20172670065190722962970827 30259005097786084444456241)
                  ·
                    refine ⟨22694253823339563333342181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30259005097786084444456241 22694253823339563333342181)
                    ·
                      refine ⟨4255172591876168125001659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22694253823339563333342181 4255172591876168125001659)
                      ·
                        rfl

theorem cell23_8286919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_8286919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286919 prefixEnd_8286919 := by exact prefixLift 8286919
  have htrace : WordTrace (prefixWord ++ tailWord_8286919) baseStart_8286919 baseEnd_8286919 := by
    simpa [prefixWord, tailWord_8286919, baseEnd_8286919] using wordTrace_append hprefix tailTrace_8286919
  have hstable : (prefixWord ++ tailWord_8286919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286919).length < 2 ^ (prefixWord ++ tailWord_8286919).sum := by decide
  have hdescent : baseEnd_8286919 < baseStart_8286919 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8286973 : List Nat := [1, 4, 1, 1, 1, 1, 5, 3, 2, 1, 3]
def baseStart_8286973 : Nat := 118140960795 + 8286973 * 2 ^ 59
def prefixEnd_8286973 : Nat := 4983230072969 + 3 ^ 40 * 8286973 * 2
def baseEnd_8286973 : Nat := 4255200319831510913726411

theorem tailTrace_8286973 : CollatzResearch.WordTrace tailWord_8286973 prefixEnd_8286973 4255200319831510913726411 := by
  unfold tailWord_8286973
  simp only [CollatzResearch.WordTrace]
  refine ⟨302250736206719598155537573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201500490804479732103691715 302250736206719598155537573)
  ·
    refine ⟨56672013038759924654163295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302250736206719598155537573 56672013038759924654163295)
    ·
      refine ⟨85008019558139886981244943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56672013038759924654163295 85008019558139886981244943)
      ·
        refine ⟨127512029337209830471867415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85008019558139886981244943 127512029337209830471867415)
        ·
          refine ⟨191268044005814745707801123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127512029337209830471867415 191268044005814745707801123)
          ·
            refine ⟨286902066008722118561701685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191268044005814745707801123 286902066008722118561701685)
            ·
              refine ⟨26897068688317698615159533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 286902066008722118561701685 26897068688317698615159533)
              ·
                refine ⟨10086400758119136980684825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26897068688317698615159533 10086400758119136980684825)
                ·
                  refine ⟨7564800568589352735513619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10086400758119136980684825 7564800568589352735513619)
                  ·
                    refine ⟨11347200852884029103270429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7564800568589352735513619 11347200852884029103270429)
                    ·
                      refine ⟨4255200319831510913726411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11347200852884029103270429 4255200319831510913726411)
                      ·
                        rfl

theorem cell23_8286973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 5, 3, 2, 1, 3].length) (baseStart_8286973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8286973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8286973 prefixEnd_8286973 := by exact prefixLift 8286973
  have htrace : WordTrace (prefixWord ++ tailWord_8286973) baseStart_8286973 baseEnd_8286973 := by
    simpa [prefixWord, tailWord_8286973, baseEnd_8286973] using wordTrace_append hprefix tailTrace_8286973
  have hstable : (prefixWord ++ tailWord_8286973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8286973).length < 2 ^ (prefixWord ++ tailWord_8286973).sum := by decide
  have hdescent : baseEnd_8286973 < baseStart_8286973 := by decide
  rcases family_descends (prefixWord ++ tailWord_8286973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287016 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 1, 6, 3]
def baseStart_8287016 : Nat := 118140960795 + 8287016 * 2 ^ 59
def prefixEnd_8287016 : Nat := 4983230072969 + 3 ^ 40 * 8287016 * 2
def baseEnd_8287016 : Nat := 4255222399499654245488713

theorem tailTrace_8287016 : CollatzResearch.WordTrace tailWord_8287016 prefixEnd_8287016 4255222399499654245488713 := by
  unfold tailWord_8287016
  simp only [CollatzResearch.WordTrace]
  refine ⟨151126152272781908249676451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201501536363709210999568601 151126152272781908249676451)
  ·
    refine ⟨226689228409172862374514677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151126152272781908249676451 226689228409172862374514677)
    ·
      refine ⟨21252115163359955847610751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 226689228409172862374514677 21252115163359955847610751)
      ·
        refine ⟨31878172745039933771416127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21252115163359955847610751 31878172745039933771416127)
        ·
          refine ⟨47817259117559900657124191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31878172745039933771416127 47817259117559900657124191)
          ·
            refine ⟨71725888676339850985686287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47817259117559900657124191 71725888676339850985686287)
            ·
              refine ⟨107588833014509776478529431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71725888676339850985686287 107588833014509776478529431)
              ·
                refine ⟨161383249521764664717794147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107588833014509776478529431 161383249521764664717794147)
                ·
                  refine ⟨242074874282646997076691221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 161383249521764664717794147 242074874282646997076691221)
                  ·
                    refine ⟨11347259731999077987969901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 242074874282646997076691221 11347259731999077987969901)
                    ·
                      refine ⟨4255222399499654245488713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11347259731999077987969901 4255222399499654245488713)
                      ·
                        rfl

theorem cell23_8287016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 1, 6, 3].length) (baseStart_8287016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287016 prefixEnd_8287016 := by exact prefixLift 8287016
  have htrace : WordTrace (prefixWord ++ tailWord_8287016) baseStart_8287016 baseEnd_8287016 := by
    simpa [prefixWord, tailWord_8287016, baseEnd_8287016] using wordTrace_append hprefix tailTrace_8287016
  have hstable : (prefixWord ++ tailWord_8287016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287016).length < 2 ^ (prefixWord ++ tailWord_8287016).sum := by decide
  have hdescent : baseEnd_8287016 < baseStart_8287016 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287026 : List Nat := [3, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4]
def baseStart_8287026 : Nat := 118140960795 + 8287026 * 2 ^ 59
def prefixEnd_8287026 : Nat := 4983230072969 + 3 ^ 40 * 8287026 * 2
def baseEnd_8287026 : Nat := 4255227534306199206363667

theorem tailTrace_8287026 : CollatzResearch.WordTrace tailWord_8287026 prefixEnd_8287026 4255227534306199206363667 := by
  unfold tailWord_8287026
  simp only [CollatzResearch.WordTrace]
  refine ⟨75563167318881897051804233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201501779517018392138144621 75563167318881897051804233)
  ·
    refine ⟨56672375489161422788853175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75563167318881897051804233 56672375489161422788853175)
    ·
      refine ⟨85008563233742134183279763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56672375489161422788853175 85008563233742134183279763)
      ·
        refine ⟨127512844850613201274919645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85008563233742134183279763 127512844850613201274919645)
        ·
          refine ⟨47817316818979950478094867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127512844850613201274919645 47817316818979950478094867)
          ·
            refine ⟨71725975228469925717142301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47817316818979950478094867 71725975228469925717142301)
            ·
              refine ⟨26897240710676222143928363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71725975228469925717142301 26897240710676222143928363)
              ·
                refine ⟨40345861066014333215892545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26897240710676222143928363 40345861066014333215892545)
                ·
                  refine ⟨30259395799510749911919409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40345861066014333215892545 30259395799510749911919409)
                  ·
                    refine ⟨22694546849633062433939557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30259395799510749911919409 22694546849633062433939557)
                    ·
                      refine ⟨4255227534306199206363667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22694546849633062433939557 4255227534306199206363667)
                      ·
                        rfl

theorem cell23_8287026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_8287026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287026 prefixEnd_8287026 := by exact prefixLift 8287026
  have htrace : WordTrace (prefixWord ++ tailWord_8287026) baseStart_8287026 baseEnd_8287026 := by
    simpa [prefixWord, tailWord_8287026, baseEnd_8287026] using wordTrace_append hprefix tailTrace_8287026
  have hstable : (prefixWord ++ tailWord_8287026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287026).length < 2 ^ (prefixWord ++ tailWord_8287026).sum := by decide
  have hdescent : baseEnd_8287026 < baseStart_8287026 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287059 : List Nat := [1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 5]
def baseStart_8287059 : Nat := 118140960795 + 8287059 * 2 ^ 59
def prefixEnd_8287059 : Nat := 4983230072969 + 3 ^ 40 * 8287059 * 2
def baseEnd_8287059 : Nat := 4255244479167797577251015

theorem tailTrace_8287059 : CollatzResearch.WordTrace tailWord_8287059 prefixEnd_8287059 4255244479167797577251015 := by
  unfold tailWord_8287059
  simp only [CollatzResearch.WordTrace]
  refine ⟨302253872884408034843168231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201502581922938689895445487 302253872884408034843168231)
  ·
    refine ⟨453380809326612052264752347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302253872884408034843168231 453380809326612052264752347)
    ·
      refine ⟨680071213989918078397128521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453380809326612052264752347 680071213989918078397128521)
      ·
        refine ⟨510053410492438558797846391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 680071213989918078397128521 510053410492438558797846391)
        ·
          refine ⟨765080115738657838196769587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510053410492438558797846391 765080115738657838196769587)
          ·
            refine ⟨1147620173607986757295154381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765080115738657838196769587 1147620173607986757295154381)
            ·
              refine ⟨430357565102995033985682893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1147620173607986757295154381 430357565102995033985682893)
              ·
                refine ⟨161384086913623137744631085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 430357565102995033985682893 161384086913623137744631085)
                ·
                  refine ⟨60519032592608676654236657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161384086913623137744631085 60519032592608676654236657)
                  ·
                    refine ⟨45389274444456507490677493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60519032592608676654236657 45389274444456507490677493)
                    ·
                      refine ⟨4255244479167797577251015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45389274444456507490677493 4255244479167797577251015)
                      ·
                        rfl

theorem cell23_8287059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 3, 2, 5].length) (baseStart_8287059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287059 prefixEnd_8287059 := by exact prefixLift 8287059
  have htrace : WordTrace (prefixWord ++ tailWord_8287059) baseStart_8287059 baseEnd_8287059 := by
    simpa [prefixWord, tailWord_8287059, baseEnd_8287059] using wordTrace_append hprefix tailTrace_8287059
  have hstable : (prefixWord ++ tailWord_8287059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287059).length < 2 ^ (prefixWord ++ tailWord_8287059).sum := by decide
  have hdescent : baseEnd_8287059 < baseStart_8287059 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287096 : List Nat := [2, 1, 2, 1, 1, 1, 1, 5, 5, 4]
def baseStart_8287096 : Nat := 118140960795 + 8287096 * 2 ^ 59
def prefixEnd_8287096 : Nat := 4983230072969 + 3 ^ 40 * 8287096 * 2
def baseEnd_8287096 : Nat := 1418421159317337977496115

theorem tailTrace_8287096 : CollatzResearch.WordTrace tailWord_8287096 prefixEnd_8287096 1418421159317337977496115 := by
  unfold tailWord_8287096
  simp only [CollatzResearch.WordTrace]
  refine ⟨151127611192636995081132571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201503481590182660108176761 151127611192636995081132571)
  ·
    refine ⟨226691416788955492621698857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151127611192636995081132571 226691416788955492621698857)
    ·
      refine ⟨170018562591716619466274143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226691416788955492621698857 170018562591716619466274143)
      ·
        refine ⟨255027843887574929199411215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170018562591716619466274143 255027843887574929199411215)
        ·
          refine ⟨382541765831362393799116823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255027843887574929199411215 382541765831362393799116823)
          ·
            refine ⟨573812648747043590698675235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382541765831362393799116823 573812648747043590698675235)
            ·
              refine ⟨860718973120565386048012853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 573812648747043590698675235 860718973120565386048012853)
              ·
                refine ⟨80692403730053004942001205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 860718973120565386048012853 80692403730053004942001205)
                ·
                  refine ⟨7564912849692469213312613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80692403730053004942001205 7564912849692469213312613)
                  ·
                    refine ⟨1418421159317337977496115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7564912849692469213312613 1418421159317337977496115)
                    ·
                      rfl

theorem cell23_8287096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 5, 5, 4].length) (baseStart_8287096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287096 prefixEnd_8287096 := by exact prefixLift 8287096
  have htrace : WordTrace (prefixWord ++ tailWord_8287096) baseStart_8287096 baseEnd_8287096 := by
    simpa [prefixWord, tailWord_8287096, baseEnd_8287096] using wordTrace_append hprefix tailTrace_8287096
  have hstable : (prefixWord ++ tailWord_8287096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287096).length < 2 ^ (prefixWord ++ tailWord_8287096).sum := by decide
  have hdescent : baseEnd_8287096 < baseStart_8287096 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287180 : List Nat := [2, 2, 1, 4, 1, 1, 1, 4, 2, 3, 2]
def baseStart_8287180 : Nat := 118140960795 + 8287180 * 2 ^ 59
def prefixEnd_8287180 : Nat := 4983230072969 + 3 ^ 40 * 8287180 * 2
def baseEnd_8287180 : Nat := 4255306610326991603837959

theorem tailTrace_8287180 : CollatzResearch.WordTrace tailWord_8287180 prefixEnd_8287180 4255306610326991603837959 := by
  unfold tailWord_8287180
  simp only [CollatzResearch.WordTrace]
  refine ⟨151129143058484836254161497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201505524077979781672215329 151129143058484836254161497)
  ·
    refine ⟨113346857293863627190621123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151129143058484836254161497 113346857293863627190621123)
    ·
      refine ⟨170020285940795440785931685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113346857293863627190621123 170020285940795440785931685)
      ·
        refine ⟨31878803613899145147362191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170020285940795440785931685 31878803613899145147362191)
        ·
          refine ⟨47818205420848717721043287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31878803613899145147362191 47818205420848717721043287)
          ·
            refine ⟨71727308131273076581564931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47818205420848717721043287 71727308131273076581564931)
            ·
              refine ⟨107590962196909614872347397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71727308131273076581564931 107590962196909614872347397)
              ·
                refine ⟨20173305411920552788565137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107590962196909614872347397 20173305411920552788565137)
                ·
                  refine ⟨15129979058940414591423853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20173305411920552788565137 15129979058940414591423853)
                  ·
                    refine ⟨5673742147102655471783945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15129979058940414591423853 5673742147102655471783945)
                    ·
                      refine ⟨4255306610326991603837959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5673742147102655471783945 4255306610326991603837959)
                      ·
                        rfl

theorem cell23_8287180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_8287180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287180 prefixEnd_8287180 := by exact prefixLift 8287180
  have htrace : WordTrace (prefixWord ++ tailWord_8287180) baseStart_8287180 baseEnd_8287180 := by
    simpa [prefixWord, tailWord_8287180, baseEnd_8287180] using wordTrace_append hprefix tailTrace_8287180
  have hstable : (prefixWord ++ tailWord_8287180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287180).length < 2 ^ (prefixWord ++ tailWord_8287180).sum := by decide
  have hdescent : baseEnd_8287180 < baseStart_8287180 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287190 : List Nat := [5, 2, 1, 1, 2, 1, 1, 2, 3, 5]
def baseStart_8287190 : Nat := 118140960795 + 8287190 * 2 ^ 59
def prefixEnd_8287190 : Nat := 4983230072969 + 3 ^ 40 * 8287190 * 2
def baseEnd_8287190 : Nat := 1418437248377845521570971

theorem tailTrace_8287190 : CollatzResearch.WordTrace tailWord_8287190 prefixEnd_8287190 1418437248377845521570971 := by
  unfold tailWord_8287190
  simp only [CollatzResearch.WordTrace]
  refine ⟨18891165677933340263511689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201505767231288962810791349 18891165677933340263511689)
  ·
    refine ⟨14168374258450005197633767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18891165677933340263511689 14168374258450005197633767)
    ·
      refine ⟨21252561387675007796450651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14168374258450005197633767 21252561387675007796450651)
      ·
        refine ⟨31878842081512511694675977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21252561387675007796450651 31878842081512511694675977)
        ·
          refine ⟨23909131561134383771006983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31878842081512511694675977 23909131561134383771006983)
          ·
            refine ⟨35863697341701575656510475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23909131561134383771006983 35863697341701575656510475)
            ·
              refine ⟨53795546012552363484765713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35863697341701575656510475 53795546012552363484765713)
              ·
                refine ⟨40346659509414272613574285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53795546012552363484765713 40346659509414272613574285)
                ·
                  refine ⟨15129997316030352230090357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40346659509414272613574285 15129997316030352230090357)
                  ·
                    refine ⟨1418437248377845521570971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15129997316030352230090357 1418437248377845521570971)
                    ·
                      rfl

theorem cell23_8287190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_8287190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287190 prefixEnd_8287190 := by exact prefixLift 8287190
  have htrace : WordTrace (prefixWord ++ tailWord_8287190) baseStart_8287190 baseEnd_8287190 := by
    simpa [prefixWord, tailWord_8287190, baseEnd_8287190] using wordTrace_append hprefix tailTrace_8287190
  have hstable : (prefixWord ++ tailWord_8287190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287190).length < 2 ^ (prefixWord ++ tailWord_8287190).sum := by decide
  have hdescent : baseEnd_8287190 < baseStart_8287190 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287193 : List Nat := [1, 2, 1, 2, 5, 1, 1, 2, 3, 1, 4]
def baseStart_8287193 : Nat := 118140960795 + 8287193 * 2 ^ 59
def prefixEnd_8287193 : Nat := 4983230072969 + 3 ^ 40 * 8287193 * 2
def baseEnd_8287193 : Nat := 4255313285575500052975399

theorem tailTrace_8287193 : CollatzResearch.WordTrace tailWord_8287193 prefixEnd_8287193 4255313285575500052975399 := by
  unfold tailWord_8287193
  simp only [CollatzResearch.WordTrace]
  refine ⟨302258760265922575728546233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201505840177281717152364155 302258760265922575728546233)
  ·
    refine ⟨226694070199441931796409675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302258760265922575728546233 226694070199441931796409675)
    ·
      refine ⟨340041105299162897694614513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226694070199441931796409675 340041105299162897694614513)
      ·
        refine ⟨255030828974372173270960885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340041105299162897694614513 255030828974372173270960885)
        ·
          refine ⟨23909140216347391244152583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 255030828974372173270960885 23909140216347391244152583)
          ·
            refine ⟨35863710324521086866228875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23909140216347391244152583 35863710324521086866228875)
            ·
              refine ⟨53795565486781630299343313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35863710324521086866228875 53795565486781630299343313)
              ·
                refine ⟨40346674115086222724507485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53795565486781630299343313 40346674115086222724507485)
                ·
                  refine ⟨15130002793157333521690307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40346674115086222724507485 15130002793157333521690307)
                  ·
                    refine ⟨22695004189736000282535461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15130002793157333521690307 22695004189736000282535461)
                    ·
                      refine ⟨4255313285575500052975399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22695004189736000282535461 4255313285575500052975399)
                      ·
                        rfl

theorem cell23_8287193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_8287193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287193 prefixEnd_8287193 := by exact prefixLift 8287193
  have htrace : WordTrace (prefixWord ++ tailWord_8287193) baseStart_8287193 baseEnd_8287193 := by
    simpa [prefixWord, tailWord_8287193, baseEnd_8287193] using wordTrace_append hprefix tailTrace_8287193
  have hstable : (prefixWord ++ tailWord_8287193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287193).length < 2 ^ (prefixWord ++ tailWord_8287193).sum := by decide
  have hdescent : baseEnd_8287193 < baseStart_8287193 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287203 : List Nat := [1, 1, 1, 6, 1, 1, 4, 1, 1, 6]
def baseStart_8287203 : Nat := 118140960795 + 8287203 * 2 ^ 59
def prefixEnd_8287203 : Nat := 4983230072969 + 3 ^ 40 * 8287203 * 2
def baseEnd_8287203 : Nat := 1418439473460681671283451

theorem tailTrace_8287203 : CollatzResearch.WordTrace tailWord_8287203 prefixEnd_8287203 1418439473460681671283451 := by
  unfold tailWord_8287203
  simp only [CollatzResearch.WordTrace]
  refine ⟨302259124995886347436410263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201506083330590898290940175 302259124995886347436410263)
  ·
    refine ⟨453388687493829521154615395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302259124995886347436410263 453388687493829521154615395)
    ·
      refine ⟨680083031240744281731923093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453388687493829521154615395 680083031240744281731923093)
      ·
        refine ⟨31878892089409888206183895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 680083031240744281731923093 31878892089409888206183895)
        ·
          refine ⟨47818338134114832309275843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31878892089409888206183895 47818338134114832309275843)
          ·
            refine ⟨71727507201172248463913765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47818338134114832309275843 71727507201172248463913765)
            ·
              refine ⟨13448907600219796586983831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71727507201172248463913765 13448907600219796586983831)
              ·
                refine ⟨20173361400329694880475747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13448907600219796586983831 20173361400329694880475747)
                ·
                  refine ⟨30260042100494542320713621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20173361400329694880475747 30260042100494542320713621)
                  ·
                    refine ⟨1418439473460681671283451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30260042100494542320713621 1418439473460681671283451)
                    ·
                      rfl

theorem cell23_8287203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 6].length) (baseStart_8287203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287203 prefixEnd_8287203 := by exact prefixLift 8287203
  have htrace : WordTrace (prefixWord ++ tailWord_8287203) baseStart_8287203 baseEnd_8287203 := by
    simpa [prefixWord, tailWord_8287203, baseEnd_8287203] using wordTrace_append hprefix tailTrace_8287203
  have hstable : (prefixWord ++ tailWord_8287203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287203).length < 2 ^ (prefixWord ++ tailWord_8287203).sum := by decide
  have hdescent : baseEnd_8287203 < baseStart_8287203 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287214 : List Nat := [4, 1, 2, 1, 4, 2, 1, 1, 2, 3, 2]
def baseStart_8287214 : Nat := 118140960795 + 8287214 * 2 ^ 59
def prefixEnd_8287214 : Nat := 4983230072969 + 3 ^ 40 * 8287214 * 2
def baseEnd_8287214 : Nat := 4255324068669244470812803

theorem tailTrace_8287214 : CollatzResearch.WordTrace tailWord_8287214 prefixEnd_8287214 4255324068669244470812803 := by
  unfold tailWord_8287214
  simp only [CollatzResearch.WordTrace]
  refine ⟨37782440774855812039382587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201506350799230997543373797 37782440774855812039382587)
  ·
    refine ⟨56673661162283718059073881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37782440774855812039382587 56673661162283718059073881)
    ·
      refine ⟨42505245871712788544305411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56673661162283718059073881 42505245871712788544305411)
      ·
        refine ⟨63757868807569182816458117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42505245871712788544305411 63757868807569182816458117)
        ·
          refine ⟨11954600401419221778085897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63757868807569182816458117 11954600401419221778085897)
          ·
            refine ⟨8965950301064416333564423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11954600401419221778085897 8965950301064416333564423)
            ·
              refine ⟨13448925451596624500346635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8965950301064416333564423 13448925451596624500346635)
              ·
                refine ⟨20173388177394936750519953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13448925451596624500346635 20173388177394936750519953)
                ·
                  refine ⟨15130041133046202562889965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20173388177394936750519953 15130041133046202562889965)
                  ·
                    refine ⟨5673765424892325961083737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15130041133046202562889965 5673765424892325961083737)
                    ·
                      refine ⟨4255324068669244470812803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5673765424892325961083737 4255324068669244470812803)
                      ·
                        rfl

theorem cell23_8287214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 1, 2, 3, 2].length) (baseStart_8287214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287214 prefixEnd_8287214 := by exact prefixLift 8287214
  have htrace : WordTrace (prefixWord ++ tailWord_8287214) baseStart_8287214 baseEnd_8287214 := by
    simpa [prefixWord, tailWord_8287214, baseEnd_8287214] using wordTrace_append hprefix tailTrace_8287214
  have hstable : (prefixWord ++ tailWord_8287214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287214).length < 2 ^ (prefixWord ++ tailWord_8287214).sum := by decide
  have hdescent : baseEnd_8287214 < baseStart_8287214 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287244 : List Nat := [2, 2, 1, 2, 3, 2, 2, 4, 1, 2, 2]
def baseStart_8287244 : Nat := 118140960795 + 8287244 * 2 ^ 59
def prefixEnd_8287244 : Nat := 4983230072969 + 3 ^ 40 * 8287244 * 2
def baseEnd_8287244 : Nat := 4255339473088879353437665

theorem tailTrace_8287244 : CollatzResearch.WordTrace tailWord_8287244 prefixEnd_8287244 4255339473088879353437665 := by
  unfold tailWord_8287244
  simp only [CollatzResearch.WordTrace]
  refine ⟨151130310194368905719326393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201507080259158540959101857 151130310194368905719326393)
  ·
    refine ⟨113347732645776679289494795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151130310194368905719326393 113347732645776679289494795)
    ·
      refine ⟨170021598968665018934242193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113347732645776679289494795 170021598968665018934242193)
      ·
        refine ⟨127516199226498764200681645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170021598968665018934242193 127516199226498764200681645)
        ·
          refine ⟨47818574709937036575255617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127516199226498764200681645 47818574709937036575255617)
          ·
            refine ⟨35863931032452777431441713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47818574709937036575255617 35863931032452777431441713)
            ·
              refine ⟨26897948274339583073581285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35863931032452777431441713 26897948274339583073581285)
              ·
                refine ⟨5043365301438671826296491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26897948274339583073581285 5043365301438671826296491)
                ·
                  refine ⟨7565047952158007739444737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5043365301438671826296491 7565047952158007739444737)
                  ·
                    refine ⟨5673785964118505804583553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7565047952158007739444737 5673785964118505804583553)
                    ·
                      refine ⟨4255339473088879353437665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5673785964118505804583553 4255339473088879353437665)
                      ·
                        rfl

theorem cell23_8287244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 1, 2, 2].length) (baseStart_8287244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287244 prefixEnd_8287244 := by exact prefixLift 8287244
  have htrace : WordTrace (prefixWord ++ tailWord_8287244) baseStart_8287244 baseEnd_8287244 := by
    simpa [prefixWord, tailWord_8287244, baseEnd_8287244] using wordTrace_append hprefix tailTrace_8287244
  have hstable : (prefixWord ++ tailWord_8287244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287244).length < 2 ^ (prefixWord ++ tailWord_8287244).sum := by decide
  have hdescent : baseEnd_8287244 < baseStart_8287244 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287264 : List Nat := [2, 1, 1, 7, 1, 1, 2, 2, 1, 2, 3]
def baseStart_8287264 : Nat := 118140960795 + 8287264 * 2 ^ 59
def prefixEnd_8287264 : Nat := 4983230072969 + 3 ^ 40 * 8287264 * 2
def baseEnd_8287264 : Nat := 4255349742701969275187573

theorem tailTrace_8287264 : CollatzResearch.WordTrace tailWord_8287264 prefixEnd_8287264 4255349742701969275187573 := by
  unfold tailWord_8287264
  simp only [CollatzResearch.WordTrace]
  refine ⟨151130674924332677427190423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201507566565776903236253897 151130674924332677427190423)
  ·
    refine ⟨226696012386499016140785635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151130674924332677427190423 226696012386499016140785635)
    ·
      refine ⟨340044018579748524211178453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226696012386499016140785635 340044018579748524211178453)
      ·
        refine ⟨7969781685462856036199495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 340044018579748524211178453 7969781685462856036199495)
        ·
          refine ⟨11954672528194284054299243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7969781685462856036199495 11954672528194284054299243)
          ·
            refine ⟨17932008792291426081448865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11954672528194284054299243 17932008792291426081448865)
            ·
              refine ⟨13449006594218569561086649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17932008792291426081448865 13449006594218569561086649)
              ·
                refine ⟨10086754945663927170814987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13449006594218569561086649 10086754945663927170814987)
                ·
                  refine ⟨15130132418495890756222481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10086754945663927170814987 15130132418495890756222481)
                  ·
                    refine ⟨11347599313871918067166861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15130132418495890756222481 11347599313871918067166861)
                    ·
                      refine ⟨4255349742701969275187573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11347599313871918067166861 4255349742701969275187573)
                      ·
                        rfl

theorem cell23_8287264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_8287264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287264 prefixEnd_8287264 := by exact prefixLift 8287264
  have htrace : WordTrace (prefixWord ++ tailWord_8287264) baseStart_8287264 baseEnd_8287264 := by
    simpa [prefixWord, tailWord_8287264, baseEnd_8287264] using wordTrace_append hprefix tailTrace_8287264
  have hstable : (prefixWord ++ tailWord_8287264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287264).length < 2 ^ (prefixWord ++ tailWord_8287264).sum := by decide
  have hdescent : baseEnd_8287264 < baseStart_8287264 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287313 : List Nat := [1, 2, 2, 1, 3, 1, 2, 3, 2, 2, 4]
def baseStart_8287313 : Nat := 118140960795 + 8287313 * 2 ^ 59
def prefixEnd_8287313 : Nat := 4983230072969 + 3 ^ 40 * 8287313 * 2
def baseEnd_8287313 : Nat := 4255374903254039583474847

theorem tailTrace_8287313 : CollatzResearch.WordTrace tailWord_8287313 prefixEnd_8287313 4255374903254039583474847 := by
  unfold tailWord_8287313
  simp only [CollatzResearch.WordTrace]
  refine ⟨302263137025487836222914593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201508758016991890815276395 302263137025487836222914593)
  ·
    refine ⟨226697352769115877167185945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302263137025487836222914593 226697352769115877167185945)
    ·
      refine ⟨170023014576836907875389459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226697352769115877167185945 170023014576836907875389459)
      ·
        refine ⟨255034521865255361813084189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170023014576836907875389459 255034521865255361813084189)
        ·
          refine ⟨95637945699470760679906571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255034521865255361813084189 95637945699470760679906571)
          ·
            refine ⟨143456918549206141019859857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95637945699470760679906571 143456918549206141019859857)
            ·
              refine ⟨107592688911904605764894893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143456918549206141019859857 107592688911904605764894893)
              ·
                refine ⟨40347258341964227161835585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107592688911904605764894893 40347258341964227161835585)
                ·
                  refine ⟨30260443756473170371376689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40347258341964227161835585 30260443756473170371376689)
                  ·
                    refine ⟨22695332817354877778532517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30260443756473170371376689 22695332817354877778532517)
                    ·
                      refine ⟨4255374903254039583474847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22695332817354877778532517 4255374903254039583474847)
                      ·
                        rfl

theorem cell23_8287313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 2, 4].length) (baseStart_8287313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287313 prefixEnd_8287313 := by exact prefixLift 8287313
  have htrace : WordTrace (prefixWord ++ tailWord_8287313) baseStart_8287313 baseEnd_8287313 := by
    simpa [prefixWord, tailWord_8287313, baseEnd_8287313] using wordTrace_append hprefix tailTrace_8287313
  have hstable : (prefixWord ++ tailWord_8287313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287313).length < 2 ^ (prefixWord ++ tailWord_8287313).sum := by decide
  have hdescent : baseEnd_8287313 < baseStart_8287313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287340 : List Nat := [2, 2, 1, 1, 3, 2, 2, 5, 5]
def baseStart_8287340 : Nat := 118140960795 + 8287340 * 2 ^ 59
def prefixEnd_8287340 : Nat := 4983230072969 + 3 ^ 40 * 8287340 * 2
def baseEnd_8287340 : Nat := 472820974136856775315247

theorem tailTrace_8287340 : CollatzResearch.WordTrace tailWord_8287340 prefixEnd_8287340 472820974136856775315247 := by
  unfold tailWord_8287340
  simp only [CollatzResearch.WordTrace]
  refine ⟨151132060898195009917073737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201509414530926679889431649 151132060898195009917073737)
  ·
    refine ⟨113349045673646257437805303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151132060898195009917073737 113349045673646257437805303)
    ·
      refine ⟨170023568510469386156707955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113349045673646257437805303 170023568510469386156707955)
      ·
        refine ⟨255035352765704079235061933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170023568510469386156707955 255035352765704079235061933)
        ·
          refine ⟨95638257287139029713148225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255035352765704079235061933 95638257287139029713148225)
          ·
            refine ⟨71728692965354272284861169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95638257287139029713148225 71728692965354272284861169)
            ·
              refine ⟨53796519724015704213645877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71728692965354272284861169 53796519724015704213645877)
              ·
                refine ⟨5043423724126472270029301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53796519724015704213645877 5043423724126472270029301)
                ·
                  refine ⟨472820974136856775315247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5043423724126472270029301 472820974136856775315247)
                  ·
                    rfl

theorem cell23_8287340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2, 5, 5].length) (baseStart_8287340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287340 prefixEnd_8287340 := by exact prefixLift 8287340
  have htrace : WordTrace (prefixWord ++ tailWord_8287340) baseStart_8287340 baseEnd_8287340 := by
    simpa [prefixWord, tailWord_8287340, baseEnd_8287340] using wordTrace_append hprefix tailTrace_8287340
  have hstable : (prefixWord ++ tailWord_8287340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287340).length < 2 ^ (prefixWord ++ tailWord_8287340).sum := by decide
  have hdescent : baseEnd_8287340 < baseStart_8287340 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287360 : List Nat := [2, 1, 1, 2, 1, 3, 3, 1, 2, 5, 2]
def baseStart_8287360 : Nat := 118140960795 + 8287360 * 2 ^ 59
def prefixEnd_8287360 : Nat := 4983230072969 + 3 ^ 40 * 8287360 * 2
def baseEnd_8287360 : Nat := 4255399036844800899587131

theorem tailTrace_8287360 : CollatzResearch.WordTrace tailWord_8287360 prefixEnd_8287360 4255399036844800899587131 := by
  unfold tailWord_8287360
  simp only [CollatzResearch.WordTrace]
  refine ⟨151132425628158781624937767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201509900837545042166583689 151132425628158781624937767)
  ·
    refine ⟨226698638442238172437406651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151132425628158781624937767 226698638442238172437406651)
    ·
      refine ⟨340047957663357258656109977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226698638442238172437406651 340047957663357258656109977)
      ·
        refine ⟨255035968247517943992082483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340047957663357258656109977 255035968247517943992082483)
        ·
          refine ⟨382553952371276915988123725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255035968247517943992082483 382553952371276915988123725)
          ·
            refine ⟨143457732139228843495546397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382553952371276915988123725 143457732139228843495546397)
            ·
              refine ⟨53796649552210816310829899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143457732139228843495546397 53796649552210816310829899)
              ·
                refine ⟨80694974328316224466244849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53796649552210816310829899 80694974328316224466244849)
                ·
                  refine ⟨60521230746237168349683637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80694974328316224466244849 60521230746237168349683637)
                  ·
                    refine ⟨5673865382459734532782841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60521230746237168349683637 5673865382459734532782841)
                    ·
                      refine ⟨4255399036844800899587131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5673865382459734532782841 4255399036844800899587131)
                      ·
                        rfl

theorem cell23_8287360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 3, 1, 2, 5, 2].length) (baseStart_8287360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287360 prefixEnd_8287360 := by exact prefixLift 8287360
  have htrace : WordTrace (prefixWord ++ tailWord_8287360) baseStart_8287360 baseEnd_8287360 := by
    simpa [prefixWord, tailWord_8287360, baseEnd_8287360] using wordTrace_append hprefix tailTrace_8287360
  have hstable : (prefixWord ++ tailWord_8287360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287360).length < 2 ^ (prefixWord ++ tailWord_8287360).sum := by decide
  have hdescent : baseEnd_8287360 < baseStart_8287360 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287363 : List Nat := [1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 5]
def baseStart_8287363 : Nat := 118140960795 + 8287363 * 2 ^ 59
def prefixEnd_8287363 : Nat := 4983230072969 + 3 ^ 40 * 8287363 * 2
def baseEnd_8287363 : Nat := 4255400577286764387849617

theorem tailTrace_8287363 : CollatzResearch.WordTrace tailWord_8287363 prefixEnd_8287363 4255400577286764387849617 := by
  unfold tailWord_8287363
  simp only [CollatzResearch.WordTrace]
  refine ⟨302264960675306694762234743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201509973783537796508156495 302264960675306694762234743)
  ·
    refine ⟨453397441012960042143352115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302264960675306694762234743 453397441012960042143352115)
    ·
      refine ⟨680096161519440063215028173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453397441012960042143352115 680096161519440063215028173)
      ·
        refine ⟨255036060569790023705635565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 680096161519440063215028173 255036060569790023705635565)
        ·
          refine ⟨95638522713671258889613337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255036060569790023705635565 95638522713671258889613337)
          ·
            refine ⟨71728892035253444167210003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95638522713671258889613337 71728892035253444167210003)
            ·
              refine ⟨107593338052880166250815005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71728892035253444167210003 107593338052880166250815005)
              ·
                refine ⟨40347501769830062344055627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107593338052880166250815005 40347501769830062344055627)
                ·
                  refine ⟨60521252654745093516083441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40347501769830062344055627 60521252654745093516083441)
                  ·
                    refine ⟨45390939491058820137062581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60521252654745093516083441 45390939491058820137062581)
                    ·
                      refine ⟨4255400577286764387849617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45390939491058820137062581 4255400577286764387849617)
                      ·
                        rfl

theorem cell23_8287363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 3, 1, 2, 5].length) (baseStart_8287363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287363 prefixEnd_8287363 := by exact prefixLift 8287363
  have htrace : WordTrace (prefixWord ++ tailWord_8287363) baseStart_8287363 baseEnd_8287363 := by
    simpa [prefixWord, tailWord_8287363, baseEnd_8287363] using wordTrace_append hprefix tailTrace_8287363
  have hstable : (prefixWord ++ tailWord_8287363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287363).length < 2 ^ (prefixWord ++ tailWord_8287363).sum := by decide
  have hdescent : baseEnd_8287363 < baseStart_8287363 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287417 : List Nat := [1, 2, 1, 4, 1, 4, 2, 1, 3, 4]
def baseStart_8287417 : Nat := 118140960795 + 8287417 * 2 ^ 59
def prefixEnd_8287417 : Nat := 4983230072969 + 3 ^ 40 * 8287417 * 2
def baseEnd_8287417 : Nat := 1418476101747369058858123

theorem tailTrace_8287417 : CollatzResearch.WordTrace tailWord_8287417 prefixEnd_8287417 1418476101747369058858123 := by
  unfold tailWord_8287417
  simp only [CollatzResearch.WordTrace]
  refine ⟨302266930217111061984700505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201511286811407374656467003 302266930217111061984700505)
  ·
    refine ⟨226700197662833296488525379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302266930217111061984700505 226700197662833296488525379)
    ·
      refine ⟨340050296494249944732788069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226700197662833296488525379 340050296494249944732788069)
      ·
        refine ⟨63759430592671864637397763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340050296494249944732788069 63759430592671864637397763)
        ·
          refine ⟨95639145889007796956096645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63759430592671864637397763 95639145889007796956096645)
          ·
            refine ⟨17932339854188961929268121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95639145889007796956096645 17932339854188961929268121)
            ·
              refine ⟨13449254890641721446951091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17932339854188961929268121 13449254890641721446951091)
              ·
                refine ⟨20173882335962582170426637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13449254890641721446951091 20173882335962582170426637)
                ·
                  refine ⟨7565205875985968313909989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20173882335962582170426637 7565205875985968313909989)
                  ·
                    refine ⟨1418476101747369058858123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7565205875985968313909989 1418476101747369058858123)
                    ·
                      rfl

theorem cell23_8287417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 4].length) (baseStart_8287417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287417 prefixEnd_8287417 := by exact prefixLift 8287417
  have htrace : WordTrace (prefixWord ++ tailWord_8287417) baseStart_8287417 baseEnd_8287417 := by
    simpa [prefixWord, tailWord_8287417, baseEnd_8287417] using wordTrace_append hprefix tailTrace_8287417
  have hstable : (prefixWord ++ tailWord_8287417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287417).length < 2 ^ (prefixWord ++ tailWord_8287417).sum := by decide
  have hdescent : baseEnd_8287417 < baseStart_8287417 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287467 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 4, 3, 2]
def baseStart_8287467 : Nat := 118140960795 + 8287467 * 2 ^ 59
def prefixEnd_8287467 : Nat := 4983230072969 + 3 ^ 40 * 8287467 * 2
def baseEnd_8287467 : Nat := 4255453979274831980949139

theorem tailTrace_8287467 : CollatzResearch.WordTrace tailWord_8287467 prefixEnd_8287467 4255453979274831980949139 := by
  unfold tailWord_8287467
  simp only [CollatzResearch.WordTrace]
  refine ⟨302268753866929920524020655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201512502577953280349347103 302268753866929920524020655)
  ·
    refine ⟨453403130800394880786030983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302268753866929920524020655 453403130800394880786030983)
    ·
      refine ⟨680104696200592321179046475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453403130800394880786030983 680104696200592321179046475)
      ·
        refine ⟨1020157044300888481768569713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680104696200592321179046475 1020157044300888481768569713)
        ·
          refine ⟨765117783225666361326427285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1020157044300888481768569713 765117783225666361326427285)
          ·
            refine ⟨35864896088703110687176279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 765117783225666361326427285 35864896088703110687176279)
            ·
              refine ⟨53797344133054666030764419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35864896088703110687176279 53797344133054666030764419)
              ·
                refine ⟨80696016199581999046146629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53797344133054666030764419 80696016199581999046146629)
                ·
                  refine ⟨15130503037421624821152493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80696016199581999046146629 15130503037421624821152493)
                  ·
                    refine ⟨5673938639033109307932185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15130503037421624821152493 5673938639033109307932185)
                    ·
                      refine ⟨4255453979274831980949139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5673938639033109307932185 4255453979274831980949139)
                      ·
                        rfl

theorem cell23_8287467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 3, 2].length) (baseStart_8287467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287467 prefixEnd_8287467 := by exact prefixLift 8287467
  have htrace : WordTrace (prefixWord ++ tailWord_8287467) baseStart_8287467 baseEnd_8287467 := by
    simpa [prefixWord, tailWord_8287467, baseEnd_8287467] using wordTrace_append hprefix tailTrace_8287467
  have hstable : (prefixWord ++ tailWord_8287467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287467).length < 2 ^ (prefixWord ++ tailWord_8287467).sum := by decide
  have hdescent : baseEnd_8287467 < baseStart_8287467 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287520 : List Nat := [2, 1, 1, 5, 3, 11]
def baseStart_8287520 : Nat := 118140960795 + 8287520 * 2 ^ 59
def prefixEnd_8287520 : Nat := 4983230072969 + 3 ^ 40 * 8287520 * 2
def baseEnd_8287520 : Nat := 17512268287035062854265

theorem tailTrace_8287520 : CollatzResearch.WordTrace tailWord_8287520 prefixEnd_8287520 17512268287035062854265 := by
  unfold tailWord_8287520
  simp only [CollatzResearch.WordTrace]
  refine ⟨151135343467868955287850007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201513791290491940383800009 151135343467868955287850007)
  ·
    refine ⟨226703015201803432931775011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151135343467868955287850007 226703015201803432931775011)
    ·
      refine ⟨340054522802705149397662517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226703015201803432931775011 340054522802705149397662517)
      ·
        refine ⟨31880111512753607756030861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 340054522802705149397662517 31880111512753607756030861)
        ·
          refine ⟨11955041817282602908511573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31880111512753607756030861 11955041817282602908511573)
          ·
            refine ⟨17512268287035062854265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11955041817282602908511573 17512268287035062854265)
            ·
              rfl

theorem cell23_8287520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 11].length) (baseStart_8287520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287520 prefixEnd_8287520 := by exact prefixLift 8287520
  have htrace : WordTrace (prefixWord ++ tailWord_8287520) baseStart_8287520 baseEnd_8287520 := by
    simpa [prefixWord, tailWord_8287520, baseEnd_8287520] using wordTrace_append hprefix tailTrace_8287520
  have hstable : (prefixWord ++ tailWord_8287520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287520).length < 2 ^ (prefixWord ++ tailWord_8287520).sum := by decide
  have hdescent : baseEnd_8287520 < baseStart_8287520 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287524 : List Nat := [2, 3, 1, 3, 1, 1, 4, 2, 2, 4]
def baseStart_8287524 : Nat := 118140960795 + 8287524 * 2 ^ 59
def prefixEnd_8287524 : Nat := 4983230072969 + 3 ^ 40 * 8287524 * 2
def baseEnd_8287524 : Nat := 1418494415890712752645459

theorem tailTrace_8287524 : CollatzResearch.WordTrace tailWord_8287524 prefixEnd_8287524 1418494415890712752645459 := by
  unfold tailWord_8287524
  simp only [CollatzResearch.WordTrace]
  refine ⟨151135416413861709629422813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201513888551815612839230417 151135416413861709629422813)
  ·
    refine ⟨56675781155198141111033555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151135416413861709629422813 56675781155198141111033555)
    ·
      refine ⟨85013671732797211666550333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56675781155198141111033555 85013671732797211666550333)
      ·
        refine ⟨31880126899798954374956375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85013671732797211666550333 31880126899798954374956375)
        ·
          refine ⟨47820190349698431562434563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31880126899798954374956375 47820190349698431562434563)
          ·
            refine ⟨71730285524547647343651845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47820190349698431562434563 71730285524547647343651845)
            ·
              refine ⟨13449428535852683876934721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71730285524547647343651845 13449428535852683876934721)
              ·
                refine ⟨10087071401889512907701041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13449428535852683876934721 10087071401889512907701041)
                ·
                  refine ⟨7565303551417134680775781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10087071401889512907701041 7565303551417134680775781)
                  ·
                    refine ⟨1418494415890712752645459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7565303551417134680775781 1418494415890712752645459)
                    ·
                      rfl

theorem cell23_8287524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 4, 2, 2, 4].length) (baseStart_8287524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287524 prefixEnd_8287524 := by exact prefixLift 8287524
  have htrace : WordTrace (prefixWord ++ tailWord_8287524) baseStart_8287524 baseEnd_8287524 := by
    simpa [prefixWord, tailWord_8287524, baseEnd_8287524] using wordTrace_append hprefix tailTrace_8287524
  have hstable : (prefixWord ++ tailWord_8287524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287524).length < 2 ^ (prefixWord ++ tailWord_8287524).sum := by decide
  have hdescent : baseEnd_8287524 < baseStart_8287524 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287537 : List Nat := [1, 2, 2, 3, 3, 3, 1, 8]
def baseStart_8287537 : Nat := 118140960795 + 8287537 * 2 ^ 59
def prefixEnd_8287537 : Nat := 4983230072969 + 3 ^ 40 * 8287537 * 2
def baseEnd_8287537 : Nat := 157610737885949878039771

theorem tailTrace_8287537 : CollatzResearch.WordTrace tailWord_8287537 prefixEnd_8287537 157610737885949878039771 := by
  unfold tailWord_8287537
  simp only [CollatzResearch.WordTrace]
  refine ⟨302271306976676322479068865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201514204651117548319379243 302271306976676322479068865)
  ·
    refine ⟨226703480232507241859301649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302271306976676322479068865 226703480232507241859301649)
    ·
      refine ⟨170027610174380431394476237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226703480232507241859301649 170027610174380431394476237)
      ·
        refine ⟨63760353815392661772928589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170027610174380431394476237 63760353815392661772928589)
        ·
          refine ⟨23910132680772248164848221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63760353815392661772928589 23910132680772248164848221)
          ·
            refine ⟨8966299755289593061818083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23910132680772248164848221 8966299755289593061818083)
            ·
              refine ⟨13449449632934389592727125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8966299755289593061818083 13449449632934389592727125)
              ·
                refine ⟨157610737885949878039771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13449449632934389592727125 157610737885949878039771)
                ·
                  rfl

theorem cell23_8287537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 3, 1, 8].length) (baseStart_8287537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287537 prefixEnd_8287537 := by exact prefixLift 8287537
  have htrace : WordTrace (prefixWord ++ tailWord_8287537) baseStart_8287537 baseEnd_8287537 := by
    simpa [prefixWord, tailWord_8287537, baseEnd_8287537] using wordTrace_append hprefix tailTrace_8287537
  have hstable : (prefixWord ++ tailWord_8287537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287537).length < 2 ^ (prefixWord ++ tailWord_8287537).sum := by decide
  have hdescent : baseEnd_8287537 < baseStart_8287537 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287560 : List Nat := [2, 1, 3, 1, 1, 2, 1, 3, 2, 2, 5]
def baseStart_8287560 : Nat := 118140960795 + 8287560 * 2 ^ 59
def prefixEnd_8287560 : Nat := 4983230072969 + 3 ^ 40 * 8287560 * 2
def baseEnd_8287560 : Nat := 4255501732975700117086211

theorem tailTrace_8287560 : CollatzResearch.WordTrace tailWord_8287560 prefixEnd_8287560 4255501732975700117086211 := by
  unfold tailWord_8287560
  simp only [CollatzResearch.WordTrace]
  refine ⟨151136072927796498703578067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201514763903728664938104089 151136072927796498703578067)
  ·
    refine ⟨226704109391694748055367101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151136072927796498703578067 226704109391694748055367101)
    ·
      refine ⟨85014041021885530520762663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226704109391694748055367101 85014041021885530520762663)
      ·
        refine ⟨127521061532828295781143995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85014041021885530520762663 127521061532828295781143995)
        ·
          refine ⟨191281592299242443671715993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127521061532828295781143995 191281592299242443671715993)
          ·
            refine ⟨143461194224431832753786995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191281592299242443671715993 143461194224431832753786995)
            ·
              refine ⟨215191791336647749130680493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143461194224431832753786995 215191791336647749130680493)
              ·
                refine ⟨80696921751242905924005185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215191791336647749130680493 80696921751242905924005185)
                ·
                  refine ⟨60522691313432179443003889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80696921751242905924005185 60522691313432179443003889)
                  ·
                    refine ⟨45392018485074134582252917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60522691313432179443003889 45392018485074134582252917)
                    ·
                      refine ⟨4255501732975700117086211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45392018485074134582252917 4255501732975700117086211)
                      ·
                        rfl

theorem cell23_8287560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_8287560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287560 prefixEnd_8287560 := by exact prefixLift 8287560
  have htrace : WordTrace (prefixWord ++ tailWord_8287560) baseStart_8287560 baseEnd_8287560 := by
    simpa [prefixWord, tailWord_8287560, baseEnd_8287560] using wordTrace_append hprefix tailTrace_8287560
  have hstable : (prefixWord ++ tailWord_8287560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287560).length < 2 ^ (prefixWord ++ tailWord_8287560).sum := by decide
  have hdescent : baseEnd_8287560 < baseStart_8287560 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287565 : List Nat := [1, 6, 1, 3, 1, 2, 2, 1, 1, 1, 4]
def baseStart_8287565 : Nat := 118140960795 + 8287565 * 2 ^ 59
def prefixEnd_8287565 : Nat := 4983230072969 + 3 ^ 40 * 8287565 * 2
def baseEnd_8287565 : Nat := 4255504300378972597523689

theorem tailTrace_8287565 : CollatzResearch.WordTrace tailWord_8287565 prefixEnd_8287565 4255504300378972597523689 := by
  unfold tailWord_8287565
  simp only [CollatzResearch.WordTrace]
  refine ⟨302272328220574883261088149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201514885480383255507392099 302272328220574883261088149)
  ·
    refine ⟨14169015385339447652863507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 302272328220574883261088149 14169015385339447652863507)
    ·
      refine ⟨21253523078009171479295261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14169015385339447652863507 21253523078009171479295261)
      ·
        refine ⟨7970071154253439304735723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21253523078009171479295261 7970071154253439304735723)
        ·
          refine ⟨11955106731380158957103585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7970071154253439304735723 11955106731380158957103585)
          ·
            refine ⟨8966330048535119217827689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11955106731380158957103585 8966330048535119217827689)
            ·
              refine ⟨6724747536401339413370767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8966330048535119217827689 6724747536401339413370767)
              ·
                refine ⟨10087121304602009120056151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6724747536401339413370767 10087121304602009120056151)
                ·
                  refine ⟨15130681956903013680084227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10087121304602009120056151 15130681956903013680084227)
                  ·
                    refine ⟨22696022935354520520126341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15130681956903013680084227 22696022935354520520126341)
                    ·
                      refine ⟨4255504300378972597523689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22696022935354520520126341 4255504300378972597523689)
                      ·
                        rfl

theorem cell23_8287565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 2, 2, 1, 1, 1, 4].length) (baseStart_8287565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287565 prefixEnd_8287565 := by exact prefixLift 8287565
  have htrace : WordTrace (prefixWord ++ tailWord_8287565) baseStart_8287565 baseEnd_8287565 := by
    simpa [prefixWord, tailWord_8287565, baseEnd_8287565] using wordTrace_append hprefix tailTrace_8287565
  have hstable : (prefixWord ++ tailWord_8287565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287565).length < 2 ^ (prefixWord ++ tailWord_8287565).sum := by decide
  have hdescent : baseEnd_8287565 < baseStart_8287565 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287597 : List Nat := [1, 5, 1, 1, 1, 3, 2, 1, 2, 6]
def baseStart_8287597 : Nat := 118140960795 + 8287597 * 2 ^ 59
def prefixEnd_8287597 : Nat := 4983230072969 + 3 ^ 40 * 8287597 * 2
def baseEnd_8287597 : Nat := 1418506910586638824107847

theorem tailTrace_8287597 : CollatzResearch.WordTrace tailWord_8287597 prefixEnd_8287597 1418506910586638824107847 := by
  unfold tailWord_8287597
  simp only [CollatzResearch.WordTrace]
  refine ⟨302273495356458952726253045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201515663570972635150835363 302273495356458952726253045)
  ·
    refine ⟨28338140189668026818086223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302273495356458952726253045 28338140189668026818086223)
    ·
      refine ⟨42507210284502040227129335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28338140189668026818086223 42507210284502040227129335)
      ·
        refine ⟨63760815426753060340694003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42507210284502040227129335 63760815426753060340694003)
        ·
          refine ⟨95641223140129590511041005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63760815426753060340694003 95641223140129590511041005)
          ·
            refine ⟨35865458677548596441640377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95641223140129590511041005 35865458677548596441640377)
            ·
              refine ⟨26899094008161447331230283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35865458677548596441640377 26899094008161447331230283)
              ·
                refine ⟨40348641012242170996845425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26899094008161447331230283 40348641012242170996845425)
                ·
                  refine ⟨30261480759181628247634069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40348641012242170996845425 30261480759181628247634069)
                  ·
                    refine ⟨1418506910586638824107847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30261480759181628247634069 1418506910586638824107847)
                    ·
                      rfl

theorem cell23_8287597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_8287597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287597 prefixEnd_8287597 := by exact prefixLift 8287597
  have htrace : WordTrace (prefixWord ++ tailWord_8287597) baseStart_8287597 baseEnd_8287597 := by
    simpa [prefixWord, tailWord_8287597, baseEnd_8287597] using wordTrace_append hprefix tailTrace_8287597
  have hstable : (prefixWord ++ tailWord_8287597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287597).length < 2 ^ (prefixWord ++ tailWord_8287597).sum := by decide
  have hdescent : baseEnd_8287597 < baseStart_8287597 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287598 : List Nat := [4, 1, 2, 4, 1, 2, 1, 1, 1, 3, 3]
def baseStart_8287598 : Nat := 118140960795 + 8287598 * 2 ^ 59
def prefixEnd_8287598 : Nat := 4983230072969 + 3 ^ 40 * 8287598 * 2
def baseEnd_8287598 : Nat := 4255521245240570968411037

theorem tailTrace_8287598 : CollatzResearch.WordTrace tailWord_8287598 prefixEnd_8287598 4255521245240570968411037 := by
  unfold tailWord_8287598
  simp only [CollatzResearch.WordTrace]
  refine ⟨37784191478681916237129931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201515687886303553264692965 37784191478681916237129931)
  ·
    refine ⟨56676287218022874355694897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37784191478681916237129931 56676287218022874355694897)
    ·
      refine ⟨42507215413517155766771173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56676287218022874355694897 42507215413517155766771173)
      ·
        refine ⟨7970102890034466706269595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42507215413517155766771173 7970102890034466706269595)
        ·
          refine ⟨11955154335051700059404393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7970102890034466706269595 11955154335051700059404393)
          ·
            refine ⟨8966365751288775044553295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11955154335051700059404393 8966365751288775044553295)
            ·
              refine ⟨13449548626933162566829943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8966365751288775044553295 13449548626933162566829943)
              ·
                refine ⟨20174322940399743850244915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13449548626933162566829943 20174322940399743850244915)
                ·
                  refine ⟨30261484410599615775367373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20174322940399743850244915 30261484410599615775367373)
                  ·
                    refine ⟨11348056653974855915762765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30261484410599615775367373 11348056653974855915762765)
                    ·
                      refine ⟨4255521245240570968411037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11348056653974855915762765 4255521245240570968411037)
                      ·
                        rfl

theorem cell23_8287598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 1, 3, 3].length) (baseStart_8287598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287598 prefixEnd_8287598 := by exact prefixLift 8287598
  have htrace : WordTrace (prefixWord ++ tailWord_8287598) baseStart_8287598 baseEnd_8287598 := by
    simpa [prefixWord, tailWord_8287598, baseEnd_8287598] using wordTrace_append hprefix tailTrace_8287598
  have hstable : (prefixWord ++ tailWord_8287598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287598).length < 2 ^ (prefixWord ++ tailWord_8287598).sum := by decide
  have hdescent : baseEnd_8287598 < baseStart_8287598 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287637 : List Nat := [1, 3, 2, 1, 1, 2, 2, 1, 4, 3, 3]
def baseStart_8287637 : Nat := 118140960795 + 8287637 * 2 ^ 59
def prefixEnd_8287637 : Nat := 4983230072969 + 3 ^ 40 * 8287637 * 2
def baseEnd_8287637 : Nat := 4255541270986096315823357

theorem tailTrace_8287637 : CollatzResearch.WordTrace tailWord_8287637 prefixEnd_8287637 4255541270986096315823357 := by
  unfold tailWord_8287637
  simp only [CollatzResearch.WordTrace]
  refine ⟨302274954276314039557709165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201516636184209359705139443 302274954276314039557709165)
  ·
    refine ⟨113353107853617764834140937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302274954276314039557709165 113353107853617764834140937)
    ·
      refine ⟨85014830890213323625605703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113353107853617764834140937 85014830890213323625605703)
      ·
        refine ⟨127522246335319985438408555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85014830890213323625605703 127522246335319985438408555)
        ·
          refine ⟨191283369502979978157612833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127522246335319985438408555 191283369502979978157612833)
          ·
            refine ⟨143462527127234983618209625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191283369502979978157612833 143462527127234983618209625)
            ·
              refine ⟨107596895345426237713657219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143462527127234983618209625 107596895345426237713657219)
              ·
                refine ⟨161395343018139356570485829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107596895345426237713657219 161395343018139356570485829)
                ·
                  refine ⟨30261626815901129356966093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161395343018139356570485829 30261626815901129356966093)
                  ·
                    refine ⟨11348110055962923508862285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30261626815901129356966093 11348110055962923508862285)
                    ·
                      refine ⟨4255541270986096315823357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11348110055962923508862285 4255541270986096315823357)
                      ·
                        rfl

theorem cell23_8287637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 4, 3, 3].length) (baseStart_8287637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287637 prefixEnd_8287637 := by exact prefixLift 8287637
  have htrace : WordTrace (prefixWord ++ tailWord_8287637) baseStart_8287637 baseEnd_8287637 := by
    simpa [prefixWord, tailWord_8287637, baseEnd_8287637] using wordTrace_append hprefix tailTrace_8287637
  have hstable : (prefixWord ++ tailWord_8287637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287637).length < 2 ^ (prefixWord ++ tailWord_8287637).sum := by decide
  have hdescent : baseEnd_8287637 < baseStart_8287637 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287684 : List Nat := [2, 3, 3, 2, 1, 1, 1, 2, 1, 2, 5]
def baseStart_8287684 : Nat := 118140960795 + 8287684 * 2 ^ 59
def prefixEnd_8287684 : Nat := 4983230072969 + 3 ^ 40 * 8287684 * 2
def baseEnd_8287684 : Nat := 4255565404576857631935641

theorem tailTrace_8287684 : CollatzResearch.WordTrace tailWord_8287684 prefixEnd_8287684 4255565404576857631935641 := by
  unfold tailWord_8287684
  simp only [CollatzResearch.WordTrace]
  refine ⟨151138334253571883292335053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201517779004762511056446737 151138334253571883292335053)
  ·
    refine ⟨56676875345089456234625645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151138334253571883292335053 56676875345089456234625645)
    ·
      refine ⟨21253828254408546087984617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56676875345089456234625645 21253828254408546087984617)
      ·
        refine ⟨15940371190806409565988463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21253828254408546087984617 15940371190806409565988463)
        ·
          refine ⟨23910556786209614348982695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15940371190806409565988463 23910556786209614348982695)
          ·
            refine ⟨35865835179314421523474043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23910556786209614348982695 35865835179314421523474043)
            ·
              refine ⟨53798752768971632285211065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35865835179314421523474043 53798752768971632285211065)
              ·
                refine ⟨40349064576728724213908299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53798752768971632285211065 40349064576728724213908299)
                ·
                  refine ⟨60523596865093086320862449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40349064576728724213908299 60523596865093086320862449)
                  ·
                    refine ⟨45392697648819814740646837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 60523596865093086320862449 45392697648819814740646837)
                    ·
                      refine ⟨4255565404576857631935641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45392697648819814740646837 4255565404576857631935641)
                      ·
                        rfl

theorem cell23_8287684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_8287684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287684 prefixEnd_8287684 := by exact prefixLift 8287684
  have htrace : WordTrace (prefixWord ++ tailWord_8287684) baseStart_8287684 baseEnd_8287684 := by
    simpa [prefixWord, tailWord_8287684, baseEnd_8287684] using wordTrace_append hprefix tailTrace_8287684
  have hstable : (prefixWord ++ tailWord_8287684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287684).length < 2 ^ (prefixWord ++ tailWord_8287684).sum := by decide
  have hdescent : baseEnd_8287684 < baseStart_8287684 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287694 : List Nat := [4, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4]
def baseStart_8287694 : Nat := 118140960795 + 8287694 * 2 ^ 59
def prefixEnd_8287694 : Nat := 4983230072969 + 3 ^ 40 * 8287694 * 2
def baseEnd_8287694 : Nat := 4255570539383402592810595

theorem tailTrace_8287694 : CollatzResearch.WordTrace tailWord_8287694 prefixEnd_8287694 4255570539383402592810595 := by
  unfold tailWord_8287694
  simp only [CollatzResearch.WordTrace]
  refine ⟨37784629154638442286566767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201518022158071692195022757 37784629154638442286566767)
  ·
    refine ⟨56676943731957663429850151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37784629154638442286566767 56676943731957663429850151)
    ·
      refine ⟨85015415597936495144775227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56676943731957663429850151 85015415597936495144775227)
      ·
        refine ⟨127523123396904742717162841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85015415597936495144775227 127523123396904742717162841)
        ·
          refine ⟨95642342547678557037872131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127523123396904742717162841 95642342547678557037872131)
          ·
            refine ⟨143463513821517835556808197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95642342547678557037872131 143463513821517835556808197)
            ·
              refine ⟨26899408841534594166901537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143463513821517835556808197 26899408841534594166901537)
              ·
                refine ⟨20174556631150945625176153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26899408841534594166901537 20174556631150945625176153)
                ·
                  refine ⟨15130917473363209218882115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20174556631150945625176153 15130917473363209218882115)
                  ·
                    refine ⟨22696376210044813828323173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15130917473363209218882115 22696376210044813828323173)
                    ·
                      refine ⟨4255570539383402592810595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22696376210044813828323173 4255570539383402592810595)
                      ·
                        rfl

theorem cell23_8287694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4].length) (baseStart_8287694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287694 prefixEnd_8287694 := by exact prefixLift 8287694
  have htrace : WordTrace (prefixWord ++ tailWord_8287694) baseStart_8287694 baseEnd_8287694 := by
    simpa [prefixWord, tailWord_8287694, baseEnd_8287694] using wordTrace_append hprefix tailTrace_8287694
  have hstable : (prefixWord ++ tailWord_8287694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287694).length < 2 ^ (prefixWord ++ tailWord_8287694).sum := by decide
  have hdescent : baseEnd_8287694 < baseStart_8287694 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287697 : List Nat := [1, 2, 2, 1, 2, 1, 1, 1, 5, 4, 3]
def baseStart_8287697 : Nat := 118140960795 + 8287697 * 2 ^ 59
def prefixEnd_8287697 : Nat := 4983230072969 + 3 ^ 40 * 8287697 * 2
def baseEnd_8287697 : Nat := 4255572079825366081073081

theorem tailTrace_8287697 : CollatzResearch.WordTrace tailWord_8287697 prefixEnd_8287697 4255572079825366081073081 := by
  unfold tailWord_8287697
  simp only [CollatzResearch.WordTrace]
  refine ⟨302277142656096669804893345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201518095104064446536595563 302277142656096669804893345)
  ·
    refine ⟨226707856992072502353670009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302277142656096669804893345 226707856992072502353670009)
    ·
      refine ⟨170030892744054376765252507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226707856992072502353670009 170030892744054376765252507)
      ·
        refine ⟨255046339116081565147878761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170030892744054376765252507 255046339116081565147878761)
        ·
          refine ⟨191284754337061173860909071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255046339116081565147878761 191284754337061173860909071)
          ·
            refine ⟨286927131505591760791363607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191284754337061173860909071 286927131505591760791363607)
            ·
              refine ⟨430390697258387641187045411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286927131505591760791363607 430390697258387641187045411)
              ·
                refine ⟨645586045887581461780568117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430390697258387641187045411 645586045887581461780568117)
                ·
                  refine ⟨60523691801960762041928261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 645586045887581461780568117 60523691801960762041928261)
                  ·
                    refine ⟨11348192212867642882861549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60523691801960762041928261 11348192212867642882861549)
                    ·
                      refine ⟨4255572079825366081073081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11348192212867642882861549 4255572079825366081073081)
                      ·
                        rfl

theorem cell23_8287697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 1, 5, 4, 3].length) (baseStart_8287697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287697 prefixEnd_8287697 := by exact prefixLift 8287697
  have htrace : WordTrace (prefixWord ++ tailWord_8287697) baseStart_8287697 baseEnd_8287697 := by
    simpa [prefixWord, tailWord_8287697, baseEnd_8287697] using wordTrace_append hprefix tailTrace_8287697
  have hstable : (prefixWord ++ tailWord_8287697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287697).length < 2 ^ (prefixWord ++ tailWord_8287697).sum := by decide
  have hdescent : baseEnd_8287697 < baseStart_8287697 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287747 : List Nat := [1, 1, 1, 3, 2, 1, 2, 2, 5, 5]
def baseStart_8287747 : Nat := 118140960795 + 8287747 * 2 ^ 59
def prefixEnd_8287747 : Nat := 4983230072969 + 3 ^ 40 * 8287747 * 2
def baseEnd_8287747 : Nat := 1418532584619363628482617

theorem tailTrace_8287747 : CollatzResearch.WordTrace tailWord_8287747 prefixEnd_8287747 1418532584619363628482617 := by
  unfold tailWord_8287747
  simp only [CollatzResearch.WordTrace]
  refine ⟨302278966305915528344213495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201519310870610352229475663 302278966305915528344213495)
  ·
    refine ⟨453418449458873292516320243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302278966305915528344213495 453418449458873292516320243)
    ·
      refine ⟨680127674188309938774480365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453418449458873292516320243 680127674188309938774480365)
      ·
        refine ⟨255047877820616227040430137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 680127674188309938774480365 255047877820616227040430137)
        ·
          refine ⟨191285908365462170280322603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255047877820616227040430137 191285908365462170280322603)
          ·
            refine ⟨286928862548193255420483905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191285908365462170280322603 286928862548193255420483905)
            ·
              refine ⟨215196646911144941565362929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286928862548193255420483905 215196646911144941565362929)
              ·
                refine ⟨161397485183358706174022197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215196646911144941565362929 161397485183358706174022197)
                ·
                  refine ⟨15131014235939878703814581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161397485183358706174022197 15131014235939878703814581)
                  ·
                    refine ⟨1418532584619363628482617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15131014235939878703814581 1418532584619363628482617)
                    ·
                      rfl

theorem cell23_8287747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 2, 5, 5].length) (baseStart_8287747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287747 prefixEnd_8287747 := by exact prefixLift 8287747
  have htrace : WordTrace (prefixWord ++ tailWord_8287747) baseStart_8287747 baseEnd_8287747 := by
    simpa [prefixWord, tailWord_8287747, baseEnd_8287747] using wordTrace_append hprefix tailTrace_8287747
  have hstable : (prefixWord ++ tailWord_8287747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287747).length < 2 ^ (prefixWord ++ tailWord_8287747).sum := by decide
  have hdescent : baseEnd_8287747 < baseStart_8287747 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287751 : List Nat := [1, 1, 4, 3, 2, 3, 1, 2, 6]
def baseStart_8287751 : Nat := 118140960795 + 8287751 * 2 ^ 59
def prefixEnd_8287751 : Nat := 4983230072969 + 3 ^ 40 * 8287751 * 2
def baseEnd_8287751 : Nat := 472844423086745429977537

theorem tailTrace_8287751 : CollatzResearch.WordTrace tailWord_8287751 prefixEnd_8287751 472844423086745429977537 := by
  unfold tailWord_8287751
  simp only [CollatzResearch.WordTrace]
  refine ⟨302279112197901037027359107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201519408131934024684906071 302279112197901037027359107)
  ·
    refine ⟨453418668296851555541038661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302279112197901037027359107 453418668296851555541038661)
    ·
      refine ⟨85016000305659666663944749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 453418668296851555541038661 85016000305659666663944749)
      ·
        refine ⟨31881000114622374998979281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85016000305659666663944749 31881000114622374998979281)
        ·
          refine ⟨23910750085966781249234461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31881000114622374998979281 23910750085966781249234461)
          ·
            refine ⟨8966531282237542968462923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23910750085966781249234461 8966531282237542968462923)
            ·
              refine ⟨13449796923356314452694385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8966531282237542968462923 13449796923356314452694385)
              ·
                refine ⟨10087347692517235839520789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13449796923356314452694385 10087347692517235839520789)
                ·
                  refine ⟨472844423086745429977537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10087347692517235839520789 472844423086745429977537)
                  ·
                    rfl

theorem cell23_8287751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 1, 2, 6].length) (baseStart_8287751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287751 prefixEnd_8287751 := by exact prefixLift 8287751
  have htrace : WordTrace (prefixWord ++ tailWord_8287751) baseStart_8287751 baseEnd_8287751 := by
    simpa [prefixWord, tailWord_8287751, baseEnd_8287751] using wordTrace_append hprefix tailTrace_8287751
  have hstable : (prefixWord ++ tailWord_8287751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287751).length < 2 ^ (prefixWord ++ tailWord_8287751).sum := by decide
  have hdescent : baseEnd_8287751 < baseStart_8287751 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287761 : List Nat := [1, 2, 2, 1, 1, 2, 6, 1, 3, 1, 3]
def baseStart_8287761 : Nat := 118140960795 + 8287761 * 2 ^ 59
def prefixEnd_8287761 : Nat := 4983230072969 + 3 ^ 40 * 8287761 * 2
def baseEnd_8287761 : Nat := 4255604942587253830672787

theorem tailTrace_8287761 : CollatzResearch.WordTrace tailWord_8287761 prefixEnd_8287761 4255604942587253830672787 := by
  unfold tailWord_8287761
  simp only [CollatzResearch.WordTrace]
  refine ⟨302279476927864808735223137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201519651285243205823482091 302279476927864808735223137)
  ·
    refine ⟨226709607695898606551417353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302279476927864808735223137 226709607695898606551417353)
    ·
      refine ⟨170032205771923954913563015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226709607695898606551417353 170032205771923954913563015)
      ·
        refine ⟨255048308657885932370344523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170032205771923954913563015 255048308657885932370344523)
        ·
          refine ⟨382572462986828898555516785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255048308657885932370344523 382572462986828898555516785)
          ·
            refine ⟨286929347240121673916637589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382572462986828898555516785 286929347240121673916637589)
            ·
              refine ⟨13449813151880703464842387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 286929347240121673916637589 13449813151880703464842387)
              ·
                refine ⟨20174719727821055197263581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13449813151880703464842387 20174719727821055197263581)
                ·
                  refine ⟨7565519897932895698973843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20174719727821055197263581 7565519897932895698973843)
                  ·
                    refine ⟨11348279846899343548460765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7565519897932895698973843 11348279846899343548460765)
                    ·
                      refine ⟨4255604942587253830672787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11348279846899343548460765 4255604942587253830672787)
                      ·
                        rfl

theorem cell23_8287761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 6, 1, 3, 1, 3].length) (baseStart_8287761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287761 prefixEnd_8287761 := by exact prefixLift 8287761
  have htrace : WordTrace (prefixWord ++ tailWord_8287761) baseStart_8287761 baseEnd_8287761 := by
    simpa [prefixWord, tailWord_8287761, baseEnd_8287761] using wordTrace_append hprefix tailTrace_8287761
  have hstable : (prefixWord ++ tailWord_8287761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287761).length < 2 ^ (prefixWord ++ tailWord_8287761).sum := by decide
  have hdescent : baseEnd_8287761 < baseStart_8287761 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287795 : List Nat := [1, 1, 1, 2, 4, 5, 1, 3, 1, 1, 3]
def baseStart_8287795 : Nat := 118140960795 + 8287795 * 2 ^ 59
def prefixEnd_8287795 : Nat := 4983230072969 + 3 ^ 40 * 8287795 * 2
def baseEnd_8287795 : Nat := 4255622400929506697647631

theorem tailTrace_8287795 : CollatzResearch.WordTrace tailWord_8287795 prefixEnd_8287795 4255622400929506697647631 := by
  unfold tailWord_8287795
  simp only [CollatzResearch.WordTrace]
  refine ⟨302280717009741632541960839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201520478006494421694640559 302280717009741632541960839)
  ·
    refine ⟨453421075514612448812941259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302280717009741632541960839 453421075514612448812941259)
    ·
      refine ⟨680131613271918673219411889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453421075514612448812941259 680131613271918673219411889)
      ·
        refine ⟨510098709953939004914558917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 680131613271918673219411889 510098709953939004914558917)
        ·
          refine ⟨95643508116363563421479797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 510098709953939004914558917 95643508116363563421479797)
          ·
            refine ⟨8966578885909084070763731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 95643508116363563421479797 8966578885909084070763731)
            ·
              refine ⟨13449868328863626106145597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8966578885909084070763731 13449868328863626106145597)
              ·
                refine ⟨5043700623323859789804599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13449868328863626106145597 5043700623323859789804599)
                ·
                  refine ⟨7565550934985789684706899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5043700623323859789804599 7565550934985789684706899)
                  ·
                    refine ⟨11348326402478684527060349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7565550934985789684706899 11348326402478684527060349)
                    ·
                      refine ⟨4255622400929506697647631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11348326402478684527060349 4255622400929506697647631)
                      ·
                        rfl

theorem cell23_8287795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 1, 3, 1, 1, 3].length) (baseStart_8287795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287795 prefixEnd_8287795 := by exact prefixLift 8287795
  have htrace : WordTrace (prefixWord ++ tailWord_8287795) baseStart_8287795 baseEnd_8287795 := by
    simpa [prefixWord, tailWord_8287795, baseEnd_8287795] using wordTrace_append hprefix tailTrace_8287795
  have hstable : (prefixWord ++ tailWord_8287795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287795).length < 2 ^ (prefixWord ++ tailWord_8287795).sum := by decide
  have hdescent : baseEnd_8287795 < baseStart_8287795 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287801 : List Nat := [1, 2, 1, 5, 1, 2, 2, 3, 1, 1, 4]
def baseStart_8287801 : Nat := 118140960795 + 8287801 * 2 ^ 59
def prefixEnd_8287801 : Nat := 4983230072969 + 3 ^ 40 * 8287801 * 2
def baseEnd_8287801 : Nat := 4255625481813433674172603

theorem tailTrace_8287801 : CollatzResearch.WordTrace tailWord_8287801 prefixEnd_8287801 4255625481813433674172603 := by
  unfold tailWord_8287801
  simp only [CollatzResearch.WordTrace]
  refine ⟨302280935847719895566679257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201520623898479930377786171 302280935847719895566679257)
  ·
    refine ⟨226710701885789921675009443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302280935847719895566679257 226710701885789921675009443)
    ·
      refine ⟨340066052828684882512514165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226710701885789921675009443 340066052828684882512514165)
      ·
        refine ⟨31881192452689207735548203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 340066052828684882512514165 31881192452689207735548203)
        ·
          refine ⟨47821788679033811603322305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31881192452689207735548203 47821788679033811603322305)
          ·
            refine ⟨35866341509275358702491729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47821788679033811603322305 35866341509275358702491729)
            ·
              refine ⟨26899756131956519026868797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35866341509275358702491729 26899756131956519026868797)
              ·
                refine ⟨10087408549483694635075799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26899756131956519026868797 10087408549483694635075799)
                ·
                  refine ⟨15131112824225541952613699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10087408549483694635075799 15131112824225541952613699)
                  ·
                    refine ⟨22696669236338312928920549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15131112824225541952613699 22696669236338312928920549)
                    ·
                      refine ⟨4255625481813433674172603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22696669236338312928920549 4255625481813433674172603)
                      ·
                        rfl

theorem cell23_8287801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_8287801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287801 prefixEnd_8287801 := by exact prefixLift 8287801
  have htrace : WordTrace (prefixWord ++ tailWord_8287801) baseStart_8287801 baseEnd_8287801 := by
    simpa [prefixWord, tailWord_8287801, baseEnd_8287801] using wordTrace_append hprefix tailTrace_8287801
  have hstable : (prefixWord ++ tailWord_8287801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287801).length < 2 ^ (prefixWord ++ tailWord_8287801).sum := by decide
  have hdescent : baseEnd_8287801 < baseStart_8287801 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287807 : List Nat := [1, 1, 2, 2, 3, 3, 11]
def baseStart_8287807 : Nat := 118140960795 + 8287807 * 2 ^ 59
def prefixEnd_8287807 : Nat := 4983230072969 + 3 ^ 40 * 8287807 * 2
def baseEnd_8287807 : Nat := 52538624230831612971575

theorem tailTrace_8287807 : CollatzResearch.WordTrace tailWord_8287807 prefixEnd_8287807 52538624230831612971575 := by
  unfold tailWord_8287807
  simp only [CollatzResearch.WordTrace]
  refine ⟨302281154685698158591397675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201520769790465439060931783 302281154685698158591397675)
  ·
    refine ⟨453421732028547237887096513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302281154685698158591397675 453421732028547237887096513)
    ·
      refine ⟨340066299021410428415322385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453421732028547237887096513 340066299021410428415322385)
      ·
        refine ⟨255049724266057821311491789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340066299021410428415322385 255049724266057821311491789)
        ·
          refine ⟨95643646599771682991809421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255049724266057821311491789 95643646599771682991809421)
          ·
            refine ⟨35866367474914381121928533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95643646599771682991809421 35866367474914381121928533)
            ·
              refine ⟨52538624230831612971575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 35866367474914381121928533 52538624230831612971575)
              ·
                rfl

theorem cell23_8287807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 11].length) (baseStart_8287807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287807 prefixEnd_8287807 := by exact prefixLift 8287807
  have htrace : WordTrace (prefixWord ++ tailWord_8287807) baseStart_8287807 baseEnd_8287807 := by
    simpa [prefixWord, tailWord_8287807, baseEnd_8287807] using wordTrace_append hprefix tailTrace_8287807
  have hstable : (prefixWord ++ tailWord_8287807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287807).length < 2 ^ (prefixWord ++ tailWord_8287807).sum := by decide
  have hdescent : baseEnd_8287807 < baseStart_8287807 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287834 : List Nat := [3, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3]
def baseStart_8287834 : Nat := 118140960795 + 8287834 * 2 ^ 59
def prefixEnd_8287834 : Nat := 4983230072969 + 3 ^ 40 * 8287834 * 2
def baseEnd_8287834 : Nat := 4255642426675032045059951

theorem tailTrace_8287834 : CollatzResearch.WordTrace tailWord_8287834 prefixEnd_8287834 4255642426675032045059951 := by
  unfold tailWord_8287834
  simp only [CollatzResearch.WordTrace]
  refine ⟨75570534864150085550657639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201521426304400228135087037 75570534864150085550657639)
  ·
    refine ⟨113355802296225128325986459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75570534864150085550657639 113355802296225128325986459)
    ·
      refine ⟨170033703444337692488979689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113355802296225128325986459 170033703444337692488979689)
      ·
        refine ⟨127525277583253269366734767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170033703444337692488979689 127525277583253269366734767)
        ·
          refine ⟨191287916374879904050102151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127525277583253269366734767 191287916374879904050102151)
          ·
            refine ⟨286931874562319856075153227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191287916374879904050102151 286931874562319856075153227)
            ·
              refine ⟨430397811843479784112729841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286931874562319856075153227 430397811843479784112729841)
              ·
                refine ⟨322798358882609838084547381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430397811843479784112729841 322798358882609838084547381)
                ·
                  refine ⟨30262346145244672320426317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 322798358882609838084547381 30262346145244672320426317)
                  ·
                    refine ⟨11348379804466752120159869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30262346145244672320426317 11348379804466752120159869)
                    ·
                      refine ⟨4255642426675032045059951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11348379804466752120159869 4255642426675032045059951)
                      ·
                        rfl

theorem cell23_8287834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 2, 5, 3, 3].length) (baseStart_8287834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287834 prefixEnd_8287834 := by exact prefixLift 8287834
  have htrace : WordTrace (prefixWord ++ tailWord_8287834) baseStart_8287834 baseEnd_8287834 := by
    simpa [prefixWord, tailWord_8287834, baseEnd_8287834] using wordTrace_append hprefix tailTrace_8287834
  have hstable : (prefixWord ++ tailWord_8287834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287834).length < 2 ^ (prefixWord ++ tailWord_8287834).sum := by decide
  have hdescent : baseEnd_8287834 < baseStart_8287834 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287869 : List Nat := [1, 4, 1, 1, 4, 3, 2, 2, 1, 2, 2]
def baseStart_8287869 : Nat := 118140960795 + 8287869 * 2 ^ 59
def prefixEnd_8287869 : Nat := 4983230072969 + 3 ^ 40 * 8287869 * 2
def baseEnd_8287869 : Nat := 4255660398497939408122291

theorem tailTrace_8287869 : CollatzResearch.WordTrace tailWord_8287869 prefixEnd_8287869 4255660398497939408122291 := by
  unfold tailWord_8287869
  simp only [CollatzResearch.WordTrace]
  refine ⟨302283416011473543180154661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201522277340982362120103107 302283416011473543180154661)
  ·
    refine ⟨56678140502151289346278999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302283416011473543180154661 56678140502151289346278999)
    ·
      refine ⟨85017210753226934019418499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56678140502151289346278999 85017210753226934019418499)
      ·
        refine ⟨127525816129840401029127749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85017210753226934019418499 127525816129840401029127749)
        ·
          refine ⟨23911090524345075192961453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127525816129840401029127749 23911090524345075192961453)
          ·
            refine ⟨8966658946629403197360545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23911090524345075192961453 8966658946629403197360545)
            ·
              refine ⟨6724994209972052398020409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8966658946629403197360545 6724994209972052398020409)
              ·
                refine ⟨5043745657479039298515307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6724994209972052398020409 5043745657479039298515307)
                ·
                  refine ⟨7565618486218558947772961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5043745657479039298515307 7565618486218558947772961)
                  ·
                    refine ⟨5674213864663919210829721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7565618486218558947772961 5674213864663919210829721)
                    ·
                      refine ⟨4255660398497939408122291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5674213864663919210829721 4255660398497939408122291)
                      ·
                        rfl

theorem cell23_8287869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 2, 1, 2, 2].length) (baseStart_8287869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287869 prefixEnd_8287869 := by exact prefixLift 8287869
  have htrace : WordTrace (prefixWord ++ tailWord_8287869) baseStart_8287869 baseEnd_8287869 := by
    simpa [prefixWord, tailWord_8287869, baseEnd_8287869] using wordTrace_append hprefix tailTrace_8287869
  have hstable : (prefixWord ++ tailWord_8287869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287869).length < 2 ^ (prefixWord ++ tailWord_8287869).sum := by decide
  have hdescent : baseEnd_8287869 < baseStart_8287869 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287884 : List Nat := [2, 2, 1, 2, 1, 1, 5, 1, 2, 6]
def baseStart_8287884 : Nat := 118140960795 + 8287884 * 2 ^ 59
def prefixEnd_8287884 : Nat := 4983230072969 + 3 ^ 40 * 8287884 * 2
def baseEnd_8287884 : Nat := 1418556033569252283144907

theorem tailTrace_8287884 : CollatzResearch.WordTrace tailWord_8287884 prefixEnd_8287884 1418556033569252283144907 := by
  unfold tailWord_8287884
  simp only [CollatzResearch.WordTrace]
  refine ⟨151141981553209600370975353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201522642070946133827967137 151141981553209600370975353)
  ·
    refine ⟨113356486164907200278231515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151141981553209600370975353 113356486164907200278231515)
    ·
      refine ⟨170034729247360800417347273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113356486164907200278231515 170034729247360800417347273)
      ·
        refine ⟨127526046935520600313010455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170034729247360800417347273 127526046935520600313010455)
        ·
          refine ⟨191289070403280900469515683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127526046935520600313010455 191289070403280900469515683)
          ·
            refine ⟨286933605604921350704273525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191289070403280900469515683 286933605604921350704273525)
            ·
              refine ⟨26900025525461376628525643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 286933605604921350704273525 26900025525461376628525643)
              ·
                refine ⟨40350038288192064942788465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26900025525461376628525643 40350038288192064942788465)
                ·
                  refine ⟨30262528716144048707091349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40350038288192064942788465 30262528716144048707091349)
                  ·
                    refine ⟨1418556033569252283144907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30262528716144048707091349 1418556033569252283144907)
                    ·
                      rfl

theorem cell23_8287884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 1, 2, 6].length) (baseStart_8287884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287884 prefixEnd_8287884 := by exact prefixLift 8287884
  have htrace : WordTrace (prefixWord ++ tailWord_8287884) baseStart_8287884 baseEnd_8287884 := by
    simpa [prefixWord, tailWord_8287884, baseEnd_8287884] using wordTrace_append hprefix tailTrace_8287884
  have hstable : (prefixWord ++ tailWord_8287884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287884).length < 2 ^ (prefixWord ++ tailWord_8287884).sum := by decide
  have hdescent : baseEnd_8287884 < baseStart_8287884 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287908 : List Nat := [2, 3, 1, 2, 2, 2, 2, 2, 1, 4, 2]
def baseStart_8287908 : Nat := 118140960795 + 8287908 * 2 ^ 59
def prefixEnd_8287908 : Nat := 4983230072969 + 3 ^ 40 * 8287908 * 2
def baseEnd_8287908 : Nat := 4255680424243464755534611

theorem tailTrace_8287908 : CollatzResearch.WordTrace tailWord_8287908 prefixEnd_8287908 4255680424243464755534611 := by
  unfold tailWord_8287908
  simp only [CollatzResearch.WordTrace]
  refine ⟨151142419229166126420412189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201523225638888168560549585 151142419229166126420412189)
  ·
    refine ⟨56678407210937297407654571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151142419229166126420412189 56678407210937297407654571)
    ·
      refine ⟨85017610816405946111481857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56678407210937297407654571 85017610816405946111481857)
      ·
        refine ⟨63763208112304459583611393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85017610816405946111481857 63763208112304459583611393)
        ·
          refine ⟨47822406084228344687708545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63763208112304459583611393 47822406084228344687708545)
          ·
            refine ⟨35866804563171258515781409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47822406084228344687708545 35866804563171258515781409)
            ·
              refine ⟨26900103422378443886836057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35866804563171258515781409 26900103422378443886836057)
              ·
                refine ⟨20175077566783832915127043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26900103422378443886836057 20175077566783832915127043)
                ·
                  refine ⟨30262616350175749372690565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20175077566783832915127043 30262616350175749372690565)
                  ·
                    refine ⟨5674240565657953007379481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30262616350175749372690565 5674240565657953007379481)
                    ·
                      refine ⟨4255680424243464755534611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5674240565657953007379481 4255680424243464755534611)
                      ·
                        rfl

theorem cell23_8287908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 2, 2, 1, 4, 2].length) (baseStart_8287908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287908 prefixEnd_8287908 := by exact prefixLift 8287908
  have htrace : WordTrace (prefixWord ++ tailWord_8287908) baseStart_8287908 baseEnd_8287908 := by
    simpa [prefixWord, tailWord_8287908, baseEnd_8287908] using wordTrace_append hprefix tailTrace_8287908
  have hstable : (prefixWord ++ tailWord_8287908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287908).length < 2 ^ (prefixWord ++ tailWord_8287908).sum := by decide
  have hdescent : baseEnd_8287908 < baseStart_8287908 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287944 : List Nat := [2, 1, 3, 1, 2, 2, 1, 1, 3, 7]
def baseStart_8287944 : Nat := 118140960795 + 8287944 * 2 ^ 59
def prefixEnd_8287944 : Nat := 4983230072969 + 3 ^ 40 * 8287944 * 2
def baseEnd_8287944 : Nat := 1418566303182342204894815

theorem tailTrace_8287944 : CollatzResearch.WordTrace tailWord_8287944 prefixEnd_8287944 1418566303182342204894815 := by
  unfold tailWord_8287944
  simp only [CollatzResearch.WordTrace]
  refine ⟨151143075743100915494567443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201524100990801220659423257 151143075743100915494567443)
  ·
    refine ⟨226714613614651373241851165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151143075743100915494567443 226714613614651373241851165)
    ·
      refine ⟨85017980105494264965694187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226714613614651373241851165 85017980105494264965694187)
      ·
        refine ⟨127526970158241397448541281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85017980105494264965694187 127526970158241397448541281)
        ·
          refine ⟨95645227618681048086405961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127526970158241397448541281 95645227618681048086405961)
          ·
            refine ⟨71733920714010786064804471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95645227618681048086405961 71733920714010786064804471)
            ·
              refine ⟨107600881071016179097206707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71733920714010786064804471 107600881071016179097206707)
              ·
                refine ⟨161401321606524268645810061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107600881071016179097206707 161401321606524268645810061)
                ·
                  refine ⟨60525495602446600742178773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161401321606524268645810061 60525495602446600742178773)
                  ·
                    refine ⟨1418566303182342204894815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60525495602446600742178773 1418566303182342204894815)
                    ·
                      rfl

theorem cell23_8287944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 1, 3, 7].length) (baseStart_8287944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287944 prefixEnd_8287944 := by exact prefixLift 8287944
  have htrace : WordTrace (prefixWord ++ tailWord_8287944) baseStart_8287944 baseEnd_8287944 := by
    simpa [prefixWord, tailWord_8287944, baseEnd_8287944] using wordTrace_append hprefix tailTrace_8287944
  have hstable : (prefixWord ++ tailWord_8287944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287944).length < 2 ^ (prefixWord ++ tailWord_8287944).sum := by decide
  have hdescent : baseEnd_8287944 < baseStart_8287944 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287951 : List Nat := [1, 1, 2, 1, 1, 3, 1, 4, 2, 5, 2]
def baseStart_8287951 : Nat := 118140960795 + 8287951 * 2 ^ 59
def prefixEnd_8287951 : Nat := 4983230072969 + 3 ^ 40 * 8287951 * 2
def baseEnd_8287951 : Nat := 4255702503911608087296913

theorem tailTrace_8287951 : CollatzResearch.WordTrace tailWord_8287951 prefixEnd_8287951 4255702503911608087296913 := by
  unfold tailWord_8287951
  simp only [CollatzResearch.WordTrace]
  refine ⟨302286406797176471184639707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201524271198117647456426471 302286406797176471184639707)
  ·
    refine ⟨453429610195764706776959561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302286406797176471184639707 453429610195764706776959561)
    ·
      refine ⟨340072207646823530082719671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453429610195764706776959561 340072207646823530082719671)
      ·
        refine ⟨510108311470235295124079507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340072207646823530082719671 510108311470235295124079507)
        ·
          refine ⟨765162467205352942686119261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510108311470235295124079507 765162467205352942686119261)
          ·
            refine ⟨286935925202007353507294723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 765162467205352942686119261 286935925202007353507294723)
            ·
              refine ⟨430403887803011030260942085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286935925202007353507294723 430403887803011030260942085)
              ·
                refine ⟨80700728963064568173926641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 430403887803011030260942085 80700728963064568173926641)
                ·
                  refine ⟨60525546722298426130444981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80700728963064568173926641 60525546722298426130444981)
                  ·
                    refine ⟨5674270005215477449729217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60525546722298426130444981 5674270005215477449729217)
                    ·
                      refine ⟨4255702503911608087296913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5674270005215477449729217 4255702503911608087296913)
                      ·
                        rfl

theorem cell23_8287951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 4, 2, 5, 2].length) (baseStart_8287951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287951 prefixEnd_8287951 := by exact prefixLift 8287951
  have htrace : WordTrace (prefixWord ++ tailWord_8287951) baseStart_8287951 baseEnd_8287951 := by
    simpa [prefixWord, tailWord_8287951, baseEnd_8287951] using wordTrace_append hprefix tailTrace_8287951
  have hstable : (prefixWord ++ tailWord_8287951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287951).length < 2 ^ (prefixWord ++ tailWord_8287951).sum := by decide
  have hdescent : baseEnd_8287951 < baseStart_8287951 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8287984 : List Nat := [2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 5]
def baseStart_8287984 : Nat := 118140960795 + 8287984 * 2 ^ 59
def prefixEnd_8287984 : Nat := 4983230072969 + 3 ^ 40 * 8287984 * 2
def baseEnd_8287984 : Nat := 4255719448773206458184261

theorem tailTrace_8287984 : CollatzResearch.WordTrace tailWord_8287984 prefixEnd_8287984 4255719448773206458184261 := by
  unfold tailWord_8287984
  simp only [CollatzResearch.WordTrace]
  refine ⟨151143805203028458910295503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201525073604037945213727337 151143805203028458910295503)
  ·
    refine ⟨226715707804542688365443255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151143805203028458910295503 226715707804542688365443255)
    ·
      refine ⟨340073561706814032548164883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226715707804542688365443255 340073561706814032548164883)
      ·
        refine ⟨510110342560221048822247325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340073561706814032548164883 510110342560221048822247325)
        ·
          refine ⟨191291378460082893308342747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 510110342560221048822247325 191291378460082893308342747)
          ·
            refine ⟨286937067690124339962514121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191291378460082893308342747 286937067690124339962514121)
            ·
              refine ⟨215202800767593254971885591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286937067690124339962514121 215202800767593254971885591)
              ·
                refine ⟨322804201151389882457828387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215202800767593254971885591 322804201151389882457828387)
                ·
                  refine ⟨484206301727084823686742581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322804201151389882457828387 484206301727084823686742581)
                  ·
                    refine ⟨45394340786914202220632117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 484206301727084823686742581 45394340786914202220632117)
                    ·
                      refine ⟨4255719448773206458184261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45394340786914202220632117 4255719448773206458184261)
                      ·
                        rfl

theorem cell23_8287984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 5].length) (baseStart_8287984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8287984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8287984 prefixEnd_8287984 := by exact prefixLift 8287984
  have htrace : WordTrace (prefixWord ++ tailWord_8287984) baseStart_8287984 baseEnd_8287984 := by
    simpa [prefixWord, tailWord_8287984, baseEnd_8287984] using wordTrace_append hprefix tailTrace_8287984
  have hstable : (prefixWord ++ tailWord_8287984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8287984).length < 2 ^ (prefixWord ++ tailWord_8287984).sum := by decide
  have hdescent : baseEnd_8287984 < baseStart_8287984 := by decide
  rcases family_descends (prefixWord ++ tailWord_8287984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288001 : List Nat := [1, 2, 4, 1, 1, 1, 2, 1, 3, 4, 3]
def baseStart_8288001 : Nat := 118140960795 + 8288001 * 2 ^ 59
def prefixEnd_8288001 : Nat := 4983230072969 + 3 ^ 40 * 8288001 * 2
def baseEnd_8288001 : Nat := 4255728177944332891671683

theorem tailTrace_8288001 : CollatzResearch.WordTrace tailWord_8288001 prefixEnd_8288001 4255728177944332891671683 := by
  unfold tailWord_8288001
  simp only [CollatzResearch.WordTrace]
  refine ⟨302288230446995329723959857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201525486964663553149306571 302288230446995329723959857)
  ·
    refine ⟨226716172835246497292969893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302288230446995329723959857 226716172835246497292969893)
    ·
      refine ⟨42509282406608718242431855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226716172835246497292969893 42509282406608718242431855)
      ·
        refine ⟨63763923609913077363647783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42509282406608718242431855 63763923609913077363647783)
        ·
          refine ⟨95645885414869616045471675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63763923609913077363647783 95645885414869616045471675)
          ·
            refine ⟨143468828122304424068207513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95645885414869616045471675 143468828122304424068207513)
            ·
              refine ⟨107601621091728318051155635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143468828122304424068207513 107601621091728318051155635)
              ·
                refine ⟨161402431637592477076733453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107601621091728318051155635 161402431637592477076733453)
                ·
                  refine ⟨60525911864097178903775045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 161402431637592477076733453 60525911864097178903775045)
                  ·
                    refine ⟨11348608474518221044457821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60525911864097178903775045 11348608474518221044457821)
                    ·
                      refine ⟨4255728177944332891671683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11348608474518221044457821 4255728177944332891671683)
                      ·
                        rfl

theorem cell23_8288001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 1, 3, 4, 3].length) (baseStart_8288001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288001 prefixEnd_8288001 := by exact prefixLift 8288001
  have htrace : WordTrace (prefixWord ++ tailWord_8288001) baseStart_8288001 baseEnd_8288001 := by
    simpa [prefixWord, tailWord_8288001, baseEnd_8288001] using wordTrace_append hprefix tailTrace_8288001
  have hstable : (prefixWord ++ tailWord_8288001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288001).length < 2 ^ (prefixWord ++ tailWord_8288001).sum := by decide
  have hdescent : baseEnd_8288001 < baseStart_8288001 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288082 : List Nat := [3, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3]
def baseStart_8288082 : Nat := 118140960795 + 8288082 * 2 ^ 59
def prefixEnd_8288082 : Nat := 4983230072969 + 3 ^ 40 * 8288082 * 2
def baseEnd_8288082 : Nat := 4255769769877347074758811

theorem tailTrace_8288082 : CollatzResearch.WordTrace tailWord_8288082 prefixEnd_8288082 4255769769877347074758811 := by
  unfold tailWord_8288082
  simp only [CollatzResearch.WordTrace]
  refine ⟨75572796189925470139414625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201527456506467920371772333 75572796189925470139414625)
  ·
    refine ⟨56679597142444102604560969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75572796189925470139414625 56679597142444102604560969)
    ·
      refine ⟨42509697856833076953420727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56679597142444102604560969 42509697856833076953420727)
      ·
        refine ⟨63764546785249615430131091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42509697856833076953420727 63764546785249615430131091)
        ·
          refine ⟨95646820177874423145196637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63764546785249615430131091 95646820177874423145196637)
          ·
            refine ⟨35867557566702908679448739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95646820177874423145196637 35867557566702908679448739)
            ·
              refine ⟨53801336350054363019173109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35867557566702908679448739 53801336350054363019173109)
              ·
                refine ⟨5043875282817596533047479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53801336350054363019173109 5043875282817596533047479)
                ·
                  refine ⟨7565812924226394799571219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5043875282817596533047479 7565812924226394799571219)
                  ·
                    refine ⟨11348719386339592199356829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7565812924226394799571219 11348719386339592199356829)
                    ·
                      refine ⟨4255769769877347074758811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11348719386339592199356829 4255769769877347074758811)
                      ·
                        rfl

theorem cell23_8288082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3].length) (baseStart_8288082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288082 prefixEnd_8288082 := by exact prefixLift 8288082
  have htrace : WordTrace (prefixWord ++ tailWord_8288082) baseStart_8288082 baseEnd_8288082 := by
    simpa [prefixWord, tailWord_8288082, baseEnd_8288082] using wordTrace_append hprefix tailTrace_8288082
  have hstable : (prefixWord ++ tailWord_8288082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288082).length < 2 ^ (prefixWord ++ tailWord_8288082).sum := by decide
  have hdescent : baseEnd_8288082 < baseStart_8288082 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288085 : List Nat := [1, 3, 2, 2, 2, 2, 4, 1, 1, 5]
def baseStart_8288085 : Nat := 118140960795 + 8288085 * 2 ^ 59
def prefixEnd_8288085 : Nat := 4983230072969 + 3 ^ 40 * 8288085 * 2
def baseEnd_8288085 : Nat := 1418590436773103521007099

theorem tailTrace_8288085 : CollatzResearch.WordTrace tailWord_8288085 prefixEnd_8288085 1418590436773103521007099 := by
  unfold tailWord_8288085
  simp only [CollatzResearch.WordTrace]
  refine ⟨302291294178691012070017709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201527529452460674713345139 302291294178691012070017709)
  ·
    refine ⟨113359235317009129526256641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302291294178691012070017709 113359235317009129526256641)
    ·
      refine ⟨85019426487756847144692481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113359235317009129526256641 85019426487756847144692481)
      ·
        refine ⟨63764569865817635358519361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85019426487756847144692481 63764569865817635358519361)
        ·
          refine ⟨47823427399363226518889521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63764569865817635358519361 47823427399363226518889521)
          ·
            refine ⟨35867570549522419889167141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47823427399363226518889521 35867570549522419889167141)
            ·
              refine ⟨6725169478035453729218839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35867570549522419889167141 6725169478035453729218839)
              ·
                refine ⟨10087754217053180593828259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6725169478035453729218839 10087754217053180593828259)
                ·
                  refine ⟨15131631325579770890742389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10087754217053180593828259 15131631325579770890742389)
                  ·
                    refine ⟨1418590436773103521007099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15131631325579770890742389 1418590436773103521007099)
                    ·
                      rfl

theorem cell23_8288085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 4, 1, 1, 5].length) (baseStart_8288085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288085 prefixEnd_8288085 := by exact prefixLift 8288085
  have htrace : WordTrace (prefixWord ++ tailWord_8288085) baseStart_8288085 baseEnd_8288085 := by
    simpa [prefixWord, tailWord_8288085, baseEnd_8288085] using wordTrace_append hprefix tailTrace_8288085
  have hstable : (prefixWord ++ tailWord_8288085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288085).length < 2 ^ (prefixWord ++ tailWord_8288085).sum := by decide
  have hdescent : baseEnd_8288085 < baseStart_8288085 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288101 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 1, 1, 6]
def baseStart_8288101 : Nat := 118140960795 + 8288101 * 2 ^ 59
def prefixEnd_8288101 : Nat := 4983230072969 + 3 ^ 40 * 8288101 * 2
def baseEnd_8288101 : Nat := 4255779526009782500421223

theorem tailTrace_8288101 : CollatzResearch.WordTrace tailWord_8288101 prefixEnd_8288101 4255779526009782500421223 := by
  unfold tailWord_8288101
  simp only [CollatzResearch.WordTrace]
  refine ⟨302291877746633046802600157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201527918497755364535066771 302291877746633046802600157)
  ·
    refine ⟨113359454154987392550975059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302291877746633046802600157 113359454154987392550975059)
    ·
      refine ⟨170039181232481088826462589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113359454154987392550975059 170039181232481088826462589)
      ·
        refine ⟨63764692962180408309923471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170039181232481088826462589 63764692962180408309923471)
        ·
          refine ⟨95647039443270612464885207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63764692962180408309923471 95647039443270612464885207)
          ·
            refine ⟨143470559164905918697327811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95647039443270612464885207 143470559164905918697327811)
            ·
              refine ⟨215205838747358878045991717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143470559164905918697327811 215205838747358878045991717)
              ·
                refine ⟨40351094765129789633623447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 215205838747358878045991717 40351094765129789633623447)
                ·
                  refine ⟨60526642147694684450435171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40351094765129789633623447 60526642147694684450435171)
                  ·
                    refine ⟨90789963221542026675652757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60526642147694684450435171 90789963221542026675652757)
                    ·
                      refine ⟨4255779526009782500421223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90789963221542026675652757 4255779526009782500421223)
                      ·
                        rfl

theorem cell23_8288101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_8288101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288101 prefixEnd_8288101 := by exact prefixLift 8288101
  have htrace : WordTrace (prefixWord ++ tailWord_8288101) baseStart_8288101 baseEnd_8288101 := by
    simpa [prefixWord, tailWord_8288101, baseEnd_8288101] using wordTrace_append hprefix tailTrace_8288101
  have hstable : (prefixWord ++ tailWord_8288101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288101).length < 2 ^ (prefixWord ++ tailWord_8288101).sum := by decide
  have hdescent : baseEnd_8288101 < baseStart_8288101 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288108 : List Nat := [2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 5]
def baseStart_8288108 : Nat := 118140960795 + 8288108 * 2 ^ 59
def prefixEnd_8288108 : Nat := 4983230072969 + 3 ^ 40 * 8288108 * 2
def baseEnd_8288108 : Nat := 4255783120374363973033691

theorem tailTrace_8288108 : CollatzResearch.WordTrace tailWord_8288108 prefixEnd_8288108 4255783120374363973033691 := by
  unfold tailWord_8288108
  simp only [CollatzResearch.WordTrace]
  refine ⟨151146066528803843499052489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201528088705071791332069985 151146066528803843499052489)
  ·
    refine ⟨113359549896602882624289367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151146066528803843499052489 113359549896602882624289367)
    ·
      refine ⟨170039324844904323936434051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113359549896602882624289367 170039324844904323936434051)
      ·
        refine ⟨255058987267356485904651077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170039324844904323936434051 255058987267356485904651077)
        ·
          refine ⟨47823560112629341107122077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255058987267356485904651077 47823560112629341107122077)
          ·
            refine ⟨17933835042236002915170779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47823560112629341107122077 17933835042236002915170779)
            ·
              refine ⟨26900752563354004372756169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17933835042236002915170779 26900752563354004372756169)
              ·
                refine ⟨20175564422515503279567127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26900752563354004372756169 20175564422515503279567127)
                ·
                  refine ⟨30263346633773254919350691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20175564422515503279567127 30263346633773254919350691)
                  ·
                    refine ⟨45395019950659882379026037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30263346633773254919350691 45395019950659882379026037)
                    ·
                      refine ⟨4255783120374363973033691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45395019950659882379026037 4255783120374363973033691)
                      ·
                        rfl

theorem cell23_8288108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_8288108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288108 prefixEnd_8288108 := by exact prefixLift 8288108
  have htrace : WordTrace (prefixWord ++ tailWord_8288108) baseStart_8288108 baseEnd_8288108 := by
    simpa [prefixWord, tailWord_8288108, baseEnd_8288108] using wordTrace_append hprefix tailTrace_8288108
  have hstable : (prefixWord ++ tailWord_8288108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288108).length < 2 ^ (prefixWord ++ tailWord_8288108).sum := by decide
  have hdescent : baseEnd_8288108 < baseStart_8288108 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288142 : List Nat := [4, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5]
def baseStart_8288142 : Nat := 118140960795 + 8288142 * 2 ^ 59
def prefixEnd_8288142 : Nat := 4983230072969 + 3 ^ 40 * 8288142 * 2
def baseEnd_8288142 : Nat := 4255800578716616840008535

theorem tailTrace_8288142 : CollatzResearch.WordTrace tailWord_8288142 prefixEnd_8288142 4255800578716616840008535 := by
  unfold tailWord_8288142
  simp only [CollatzResearch.WordTrace]
  refine ⟨37786671642435563850605335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201528915426323007203228453 37786671642435563850605335)
  ·
    refine ⟨56680007463653345775908003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37786671642435563850605335 56680007463653345775908003)
    ·
      refine ⟨85020011195480018663862005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56680007463653345775908003 85020011195480018663862005)
      ·
        refine ⟨7970626049576251749737063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85020011195480018663862005 7970626049576251749737063)
        ·
          refine ⟨11955939074364377624605595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7970626049576251749737063 11955939074364377624605595)
          ·
            refine ⟨17933908611546566436908393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11955939074364377624605595 17933908611546566436908393)
            ·
              refine ⟨13450431458659924827681295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17933908611546566436908393 13450431458659924827681295)
              ·
                refine ⟨20175647187989887241521943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13450431458659924827681295 20175647187989887241521943)
                ·
                  refine ⟨30263470781984830862282915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20175647187989887241521943 30263470781984830862282915)
                  ·
                    refine ⟨45395206172977246293424373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30263470781984830862282915 45395206172977246293424373)
                    ·
                      refine ⟨4255800578716616840008535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45395206172977246293424373 4255800578716616840008535)
                      ·
                        rfl

theorem cell23_8288142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 2, 1, 1, 1, 5].length) (baseStart_8288142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288142 prefixEnd_8288142 := by exact prefixLift 8288142
  have htrace : WordTrace (prefixWord ++ tailWord_8288142) baseStart_8288142 baseEnd_8288142 := by
    simpa [prefixWord, tailWord_8288142, baseEnd_8288142] using wordTrace_append hprefix tailTrace_8288142
  have hstable : (prefixWord ++ tailWord_8288142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288142).length < 2 ^ (prefixWord ++ tailWord_8288142).sum := by decide
  have hdescent : baseEnd_8288142 < baseStart_8288142 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288150 : List Nat := [5, 3, 1, 1, 2, 1, 3, 2, 1, 1, 3]
def baseStart_8288150 : Nat := 118140960795 + 8288150 * 2 ^ 59
def prefixEnd_8288150 : Nat := 4983230072969 + 3 ^ 40 * 8288150 * 2
def baseEnd_8288150 : Nat := 4255804686561852808708499

theorem tailTrace_8288150 : CollatzResearch.WordTrace tailWord_8288150 prefixEnd_8288150 4255804686561852808708499 := by
  unfold tailWord_8288150
  simp only [CollatzResearch.WordTrace]
  refine ⟨18893354057715970510695869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201529109948970352114089269 18893354057715970510695869)
  ·
    refine ⟨7085007771643488941510951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 18893354057715970510695869 7085007771643488941510951)
    ·
      refine ⟨10627511657465233412266427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7085007771643488941510951 10627511657465233412266427)
      ·
        refine ⟨15941267486197850118399641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10627511657465233412266427 15941267486197850118399641)
        ·
          refine ⟨11955950614648387588799731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15941267486197850118399641 11955950614648387588799731)
          ·
            refine ⟨17933925921972581383199597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11955950614648387588799731 17933925921972581383199597)
            ·
              refine ⟨6725222220739718018699849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17933925921972581383199597 6725222220739718018699849)
              ·
                refine ⟨5043916665554788514024887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6725222220739718018699849 5043916665554788514024887)
                ·
                  refine ⟨7565874998332182771037331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5043916665554788514024887 7565874998332182771037331)
                  ·
                    refine ⟨11348812497498274156555997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7565874998332182771037331 11348812497498274156555997)
                    ·
                      refine ⟨4255804686561852808708499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11348812497498274156555997 4255804686561852808708499)
                      ·
                        rfl

theorem cell23_8288150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 2, 1, 1, 3].length) (baseStart_8288150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288150 prefixEnd_8288150 := by exact prefixLift 8288150
  have htrace : WordTrace (prefixWord ++ tailWord_8288150) baseStart_8288150 baseEnd_8288150 := by
    simpa [prefixWord, tailWord_8288150, baseEnd_8288150] using wordTrace_append hprefix tailTrace_8288150
  have hstable : (prefixWord ++ tailWord_8288150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288150).length < 2 ^ (prefixWord ++ tailWord_8288150).sum := by decide
  have hdescent : baseEnd_8288150 < baseStart_8288150 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288201 : List Nat := [1, 2, 1, 1, 2, 1, 2, 4, 9]
def baseStart_8288201 : Nat := 118140960795 + 8288201 * 2 ^ 59
def prefixEnd_8288201 : Nat := 4983230072969 + 3 ^ 40 * 8288201 * 2
def baseEnd_8288201 : Nat := 472870097119470234352307

theorem tailTrace_8288201 : CollatzResearch.WordTrace tailWord_8288201 prefixEnd_8288201 472870097119470234352307 := by
  unfold tailWord_8288201
  simp only [CollatzResearch.WordTrace]
  refine ⟨302295525046270763881240457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201530350030847175920826971 302295525046270763881240457)
  ·
    refine ⟨226721643784703072910930343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302295525046270763881240457 226721643784703072910930343)
    ·
      refine ⟨340082465677054609366395515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226721643784703072910930343 340082465677054609366395515)
      ·
        refine ⟨510123698515581914049593273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340082465677054609366395515 510123698515581914049593273)
        ·
          refine ⟨382592773886686435537194955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510123698515581914049593273 382592773886686435537194955)
          ·
            refine ⟨573889160830029653305792433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382592773886686435537194955 573889160830029653305792433)
            ·
              refine ⟨430416870622522239979344325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 573889160830029653305792433 430416870622522239979344325)
              ·
                refine ⟨80703163241722919996127061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 430416870622522239979344325 80703163241722919996127061)
                ·
                  refine ⟨472870097119470234352307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 80703163241722919996127061 472870097119470234352307)
                  ·
                    rfl

theorem cell23_8288201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 4, 9].length) (baseStart_8288201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288201 prefixEnd_8288201 := by exact prefixLift 8288201
  have htrace : WordTrace (prefixWord ++ tailWord_8288201) baseStart_8288201 baseEnd_8288201 := by
    simpa [prefixWord, tailWord_8288201, baseEnd_8288201] using wordTrace_append hprefix tailTrace_8288201
  have hstable : (prefixWord ++ tailWord_8288201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288201).length < 2 ^ (prefixWord ++ tailWord_8288201).sum := by decide
  have hdescent : baseEnd_8288201 < baseStart_8288201 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288285 : List Nat := [1, 4, 2, 2, 2, 1, 1, 2, 1, 3, 4]
def baseStart_8288285 : Nat := 118140960795 + 8288285 * 2 ^ 59
def prefixEnd_8288285 : Nat := 4983230072969 + 3 ^ 40 * 8288285 * 2
def baseEnd_8288285 : Nat := 4255874006450209780520377

theorem tailTrace_8288285 : CollatzResearch.WordTrace tailWord_8288285 prefixEnd_8288285 4255874006450209780520377 := by
  unfold tailWord_8288285
  simp only [CollatzResearch.WordTrace]
  refine ⟨302298588777966446227298309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201532392518644297484865539 302298588777966446227298309)
  ·
    refine ⟨56680985395868708667618433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302298588777966446227298309 56680985395868708667618433)
    ·
      refine ⟨42510739046901531500713825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56680985395868708667618433 42510739046901531500713825)
      ·
        refine ⟨31883054285176148625535369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42510739046901531500713825 31883054285176148625535369)
        ·
          refine ⟨23912290713882111469151527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31883054285176148625535369 23912290713882111469151527)
          ·
            refine ⟨35868436070823167203727291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23912290713882111469151527 35868436070823167203727291)
            ·
              refine ⟨53802654106234750805590937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35868436070823167203727291 53802654106234750805590937)
              ·
                refine ⟨40351990579676063104193203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53802654106234750805590937 40351990579676063104193203)
                ·
                  refine ⟨60527985869514094656289805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40351990579676063104193203 60527985869514094656289805)
                  ·
                    refine ⟨22697994701067785496108677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60527985869514094656289805 22697994701067785496108677)
                    ·
                      refine ⟨4255874006450209780520377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22697994701067785496108677 4255874006450209780520377)
                      ·
                        rfl

theorem cell23_8288285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 1, 2, 1, 3, 4].length) (baseStart_8288285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288285 prefixEnd_8288285 := by exact prefixLift 8288285
  have htrace : WordTrace (prefixWord ++ tailWord_8288285) baseStart_8288285 baseEnd_8288285 := by
    simpa [prefixWord, tailWord_8288285, baseEnd_8288285] using wordTrace_append hprefix tailTrace_8288285
  have hstable : (prefixWord ++ tailWord_8288285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288285).length < 2 ^ (prefixWord ++ tailWord_8288285).sum := by decide
  have hdescent : baseEnd_8288285 < baseStart_8288285 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288305 : List Nat := [1, 2, 2, 3, 1, 3, 2, 1, 1, 4, 3]
def baseStart_8288305 : Nat := 118140960795 + 8288305 * 2 ^ 59
def prefixEnd_8288305 : Nat := 4983230072969 + 3 ^ 40 * 8288305 * 2
def baseEnd_8288305 : Nat := 4255884276063299702270285

theorem tailTrace_8288305 : CollatzResearch.WordTrace tailWord_8288305 prefixEnd_8288305 4255884276063299702270285 := by
  unfold tailWord_8288305
  simp only [CollatzResearch.WordTrace]
  refine ⟨302299318237893989643026369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201532878825262659762017579 302299318237893989643026369)
  ·
    refine ⟨226724488678420492232269777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302299318237893989643026369 226724488678420492232269777)
    ·
      refine ⟨170043366508815369174202333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226724488678420492232269777 170043366508815369174202333)
      ·
        refine ⟨63766262440805763440325875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170043366508815369174202333 63766262440805763440325875)
        ·
          refine ⟨95649393661208645160488813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63766262440805763440325875 95649393661208645160488813)
          ·
            refine ⟨35868522622953241935183305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95649393661208645160488813 35868522622953241935183305)
            ·
              refine ⟨26901391967214931451387479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35868522622953241935183305 26901391967214931451387479)
              ·
                refine ⟨40352087950822397177081219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26901391967214931451387479 40352087950822397177081219)
                ·
                  refine ⟨60528131926233595765621829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40352087950822397177081219 60528131926233595765621829)
                  ·
                    refine ⟨11349024736168799206054093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60528131926233595765621829 11349024736168799206054093)
                    ·
                      refine ⟨4255884276063299702270285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11349024736168799206054093 4255884276063299702270285)
                      ·
                        rfl

theorem cell23_8288305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 2, 1, 1, 4, 3].length) (baseStart_8288305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288305 prefixEnd_8288305 := by exact prefixLift 8288305
  have htrace : WordTrace (prefixWord ++ tailWord_8288305) baseStart_8288305 baseEnd_8288305 := by
    simpa [prefixWord, tailWord_8288305, baseEnd_8288305] using wordTrace_append hprefix tailTrace_8288305
  have hstable : (prefixWord ++ tailWord_8288305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288305).length < 2 ^ (prefixWord ++ tailWord_8288305).sum := by decide
  have hdescent : baseEnd_8288305 < baseStart_8288305 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288328 : List Nat := [2, 1, 3, 1, 1, 1, 2, 3, 1, 2, 6]
def baseStart_8288328 : Nat := 118140960795 + 8288328 * 2 ^ 59
def prefixEnd_8288328 : Nat := 4983230072969 + 3 ^ 40 * 8288328 * 2
def baseEnd_8288328 : Nat := 4255896086118353112282679

theorem tailTrace_8288328 : CollatzResearch.WordTrace tailWord_8288328 prefixEnd_8288328 4255896086118353112282679 := by
  unfold tailWord_8288328
  simp only [CollatzResearch.WordTrace]
  refine ⟨151150078558405332285556819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201533438077873776380742425 151150078558405332285556819)
  ·
    refine ⟨226725117837607998428335229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151150078558405332285556819 226725117837607998428335229)
    ·
      refine ⟨85021919189102999410625711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226725117837607998428335229 85021919189102999410625711)
      ·
        refine ⟨127532878783654499115938567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85021919189102999410625711 127532878783654499115938567)
        ·
          refine ⟨191299318175481748673907851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127532878783654499115938567 191299318175481748673907851)
          ·
            refine ⟨286948977263222623010861777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191299318175481748673907851 286948977263222623010861777)
            ·
              refine ⟨215211732947416967258146333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286948977263222623010861777 215211732947416967258146333)
              ·
                refine ⟨80704399855281362721804875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215211732947416967258146333 80704399855281362721804875)
                ·
                  refine ⟨121056599782922044082707313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80704399855281362721804875 121056599782922044082707313)
                  ·
                    refine ⟨90792449837191533062030485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 121056599782922044082707313 90792449837191533062030485)
                    ·
                      refine ⟨4255896086118353112282679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90792449837191533062030485 4255896086118353112282679)
                      ·
                        rfl

theorem cell23_8288328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 3, 1, 2, 6].length) (baseStart_8288328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288328 prefixEnd_8288328 := by exact prefixLift 8288328
  have htrace : WordTrace (prefixWord ++ tailWord_8288328) baseStart_8288328 baseEnd_8288328 := by
    simpa [prefixWord, tailWord_8288328, baseEnd_8288328] using wordTrace_append hprefix tailTrace_8288328
  have hstable : (prefixWord ++ tailWord_8288328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288328).length < 2 ^ (prefixWord ++ tailWord_8288328).sum := by decide
  have hdescent : baseEnd_8288328 < baseStart_8288328 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288329 : List Nat := [1, 2, 1, 1, 2, 2, 7, 2, 1, 4]
def baseStart_8288329 : Nat := 118140960795 + 8288329 * 2 ^ 59
def prefixEnd_8288329 : Nat := 4983230072969 + 3 ^ 40 * 8288329 * 2
def baseEnd_8288329 : Nat := 1418632199866335869456725

theorem tailTrace_8288329 : CollatzResearch.WordTrace tailWord_8288329 prefixEnd_8288329 1418632199866335869456725 := by
  unfold tailWord_8288329
  simp only [CollatzResearch.WordTrace]
  refine ⟨302300193589807041741900041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201533462393204694494600027 302300193589807041741900041)
  ·
    refine ⟨226725145192355281306425031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302300193589807041741900041 226725145192355281306425031)
    ·
      refine ⟨340087717788532921959637547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226725145192355281306425031 340087717788532921959637547)
      ·
        refine ⟨510131576682799382939456321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340087717788532921959637547 510131576682799382939456321)
        ·
          refine ⟨382598682512099537204592241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510131576682799382939456321 382598682512099537204592241)
          ·
            refine ⟨286949011884074652903444181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382598682512099537204592241 286949011884074652903444181)
            ·
              refine ⟨6725367466032999677424473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 286949011884074652903444181 6725367466032999677424473)
              ·
                refine ⟨5044025599524749758068355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6725367466032999677424473 5044025599524749758068355)
                ·
                  refine ⟨7566038399287124637102533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5044025599524749758068355 7566038399287124637102533)
                  ·
                    refine ⟨1418632199866335869456725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7566038399287124637102533 1418632199866335869456725)
                    ·
                      rfl

theorem cell23_8288329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 7, 2, 1, 4].length) (baseStart_8288329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288329 prefixEnd_8288329 := by exact prefixLift 8288329
  have htrace : WordTrace (prefixWord ++ tailWord_8288329) baseStart_8288329 baseEnd_8288329 := by
    simpa [prefixWord, tailWord_8288329, baseEnd_8288329] using wordTrace_append hprefix tailTrace_8288329
  have hstable : (prefixWord ++ tailWord_8288329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288329).length < 2 ^ (prefixWord ++ tailWord_8288329).sum := by decide
  have hdescent : baseEnd_8288329 < baseStart_8288329 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288369 : List Nat := [1, 2, 2, 2, 1, 1, 4, 5, 1, 1, 3]
def baseStart_8288369 : Nat := 118140960795 + 8288369 * 2 ^ 59
def prefixEnd_8288369 : Nat := 4983230072969 + 3 ^ 40 * 8288369 * 2
def baseEnd_8288369 : Nat := 4255917138825187451869991

theorem tailTrace_8288369 : CollatzResearch.WordTrace tailWord_8288369 prefixEnd_8288369 4255917138825187451869991 := by
  unfold tailWord_8288369
  simp only [CollatzResearch.WordTrace]
  refine ⟨302301652509662128573356161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201534435006441419048904107 302301652509662128573356161)
  ·
    refine ⟨226726239382246596430017121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302301652509662128573356161 226726239382246596430017121)
    ·
      refine ⟨170044679536684947322512841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226726239382246596430017121 170044679536684947322512841)
      ·
        refine ⟨127533509652513710491884631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170044679536684947322512841 127533509652513710491884631)
        ·
          refine ⟨191300264478770565737826947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127533509652513710491884631 191300264478770565737826947)
          ·
            refine ⟨286950396718155848606740421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191300264478770565737826947 286950396718155848606740421)
            ·
              refine ⟨53803199384654221613763829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 286950396718155848606740421 53803199384654221613763829)
              ·
                refine ⟨5044049942311333276290359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 53803199384654221613763829 5044049942311333276290359)
                ·
                  refine ⟨7566074913466999914435539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5044049942311333276290359 7566074913466999914435539)
                  ·
                    refine ⟨11349112370200499871653309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7566074913466999914435539 11349112370200499871653309)
                    ·
                      refine ⟨4255917138825187451869991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11349112370200499871653309 4255917138825187451869991)
                      ·
                        rfl

theorem cell23_8288369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 1, 1, 3].length) (baseStart_8288369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288369 prefixEnd_8288369 := by exact prefixLift 8288369
  have htrace : WordTrace (prefixWord ++ tailWord_8288369) baseStart_8288369 baseEnd_8288369 := by
    simpa [prefixWord, tailWord_8288369, baseEnd_8288369] using wordTrace_append hprefix tailTrace_8288369
  have hstable : (prefixWord ++ tailWord_8288369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288369).length < 2 ^ (prefixWord ++ tailWord_8288369).sum := by decide
  have hdescent : baseEnd_8288369 < baseStart_8288369 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288392 : List Nat := [2, 1, 3, 4, 1, 1, 1, 2, 3, 1, 4]
def baseStart_8288392 : Nat := 118140960795 + 8288392 * 2 ^ 59
def prefixEnd_8288392 : Nat := 4983230072969 + 3 ^ 40 * 8288392 * 2
def baseEnd_8288392 : Nat := 4255928948880240861882385

theorem tailTrace_8288392 : CollatzResearch.WordTrace tailWord_8288392 prefixEnd_8288392 4255928948880240861882385 := by
  unfold tailWord_8288392
  simp only [CollatzResearch.WordTrace]
  refine ⟨151151245694289401750721715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201534994259052535667628953 151151245694289401750721715)
  ·
    refine ⟨226726868541434102626082573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151151245694289401750721715 226726868541434102626082573)
    ·
      refine ⟨85022575703037788484780965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226726868541434102626082573 85022575703037788484780965)
      ·
        refine ⟨15941732944319585340896431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85022575703037788484780965 15941732944319585340896431)
        ·
          refine ⟨23912599416479378011344647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15941732944319585340896431 23912599416479378011344647)
          ·
            refine ⟨35868899124719067017016971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23912599416479378011344647 35868899124719067017016971)
            ·
              refine ⟨53803348687078600525525457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35868899124719067017016971 53803348687078600525525457)
              ·
                refine ⟨40352511515308950394144093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53803348687078600525525457 40352511515308950394144093)
                ·
                  refine ⟨15132191818240856397804035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40352511515308950394144093 15132191818240856397804035)
                  ·
                    refine ⟨22698287727361284596706053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15132191818240856397804035 22698287727361284596706053)
                    ·
                      refine ⟨4255928948880240861882385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22698287727361284596706053 4255928948880240861882385)
                      ·
                        rfl

theorem cell23_8288392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_8288392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288392 prefixEnd_8288392 := by exact prefixLift 8288392
  have htrace : WordTrace (prefixWord ++ tailWord_8288392) baseStart_8288392 baseEnd_8288392 := by
    simpa [prefixWord, tailWord_8288392, baseEnd_8288392] using wordTrace_append hprefix tailTrace_8288392
  have hstable : (prefixWord ++ tailWord_8288392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288392).length < 2 ^ (prefixWord ++ tailWord_8288392).sum := by decide
  have hdescent : baseEnd_8288392 < baseStart_8288392 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288402 : List Nat := [3, 2, 3, 1, 1, 1, 4, 1, 1, 6]
def baseStart_8288402 : Nat := 118140960795 + 8288402 * 2 ^ 59
def prefixEnd_8288402 : Nat := 4983230072969 + 3 ^ 40 * 8288402 * 2
def baseEnd_8288402 : Nat := 1418644694562261940919113

theorem tailTrace_8288402 : CollatzResearch.WordTrace tailWord_8288402 prefixEnd_8288402 1418644694562261940919113 := by
  unfold tailWord_8288402
  simp only [CollatzResearch.WordTrace]
  refine ⟨75575714029635643802326865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201535237412361716806204973 75575714029635643802326865)
  ·
    refine ⟨56681785522226732851745149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75575714029635643802326865 56681785522226732851745149)
    ·
      refine ⟨21255669570835024819404431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56681785522226732851745149 21255669570835024819404431)
      ·
        refine ⟨31883504356252537229106647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21255669570835024819404431 31883504356252537229106647)
        ·
          refine ⟨47825256534378805843659971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31883504356252537229106647 47825256534378805843659971)
          ·
            refine ⟨71737884801568208765489957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47825256534378805843659971 71737884801568208765489957)
            ·
              refine ⟨13450853400294039143529367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71737884801568208765489957 13450853400294039143529367)
              ·
                refine ⟨20176280100441058715294051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13450853400294039143529367 20176280100441058715294051)
                ·
                  refine ⟨30264420150661588072941077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20176280100441058715294051 30264420150661588072941077)
                  ·
                    refine ⟨1418644694562261940919113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30264420150661588072941077 1418644694562261940919113)
                    ·
                      rfl

theorem cell23_8288402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 4, 1, 1, 6].length) (baseStart_8288402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288402 prefixEnd_8288402 := by exact prefixLift 8288402
  have htrace : WordTrace (prefixWord ++ tailWord_8288402) baseStart_8288402 baseEnd_8288402 := by
    simpa [prefixWord, tailWord_8288402, baseEnd_8288402] using wordTrace_append hprefix tailTrace_8288402
  have hstable : (prefixWord ++ tailWord_8288402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288402).length < 2 ^ (prefixWord ++ tailWord_8288402).sum := by decide
  have hdescent : baseEnd_8288402 < baseStart_8288402 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288412 : List Nat := [2, 2, 3, 2, 1, 1, 1, 3, 3, 2, 3]
def baseStart_8288412 : Nat := 118140960795 + 8288412 * 2 ^ 59
def prefixEnd_8288412 : Nat := 4983230072969 + 3 ^ 40 * 8288412 * 2
def baseEnd_8288412 : Nat := 4255939218493330783632293

theorem tailTrace_8288412 : CollatzResearch.WordTrace tailWord_8288412 prefixEnd_8288412 4255939218493330783632293 := by
  unfold tailWord_8288412
  simp only [CollatzResearch.WordTrace]
  refine ⟨151151610424253173458585745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201535480565670897944780993 151151610424253173458585745)
  ·
    refine ⟨113363707818189880093939309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151151610424253173458585745 113363707818189880093939309)
    ·
      refine ⟨42511390431821205035227241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113363707818189880093939309 42511390431821205035227241)
      ·
        refine ⟨31883542823865903776420431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42511390431821205035227241 31883542823865903776420431)
        ·
          refine ⟨47825314235798855664630647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31883542823865903776420431 47825314235798855664630647)
          ·
            refine ⟨71737971353698283496945971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47825314235798855664630647 71737971353698283496945971)
            ·
              refine ⟨107606957030547425245418957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71737971353698283496945971 107606957030547425245418957)
              ·
                refine ⟨40352608886455284467032109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107606957030547425245418957 40352608886455284467032109)
                ·
                  refine ⟨15132228332420731675137041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40352608886455284467032109 15132228332420731675137041)
                  ·
                    refine ⟨11349171249315548756352781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15132228332420731675137041 11349171249315548756352781)
                    ·
                      refine ⟨4255939218493330783632293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11349171249315548756352781 4255939218493330783632293)
                      ·
                        rfl

theorem cell23_8288412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_8288412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288412 prefixEnd_8288412 := by exact prefixLift 8288412
  have htrace : WordTrace (prefixWord ++ tailWord_8288412) baseStart_8288412 baseEnd_8288412 := by
    simpa [prefixWord, tailWord_8288412, baseEnd_8288412] using wordTrace_append hprefix tailTrace_8288412
  have hstable : (prefixWord ++ tailWord_8288412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288412).length < 2 ^ (prefixWord ++ tailWord_8288412).sum := by decide
  have hdescent : baseEnd_8288412 < baseStart_8288412 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288423 : List Nat := [1, 1, 6, 2, 3, 1, 2, 1, 1, 5]
def baseStart_8288423 : Nat := 118140960795 + 8288423 * 2 ^ 59
def prefixEnd_8288423 : Nat := 4983230072969 + 3 ^ 40 * 8288423 * 2
def baseEnd_8288423 : Nat := 1418648288926843413531581

theorem tailTrace_8288423 : CollatzResearch.WordTrace tailWord_8288423 prefixEnd_8288423 1418648288926843413531581 := by
  unfold tailWord_8288423
  simp only [CollatzResearch.WordTrace]
  refine ⟨302303622051466495795821923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201535748034310997197214615 302303622051466495795821923)
  ·
    refine ⟨453455433077199743693732885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302303622051466495795821923 453455433077199743693732885)
    ·
      refine ⟨21255723425493737985643729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 453455433077199743693732885 21255723425493737985643729)
      ·
        refine ⟨15941792569120303489232797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21255723425493737985643729 15941792569120303489232797)
        ·
          refine ⟨5978172213420113808462299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15941792569120303489232797 5978172213420113808462299)
          ·
            refine ⟨8967258320130170712693449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5978172213420113808462299 8967258320130170712693449)
            ·
              refine ⟨6725443740097628034520087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8967258320130170712693449 6725443740097628034520087)
              ·
                refine ⟨10088165610146442051780131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6725443740097628034520087 10088165610146442051780131)
                ·
                  refine ⟨15132248415219663077670197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10088165610146442051780131 15132248415219663077670197)
                  ·
                    refine ⟨1418648288926843413531581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15132248415219663077670197 1418648288926843413531581)
                    ·
                      rfl

theorem cell23_8288423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 2, 1, 1, 5].length) (baseStart_8288423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288423 prefixEnd_8288423 := by exact prefixLift 8288423
  have htrace : WordTrace (prefixWord ++ tailWord_8288423) baseStart_8288423 baseEnd_8288423 := by
    simpa [prefixWord, tailWord_8288423, baseEnd_8288423] using wordTrace_append hprefix tailTrace_8288423
  have hstable : (prefixWord ++ tailWord_8288423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288423).length < 2 ^ (prefixWord ++ tailWord_8288423).sum := by decide
  have hdescent : baseEnd_8288423 < baseStart_8288423 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288426 : List Nat := [3, 1, 5, 1, 2, 1, 1, 3, 1, 1, 4]
def baseStart_8288426 : Nat := 118140960795 + 8288426 * 2 ^ 59
def prefixEnd_8288426 : Nat := 4983230072969 + 3 ^ 40 * 8288426 * 2
def baseEnd_8288426 : Nat := 4255946407222493728857229

theorem tailTrace_8288426 : CollatzResearch.WordTrace tailWord_8288426 prefixEnd_8288426 4255946407222493728857229 := by
  unfold tailWord_8288426
  simp only [CollatzResearch.WordTrace]
  refine ⟨75575932867613906827045283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201535820980303751538787421 75575932867613906827045283)
  ·
    refine ⟨113363899301420860240567925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75575932867613906827045283 113363899301420860240567925)
    ·
      refine ⟨10627865559508205647553243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113363899301420860240567925 10627865559508205647553243)
      ·
        refine ⟨15941798339262308471329865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10627865559508205647553243 15941798339262308471329865)
        ·
          refine ⟨11956348754446731353497399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15941798339262308471329865 11956348754446731353497399)
          ·
            refine ⟨17934523131670097030246099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11956348754446731353497399 17934523131670097030246099)
            ·
              refine ⟨26901784697505145545369149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17934523131670097030246099 26901784697505145545369149)
              ·
                refine ⟨10088169261564429579513431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26901784697505145545369149 10088169261564429579513431)
                ·
                  refine ⟨15132253892346644369270147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10088169261564429579513431 15132253892346644369270147)
                  ·
                    refine ⟨22698380838519966553905221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15132253892346644369270147 22698380838519966553905221)
                    ·
                      refine ⟨4255946407222493728857229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22698380838519966553905221 4255946407222493728857229)
                      ·
                        rfl

theorem cell23_8288426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 1, 1, 3, 1, 1, 4].length) (baseStart_8288426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288426 prefixEnd_8288426 := by exact prefixLift 8288426
  have htrace : WordTrace (prefixWord ++ tailWord_8288426) baseStart_8288426 baseEnd_8288426 := by
    simpa [prefixWord, tailWord_8288426, baseEnd_8288426] using wordTrace_append hprefix tailTrace_8288426
  have hstable : (prefixWord ++ tailWord_8288426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288426).length < 2 ^ (prefixWord ++ tailWord_8288426).sum := by decide
  have hdescent : baseEnd_8288426 < baseStart_8288426 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288465 : List Nat := [1, 2, 2, 1, 2, 2, 2, 2, 2, 3, 4]
def baseStart_8288465 : Nat := 118140960795 + 8288465 * 2 ^ 59
def prefixEnd_8288465 : Nat := 4983230072969 + 3 ^ 40 * 8288465 * 2
def baseEnd_8288465 : Nat := 4255966432968019076269549

theorem tailTrace_8288465 : CollatzResearch.WordTrace tailWord_8288465 prefixEnd_8288465 4255966432968019076269549 := by
  unfold tailWord_8288465
  simp only [CollatzResearch.WordTrace]
  refine ⟨302305153917314336968850849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201536769278209557979233899 302305153917314336968850849)
  ·
    refine ⟨226728865437985752726638137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302305153917314336968850849 226728865437985752726638137)
    ·
      refine ⟨170046649078489314544978603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226728865437985752726638137 170046649078489314544978603)
      ·
        refine ⟨255069973617733971817467905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170046649078489314544978603 255069973617733971817467905)
        ·
          refine ⟨191302480213300478863100929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255069973617733971817467905 191302480213300478863100929)
          ·
            refine ⟨143476860159975359147325697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191302480213300478863100929 143476860159975359147325697)
            ·
              refine ⟨107607645119981519360494273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143476860159975359147325697 107607645119981519360494273)
              ·
                refine ⟨80705733839986139520370705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107607645119981519360494273 80705733839986139520370705)
                ·
                  refine ⟨60529300379989604640278029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80705733839986139520370705 60529300379989604640278029)
                  ·
                    refine ⟨22698487642496101740104261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60529300379989604640278029 22698487642496101740104261)
                    ·
                      refine ⟨4255966432968019076269549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22698487642496101740104261 4255966432968019076269549)
                      ·
                        rfl

theorem cell23_8288465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 2, 2, 2, 3, 4].length) (baseStart_8288465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288465 prefixEnd_8288465 := by exact prefixLift 8288465
  have htrace : WordTrace (prefixWord ++ tailWord_8288465) baseStart_8288465 baseEnd_8288465 := by
    simpa [prefixWord, tailWord_8288465, baseEnd_8288465] using wordTrace_append hprefix tailTrace_8288465
  have hstable : (prefixWord ++ tailWord_8288465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288465).length < 2 ^ (prefixWord ++ tailWord_8288465).sum := by decide
  have hdescent : baseEnd_8288465 < baseStart_8288465 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288499 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 4, 2, 2]
def baseStart_8288499 : Nat := 118140960795 + 8288499 * 2 ^ 59
def prefixEnd_8288499 : Nat := 4983230072969 + 3 ^ 40 * 8288499 * 2
def baseEnd_8288499 : Nat := 4255983891310271943244393

theorem tailTrace_8288499 : CollatzResearch.WordTrace tailWord_8288499 prefixEnd_8288499 4255983891310271943244393 := by
  unfold tailWord_8288499
  simp only [CollatzResearch.WordTrace]
  refine ⟨302306393999191160775588551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201537595999460773850392367 302306393999191160775588551)
  ·
    refine ⟨453459590998786741163382827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302306393999191160775588551 453459590998786741163382827)
    ·
      refine ⟨680189386498180111745074241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453459590998786741163382827 680189386498180111745074241)
      ·
        refine ⟨510142039873635083808805681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 680189386498180111745074241 510142039873635083808805681)
        ·
          refine ⟨382606529905226312856604261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510142039873635083808805681 382606529905226312856604261)
          ·
            refine ⟨71738724357229933660613299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 382606529905226312856604261 71738724357229933660613299)
            ·
              refine ⟨107608086535844900490919949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71738724357229933660613299 107608086535844900490919949)
              ·
                refine ⟨40353032450941837684094981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107608086535844900490919949 40353032450941837684094981)
                ·
                  refine ⟨7566193584551594565767809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40353032450941837684094981 7566193584551594565767809)
                  ·
                    refine ⟨5674645188413695924325857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7566193584551594565767809 5674645188413695924325857)
                    ·
                      refine ⟨4255983891310271943244393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5674645188413695924325857 4255983891310271943244393)
                      ·
                        rfl

theorem cell23_8288499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 4, 2, 2].length) (baseStart_8288499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288499 prefixEnd_8288499 := by exact prefixLift 8288499
  have htrace : WordTrace (prefixWord ++ tailWord_8288499) baseStart_8288499 baseEnd_8288499 := by
    simpa [prefixWord, tailWord_8288499, baseEnd_8288499] using wordTrace_append hprefix tailTrace_8288499
  have hstable : (prefixWord ++ tailWord_8288499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288499).length < 2 ^ (prefixWord ++ tailWord_8288499).sum := by decide
  have hdescent : baseEnd_8288499 < baseStart_8288499 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288505 : List Nat := [1, 2, 1, 3, 1, 1, 2, 5, 7]
def baseStart_8288505 : Nat := 118140960795 + 8288505 * 2 ^ 59
def prefixEnd_8288505 : Nat := 4983230072969 + 3 ^ 40 * 8288505 * 2
def baseEnd_8288505 : Nat := 472887441354910991085485

theorem tailTrace_8288505 : CollatzResearch.WordTrace tailWord_8288505 prefixEnd_8288505 472887441354910991085485 := by
  unfold tailWord_8288505
  simp only [CollatzResearch.WordTrace]
  refine ⟨302306612837169423800306969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201537741891446282533537979 302306612837169423800306969)
  ·
    refine ⟨226729959627877067850230227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302306612837169423800306969 226729959627877067850230227)
    ·
      refine ⟨340094939441815601775345341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226729959627877067850230227 340094939441815601775345341)
      ·
        refine ⟨127535602290680850665754503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340094939441815601775345341 127535602290680850665754503)
        ·
          refine ⟨191303403436021275998631755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127535602290680850665754503 191303403436021275998631755)
          ·
            refine ⟨286955105154031913997947633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191303403436021275998631755 286955105154031913997947633)
            ·
              refine ⟨215216328865523935498460725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286955105154031913997947633 215216328865523935498460725)
              ·
                refine ⟨20176530831142868952980693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215216328865523935498460725 20176530831142868952980693)
                ·
                  refine ⟨472887441354910991085485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20176530831142868952980693 472887441354910991085485)
                  ·
                    rfl

theorem cell23_8288505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 5, 7].length) (baseStart_8288505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288505 prefixEnd_8288505 := by exact prefixLift 8288505
  have htrace : WordTrace (prefixWord ++ tailWord_8288505) baseStart_8288505 baseEnd_8288505 := by
    simpa [prefixWord, tailWord_8288505, baseEnd_8288505] using wordTrace_append hprefix tailTrace_8288505
  have hstable : (prefixWord ++ tailWord_8288505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288505).length < 2 ^ (prefixWord ++ tailWord_8288505).sum := by decide
  have hdescent : baseEnd_8288505 < baseStart_8288505 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288572 : List Nat := [2, 2, 2, 2, 1, 2, 2, 2, 1, 3, 4]
def baseStart_8288572 : Nat := 118140960795 + 8288572 * 2 ^ 59
def prefixEnd_8288572 : Nat := 4983230072969 + 3 ^ 40 * 8288572 * 2
def baseEnd_8288572 : Nat := 4256021375398050157631557

theorem tailTrace_8288572 : CollatzResearch.WordTrace tailWord_8288572 prefixEnd_8288572 4256021375398050157631557 := by
  unfold tailWord_8288572
  simp only [CollatzResearch.WordTrace]
  refine ⟨151154528263963347121497985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201539371018617796161997313 151154528263963347121497985)
  ·
    refine ⟨113365896197972510341123489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151154528263963347121497985 113365896197972510341123489)
    ·
      refine ⟨85024422148479382755842617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113365896197972510341123489 85024422148479382755842617)
      ·
        refine ⟨63768316611359537066881963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85024422148479382755842617 63768316611359537066881963)
        ·
          refine ⟨95652474917039305600322945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63768316611359537066881963 95652474917039305600322945)
          ·
            refine ⟨71739356187779479200242209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95652474917039305600322945 71739356187779479200242209)
            ·
              refine ⟨53804517140834609400181657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71739356187779479200242209 53804517140834609400181657)
              ·
                refine ⟨40353387855625957050136243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53804517140834609400181657 40353387855625957050136243)
                ·
                  refine ⟨60530081783438935575204365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40353387855625957050136243 60530081783438935575204365)
                  ·
                    refine ⟨22698780668789600840701637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60530081783438935575204365 22698780668789600840701637)
                    ·
                      refine ⟨4256021375398050157631557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22698780668789600840701637 4256021375398050157631557)
                      ·
                        rfl

theorem cell23_8288572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 2, 2, 1, 3, 4].length) (baseStart_8288572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288572 prefixEnd_8288572 := by exact prefixLift 8288572
  have htrace : WordTrace (prefixWord ++ tailWord_8288572) baseStart_8288572 baseEnd_8288572 := by
    simpa [prefixWord, tailWord_8288572, baseEnd_8288572] using wordTrace_append hprefix tailTrace_8288572
  have hstable : (prefixWord ++ tailWord_8288572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288572).length < 2 ^ (prefixWord ++ tailWord_8288572).sum := by decide
  have hdescent : baseEnd_8288572 < baseStart_8288572 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288612 : List Nat := [2, 3, 1, 1, 3, 1, 3, 1, 8]
def baseStart_8288612 : Nat := 118140960795 + 8288612 * 2 ^ 59
def prefixEnd_8288612 : Nat := 4983230072969 + 3 ^ 40 * 8288612 * 2
def baseEnd_8288612 : Nat := 472893546069358889014597

theorem tailTrace_8288612 : CollatzResearch.WordTrace tailWord_8288612 prefixEnd_8288612 472893546069358889014597 := by
  unfold tailWord_8288612
  simp only [CollatzResearch.WordTrace]
  refine ⟨151155257723890890537226045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201540343631854520716301393 151155257723890890537226045)
  ·
    refine ⟨56683221646459083951459767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151155257723890890537226045 56683221646459083951459767)
    ·
      refine ⟨85024832469688625927189651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56683221646459083951459767 85024832469688625927189651)
      ·
        refine ⟨127537248704532938890784477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85024832469688625927189651 127537248704532938890784477)
        ·
          refine ⟨47826468264199852084044179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127537248704532938890784477 47826468264199852084044179)
          ·
            refine ⟨71739702396299778126066269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47826468264199852084044179 71739702396299778126066269)
            ·
              refine ⟨26902388398612416797274851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71739702396299778126066269 26902388398612416797274851)
              ·
                refine ⟨40353582597918625195912277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26902388398612416797274851 40353582597918625195912277)
                ·
                  refine ⟨472893546069358889014597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40353582597918625195912277 472893546069358889014597)
                  ·
                    rfl

theorem cell23_8288612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 1, 8].length) (baseStart_8288612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288612 prefixEnd_8288612 := by exact prefixLift 8288612
  have htrace : WordTrace (prefixWord ++ tailWord_8288612) baseStart_8288612 baseEnd_8288612 := by
    simpa [prefixWord, tailWord_8288612, baseEnd_8288612] using wordTrace_append hprefix tailTrace_8288612
  have hstable : (prefixWord ++ tailWord_8288612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288612).length < 2 ^ (prefixWord ++ tailWord_8288612).sum := by decide
  have hdescent : baseEnd_8288612 < baseStart_8288612 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288616 : List Nat := [2, 1, 4, 2, 2, 2, 2, 1, 3, 4]
def baseStart_8288616 : Nat := 118140960795 + 8288616 * 2 ^ 59
def prefixEnd_8288616 : Nat := 4983230072969 + 3 ^ 40 * 8288616 * 2
def baseEnd_8288616 : Nat := 1418681322848949328493785

theorem tailTrace_8288616 : CollatzResearch.WordTrace tailWord_8288616 prefixEnd_8288616 1418681322848949328493785 := by
  unfold tailWord_8288616
  simp only [CollatzResearch.WordTrace]
  refine ⟨151155330669883644878798851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201540440893178193171731801 151155330669883644878798851)
  ·
    refine ⟨226732996004825467318198277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151155330669883644878798851 226732996004825467318198277)
    ·
      refine ⟨42512436750904775122162177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226732996004825467318198277 42512436750904775122162177)
      ·
        refine ⟨31884327563178581341621633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42512436750904775122162177 31884327563178581341621633)
        ·
          refine ⟨23913245672383936006216225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31884327563178581341621633 23913245672383936006216225)
          ·
            refine ⟨17934934254287952004662169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23913245672383936006216225 17934934254287952004662169)
            ·
              refine ⟨13451200690715964003496627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17934934254287952004662169 13451200690715964003496627)
              ·
                refine ⟨20176801036073946005244941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13451200690715964003496627 20176801036073946005244941)
                ·
                  refine ⟨7566300388527729751966853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20176801036073946005244941 7566300388527729751966853)
                  ·
                    refine ⟨1418681322848949328493785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7566300388527729751966853 1418681322848949328493785)
                    ·
                      rfl

theorem cell23_8288616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 2, 2, 1, 3, 4].length) (baseStart_8288616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288616 prefixEnd_8288616 := by exact prefixLift 8288616
  have htrace : WordTrace (prefixWord ++ tailWord_8288616) baseStart_8288616 baseEnd_8288616 := by
    simpa [prefixWord, tailWord_8288616, baseEnd_8288616] using wordTrace_append hprefix tailTrace_8288616
  have hstable : (prefixWord ++ tailWord_8288616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288616).length < 2 ^ (prefixWord ++ tailWord_8288616).sum := by decide
  have hdescent : baseEnd_8288616 < baseStart_8288616 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288666 : List Nat := [3, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2]
def baseStart_8288666 : Nat := 118140960795 + 8288666 * 2 ^ 59
def prefixEnd_8288666 : Nat := 4983230072969 + 3 ^ 40 * 8288666 * 2
def baseEnd_8288666 : Nat := 4256069642579572789856125

theorem tailTrace_8288666 : CollatzResearch.WordTrace tailWord_8288666 prefixEnd_8288666 4256069642579572789856125 := by
  unfold tailWord_8288666
  simp only [CollatzResearch.WordTrace]
  refine ⟨75578121247396537074229463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201541656659724098864611901 75578121247396537074229463)
  ·
    refine ⟨113367181871094805611344195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75578121247396537074229463 113367181871094805611344195)
    ·
      refine ⟨170050772806642208417016293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113367181871094805611344195 170050772806642208417016293)
      ·
        refine ⟨31884519901245414078190555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170050772806642208417016293 31884519901245414078190555)
        ·
          refine ⟨47826779851868121117285833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31884519901245414078190555 47826779851868121117285833)
          ·
            refine ⟨35870084888901090837964375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47826779851868121117285833 35870084888901090837964375)
            ·
              refine ⟨53805127333351636256946563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35870084888901090837964375 53805127333351636256946563)
              ·
                refine ⟨80707691000027454385419845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53805127333351636256946563 80707691000027454385419845)
                ·
                  refine ⟨15132692062505147697266221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80707691000027454385419845 15132692062505147697266221)
                  ·
                    refine ⟨5674759523439430386474833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15132692062505147697266221 5674759523439430386474833)
                    ·
                      refine ⟨4256069642579572789856125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5674759523439430386474833 4256069642579572789856125)
                      ·
                        rfl

theorem cell23_8288666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 1, 4, 3, 2].length) (baseStart_8288666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288666 prefixEnd_8288666 := by exact prefixLift 8288666
  have htrace : WordTrace (prefixWord ++ tailWord_8288666) baseStart_8288666 baseEnd_8288666 := by
    simpa [prefixWord, tailWord_8288666, baseEnd_8288666] using wordTrace_append hprefix tailTrace_8288666
  have hstable : (prefixWord ++ tailWord_8288666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288666).length < 2 ^ (prefixWord ++ tailWord_8288666).sum := by decide
  have hdescent : baseEnd_8288666 < baseStart_8288666 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288693 : List Nat := [1, 3, 3, 2, 3, 2, 1, 2, 1, 5]
def baseStart_8288693 : Nat := 118140960795 + 8288693 * 2 ^ 59
def prefixEnd_8288693 : Nat := 4983230072969 + 3 ^ 40 * 8288693 * 2
def baseEnd_8288693 : Nat := 1418694502185748061406167

theorem tailTrace_8288693 : CollatzResearch.WordTrace tailWord_8288693 prefixEnd_8288693 1418694502185748061406167 := by
  unfold tailWord_8288693
  simp only [CollatzResearch.WordTrace]
  refine ⟨302313469760488331908150733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201542313173658887938767155 302313469760488331908150733)
  ·
    refine ⟨113367551160183124465556525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302313469760488331908150733 113367551160183124465556525)
    ·
      refine ⟨42512831685068671674583697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113367551160183124465556525 42512831685068671674583697)
      ·
        refine ⟨31884623763801503755937773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42512831685068671674583697 31884623763801503755937773)
        ·
          refine ⟨11956733911425563908476665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31884623763801503755937773 11956733911425563908476665)
          ·
            refine ⟨8967550433569172931357499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11956733911425563908476665 8967550433569172931357499)
            ·
              refine ⟨13451325650353759397036249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8967550433569172931357499 13451325650353759397036249)
              ·
                refine ⟨10088494237765319547777187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13451325650353759397036249 10088494237765319547777187)
                ·
                  refine ⟨15132741356647979321665781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10088494237765319547777187 15132741356647979321665781)
                  ·
                    refine ⟨1418694502185748061406167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15132741356647979321665781 1418694502185748061406167)
                    ·
                      rfl

theorem cell23_8288693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 5].length) (baseStart_8288693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288693 prefixEnd_8288693 := by exact prefixLift 8288693
  have htrace : WordTrace (prefixWord ++ tailWord_8288693) baseStart_8288693 baseEnd_8288693 := by
    simpa [prefixWord, tailWord_8288693, baseEnd_8288693] using wordTrace_append hprefix tailTrace_8288693
  have hstable : (prefixWord ++ tailWord_8288693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288693).length < 2 ^ (prefixWord ++ tailWord_8288693).sum := by decide
  have hdescent : baseEnd_8288693 < baseStart_8288693 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288696 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 5, 2, 2]
def baseStart_8288696 : Nat := 118140960795 + 8288696 * 2 ^ 59
def prefixEnd_8288696 : Nat := 4983230072969 + 3 ^ 40 * 8288696 * 2
def baseEnd_8288696 : Nat := 4256085046999207672480987

theorem tailTrace_8288696 : CollatzResearch.WordTrace tailWord_8288696 prefixEnd_8288696 4256085046999207672480987 := by
  unfold tailWord_8288696
  simp only [CollatzResearch.WordTrace]
  refine ⟨151156789589738731710254971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201542386119651642280339961 151156789589738731710254971)
  ·
    refine ⟨226735184384608097565382457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151156789589738731710254971 226735184384608097565382457)
    ·
      refine ⟨170051388288456073174036843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226735184384608097565382457 170051388288456073174036843)
      ·
        refine ⟨255077082432684109761055265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170051388288456073174036843 255077082432684109761055265)
        ·
          refine ⟨191307811824513082320791449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255077082432684109761055265 191307811824513082320791449)
          ·
            refine ⟨143480858868384811740593587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191307811824513082320791449 143480858868384811740593587)
            ·
              refine ⟨215221288302577217610890381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143480858868384811740593587 215221288302577217610890381)
              ·
                refine ⟨80707983113466456604083893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215221288302577217610890381 80707983113466456604083893)
                ·
                  refine ⟨7566373416887480306632865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80707983113466456604083893 7566373416887480306632865)
                  ·
                    refine ⟨5674780062665610229974649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7566373416887480306632865 5674780062665610229974649)
                    ·
                      refine ⟨4256085046999207672480987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5674780062665610229974649 4256085046999207672480987)
                      ·
                        rfl

theorem cell23_8288696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 5, 2, 2].length) (baseStart_8288696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288696 prefixEnd_8288696 := by exact prefixLift 8288696
  have htrace : WordTrace (prefixWord ++ tailWord_8288696) baseStart_8288696 baseEnd_8288696 := by
    simpa [prefixWord, tailWord_8288696, baseEnd_8288696] using wordTrace_append hprefix tailTrace_8288696
  have hstable : (prefixWord ++ tailWord_8288696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288696).length < 2 ^ (prefixWord ++ tailWord_8288696).sum := by decide
  have hdescent : baseEnd_8288696 < baseStart_8288696 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288726 : List Nat := [5, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_8288726 : Nat := 118140960795 + 8288726 * 2 ^ 59
def prefixEnd_8288726 : Nat := 4983230072969 + 3 ^ 40 * 8288726 * 2
def baseEnd_8288726 : Nat := 4256100451418842555105849

theorem tailTrace_8288726 : CollatzResearch.WordTrace tailWord_8288726 prefixEnd_8288726 4256100451418842555105849 := by
  unfold tailWord_8288726
  simp only [CollatzResearch.WordTrace]
  refine ⟨18894667085585548659006377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201543115579579185696068021 18894667085585548659006377)
  ·
    refine ⟨14171000314189161494254783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18894667085585548659006377 14171000314189161494254783)
    ·
      refine ⟨21256500471283742241382175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14171000314189161494254783 21256500471283742241382175)
      ·
        refine ⟨31884750706925613362073263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21256500471283742241382175 31884750706925613362073263)
        ·
          refine ⟨47827126060388420043109895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31884750706925613362073263 47827126060388420043109895)
          ·
            refine ⟨71740689090582630064664843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47827126060388420043109895 71740689090582630064664843)
            ·
              refine ⟨107611033635873945096997265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71740689090582630064664843 107611033635873945096997265)
              ·
                refine ⟨80708275226905458822747949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107611033635873945096997265 80708275226905458822747949)
                ·
                  refine ⟨30265603210089547058530481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80708275226905458822747949 30265603210089547058530481)
                  ·
                    refine ⟨22699202407567160293897861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30265603210089547058530481 22699202407567160293897861)
                    ·
                      refine ⟨4256100451418842555105849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22699202407567160293897861 4256100451418842555105849)
                      ·
                        rfl

theorem cell23_8288726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_8288726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288726 prefixEnd_8288726 := by exact prefixLift 8288726
  have htrace : WordTrace (prefixWord ++ tailWord_8288726) baseStart_8288726 baseEnd_8288726 := by
    simpa [prefixWord, tailWord_8288726, baseEnd_8288726] using wordTrace_append hprefix tailTrace_8288726
  have hstable : (prefixWord ++ tailWord_8288726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288726).length < 2 ^ (prefixWord ++ tailWord_8288726).sum := by decide
  have hdescent : baseEnd_8288726 < baseStart_8288726 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288729 : List Nat := [1, 2, 1, 2, 4, 1, 1, 2, 3, 3, 3]
def baseStart_8288729 : Nat := 118140960795 + 8288729 * 2 ^ 59
def prefixEnd_8288729 : Nat := 4983230072969 + 3 ^ 40 * 8288729 * 2
def baseEnd_8288729 : Nat := 4256101991860806043368335

theorem tailTrace_8288729 : CollatzResearch.WordTrace tailWord_8288729 prefixEnd_8288729 4256101991860806043368335 := by
  unfold tailWord_8288729
  simp only [CollatzResearch.WordTrace]
  refine ⟨302314782788357910056461241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201543188525571940037640827 302314782788357910056461241)
  ·
    refine ⟨226736087091268432542345931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302314782788357910056461241 226736087091268432542345931)
    ·
      refine ⟨340104130636902648813518897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226736087091268432542345931 340104130636902648813518897)
      ·
        refine ⟨255078097977676986610139173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340104130636902648813518897 255078097977676986610139173)
        ·
          refine ⟨47827143370814434989401095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255078097977676986610139173 47827143370814434989401095)
          ·
            refine ⟨71740715056221652484101643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47827143370814434989401095 71740715056221652484101643)
            ·
              refine ⟨107611072584332478726152465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71740715056221652484101643 107611072584332478726152465)
              ·
                refine ⟨80708304438249359044614349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107611072584332478726152465 80708304438249359044614349)
                ·
                  refine ⟨30265614164343509641730381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80708304438249359044614349 30265614164343509641730381)
                  ·
                    refine ⟨11349605311628816115648893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30265614164343509641730381 11349605311628816115648893)
                    ·
                      refine ⟨4256101991860806043368335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11349605311628816115648893 4256101991860806043368335)
                      ·
                        rfl

theorem cell23_8288729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 3, 3, 3].length) (baseStart_8288729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288729 prefixEnd_8288729 := by exact prefixLift 8288729
  have htrace : WordTrace (prefixWord ++ tailWord_8288729) baseStart_8288729 baseEnd_8288729 := by
    simpa [prefixWord, tailWord_8288729, baseEnd_8288729] using wordTrace_append hprefix tailTrace_8288729
  have hstable : (prefixWord ++ tailWord_8288729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288729).length < 2 ^ (prefixWord ++ tailWord_8288729).sum := by decide
  have hdescent : baseEnd_8288729 < baseStart_8288729 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288730 : List Nat := [3, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2]
def baseStart_8288730 : Nat := 118140960795 + 8288730 * 2 ^ 59
def prefixEnd_8288730 : Nat := 4983230072969 + 3 ^ 40 * 8288730 * 2
def baseEnd_8288730 : Nat := 4256102505341460539455831

theorem tailTrace_8288730 : CollatzResearch.WordTrace tailWord_8288730 prefixEnd_8288730 4256102505341460539455831 := by
  unfold tailWord_8288730
  simp only [CollatzResearch.WordTrace]
  refine ⟨75578704815338571806811911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201543212840902858151498429 75578704815338571806811911)
  ·
    refine ⟨113368057223007857710217867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75578704815338571806811911 113368057223007857710217867)
    ·
      refine ⟨170052085834511786565326801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113368057223007857710217867 170052085834511786565326801)
      ·
        refine ⟨127539064375883839923995101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170052085834511786565326801 127539064375883839923995101)
        ·
          refine ⟨47827149140956439971498163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127539064375883839923995101 47827149140956439971498163)
          ·
            refine ⟨71740723711434659957247245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47827149140956439971498163 71740723711434659957247245)
            ·
              refine ⟨26902771391787997483967717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71740723711434659957247245 26902771391787997483967717)
              ·
                refine ⟨5044269635960249528243947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26902771391787997483967717 5044269635960249528243947)
                ·
                  refine ⟨7566404453940374292365921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5044269635960249528243947 7566404453940374292365921)
                  ·
                    refine ⟨5674803340455280719274441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7566404453940374292365921 5674803340455280719274441)
                    ·
                      refine ⟨4256102505341460539455831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5674803340455280719274441 4256102505341460539455831)
                      ·
                        rfl

theorem cell23_8288730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 4, 1, 2, 2].length) (baseStart_8288730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288730 prefixEnd_8288730 := by exact prefixLift 8288730
  have htrace : WordTrace (prefixWord ++ tailWord_8288730) baseStart_8288730 baseEnd_8288730 := by
    simpa [prefixWord, tailWord_8288730, baseEnd_8288730] using wordTrace_append hprefix tailTrace_8288730
  have hstable : (prefixWord ++ tailWord_8288730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288730).length < 2 ^ (prefixWord ++ tailWord_8288730).sum := by decide
  have hdescent : baseEnd_8288730 < baseStart_8288730 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288746 : List Nat := [3, 1, 3, 1, 3, 1, 1, 3, 1, 3, 3]
def baseStart_8288746 : Nat := 118140960795 + 8288746 * 2 ^ 59
def prefixEnd_8288746 : Nat := 4983230072969 + 3 ^ 40 * 8288746 * 2
def baseEnd_8288746 : Nat := 4256110721031932476855757

theorem tailTrace_8288746 : CollatzResearch.WordTrace tailWord_8288746 prefixEnd_8288746 4256110721031932476855757 := by
  unfold tailWord_8288746
  simp only [CollatzResearch.WordTrace]
  refine ⟨75578850707324080489957523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201543601886197547973220061 75578850707324080489957523)
  ·
    refine ⟨113368276060986120734936285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75578850707324080489957523 113368276060986120734936285)
    ·
      refine ⟨42513103522869795275601107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113368276060986120734936285 42513103522869795275601107)
      ·
        refine ⟨63769655284304692913401661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42513103522869795275601107 63769655284304692913401661)
        ·
          refine ⟨23913620731614259842525623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63769655284304692913401661 23913620731614259842525623)
          ·
            refine ⟨35870431097421389763788435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23913620731614259842525623 35870431097421389763788435)
            ·
              refine ⟨53805646646132084645682653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35870431097421389763788435 53805646646132084645682653)
              ·
                refine ⟨20177117492299531742130995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53805646646132084645682653 20177117492299531742130995)
                ·
                  refine ⟨30265676238449297613196493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20177117492299531742130995 30265676238449297613196493)
                  ·
                    refine ⟨11349628589418486604948685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30265676238449297613196493 11349628589418486604948685)
                    ·
                      refine ⟨4256110721031932476855757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11349628589418486604948685 4256110721031932476855757)
                      ·
                        rfl

theorem cell23_8288746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 3, 1, 3, 3].length) (baseStart_8288746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288746 prefixEnd_8288746 := by exact prefixLift 8288746
  have htrace : WordTrace (prefixWord ++ tailWord_8288746) baseStart_8288746 baseEnd_8288746 := by
    simpa [prefixWord, tailWord_8288746, baseEnd_8288746] using wordTrace_append hprefix tailTrace_8288746
  have hstable : (prefixWord ++ tailWord_8288746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288746).length < 2 ^ (prefixWord ++ tailWord_8288746).sum := by decide
  have hdescent : baseEnd_8288746 < baseStart_8288746 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288774 : List Nat := [6, 2, 1, 1, 1, 3, 1, 2, 2, 4]
def baseStart_8288774 : Nat := 118140960795 + 8288774 * 2 ^ 59
def prefixEnd_8288774 : Nat := 4983230072969 + 3 ^ 40 * 8288774 * 2
def baseEnd_8288774 : Nat := 1418708366163419455768543

theorem tailTrace_8288774 : CollatzResearch.WordTrace tailWord_8288774 prefixEnd_8288774 1418708366163419455768543 := by
  unfold tailWord_8288774
  simp only [CollatzResearch.WordTrace]
  refine ⟨9447388252287340085682793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 201544282715463255161232917 9447388252287340085682793)
  ·
    refine ⟨7085541189215505064262095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9447388252287340085682793 7085541189215505064262095)
    ·
      refine ⟨10628311783823257596393143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7085541189215505064262095 10628311783823257596393143)
      ·
        refine ⟨15942467675734886394589715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10628311783823257596393143 15942467675734886394589715)
        ·
          refine ⟨23913701513602329591884573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15942467675734886394589715 23913701513602329591884573)
          ·
            refine ⟨8967638067600873596956715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23913701513602329591884573 8967638067600873596956715)
            ·
              refine ⟨13451457101401310395435073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8967638067600873596956715 13451457101401310395435073)
              ·
                refine ⟨10088592826050982796576305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13451457101401310395435073 10088592826050982796576305)
                ·
                  refine ⟨7566444619538237097432229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10088592826050982796576305 7566444619538237097432229)
                  ·
                    refine ⟨1418708366163419455768543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7566444619538237097432229 1418708366163419455768543)
                    ·
                      rfl

theorem cell23_8288774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_8288774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288774 prefixEnd_8288774 := by exact prefixLift 8288774
  have htrace : WordTrace (prefixWord ++ tailWord_8288774) baseStart_8288774 baseEnd_8288774 := by
    simpa [prefixWord, tailWord_8288774, baseEnd_8288774] using wordTrace_append hprefix tailTrace_8288774
  have hstable : (prefixWord ++ tailWord_8288774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288774).length < 2 ^ (prefixWord ++ tailWord_8288774).sum := by decide
  have hdescent : baseEnd_8288774 < baseStart_8288774 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288779 : List Nat := [1, 1, 1, 1, 7, 1, 1, 2, 2, 6]
def baseStart_8288779 : Nat := 118140960795 + 8288779 * 2 ^ 59
def prefixEnd_8288779 : Nat := 4983230072969 + 3 ^ 40 * 8288779 * 2
def baseEnd_8288779 : Nat := 1418709221964510282581035

theorem tailTrace_8288779 : CollatzResearch.WordTrace tailWord_8288779 prefixEnd_8288779 1418709221964510282581035 := by
  unfold tailWord_8288779
  simp only [CollatzResearch.WordTrace]
  refine ⟨302316606438176768595781391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201544404292117845730520927 302316606438176768595781391)
  ·
    refine ⟨453474909657265152893672087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302316606438176768595781391 453474909657265152893672087)
    ·
      refine ⟨680212364485897729340508131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453474909657265152893672087 680212364485897729340508131)
      ·
        refine ⟨1020318546728846594010762197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680212364485897729340508131 1020318546728846594010762197)
        ·
          refine ⟨23913715938957342047127239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1020318546728846594010762197 23913715938957342047127239)
          ·
            refine ⟨35870573908436013070690859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23913715938957342047127239 35870573908436013070690859)
            ·
              refine ⟨53805860862654019606036289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35870573908436013070690859 53805860862654019606036289)
              ·
                refine ⟨40354395646990514704527217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53805860862654019606036289 40354395646990514704527217)
                ·
                  refine ⟨30265796735242886028395413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40354395646990514704527217 30265796735242886028395413)
                  ·
                    refine ⟨1418709221964510282581035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30265796735242886028395413 1418709221964510282581035)
                    ·
                      rfl

theorem cell23_8288779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 6].length) (baseStart_8288779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288779 prefixEnd_8288779 := by exact prefixLift 8288779
  have htrace : WordTrace (prefixWord ++ tailWord_8288779) baseStart_8288779 baseEnd_8288779 := by
    simpa [prefixWord, tailWord_8288779, baseEnd_8288779] using wordTrace_append hprefix tailTrace_8288779
  have hstable : (prefixWord ++ tailWord_8288779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288779).length < 2 ^ (prefixWord ++ tailWord_8288779).sum := by decide
  have hdescent : baseEnd_8288779 < baseStart_8288779 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288780 : List Nat := [2, 2, 1, 2, 4, 3, 1, 2, 2, 1, 3]
def baseStart_8288780 : Nat := 118140960795 + 8288780 * 2 ^ 59
def prefixEnd_8288780 : Nat := 4983230072969 + 3 ^ 40 * 8288780 * 2
def baseEnd_8288780 : Nat := 4256128179374185343830601

theorem tailTrace_8288780 : CollatzResearch.WordTrace tailWord_8288780 prefixEnd_8288780 4256128179374185343830601 := by
  unfold tailWord_8288780
  simp only [CollatzResearch.WordTrace]
  refine ⟨151158321455586572883283897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201544428607448763844378529 151158321455586572883283897)
  ·
    refine ⟨113368741091689929662462923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151158321455586572883283897 113368741091689929662462923)
    ·
      refine ⟨170053111637534894493694385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113368741091689929662462923 170053111637534894493694385)
      ·
        refine ⟨127539833728151170870270789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170053111637534894493694385 127539833728151170870270789)
        ·
          refine ⟨23913718824028344538175773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127539833728151170870270789 23913718824028344538175773)
          ·
            refine ⟨8967644559010629201815915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23913718824028344538175773 8967644559010629201815915)
            ·
              refine ⟨13451466838515943802723873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8967644559010629201815915 13451466838515943802723873)
              ·
                refine ⟨10088600128886957852042905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13451466838515943802723873 10088600128886957852042905)
                ·
                  refine ⟨7566450096665218389032179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10088600128886957852042905 7566450096665218389032179)
                  ·
                    refine ⟨11349675144997827583548269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7566450096665218389032179 11349675144997827583548269)
                    ·
                      refine ⟨4256128179374185343830601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11349675144997827583548269 4256128179374185343830601)
                      ·
                        rfl

theorem cell23_8288780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_8288780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288780 prefixEnd_8288780 := by exact prefixLift 8288780
  have htrace : WordTrace (prefixWord ++ tailWord_8288780) baseStart_8288780 baseEnd_8288780 := by
    simpa [prefixWord, tailWord_8288780, baseEnd_8288780] using wordTrace_append hprefix tailTrace_8288780
  have hstable : (prefixWord ++ tailWord_8288780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288780).length < 2 ^ (prefixWord ++ tailWord_8288780).sum := by decide
  have hdescent : baseEnd_8288780 < baseStart_8288780 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288803 : List Nat := [1, 1, 1, 4, 4, 1, 3, 1, 1, 4, 2]
def baseStart_8288803 : Nat := 118140960795 + 8288803 * 2 ^ 59
def prefixEnd_8288803 : Nat := 4983230072969 + 3 ^ 40 * 8288803 * 2
def baseEnd_8288803 : Nat := 4256139989429238753842995

theorem tailTrace_8288803 : CollatzResearch.WordTrace tailWord_8288803 prefixEnd_8288803 4256139989429238753842995 := by
  unfold tailWord_8288803
  simp only [CollatzResearch.WordTrace]
  refine ⟨302317481790089820694655063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201544987860059880463103375 302317481790089820694655063)
  ·
    refine ⟨453476222685134731041982595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302317481790089820694655063 453476222685134731041982595)
    ·
      refine ⟨680214334027702096562973893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453476222685134731041982595 680214334027702096562973893)
      ·
        refine ⟨127540187630194143105557605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 680214334027702096562973893 127540187630194143105557605)
        ·
          refine ⟨23913785180661401832292051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127540187630194143105557605 23913785180661401832292051)
          ·
            refine ⟨35870677770992102748438077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23913785180661401832292051 35870677770992102748438077)
            ·
              refine ⟨13451504164122038530664279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35870677770992102748438077 13451504164122038530664279)
              ·
                refine ⟨20177256246183057795996419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13451504164122038530664279 20177256246183057795996419)
                ·
                  refine ⟨30265884369274586693994629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20177256246183057795996419 30265884369274586693994629)
                  ·
                    refine ⟨5674853319238985005123993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30265884369274586693994629 5674853319238985005123993)
                    ·
                      refine ⟨4256139989429238753842995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5674853319238985005123993 4256139989429238753842995)
                      ·
                        rfl

theorem cell23_8288803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 4, 2].length) (baseStart_8288803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288803 prefixEnd_8288803 := by exact prefixLift 8288803
  have htrace : WordTrace (prefixWord ++ tailWord_8288803) baseStart_8288803 baseEnd_8288803 := by
    simpa [prefixWord, tailWord_8288803, baseEnd_8288803] using wordTrace_append hprefix tailTrace_8288803
  have hstable : (prefixWord ++ tailWord_8288803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288803).length < 2 ^ (prefixWord ++ tailWord_8288803).sum := by decide
  have hdescent : baseEnd_8288803 < baseStart_8288803 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288849 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 1, 1, 7]
def baseStart_8288849 : Nat := 118140960795 + 8288849 * 2 ^ 59
def prefixEnd_8288849 : Nat := 4983230072969 + 3 ^ 40 * 8288849 * 2
def baseEnd_8288849 : Nat := 4256163609539345573867783

theorem tailTrace_8288849 : CollatzResearch.WordTrace tailWord_8288849 prefixEnd_8288849 4256163609539345573867783 := by
  unfold tailWord_8288849
  simp only [CollatzResearch.WordTrace]
  refine ⟨302319159547923170550829601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201546106365282113700553067 302319159547923170550829601)
  ·
    refine ⟨226739369660942377913122201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302319159547923170550829601 226739369660942377913122201)
    ·
      refine ⟨170054527245706783434841651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226739369660942377913122201 170054527245706783434841651)
      ·
        refine ⟨255081790868560175152262477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170054527245706783434841651 255081790868560175152262477)
        ·
          refine ⟨95655671575710065682098429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255081790868560175152262477 95655671575710065682098429)
          ·
            refine ⟨35870876840891274630786911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95655671575710065682098429 35870876840891274630786911)
            ·
              refine ⟨53806315261336911946180367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35870876840891274630786911 53806315261336911946180367)
              ·
                refine ⟨80709472892005367919270551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53806315261336911946180367 80709472892005367919270551)
                ·
                  refine ⟨121064209338008051878905827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80709472892005367919270551 121064209338008051878905827)
                  ·
                    refine ⟨181596314007012077818358741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121064209338008051878905827 181596314007012077818358741)
                    ·
                      refine ⟨4256163609539345573867783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 181596314007012077818358741 4256163609539345573867783)
                      ·
                        rfl

theorem cell23_8288849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 1, 7].length) (baseStart_8288849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288849 prefixEnd_8288849 := by exact prefixLift 8288849
  have htrace : WordTrace (prefixWord ++ tailWord_8288849) baseStart_8288849 baseEnd_8288849 := by
    simpa [prefixWord, tailWord_8288849, baseEnd_8288849] using wordTrace_append hprefix tailTrace_8288849
  have hstable : (prefixWord ++ tailWord_8288849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288849).length < 2 ^ (prefixWord ++ tailWord_8288849).sum := by decide
  have hdescent : baseEnd_8288849 < baseStart_8288849 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288876 : List Nat := [2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 4]
def baseStart_8288876 : Nat := 118140960795 + 8288876 * 2 ^ 59
def prefixEnd_8288876 : Nat := 4983230072969 + 3 ^ 40 * 8288876 * 2
def baseEnd_8288876 : Nat := 4256177473517016968230159

theorem tailTrace_8288876 : CollatzResearch.WordTrace tailWord_8288876 prefixEnd_8288876 4256177473517016968230159 := by
  unfold tailWord_8288876
  simp only [CollatzResearch.WordTrace]
  refine ⟨151160072159412677081031241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201546762879216902774708321 151160072159412677081031241)
  ·
    refine ⟨113370054119559507810773431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151160072159412677081031241 113370054119559507810773431)
    ·
      refine ⟨170055081179339261716160147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113370054119559507810773431 170055081179339261716160147)
      ·
        refine ⟨255082621769008892574240221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170055081179339261716160147 255082621769008892574240221)
        ·
          refine ⟨95655983163378334715340083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255082621769008892574240221 95655983163378334715340083)
          ·
            refine ⟨143483974745067502073010125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95655983163378334715340083 143483974745067502073010125)
            ·
              refine ⟨53806490529400313277378797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143483974745067502073010125 53806490529400313277378797)
              ·
                refine ⟨20177433948525117479017049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53806490529400313277378797 20177433948525117479017049)
                ·
                  refine ⟨15133075461393838109262787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20177433948525117479017049 15133075461393838109262787)
                  ·
                    refine ⟨22699613192090757163894181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15133075461393838109262787 22699613192090757163894181)
                    ·
                      refine ⟨4256177473517016968230159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22699613192090757163894181 4256177473517016968230159)
                      ·
                        rfl

theorem cell23_8288876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_8288876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288876 prefixEnd_8288876 := by exact prefixLift 8288876
  have htrace : WordTrace (prefixWord ++ tailWord_8288876) baseStart_8288876 baseEnd_8288876 := by
    simpa [prefixWord, tailWord_8288876, baseEnd_8288876] using wordTrace_append hprefix tailTrace_8288876
  have hstable : (prefixWord ++ tailWord_8288876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288876).length < 2 ^ (prefixWord ++ tailWord_8288876).sum := by decide
  have hdescent : baseEnd_8288876 < baseStart_8288876 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288899 : List Nat := [1, 1, 1, 3, 3, 1, 2, 3, 8]
def baseStart_8288899 : Nat := 118140960795 + 8288899 * 2 ^ 59
def prefixEnd_8288899 : Nat := 4983230072969 + 3 ^ 40 * 8288899 * 2
def baseEnd_8288899 : Nat := 472909920396896708693617

theorem tailTrace_8288899 : CollatzResearch.WordTrace tailWord_8288899 prefixEnd_8288899 472909920396896708693617 := by
  unfold tailWord_8288899
  simp only [CollatzResearch.WordTrace]
  refine ⟨302320983197742029090149751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201547322131828019393433167 302320983197742029090149751)
  ·
    refine ⟨453481474796613043635224627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302320983197742029090149751 453481474796613043635224627)
    ·
      refine ⟨680222212194919565452836941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453481474796613043635224627 680222212194919565452836941)
      ·
        refine ⟨255083329573094837044813853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 680222212194919565452836941 255083329573094837044813853)
        ·
          refine ⟨95656248589910563891805195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255083329573094837044813853 95656248589910563891805195)
          ·
            refine ⟨143484372884865845837707793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95656248589910563891805195 143484372884865845837707793)
            ·
              refine ⟨107613279663649384378280845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143484372884865845837707793 107613279663649384378280845)
              ·
                refine ⟨40354979873868519141855317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107613279663649384378280845 40354979873868519141855317)
                ·
                  refine ⟨472909920396896708693617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40354979873868519141855317 472909920396896708693617)
                  ·
                    rfl

theorem cell23_8288899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 3, 8].length) (baseStart_8288899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288899 prefixEnd_8288899 := by exact prefixLift 8288899
  have htrace : WordTrace (prefixWord ++ tailWord_8288899) baseStart_8288899 baseEnd_8288899 := by
    simpa [prefixWord, tailWord_8288899, baseEnd_8288899] using wordTrace_append hprefix tailTrace_8288899
  have hstable : (prefixWord ++ tailWord_8288899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288899).length < 2 ^ (prefixWord ++ tailWord_8288899).sum := by decide
  have hdescent : baseEnd_8288899 < baseStart_8288899 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288950 : List Nat := [5, 1, 3, 1, 2, 1, 1, 1, 8]
def baseStart_8288950 : Nat := 118140960795 + 8288950 * 2 ^ 59
def prefixEnd_8288950 : Nat := 4983230072969 + 3 ^ 40 * 8288950 * 2
def baseEnd_8288950 : Nat := 472912830120605519856091

theorem tailTrace_8288950 : CollatzResearch.WordTrace tailWord_8288950 prefixEnd_8288950 472912830120605519856091 := by
  unfold tailWord_8288950
  simp only [CollatzResearch.WordTrace]
  refine ⟨18895177707534829050016019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201548562213704843200170869 18895177707534829050016019)
  ·
    refine ⟨28342766561302243575024029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18895177707534829050016019 28342766561302243575024029)
    ·
      refine ⟨10628537460488341340634011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28342766561302243575024029 10628537460488341340634011)
      ·
        refine ⟨15942806190732512010951017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10628537460488341340634011 15942806190732512010951017)
        ·
          refine ⟨11957104643049384008213263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15942806190732512010951017 11957104643049384008213263)
          ·
            refine ⟨17935656964574076012319895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11957104643049384008213263 17935656964574076012319895)
            ·
              refine ⟨26903485446861114018479843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17935656964574076012319895 26903485446861114018479843)
              ·
                refine ⟨40355228170291671027719765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26903485446861114018479843 40355228170291671027719765)
                ·
                  refine ⟨472912830120605519856091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 40355228170291671027719765 472912830120605519856091)
                  ·
                    rfl

theorem cell23_8288950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 1, 8].length) (baseStart_8288950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288950 prefixEnd_8288950 := by exact prefixLift 8288950
  have htrace : WordTrace (prefixWord ++ tailWord_8288950) baseStart_8288950 baseEnd_8288950 := by
    simpa [prefixWord, tailWord_8288950, baseEnd_8288950] using wordTrace_append hprefix tailTrace_8288950
  have hstable : (prefixWord ++ tailWord_8288950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288950).length < 2 ^ (prefixWord ++ tailWord_8288950).sum := by decide
  have hdescent : baseEnd_8288950 < baseStart_8288950 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288953 : List Nat := [1, 2, 1, 4, 1, 1, 1, 3, 4, 3, 2]
def baseStart_8288953 : Nat := 118140960795 + 8288953 * 2 ^ 59
def prefixEnd_8288953 : Nat := 4983230072969 + 3 ^ 40 * 8288953 * 2
def baseEnd_8288953 : Nat := 4256217011527413166967305

theorem tailTrace_8288953 : CollatzResearch.WordTrace tailWord_8288953 prefixEnd_8288953 4256217011527413166967305 := by
  unfold tailWord_8288953
  simp only [CollatzResearch.WordTrace]
  refine ⟨302322952739546396312615513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201548635159697597541743675 302322952739546396312615513)
  ·
    refine ⟨226742214554659797234461635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302322952739546396312615513 226742214554659797234461635)
    ·
      refine ⟨340113321831989695851692453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226742214554659797234461635 340113321831989695851692453)
      ·
        refine ⟨63771247843498067972192335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340113321831989695851692453 63771247843498067972192335)
        ·
          refine ⟨95656871765247101958288503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63771247843498067972192335 95656871765247101958288503)
          ·
            refine ⟨143485307647870652937432755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95656871765247101958288503 143485307647870652937432755)
            ·
              refine ⟨215227961471805979406149133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143485307647870652937432755 215227961471805979406149133)
              ·
                refine ⟨80710485551927242277305925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215227961471805979406149133 80710485551927242277305925)
                ·
                  refine ⟨15133216040986357926994861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80710485551927242277305925 15133216040986357926994861)
                  ·
                    refine ⟨5674956015369884222623073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15133216040986357926994861 5674956015369884222623073)
                    ·
                      refine ⟨4256217011527413166967305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5674956015369884222623073 4256217011527413166967305)
                      ·
                        rfl

theorem cell23_8288953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 3, 4, 3, 2].length) (baseStart_8288953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288953 prefixEnd_8288953 := by exact prefixLift 8288953
  have htrace : WordTrace (prefixWord ++ tailWord_8288953) baseStart_8288953 baseEnd_8288953 := by
    simpa [prefixWord, tailWord_8288953, baseEnd_8288953] using wordTrace_append hprefix tailTrace_8288953
  have hstable : (prefixWord ++ tailWord_8288953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288953).length < 2 ^ (prefixWord ++ tailWord_8288953).sum := by decide
  have hdescent : baseEnd_8288953 < baseStart_8288953 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288960 : List Nat := [2, 1, 1, 2, 4, 3, 2, 1, 3, 1, 3]
def baseStart_8288960 : Nat := 118140960795 + 8288960 * 2 ^ 59
def prefixEnd_8288960 : Nat := 4983230072969 + 3 ^ 40 * 8288960 * 2
def baseEnd_8288960 : Nat := 4256220605891994639579773

theorem tailTrace_8288960 : CollatzResearch.WordTrace tailWord_8288960 prefixEnd_8288960 4256220605891994639579773 := by
  unfold tailWord_8288960
  simp only [CollatzResearch.WordTrace]
  refine ⟨151161604025260518254060167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201548805367014024338746889 151161604025260518254060167)
  ·
    refine ⟨226742406037890777381090251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151161604025260518254060167 226742406037890777381090251)
    ·
      refine ⟨340113609056836166071635377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226742406037890777381090251 340113609056836166071635377)
      ·
        refine ⟨255085206792627124553726533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340113609056836166071635377 255085206792627124553726533)
        ·
          refine ⟨47828476273617585853823725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255085206792627124553726533 47828476273617585853823725)
          ·
            refine ⟨17935678602606594695183897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47828476273617585853823725 17935678602606594695183897)
            ·
              refine ⟨13451758951954946021387923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17935678602606594695183897 13451758951954946021387923)
              ·
                refine ⟨20177638427932419032081885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13451758951954946021387923 20177638427932419032081885)
                ·
                  refine ⟨7566614410474657137030707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20177638427932419032081885 7566614410474657137030707)
                  ·
                    refine ⟨11349921615711985705546061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7566614410474657137030707 11349921615711985705546061)
                    ·
                      refine ⟨4256220605891994639579773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11349921615711985705546061 4256220605891994639579773)
                      ·
                        rfl

theorem cell23_8288960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 2, 1, 3, 1, 3].length) (baseStart_8288960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288960 prefixEnd_8288960 := by exact prefixLift 8288960
  have htrace : WordTrace (prefixWord ++ tailWord_8288960) baseStart_8288960 baseEnd_8288960 := by
    simpa [prefixWord, tailWord_8288960, baseEnd_8288960] using wordTrace_append hprefix tailTrace_8288960
  have hstable : (prefixWord ++ tailWord_8288960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288960).length < 2 ^ (prefixWord ++ tailWord_8288960).sum := by decide
  have hdescent : baseEnd_8288960 < baseStart_8288960 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288983 : List Nat := [1, 1, 3, 2, 1, 4, 1, 4, 1, 1, 4]
def baseStart_8288983 : Nat := 118140960795 + 8288983 * 2 ^ 59
def prefixEnd_8288983 : Nat := 4983230072969 + 3 ^ 40 * 8288983 * 2
def baseEnd_8288983 : Nat := 4256232415947048049592167

theorem tailTrace_8288983 : CollatzResearch.WordTrace tailWord_8288983 prefixEnd_8288983 4256232415947048049592167 := by
  unfold tailWord_8288983
  simp only [CollatzResearch.WordTrace]
  refine ⟨302324046929437711436207603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201549364619625140957471735 302324046929437711436207603)
  ·
    refine ⟨453486070394156567154311405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302324046929437711436207603 453486070394156567154311405)
    ·
      refine ⟨170057276397808712682866777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 453486070394156567154311405 170057276397808712682866777)
      ·
        refine ⟨127542957298356534512150083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170057276397808712682866777 127542957298356534512150083)
        ·
          refine ⟨191314435947534801768225125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127542957298356534512150083 191314435947534801768225125)
          ·
            refine ⟨35871456740162775331542211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191314435947534801768225125 35871456740162775331542211)
            ·
              refine ⟨53807185110244162997313317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35871456740162775331542211 53807185110244162997313317)
              ·
                refine ⟨10088847208170780561996247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53807185110244162997313317 10088847208170780561996247)
                ·
                  refine ⟨15133270812256170842994371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10088847208170780561996247 15133270812256170842994371)
                  ·
                    refine ⟨22699906218384256264491557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15133270812256170842994371 22699906218384256264491557)
                    ·
                      refine ⟨4256232415947048049592167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22699906218384256264491557 4256232415947048049592167)
                      ·
                        rfl

theorem cell23_8288983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 1, 4, 1, 1, 4].length) (baseStart_8288983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288983 prefixEnd_8288983 := by exact prefixLift 8288983
  have htrace : WordTrace (prefixWord ++ tailWord_8288983) baseStart_8288983 baseEnd_8288983 := by
    simpa [prefixWord, tailWord_8288983, baseEnd_8288983] using wordTrace_append hprefix tailTrace_8288983
  have hstable : (prefixWord ++ tailWord_8288983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288983).length < 2 ^ (prefixWord ++ tailWord_8288983).sum := by decide
  have hdescent : baseEnd_8288983 < baseStart_8288983 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288986 : List Nat := [3, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5]
def baseStart_8288986 : Nat := 118140960795 + 8288986 * 2 ^ 59
def prefixEnd_8288986 : Nat := 4983230072969 + 3 ^ 40 * 8288986 * 2
def baseEnd_8288986 : Nat := 4256233956389011537854653

theorem tailTrace_8288986 : CollatzResearch.WordTrace tailWord_8288986 prefixEnd_8288986 4256233956389011537854653 := by
  unfold tailWord_8288986
  simp only [CollatzResearch.WordTrace]
  refine ⟨75581039087106710737141703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201549437565617895299044541 75581039087106710737141703)
  ·
    refine ⟨113371558630660066105712555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75581039087106710737141703 113371558630660066105712555)
    ·
      refine ⟨170057337945990099158568833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113371558630660066105712555 170057337945990099158568833)
      ·
        refine ⟨127543003459492574368926625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170057337945990099158568833 127543003459492574368926625)
        ·
          refine ⟨95657252594619430776694969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127543003459492574368926625 95657252594619430776694969)
          ·
            refine ⟨71742939445964573082521227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95657252594619430776694969 71742939445964573082521227)
            ·
              refine ⟨107614409168946859623781841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71742939445964573082521227 107614409168946859623781841)
              ·
                refine ⟨80710806876710144717836381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107614409168946859623781841 80710806876710144717836381)
                ·
                  refine ⟨30266552578766304269188643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80710806876710144717836381 30266552578766304269188643)
                  ·
                    refine ⟨45399828868149456403782965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30266552578766304269188643 45399828868149456403782965)
                    ·
                      refine ⟨4256233956389011537854653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45399828868149456403782965 4256233956389011537854653)
                      ·
                        rfl

theorem cell23_8288986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 2, 3, 1, 5].length) (baseStart_8288986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288986 prefixEnd_8288986 := by exact prefixLift 8288986
  have htrace : WordTrace (prefixWord ++ tailWord_8288986) baseStart_8288986 baseEnd_8288986 := by
    simpa [prefixWord, tailWord_8288986, baseEnd_8288986] using wordTrace_append hprefix tailTrace_8288986
  have hstable : (prefixWord ++ tailWord_8288986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288986).length < 2 ^ (prefixWord ++ tailWord_8288986).sum := by decide
  have hdescent : baseEnd_8288986 < baseStart_8288986 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8288993 : List Nat := [1, 2, 3, 1, 4, 1, 1, 2, 4, 4]
def baseStart_8288993 : Nat := 118140960795 + 8288993 * 2 ^ 59
def prefixEnd_8288993 : Nat := 4983230072969 + 3 ^ 40 * 8288993 * 2
def baseEnd_8288993 : Nat := 1418745850251197670155707

theorem tailTrace_8288993 : CollatzResearch.WordTrace tailWord_8288993 prefixEnd_8288993 1418745850251197670155707 := by
  unfold tailWord_8288993
  simp only [CollatzResearch.WordTrace]
  refine ⟨302324411659401483144071633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201549607772934322096047755 302324411659401483144071633)
  ·
    refine ⟨226743308744551112358053725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302324411659401483144071633 226743308744551112358053725)
    ·
      refine ⟨85028740779206667134270147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226743308744551112358053725 85028740779206667134270147)
      ·
        refine ⟨127543111168810000701405221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85028740779206667134270147 127543111168810000701405221)
        ·
          refine ⟨23914333344151875131513479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127543111168810000701405221 23914333344151875131513479)
          ·
            refine ⟨35871500016227812697270219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23914333344151875131513479 35871500016227812697270219)
            ·
              refine ⟨53807250024341719045905329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35871500016227812697270219 53807250024341719045905329)
              ·
                refine ⟨40355437518256289284428997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53807250024341719045905329 40355437518256289284428997)
                ·
                  refine ⟨7566644534673054240830437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40355437518256289284428997 7566644534673054240830437)
                  ·
                    refine ⟨1418745850251197670155707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7566644534673054240830437 1418745850251197670155707)
                    ·
                      rfl

theorem cell23_8288993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 4].length) (baseStart_8288993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8288993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8288993 prefixEnd_8288993 := by exact prefixLift 8288993
  have htrace : WordTrace (prefixWord ++ tailWord_8288993) baseStart_8288993 baseEnd_8288993 := by
    simpa [prefixWord, tailWord_8288993, baseEnd_8288993] using wordTrace_append hprefix tailTrace_8288993
  have hstable : (prefixWord ++ tailWord_8288993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8288993).length < 2 ^ (prefixWord ++ tailWord_8288993).sum := by decide
  have hdescent : baseEnd_8288993 < baseStart_8288993 := by decide
  rcases family_descends (prefixWord ++ tailWord_8288993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289006 : List Nat := [4, 1, 2, 1, 1, 3, 11]
def baseStart_8289006 : Nat := 118140960795 + 8289006 * 2 ^ 59
def prefixEnd_8289006 : Nat := 4983230072969 + 3 ^ 40 * 8289006 * 2
def baseEnd_8289006 : Nat := 52546225012371622958081

theorem tailTrace_8289006 : CollatzResearch.WordTrace tailWord_8289006 prefixEnd_8289006 52546225012371622958081 := by
  unfold tailWord_8289006
  simp only [CollatzResearch.WordTrace]
  refine ⟨37790610726044298295536859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201549923872236257576196581 37790610726044298295536859)
  ·
    refine ⟨56685916089066447443305289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37790610726044298295536859 56685916089066447443305289)
    ·
      refine ⟨42514437066799835582478967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56685916089066447443305289 42514437066799835582478967)
      ·
        refine ⟨63771655600199753373718451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42514437066799835582478967 63771655600199753373718451)
        ·
          refine ⟨95657483400299630060577677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63771655600199753373718451 95657483400299630060577677)
          ·
            refine ⟨35871556275112361272716629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95657483400299630060577677 35871556275112361272716629)
            ·
              refine ⟨52546225012371622958081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 35871556275112361272716629 52546225012371622958081)
              ·
                rfl

theorem cell23_8289006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 11].length) (baseStart_8289006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289006 prefixEnd_8289006 := by exact prefixLift 8289006
  have htrace : WordTrace (prefixWord ++ tailWord_8289006) baseStart_8289006 baseEnd_8289006 := by
    simpa [prefixWord, tailWord_8289006, baseEnd_8289006] using wordTrace_append hprefix tailTrace_8289006
  have hstable : (prefixWord ++ tailWord_8289006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289006).length < 2 ^ (prefixWord ++ tailWord_8289006).sum := by decide
  have hdescent : baseEnd_8289006 < baseStart_8289006 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289017 : List Nat := [1, 2, 1, 3, 1, 1, 1, 8, 1, 2, 2]
def baseStart_8289017 : Nat := 118140960795 + 8289017 * 2 ^ 59
def prefixEnd_8289017 : Nat := 4983230072969 + 3 ^ 40 * 8289017 * 2
def baseEnd_8289017 : Nat := 4256249874289300916567011

theorem tailTrace_8289017 : CollatzResearch.WordTrace tailWord_8289017 prefixEnd_8289017 4256249874289300916567011 := by
  unfold tailWord_8289017
  simp only [CollatzResearch.WordTrace]
  refine ⟨302325287011314535242945305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201550191340876356828630203 302325287011314535242945305)
  ·
    refine ⟨226743965258485901432208979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302325287011314535242945305 226743965258485901432208979)
    ·
      refine ⟨340115947887728852148313469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226743965258485901432208979 340115947887728852148313469)
      ·
        refine ⟨127543480457898319555617551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340115947887728852148313469 127543480457898319555617551)
        ·
          refine ⟨191315220686847479333426327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127543480457898319555617551 191315220686847479333426327)
          ·
            refine ⟨286972831030271219000139491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191315220686847479333426327 286972831030271219000139491)
            ·
              refine ⟨430459246545406828500209237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286972831030271219000139491 430459246545406828500209237)
              ·
                refine ⟨5044444295453986271486827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 430459246545406828500209237 5044444295453986271486827)
                ·
                  refine ⟨7566666443180979407230241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5044444295453986271486827 7566666443180979407230241)
                  ·
                    refine ⟨5674999832385734555422681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7566666443180979407230241 5674999832385734555422681)
                    ·
                      refine ⟨4256249874289300916567011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5674999832385734555422681 4256249874289300916567011)
                      ·
                        rfl

theorem cell23_8289017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 1, 2, 2].length) (baseStart_8289017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289017 prefixEnd_8289017 := by exact prefixLift 8289017
  have htrace : WordTrace (prefixWord ++ tailWord_8289017) baseStart_8289017 baseEnd_8289017 := by
    simpa [prefixWord, tailWord_8289017, baseEnd_8289017] using wordTrace_append hprefix tailTrace_8289017
  have hstable : (prefixWord ++ tailWord_8289017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289017).length < 2 ^ (prefixWord ++ tailWord_8289017).sum := by decide
  have hdescent : baseEnd_8289017 < baseStart_8289017 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289124 : List Nat := [2, 3, 1, 1, 4, 1, 3, 2, 2, 2, 2]
def baseStart_8289124 : Nat := 118140960795 + 8289124 * 2 ^ 59
def prefixEnd_8289124 : Nat := 4983230072969 + 3 ^ 40 * 8289124 * 2
def baseEnd_8289124 : Nat := 4256304816719331997929019

theorem tailTrace_8289124 : CollatzResearch.WordTrace tailWord_8289124 prefixEnd_8289124 4256304816719331997929019 := by
  unfold tailWord_8289124
  simp only [CollatzResearch.WordTrace]
  refine ⟨151164594810963446258545213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201552793081284595011393617 151164594810963446258545213)
  ·
    refine ⟨56686723054111292346954455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151164594810963446258545213 56686723054111292346954455)
    ·
      refine ⟨85030084581166938520431683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56686723054111292346954455 85030084581166938520431683)
      ·
        refine ⟨127545126871750407780647525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85030084581166938520431683 127545126871750407780647525)
        ·
          refine ⟨23914711288453201458871411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127545126871750407780647525 23914711288453201458871411)
          ·
            refine ⟨35872066932679802188307117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23914711288453201458871411 35872066932679802188307117)
            ·
              refine ⟨13452025099754925820615169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35872066932679802188307117 13452025099754925820615169)
              ·
                refine ⟨10089018824816194365461377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13452025099754925820615169 10089018824816194365461377)
                ·
                  refine ⟨7566764118612145774096033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10089018824816194365461377 7566764118612145774096033)
                  ·
                    refine ⟨5675073088959109330572025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7566764118612145774096033 5675073088959109330572025)
                    ·
                      refine ⟨4256304816719331997929019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5675073088959109330572025 4256304816719331997929019)
                      ·
                        rfl

theorem cell23_8289124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 3, 2, 2, 2, 2].length) (baseStart_8289124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289124 prefixEnd_8289124 := by exact prefixLift 8289124
  have htrace : WordTrace (prefixWord ++ tailWord_8289124) baseStart_8289124 baseEnd_8289124 := by
    simpa [prefixWord, tailWord_8289124, baseEnd_8289124] using wordTrace_append hprefix tailTrace_8289124
  have hstable : (prefixWord ++ tailWord_8289124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289124).length < 2 ^ (prefixWord ++ tailWord_8289124).sum := by decide
  have hdescent : baseEnd_8289124 < baseStart_8289124 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289141 : List Nat := [1, 3, 4, 1, 1, 3, 3, 1, 2, 2, 2]
def baseStart_8289141 : Nat := 118140960795 + 8289141 * 2 ^ 59
def prefixEnd_8289141 : Nat := 4983230072969 + 3 ^ 40 * 8289141 * 2
def baseEnd_8289141 : Nat := 4256313545890458431416441

theorem tailTrace_8289141 : CollatzResearch.WordTrace tailWord_8289141 prefixEnd_8289141 4256313545890458431416441 := by
  unfold tailWord_8289141
  simp only [CollatzResearch.WordTrace]
  refine ⟨302329809662865304420459277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201553206441910202946972851 302329809662865304420459277)
  ·
    refine ⟨113373678623574489157672229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302329809662865304420459277 113373678623574489157672229)
    ·
      refine ⟨21257564741920216717063543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113373678623574489157672229 21257564741920216717063543)
      ·
        refine ⟨31886347112880325075595315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21257564741920216717063543 31886347112880325075595315)
        ·
          refine ⟨47829520669320487613392973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31886347112880325075595315 47829520669320487613392973)
          ·
            refine ⟨17936070250995182855022365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47829520669320487613392973 17936070250995182855022365)
            ·
              refine ⟨6726026344123193570633387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17936070250995182855022365 6726026344123193570633387)
              ·
                refine ⟨10089039516184790355950081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6726026344123193570633387 10089039516184790355950081)
                ·
                  refine ⟨7566779637138592766962561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10089039516184790355950081 7566779637138592766962561)
                  ·
                    refine ⟨5675084727853944575221921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7566779637138592766962561 5675084727853944575221921)
                    ·
                      refine ⟨4256313545890458431416441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5675084727853944575221921 4256313545890458431416441)
                      ·
                        rfl

theorem cell23_8289141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 3, 1, 2, 2, 2].length) (baseStart_8289141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289141 prefixEnd_8289141 := by exact prefixLift 8289141
  have htrace : WordTrace (prefixWord ++ tailWord_8289141) baseStart_8289141 baseEnd_8289141 := by
    simpa [prefixWord, tailWord_8289141, baseEnd_8289141] using wordTrace_append hprefix tailTrace_8289141
  have hstable : (prefixWord ++ tailWord_8289141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289141).length < 2 ^ (prefixWord ++ tailWord_8289141).sum := by decide
  have hdescent : baseEnd_8289141 < baseStart_8289141 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289163 : List Nat := [1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 4]
def baseStart_8289163 : Nat := 118140960795 + 8289163 * 2 ^ 59
def prefixEnd_8289163 : Nat := 4983230072969 + 3 ^ 40 * 8289163 * 2
def baseEnd_8289163 : Nat := 4256324842464857345341339

theorem tailTrace_8289163 : CollatzResearch.WordTrace tailWord_8289163 prefixEnd_8289163 4256324842464857345341339 := by
  unfold tailWord_8289163
  simp only [CollatzResearch.WordTrace]
  refine ⟨302330612068785602177760143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201553741379190401451840095 302330612068785602177760143)
  ·
    refine ⟨453495918103178403266640215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302330612068785602177760143 453495918103178403266640215)
    ·
      refine ⟨680243877154767604899960323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453495918103178403266640215 680243877154767604899960323)
      ·
        refine ⟨1020365815732151407349940485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680243877154767604899960323 1020365815732151407349940485)
        ·
          refine ⟨191318590449778388878113841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1020365815732151407349940485 191318590449778388878113841)
          ·
            refine ⟨143488942837333791658585381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191318590449778388878113841 143488942837333791658585381)
            ·
              refine ⟨26904176782000085935984759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 143488942837333791658585381 26904176782000085935984759)
              ·
                refine ⟨40356265173000128903977139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26904176782000085935984759 40356265173000128903977139)
                ·
                  refine ⟨60534397759500193355965709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40356265173000128903977139 60534397759500193355965709)
                  ·
                    refine ⟨22700399159812572508487141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60534397759500193355965709 22700399159812572508487141)
                    ·
                      refine ⟨4256324842464857345341339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22700399159812572508487141 4256324842464857345341339)
                      ·
                        rfl

theorem cell23_8289163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 3, 4].length) (baseStart_8289163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289163 prefixEnd_8289163 := by exact prefixLift 8289163
  have htrace : WordTrace (prefixWord ++ tailWord_8289163) baseStart_8289163 baseEnd_8289163 := by
    simpa [prefixWord, tailWord_8289163, baseEnd_8289163] using wordTrace_append hprefix tailTrace_8289163
  have hstable : (prefixWord ++ tailWord_8289163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289163).length < 2 ^ (prefixWord ++ tailWord_8289163).sum := by decide
  have hdescent : baseEnd_8289163 < baseStart_8289163 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289237 : List Nat := [1, 3, 2, 3, 3, 1, 2, 2, 6]
def baseStart_8289237 : Nat := 118140960795 + 8289237 * 2 ^ 59
def prefixEnd_8289237 : Nat := 4983230072969 + 3 ^ 40 * 8289237 * 2
def baseEnd_8289237 : Nat := 472929204448143339535111

theorem tailTrace_8289237 : CollatzResearch.WordTrace tailWord_8289237 prefixEnd_8289237 472929204448143339535111 := by
  unfold tailWord_8289237
  simp only [CollatzResearch.WordTrace]
  refine ⟨302333311070517512815953965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201555540713678341877302643 302333311070517512815953965)
  ·
    refine ⟨113374991651444067305982737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302333311070517512815953965 113374991651444067305982737)
    ·
      refine ⟨85031243738583050479487053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113374991651444067305982737 85031243738583050479487053)
      ·
        refine ⟨31886716401968643929807645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85031243738583050479487053 31886716401968643929807645)
        ·
          refine ⟨11957518650738241473677867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31886716401968643929807645 11957518650738241473677867)
          ·
            refine ⟨17936277976107362210516801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11957518650738241473677867 17936277976107362210516801)
            ·
              refine ⟨13452208482080521657887601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17936277976107362210516801 13452208482080521657887601)
              ·
                refine ⟨10089156361560391243415701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13452208482080521657887601 10089156361560391243415701)
                ·
                  refine ⟨472929204448143339535111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10089156361560391243415701 472929204448143339535111)
                  ·
                    rfl

theorem cell23_8289237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 2, 6].length) (baseStart_8289237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289237 prefixEnd_8289237 := by exact prefixLift 8289237
  have htrace : WordTrace (prefixWord ++ tailWord_8289237) baseStart_8289237 baseEnd_8289237 := by
    simpa [prefixWord, tailWord_8289237, baseEnd_8289237] using wordTrace_append hprefix tailTrace_8289237
  have hstable : (prefixWord ++ tailWord_8289237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289237).length < 2 ^ (prefixWord ++ tailWord_8289237).sum := by decide
  have hdescent : baseEnd_8289237 < baseStart_8289237 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289241 : List Nat := [1, 2, 1, 2, 5, 3, 2, 2, 1, 4]
def baseStart_8289241 : Nat := 118140960795 + 8289241 * 2 ^ 59
def prefixEnd_8289241 : Nat := 4983230072969 + 3 ^ 40 * 8289241 * 2
def baseEnd_8289241 : Nat := 1418788297985302680055327

theorem tailTrace_8289241 : CollatzResearch.WordTrace tailWord_8289241 prefixEnd_8289241 1418788297985302680055327 := by
  unfold tailWord_8289241
  simp only [CollatzResearch.WordTrace]
  refine ⟨302333456962503021499099577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201555637975002014332733051 302333456962503021499099577)
  ·
    refine ⟨226750092721877266124324683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302333456962503021499099577 226750092721877266124324683)
    ·
      refine ⟨340125139082815899186487025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226750092721877266124324683 340125139082815899186487025)
      ·
        refine ⟨255093854312111924389865269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340125139082815899186487025 255093854312111924389865269)
        ·
          refine ⟨23915048841760492911549869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 255093854312111924389865269 23915048841760492911549869)
          ·
            refine ⟨8968143315660184841831201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23915048841760492911549869 8968143315660184841831201)
            ·
              refine ⟨6726107486745138631373401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8968143315660184841831201 6726107486745138631373401)
              ·
                refine ⟨5044580615058853973530051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6726107486745138631373401 5044580615058853973530051)
                ·
                  refine ⟨7566870922588280960295077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5044580615058853973530051 7566870922588280960295077)
                  ·
                    refine ⟨1418788297985302680055327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7566870922588280960295077 1418788297985302680055327)
                    ·
                      rfl

theorem cell23_8289241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 3, 2, 2, 1, 4].length) (baseStart_8289241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289241 prefixEnd_8289241 := by exact prefixLift 8289241
  have htrace : WordTrace (prefixWord ++ tailWord_8289241) baseStart_8289241 baseEnd_8289241 := by
    simpa [prefixWord, tailWord_8289241, baseEnd_8289241] using wordTrace_append hprefix tailTrace_8289241
  have hstable : (prefixWord ++ tailWord_8289241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289241).length < 2 ^ (prefixWord ++ tailWord_8289241).sum := by decide
  have hdescent : baseEnd_8289241 < baseStart_8289241 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289268 : List Nat := [2, 6, 2, 1, 1, 1, 1, 1, 1, 4, 3]
def baseStart_8289268 : Nat := 118140960795 + 8289268 * 2 ^ 59
def prefixEnd_8289268 : Nat := 4983230072969 + 3 ^ 40 * 8289268 * 2
def baseEnd_8289268 : Nat := 4256378757933579434528357

theorem tailTrace_8289268 : CollatzResearch.WordTrace tailWord_8289268 prefixEnd_8289268 4256378757933579434528357 := by
  unfold tailWord_8289268
  simp only [CollatzResearch.WordTrace]
  refine ⟨151167220866702602555166229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201556294488936803406888305 151167220866702602555166229)
  ·
    refine ⟨7085963478126684494773417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 151167220866702602555166229 7085963478126684494773417)
    ·
      refine ⟨5314472608595013371080063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7085963478126684494773417 5314472608595013371080063)
      ·
        refine ⟨7971708912892520056620095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5314472608595013371080063 7971708912892520056620095)
        ·
          refine ⟨11957563369338780084930143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7971708912892520056620095 11957563369338780084930143)
          ·
            refine ⟨17936345054008170127395215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11957563369338780084930143 17936345054008170127395215)
            ·
              refine ⟨26904517581012255191092823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17936345054008170127395215 26904517581012255191092823)
              ·
                refine ⟨40356776371518382786639235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26904517581012255191092823 40356776371518382786639235)
                ·
                  refine ⟨60535164557277574179958853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40356776371518382786639235 60535164557277574179958853)
                  ·
                    refine ⟨11350343354489545158742285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60535164557277574179958853 11350343354489545158742285)
                    ·
                      refine ⟨4256378757933579434528357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11350343354489545158742285 4256378757933579434528357)
                      ·
                        rfl

theorem cell23_8289268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_8289268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289268 prefixEnd_8289268 := by exact prefixLift 8289268
  have htrace : WordTrace (prefixWord ++ tailWord_8289268) baseStart_8289268 baseEnd_8289268 := by
    simpa [prefixWord, tailWord_8289268, baseEnd_8289268] using wordTrace_append hprefix tailTrace_8289268
  have hstable : (prefixWord ++ tailWord_8289268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289268).length < 2 ^ (prefixWord ++ tailWord_8289268).sum := by decide
  have hdescent : baseEnd_8289268 < baseStart_8289268 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289281 : List Nat := [1, 2, 4, 1, 2, 3, 2, 3, 1, 1, 3]
def baseStart_8289281 : Nat := 118140960795 + 8289281 * 2 ^ 59
def prefixEnd_8289281 : Nat := 4983230072969 + 3 ^ 40 * 8289281 * 2
def baseEnd_8289281 : Nat := 4256385433182087883665797

theorem tailTrace_8289281 : CollatzResearch.WordTrace tailWord_8289281 prefixEnd_8289281 4256385433182087883665797 := by
  unfold tailWord_8289281
  simp only [CollatzResearch.WordTrace]
  refine ⟨302334915882358108330555697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201556610588238738887037131 302334915882358108330555697)
  ·
    refine ⟨226751186911768581247916773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302334915882358108330555697 226751186911768581247916773)
    ·
      refine ⟨42515847545956608983984395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226751186911768581247916773 42515847545956608983984395)
      ·
        refine ⟨63773771318934913475976593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42515847545956608983984395 63773771318934913475976593)
        ·
          refine ⟨47830328489201185106982445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63773771318934913475976593 47830328489201185106982445)
          ·
            refine ⟨17936373183450444415118417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47830328489201185106982445 17936373183450444415118417)
            ·
              refine ⟨13452279887587833311338813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17936373183450444415118417 13452279887587833311338813)
              ·
                refine ⟨5044604957845437491752055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13452279887587833311338813 5044604957845437491752055)
                ·
                  refine ⟨7566907436768156237628083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5044604957845437491752055 7566907436768156237628083)
                  ·
                    refine ⟨11350361155152234356442125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7566907436768156237628083 11350361155152234356442125)
                    ·
                      refine ⟨4256385433182087883665797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11350361155152234356442125 4256385433182087883665797)
                      ·
                        rfl

theorem cell23_8289281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 3, 1, 1, 3].length) (baseStart_8289281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289281 prefixEnd_8289281 := by exact prefixLift 8289281
  have htrace : WordTrace (prefixWord ++ tailWord_8289281) baseStart_8289281 baseEnd_8289281 := by
    simpa [prefixWord, tailWord_8289281, baseEnd_8289281] using wordTrace_append hprefix tailTrace_8289281
  have hstable : (prefixWord ++ tailWord_8289281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289281).length < 2 ^ (prefixWord ++ tailWord_8289281).sum := by decide
  have hdescent : baseEnd_8289281 < baseStart_8289281 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289283 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 6]
def baseStart_8289283 : Nat := 118140960795 + 8289283 * 2 ^ 59
def prefixEnd_8289283 : Nat := 4983230072969 + 3 ^ 40 * 8289283 * 2
def baseEnd_8289283 : Nat := 4256386460143396875840787

theorem tailTrace_8289283 : CollatzResearch.WordTrace tailWord_8289283 prefixEnd_8289283 4256386460143396875840787 := by
  unfold tailWord_8289283
  simp only [CollatzResearch.WordTrace]
  refine ⟨302334988828350862672128503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201556659218900575114752335 302334988828350862672128503)
  ·
    refine ⟨453502483242526294008192755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302334988828350862672128503 453502483242526294008192755)
    ·
      refine ⟨680253724863789441012289133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453502483242526294008192755 680253724863789441012289133)
      ·
        refine ⟨255095146823921040379608425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 680253724863789441012289133 255095146823921040379608425)
        ·
          refine ⟨191321360117940780284706319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255095146823921040379608425 191321360117940780284706319)
          ·
            refine ⟨286982040176911170427059479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191321360117940780284706319 286982040176911170427059479)
            ·
              refine ⟨430473060265366755640589219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 286982040176911170427059479 430473060265366755640589219)
              ·
                refine ⟨645709590398050133460883829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430473060265366755640589219 645709590398050133460883829)
                ·
                  refine ⟨60535274099817200011957859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 645709590398050133460883829 60535274099817200011957859)
                  ·
                    refine ⟨90802911149725800017936789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60535274099817200011957859 90802911149725800017936789)
                    ·
                      refine ⟨4256386460143396875840787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90802911149725800017936789 4256386460143396875840787)
                      ·
                        rfl

theorem cell23_8289283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 6].length) (baseStart_8289283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289283 prefixEnd_8289283 := by exact prefixLift 8289283
  have htrace : WordTrace (prefixWord ++ tailWord_8289283) baseStart_8289283 baseEnd_8289283 := by
    simpa [prefixWord, tailWord_8289283, baseEnd_8289283] using wordTrace_append hprefix tailTrace_8289283
  have hstable : (prefixWord ++ tailWord_8289283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289283).length < 2 ^ (prefixWord ++ tailWord_8289283).sum := by decide
  have hdescent : baseEnd_8289283 < baseStart_8289283 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289287 : List Nat := [1, 1, 4, 3, 1, 1, 3, 3, 1, 1, 4]
def baseStart_8289287 : Nat := 118140960795 + 8289287 * 2 ^ 59
def prefixEnd_8289287 : Nat := 4983230072969 + 3 ^ 40 * 8289287 * 2
def baseEnd_8289287 : Nat := 4256388514066014860190769

theorem tailTrace_8289287 : CollatzResearch.WordTrace tailWord_8289287 prefixEnd_8289287 4256388514066014860190769 := by
  unfold tailWord_8289287
  simp only [CollatzResearch.WordTrace]
  refine ⟨302335134720336371355274115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201556756480224247570182743 302335134720336371355274115)
  ·
    refine ⟨453502702080504557032911173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302335134720336371355274115 453502702080504557032911173)
    ·
      refine ⟨85031756640094604443670845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 453502702080504557032911173 85031756640094604443670845)
      ·
        refine ⟨31886908740035476666376567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85031756640094604443670845 31886908740035476666376567)
        ·
          refine ⟨47830363110053214999564851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31886908740035476666376567 47830363110053214999564851)
          ·
            refine ⟨71745544665079822499347277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47830363110053214999564851 71745544665079822499347277)
            ·
              refine ⟨26904579249404933437255229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71745544665079822499347277 26904579249404933437255229)
              ·
                refine ⟨10089217218526850038970711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26904579249404933437255229 10089217218526850038970711)
                ·
                  refine ⟨15133825827790275058456067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10089217218526850038970711 15133825827790275058456067)
                  ·
                    refine ⟨22700738741685412587684101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15133825827790275058456067 22700738741685412587684101)
                    ·
                      refine ⟨4256388514066014860190769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22700738741685412587684101 4256388514066014860190769)
                      ·
                        rfl

theorem cell23_8289287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 3, 3, 1, 1, 4].length) (baseStart_8289287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289287 prefixEnd_8289287 := by exact prefixLift 8289287
  have htrace : WordTrace (prefixWord ++ tailWord_8289287) baseStart_8289287 baseEnd_8289287 := by
    simpa [prefixWord, tailWord_8289287, baseEnd_8289287] using wordTrace_append hprefix tailTrace_8289287
  have hstable : (prefixWord ++ tailWord_8289287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289287).length < 2 ^ (prefixWord ++ tailWord_8289287).sum := by decide
  have hdescent : baseEnd_8289287 < baseStart_8289287 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289304 : List Nat := [2, 1, 2, 3, 2, 2, 1, 3, 3, 2, 2]
def baseStart_8289304 : Nat := 118140960795 + 8289304 * 2 ^ 59
def prefixEnd_8289304 : Nat := 4983230072969 + 3 ^ 40 * 8289304 * 2
def baseEnd_8289304 : Nat := 4256397243237141293678191

theorem tailTrace_8289304 : CollatzResearch.WordTrace tailWord_8289304 prefixEnd_8289304 4256397243237141293678191 := by
  unfold tailWord_8289304
  simp only [CollatzResearch.WordTrace]
  refine ⟨151167877380637391629321483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201557169840849855505761977 151167877380637391629321483)
  ·
    refine ⟨226751816070956087443982225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151167877380637391629321483 226751816070956087443982225)
    ·
      refine ⟨170063862053217065582986669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226751816070956087443982225 170063862053217065582986669)
      ·
        refine ⟨63773948269956399593620001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170063862053217065582986669 63773948269956399593620001)
        ·
          refine ⟨47830461202467299695215001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63773948269956399593620001 47830461202467299695215001)
          ·
            refine ⟨35872845901850474771411251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47830461202467299695215001 35872845901850474771411251)
            ·
              refine ⟨53809268852775712157116877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35872845901850474771411251 53809268852775712157116877)
              ·
                refine ⟨20178475819790892058918829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53809268852775712157116877 20178475819790892058918829)
                ·
                  refine ⟨7566928432421584522094561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20178475819790892058918829 7566928432421584522094561)
                  ·
                    refine ⟨5675196324316188391570921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7566928432421584522094561 5675196324316188391570921)
                    ·
                      refine ⟨4256397243237141293678191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5675196324316188391570921 4256397243237141293678191)
                      ·
                        rfl

theorem cell23_8289304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_8289304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289304 prefixEnd_8289304 := by exact prefixLift 8289304
  have htrace : WordTrace (prefixWord ++ tailWord_8289304) baseStart_8289304 baseEnd_8289304 := by
    simpa [prefixWord, tailWord_8289304, baseEnd_8289304] using wordTrace_append hprefix tailTrace_8289304
  have hstable : (prefixWord ++ tailWord_8289304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289304).length < 2 ^ (prefixWord ++ tailWord_8289304).sum := by decide
  have hdescent : baseEnd_8289304 < baseStart_8289304 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289394 : List Nat := [3, 2, 1, 2, 2, 1, 3, 2, 1, 4, 2]
def baseStart_8289394 : Nat := 118140960795 + 8289394 * 2 ^ 59
def prefixEnd_8289394 : Nat := 4983230072969 + 3 ^ 40 * 8289394 * 2
def baseEnd_8289394 : Nat := 4256443456496045941552777

theorem tailTrace_8289394 : CollatzResearch.WordTrace tailWord_8289394 prefixEnd_8289394 4256443456496045941552777 := by
  unfold tailWord_8289394
  simp only [CollatzResearch.WordTrace]
  refine ⟨75584759332737182157354809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201559358220632485752946157 75584759332737182157354809)
  ·
    refine ⟨56688569499552886618016107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75584759332737182157354809 56688569499552886618016107)
    ·
      refine ⟨85032854249329329927024161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56688569499552886618016107 85032854249329329927024161)
      ·
        refine ⟨63774640686996997445268121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85032854249329329927024161 63774640686996997445268121)
        ·
          refine ⟨47830980515247748083951091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63774640686996997445268121 47830980515247748083951091)
          ·
            refine ⟨71746470772871622125926637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47830980515247748083951091 71746470772871622125926637)
            ·
              refine ⟨26904926539826858297222489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71746470772871622125926637 26904926539826858297222489)
              ·
                refine ⟨20178694904870143722916867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26904926539826858297222489 20178694904870143722916867)
                ·
                  refine ⟨30268042357305215584375301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20178694904870143722916867 30268042357305215584375301)
                  ·
                    refine ⟨5675257941994727922070369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30268042357305215584375301 5675257941994727922070369)
                    ·
                      refine ⟨4256443456496045941552777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5675257941994727922070369 4256443456496045941552777)
                      ·
                        rfl

theorem cell23_8289394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 3, 2, 1, 4, 2].length) (baseStart_8289394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289394 prefixEnd_8289394 := by exact prefixLift 8289394
  have htrace : WordTrace (prefixWord ++ tailWord_8289394) baseStart_8289394 baseEnd_8289394 := by
    simpa [prefixWord, tailWord_8289394, baseEnd_8289394] using wordTrace_append hprefix tailTrace_8289394
  have hstable : (prefixWord ++ tailWord_8289394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289394).length < 2 ^ (prefixWord ++ tailWord_8289394).sum := by decide
  have hdescent : baseEnd_8289394 < baseStart_8289394 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289398 : List Nat := [5, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2]
def baseStart_8289398 : Nat := 118140960795 + 8289398 * 2 ^ 59
def prefixEnd_8289398 : Nat := 4983230072969 + 3 ^ 40 * 8289398 * 2
def baseEnd_8289398 : Nat := 4256445510418663925902759

theorem tailTrace_8289398 : CollatzResearch.WordTrace tailWord_8289398 prefixEnd_8289398 4256445510418663925902759 := by
  unfold tailWord_8289398
  simp only [CollatzResearch.WordTrace]
  refine ⟨18896198951433389832035303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201559455481956158208376565 18896198951433389832035303)
  ·
    refine ⟨28344298427150084748052955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 18896198951433389832035303 28344298427150084748052955)
    ·
      refine ⟨42516447640725127122079433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28344298427150084748052955 42516447640725127122079433)
      ·
        refine ⟨31887335730543845341559575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42516447640725127122079433 31887335730543845341559575)
        ·
          refine ⟨47831003595815768012339363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31887335730543845341559575 47831003595815768012339363)
          ·
            refine ⟨71746505393723652018509045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47831003595815768012339363 71746505393723652018509045)
            ·
              refine ⟨6726234880661592376735223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 71746505393723652018509045 6726234880661592376735223)
              ·
                refine ⟨10089352320992388565102835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6726234880661592376735223 10089352320992388565102835)
                ·
                  refine ⟨15134028481488582847654253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10089352320992388565102835 15134028481488582847654253)
                  ·
                    refine ⟨5675260680558218567870345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15134028481488582847654253 5675260680558218567870345)
                    ·
                      refine ⟨4256445510418663925902759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5675260680558218567870345 4256445510418663925902759)
                      ·
                        rfl

theorem cell23_8289398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2].length) (baseStart_8289398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289398 prefixEnd_8289398 := by exact prefixLift 8289398
  have htrace : WordTrace (prefixWord ++ tailWord_8289398) baseStart_8289398 baseEnd_8289398 := by
    simpa [prefixWord, tailWord_8289398, baseEnd_8289398] using wordTrace_append hprefix tailTrace_8289398
  have hstable : (prefixWord ++ tailWord_8289398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289398).length < 2 ^ (prefixWord ++ tailWord_8289398).sum := by decide
  have hdescent : baseEnd_8289398 < baseStart_8289398 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289406 : List Nat := [4, 2, 4, 1, 1, 2, 2, 2, 1, 2, 2]
def baseStart_8289406 : Nat := 118140960795 + 8289406 * 2 ^ 59
def prefixEnd_8289406 : Nat := 4983230072969 + 3 ^ 40 * 8289406 * 2
def baseEnd_8289406 : Nat := 4256449618263899894602723

theorem tailTrace_8289406 : CollatzResearch.WordTrace tailWord_8289406 prefixEnd_8289406 4256449618263899894602723 := by
  unfold tailWord_8289406
  simp only [CollatzResearch.WordTrace]
  refine ⟨37792434375863156834857009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201559650004603503119237381 37792434375863156834857009)
  ·
    refine ⟨28344325781897367626142757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37792434375863156834857009 28344325781897367626142757)
    ·
      refine ⟨5314561084105756429901767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28344325781897367626142757 5314561084105756429901767)
      ·
        refine ⟨7971841626158634644852651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5314561084105756429901767 7971841626158634644852651)
        ·
          refine ⟨11957762439237951967278977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7971841626158634644852651 11957762439237951967278977)
          ·
            refine ⟨8968321829428463975459233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11957762439237951967278977 8968321829428463975459233)
            ·
              refine ⟨6726241372071347981594425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8968321829428463975459233 6726241372071347981594425)
              ·
                refine ⟨5044681029053510986195819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6726241372071347981594425 5044681029053510986195819)
                ·
                  refine ⟨7567021543580266479293729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5044681029053510986195819 7567021543580266479293729)
                  ·
                    refine ⟨5675266157685199859470297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7567021543580266479293729 5675266157685199859470297)
                    ·
                      refine ⟨4256449618263899894602723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5675266157685199859470297 4256449618263899894602723)
                      ·
                        rfl

theorem cell23_8289406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 2, 1, 2, 2].length) (baseStart_8289406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289406 prefixEnd_8289406 := by exact prefixLift 8289406
  have htrace : WordTrace (prefixWord ++ tailWord_8289406) baseStart_8289406 baseEnd_8289406 := by
    simpa [prefixWord, tailWord_8289406, baseEnd_8289406] using wordTrace_append hprefix tailTrace_8289406
  have hstable : (prefixWord ++ tailWord_8289406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289406).length < 2 ^ (prefixWord ++ tailWord_8289406).sum := by decide
  have hdescent : baseEnd_8289406 < baseStart_8289406 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289411 : List Nat := [1, 1, 1, 3, 3, 2, 4, 2, 2, 2, 2]
def baseStart_8289411 : Nat := 118140960795 + 8289411 * 2 ^ 59
def prefixEnd_8289411 : Nat := 4983230072969 + 3 ^ 40 * 8289411 * 2
def baseEnd_8289411 : Nat := 4256452185667172375040199

theorem tailTrace_8289411 : CollatzResearch.WordTrace tailWord_8289411 prefixEnd_8289411 4256452185667172375040199 := by
  unfold tailWord_8289411
  simp only [CollatzResearch.WordTrace]
  refine ⟨302339657371887140532788087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201559771581258093688525391 302339657371887140532788087)
  ·
    refine ⟨453509486057830710799182131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302339657371887140532788087 453509486057830710799182131)
    ·
      refine ⟨680264229086746066198773197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453509486057830710799182131 680264229086746066198773197)
      ·
        refine ⟨255099085907529774824539949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 680264229086746066198773197 255099085907529774824539949)
        ·
          refine ⟨95662157215323665559202481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255099085907529774824539949 95662157215323665559202481)
          ·
            refine ⟨71746617911492749169401861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95662157215323665559202481 71746617911492749169401861)
            ·
              refine ⟨13452490858404890469262849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71746617911492749169401861 13452490858404890469262849)
              ·
                refine ⟨10089368143803667851947137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13452490858404890469262849 10089368143803667851947137)
                ·
                  refine ⟨7567026107852750888960353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10089368143803667851947137 7567026107852750888960353)
                  ·
                    refine ⟨5675269580889563166720265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7567026107852750888960353 5675269580889563166720265)
                    ·
                      refine ⟨4256452185667172375040199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5675269580889563166720265 4256452185667172375040199)
                      ·
                        rfl

theorem cell23_8289411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 2, 2].length) (baseStart_8289411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289411 prefixEnd_8289411 := by exact prefixLift 8289411
  have htrace : WordTrace (prefixWord ++ tailWord_8289411) baseStart_8289411 baseEnd_8289411 := by
    simpa [prefixWord, tailWord_8289411, baseEnd_8289411] using wordTrace_append hprefix tailTrace_8289411
  have hstable : (prefixWord ++ tailWord_8289411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289411).length < 2 ^ (prefixWord ++ tailWord_8289411).sum := by decide
  have hdescent : baseEnd_8289411 < baseStart_8289411 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289487 : List Nat := [1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 3]
def baseStart_8289487 : Nat := 118140960795 + 8289487 * 2 ^ 59
def prefixEnd_8289487 : Nat := 4983230072969 + 3 ^ 40 * 8289487 * 2
def baseEnd_8289487 : Nat := 4256491210196914077689849

theorem tailTrace_8289487 : CollatzResearch.WordTrace tailWord_8289487 prefixEnd_8289487 4256491210196914077689849 := by
  unfold tailWord_8289487
  simp only [CollatzResearch.WordTrace]
  refine ⟨302342429319611805512554715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201561619546407870341703143 302342429319611805512554715)
  ·
    refine ⟨453513643979417708268832073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302342429319611805512554715 453513643979417708268832073)
    ·
      refine ⟨340135232984563281201624055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453513643979417708268832073 340135232984563281201624055)
      ·
        refine ⟨510202849476844921802436083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340135232984563281201624055 510202849476844921802436083)
        ·
          refine ⟨765304274215267382703654125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510202849476844921802436083 765304274215267382703654125)
          ·
            refine ⟨286989102830725268513870297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 765304274215267382703654125 286989102830725268513870297)
            ·
              refine ⟨215241827123043951385402723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286989102830725268513870297 215241827123043951385402723)
              ·
                refine ⟨322862740684565927078104085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215241827123043951385402723 322862740684565927078104085)
                ·
                  refine ⟨15134190969589027831786129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 322862740684565927078104085 15134190969589027831786129)
                  ·
                    refine ⟨11350643227191770873839597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15134190969589027831786129 11350643227191770873839597)
                    ·
                      refine ⟨4256491210196914077689849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11350643227191770873839597 4256491210196914077689849)
                      ·
                        rfl

theorem cell23_8289487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 1, 6, 2, 3].length) (baseStart_8289487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289487 prefixEnd_8289487 := by exact prefixLift 8289487
  have htrace : WordTrace (prefixWord ++ tailWord_8289487) baseStart_8289487 baseEnd_8289487 := by
    simpa [prefixWord, tailWord_8289487, baseEnd_8289487] using wordTrace_append hprefix tailTrace_8289487
  have hstable : (prefixWord ++ tailWord_8289487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289487).length < 2 ^ (prefixWord ++ tailWord_8289487).sum := by decide
  have hdescent : baseEnd_8289487 < baseStart_8289487 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289571 : List Nat := [1, 1, 1, 4, 2, 4, 3, 1, 1, 5]
def baseStart_8289571 : Nat := 118140960795 + 8289571 * 2 ^ 59
def prefixEnd_8289571 : Nat := 4983230072969 + 3 ^ 40 * 8289571 * 2
def baseEnd_8289571 : Nat := 1418844780857297249679821

theorem tailTrace_8289571 : CollatzResearch.WordTrace tailWord_8289571 prefixEnd_8289571 1418844780857297249679821 := by
  unfold tailWord_8289571
  simp only [CollatzResearch.WordTrace]
  refine ⟨302345493051307487858612567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201563662034204991905741711 302345493051307487858612567)
  ·
    refine ⟨453518239576961231787918851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302345493051307487858612567 453518239576961231787918851)
    ·
      refine ⟨680277359365441847681878277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453518239576961231787918851 680277359365441847681878277)
      ·
        refine ⟨127552004881020346440352177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 680277359365441847681878277 127552004881020346440352177)
        ·
          refine ⟨95664003660765259830264133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127552004881020346440352177 95664003660765259830264133)
          ·
            refine ⟨17937000686393486218174525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95664003660765259830264133 17937000686393486218174525)
            ·
              refine ⟨6726375257397557331815447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17937000686393486218174525 6726375257397557331815447)
              ·
                refine ⟨10089562886096335997723171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6726375257397557331815447 10089562886096335997723171)
                ·
                  refine ⟨15134344329144503996584757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10089562886096335997723171 15134344329144503996584757)
                  ·
                    refine ⟨1418844780857297249679821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15134344329144503996584757 1418844780857297249679821)
                    ·
                      rfl

theorem cell23_8289571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 3, 1, 1, 5].length) (baseStart_8289571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289571 prefixEnd_8289571 := by exact prefixLift 8289571
  have htrace : WordTrace (prefixWord ++ tailWord_8289571) baseStart_8289571 baseEnd_8289571 := by
    simpa [prefixWord, tailWord_8289571, baseEnd_8289571] using wordTrace_append hprefix tailTrace_8289571
  have hstable : (prefixWord ++ tailWord_8289571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289571).length < 2 ^ (prefixWord ++ tailWord_8289571).sum := by decide
  have hdescent : baseEnd_8289571 < baseStart_8289571 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289577 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 4, 6, 3]
def baseStart_8289577 : Nat := 118140960795 + 8289577 * 2 ^ 59
def prefixEnd_8289577 : Nat := 4983230072969 + 3 ^ 40 * 8289577 * 2
def baseEnd_8289577 : Nat := 4256537423455818725564435

theorem tailTrace_8289577 : CollatzResearch.WordTrace tailWord_8289577 prefixEnd_8289577 4256537423455818725564435 := by
  unfold tailWord_8289577
  simp only [CollatzResearch.WordTrace]
  refine ⟨302345711889285750883330985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201563807926190500588887323 302345711889285750883330985)
  ·
    refine ⟨226759283916964313162498239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302345711889285750883330985 226759283916964313162498239)
    ·
      refine ⟨340138925875446469743747359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226759283916964313162498239 340138925875446469743747359)
      ·
        refine ⟨510208388813169704615621039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340138925875446469743747359 510208388813169704615621039)
        ·
          refine ⟨765312583219754556923431559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510208388813169704615621039 765312583219754556923431559)
          ·
            refine ⟨1147968874829631835385147339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765312583219754556923431559 1147968874829631835385147339)
            ·
              refine ⟨1721953312244447753077721009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1147968874829631835385147339 1721953312244447753077721009)
              ·
                refine ⟨1291464984183335814808290757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1721953312244447753077721009 1291464984183335814808290757)
                ·
                  refine ⟨242149684534375465276554517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1291464984183335814808290757 242149684534375465276554517)
                  ·
                    refine ⟨11350766462548849934838493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 242149684534375465276554517 11350766462548849934838493)
                    ·
                      refine ⟨4256537423455818725564435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11350766462548849934838493 4256537423455818725564435)
                      ·
                        rfl

theorem cell23_8289577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 6, 3].length) (baseStart_8289577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289577 prefixEnd_8289577 := by exact prefixLift 8289577
  have htrace : WordTrace (prefixWord ++ tailWord_8289577) baseStart_8289577 baseEnd_8289577 := by
    simpa [prefixWord, tailWord_8289577, baseEnd_8289577] using wordTrace_append hprefix tailTrace_8289577
  have hstable : (prefixWord ++ tailWord_8289577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289577).length < 2 ^ (prefixWord ++ tailWord_8289577).sum := by decide
  have hdescent : baseEnd_8289577 < baseStart_8289577 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289578 : List Nat := [3, 1, 4, 2, 1, 1, 2, 2, 2, 3, 2]
def baseStart_8289578 : Nat := 118140960795 + 8289578 * 2 ^ 59
def prefixEnd_8289578 : Nat := 4983230072969 + 3 ^ 40 * 8289578 * 2
def baseEnd_8289578 : Nat := 4256537936936473221651931

theorem tailTrace_8289578 : CollatzResearch.WordTrace tailWord_8289578 prefixEnd_8289578 4256537936936473221651931 := by
  unfold tailWord_8289578
  simp only [CollatzResearch.WordTrace]
  refine ⟨75586437090570532013529347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201563832241521418702744925 75586437090570532013529347)
  ·
    refine ⟨113379655635855798020294021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75586437090570532013529347 113379655635855798020294021)
    ·
      refine ⟨21258685431722962128805129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 113379655635855798020294021 21258685431722962128805129)
      ·
        refine ⟨15944014073792221596603847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21258685431722962128805129 15944014073792221596603847)
        ·
          refine ⟨23916021110688332394905771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15944014073792221596603847 23916021110688332394905771)
          ·
            refine ⟨35874031666032498592358657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23916021110688332394905771 35874031666032498592358657)
            ·
              refine ⟨26905523749524373944268993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35874031666032498592358657 26905523749524373944268993)
              ·
                refine ⟨20179142812143280458201745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26905523749524373944268993 20179142812143280458201745)
                ·
                  refine ⟨15134357109107460343651309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20179142812143280458201745 15134357109107460343651309)
                  ·
                    refine ⟨5675383915915297628869241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15134357109107460343651309 5675383915915297628869241)
                    ·
                      refine ⟨4256537936936473221651931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5675383915915297628869241 4256537936936473221651931)
                      ·
                        rfl

theorem cell23_8289578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 2, 2, 3, 2].length) (baseStart_8289578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289578 prefixEnd_8289578 := by exact prefixLift 8289578
  have htrace : WordTrace (prefixWord ++ tailWord_8289578) baseStart_8289578 baseEnd_8289578 := by
    simpa [prefixWord, tailWord_8289578, baseEnd_8289578] using wordTrace_append hprefix tailTrace_8289578
  have hstable : (prefixWord ++ tailWord_8289578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289578).length < 2 ^ (prefixWord ++ tailWord_8289578).sum := by decide
  have hdescent : baseEnd_8289578 < baseStart_8289578 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289585 : List Nat := [1, 2, 2, 3, 3, 1, 4, 2, 1, 1, 3]
def baseStart_8289585 : Nat := 118140960795 + 8289585 * 2 ^ 59
def prefixEnd_8289585 : Nat := 4983230072969 + 3 ^ 40 * 8289585 * 2
def baseEnd_8289585 : Nat := 4256541531301054694264399

theorem tailTrace_8289585 : CollatzResearch.WordTrace tailWord_8289585 prefixEnd_8289585 4256541531301054694264399 := by
  unfold tailWord_8289585
  simp only [CollatzResearch.WordTrace]
  refine ⟨302346003673256768249622209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201564002448837845499748139 302346003673256768249622209)
  ·
    refine ⟨226759502754942576187216657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302346003673256768249622209 226759502754942576187216657)
    ·
      refine ⟨170069627066206932140412493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226759502754942576187216657 170069627066206932140412493)
      ·
        refine ⟨63776110149827599552654685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170069627066206932140412493 63776110149827599552654685)
        ·
          refine ⟨23916041306185349832245507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63776110149827599552654685 23916041306185349832245507)
          ·
            refine ⟨35874061959278024748368261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23916041306185349832245507 35874061959278024748368261)
            ·
              refine ⟨6726386617364629640319049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35874061959278024748368261 6726386617364629640319049)
              ·
                refine ⟨5044789963023472230239287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6726386617364629640319049 5044789963023472230239287)
                ·
                  refine ⟨7567184944535208345358931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5044789963023472230239287 7567184944535208345358931)
                  ·
                    refine ⟨11350777416802812518038397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7567184944535208345358931 11350777416802812518038397)
                    ·
                      refine ⟨4256541531301054694264399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11350777416802812518038397 4256541531301054694264399)
                      ·
                        rfl

theorem cell23_8289585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 2, 1, 1, 3].length) (baseStart_8289585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289585 prefixEnd_8289585 := by exact prefixLift 8289585
  have htrace : WordTrace (prefixWord ++ tailWord_8289585) baseStart_8289585 baseEnd_8289585 := by
    simpa [prefixWord, tailWord_8289585, baseEnd_8289585] using wordTrace_append hprefix tailTrace_8289585
  have hstable : (prefixWord ++ tailWord_8289585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289585).length < 2 ^ (prefixWord ++ tailWord_8289585).sum := by decide
  have hdescent : baseEnd_8289585 < baseStart_8289585 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289594 : List Nat := [3, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3]
def baseStart_8289594 : Nat := 118140960795 + 8289594 * 2 ^ 59
def prefixEnd_8289594 : Nat := 4983230072969 + 3 ^ 40 * 8289594 * 2
def baseEnd_8289594 : Nat := 4256546152626945159051857

theorem tailTrace_8289594 : CollatzResearch.WordTrace tailWord_8289594 prefixEnd_8289594 4256546152626945159051857 := by
  unfold tailWord_8289594
  simp only [CollatzResearch.WordTrace]
  refine ⟨75586582982556040696674959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201564221286816108524466557 75586582982556040696674959)
  ·
    refine ⟨113379874473834061045012439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75586582982556040696674959 113379874473834061045012439)
    ·
      refine ⟨170069811710751091567518659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113379874473834061045012439 170069811710751091567518659)
      ·
        refine ⟨255104717566126637351277989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170069811710751091567518659 255104717566126637351277989)
        ·
          refine ⟨47832134543648744503364623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255104717566126637351277989 47832134543648744503364623)
          ·
            refine ⟨71748201815473116755046935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47832134543648744503364623 71748201815473116755046935)
            ·
              refine ⟨107622302723209675132570403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71748201815473116755046935 107622302723209675132570403)
              ·
                refine ⟨161433454084814512698855605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107622302723209675132570403 161433454084814512698855605)
                ·
                  refine ⟨15134386320451360565517713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161433454084814512698855605 15134386320451360565517713)
                  ·
                    refine ⟨11350789740338520424138285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15134386320451360565517713 11350789740338520424138285)
                    ·
                      refine ⟨4256546152626945159051857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11350789740338520424138285 4256546152626945159051857)
                      ·
                        rfl

theorem cell23_8289594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 1, 1, 5, 2, 3].length) (baseStart_8289594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289594 prefixEnd_8289594 := by exact prefixLift 8289594
  have htrace : WordTrace (prefixWord ++ tailWord_8289594) baseStart_8289594 baseEnd_8289594 := by
    simpa [prefixWord, tailWord_8289594, baseEnd_8289594] using wordTrace_append hprefix tailTrace_8289594
  have hstable : (prefixWord ++ tailWord_8289594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289594).length < 2 ^ (prefixWord ++ tailWord_8289594).sum := by decide
  have hdescent : baseEnd_8289594 < baseStart_8289594 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289601 : List Nat := [1, 2, 5, 2, 1, 2, 2, 1, 1, 6]
def baseStart_8289601 : Nat := 118140960795 + 8289601 * 2 ^ 59
def prefixEnd_8289601 : Nat := 4983230072969 + 3 ^ 40 * 8289601 * 2
def baseEnd_8289601 : Nat := 1418849915663842210554775

theorem tailTrace_8289601 : CollatzResearch.WordTrace tailWord_8289601 prefixEnd_8289601 1418849915663842210554775 := by
  unfold tailWord_8289601
  simp only [CollatzResearch.WordTrace]
  refine ⟨302346587241198802982204657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201564391494132535321469771 302346587241198802982204657)
  ·
    refine ⟨226759940430899102236653493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302346587241198802982204657 226759940430899102236653493)
    ·
      refine ⟨21258744415396790834686265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 226759940430899102236653493 21258744415396790834686265)
      ·
        refine ⟨15944058311547593126014699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21258744415396790834686265 15944058311547593126014699)
        ·
          refine ⟨23916087467321389689022049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15944058311547593126014699 23916087467321389689022049)
          ·
            refine ⟨17937065600491042266766537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23916087467321389689022049 17937065600491042266766537)
            ·
              refine ⟨13452799200368281700074903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17937065600491042266766537 13452799200368281700074903)
              ·
                refine ⟨20179198800552422550112355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13452799200368281700074903 20179198800552422550112355)
                ·
                  refine ⟨30268798200828633825168533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20179198800552422550112355 30268798200828633825168533)
                  ·
                    refine ⟨1418849915663842210554775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30268798200828633825168533 1418849915663842210554775)
                    ·
                      rfl

theorem cell23_8289601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 6].length) (baseStart_8289601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289601 prefixEnd_8289601 := by exact prefixLift 8289601
  have htrace : WordTrace (prefixWord ++ tailWord_8289601) baseStart_8289601 baseEnd_8289601 := by
    simpa [prefixWord, tailWord_8289601, baseEnd_8289601] using wordTrace_append hprefix tailTrace_8289601
  have hstable : (prefixWord ++ tailWord_8289601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289601).length < 2 ^ (prefixWord ++ tailWord_8289601).sum := by decide
  have hdescent : baseEnd_8289601 < baseStart_8289601 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289614 : List Nat := [4, 1, 1, 1, 1, 1, 7, 7]
def baseStart_8289614 : Nat := 118140960795 + 8289614 * 2 ^ 59
def prefixEnd_8289614 : Nat := 4983230072969 + 3 ^ 40 * 8289614 * 2
def baseEnd_8289614 : Nat := 157650237860742040029695

theorem tailTrace_8289614 : CollatzResearch.WordTrace tailWord_8289614 prefixEnd_8289614 157650237860742040029695 := by
  unfold tailWord_8289614
  simp only [CollatzResearch.WordTrace]
  refine ⟨37793382673768963275303487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201564707593434470801618597 37793382673768963275303487)
  ·
    refine ⟨56690074010653444912955231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37793382673768963275303487 56690074010653444912955231)
    ·
      refine ⟨85035111015980167369432847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56690074010653444912955231 85035111015980167369432847)
      ·
        refine ⟨127552666523970251054149271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85035111015980167369432847 127552666523970251054149271)
        ·
          refine ⟨191328999785955376581223907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127552666523970251054149271 191328999785955376581223907)
          ·
            refine ⟨286993499678933064871835861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191328999785955376581223907 286993499678933064871835861)
            ·
              refine ⟨6726410148724993707933653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 286993499678933064871835861 6726410148724993707933653)
              ·
                refine ⟨157650237860742040029695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6726410148724993707933653 157650237860742040029695)
                ·
                  rfl

theorem cell23_8289614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 7, 7].length) (baseStart_8289614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289614 prefixEnd_8289614 := by exact prefixLift 8289614
  have htrace : WordTrace (prefixWord ++ tailWord_8289614) baseStart_8289614 baseEnd_8289614 := by
    simpa [prefixWord, tailWord_8289614, baseEnd_8289614] using wordTrace_append hprefix tailTrace_8289614
  have hstable : (prefixWord ++ tailWord_8289614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289614).length < 2 ^ (prefixWord ++ tailWord_8289614).sum := by decide
  have hdescent : baseEnd_8289614 < baseStart_8289614 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289622 : List Nat := [5, 2, 3, 1, 1, 1, 1, 3, 1, 5]
def baseStart_8289622 : Nat := 118140960795 + 8289622 * 2 ^ 59
def prefixEnd_8289622 : Nat := 4983230072969 + 3 ^ 40 * 8289622 * 2
def baseEnd_8289622 : Nat := 1418853510028423683167243

theorem tailTrace_8289622 : CollatzResearch.WordTrace tailWord_8289622 prefixEnd_8289622 1418853510028423683167243 := by
  unfold tailWord_8289622
  simp only [CollatzResearch.WordTrace]
  refine ⟨18896709573382670223044945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201564902116081815712479413 18896709573382670223044945)
  ·
    refine ⟨14172532180037002667283709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18896709573382670223044945 14172532180037002667283709)
    ·
      refine ⟨5314699567513876000231391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14172532180037002667283709 5314699567513876000231391)
      ·
        refine ⟨7972049351270814000347087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5314699567513876000231391 7972049351270814000347087)
        ·
          refine ⟨11958074026906221000520631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7972049351270814000347087 11958074026906221000520631)
          ·
            refine ⟨17937111040359331500780947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11958074026906221000520631 17937111040359331500780947)
            ·
              refine ⟨26905666560538997251171421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17937111040359331500780947 26905666560538997251171421)
              ·
                refine ⟨10089624960202123969189283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26905666560538997251171421 10089624960202123969189283)
                ·
                  refine ⟨15134437440303185953783925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10089624960202123969189283 15134437440303185953783925)
                  ·
                    refine ⟨1418853510028423683167243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15134437440303185953783925 1418853510028423683167243)
                    ·
                      rfl

theorem cell23_8289622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_8289622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289622 prefixEnd_8289622 := by exact prefixLift 8289622
  have htrace : WordTrace (prefixWord ++ tailWord_8289622) baseStart_8289622 baseEnd_8289622 := by
    simpa [prefixWord, tailWord_8289622, baseEnd_8289622] using wordTrace_append hprefix tailTrace_8289622
  have hstable : (prefixWord ++ tailWord_8289622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289622).length < 2 ^ (prefixWord ++ tailWord_8289622).sum := by decide
  have hdescent : baseEnd_8289622 < baseStart_8289622 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289624 : List Nat := [2, 1, 2, 2, 1, 1, 3, 4, 1, 3, 3]
def baseStart_8289624 : Nat := 118140960795 + 8289624 * 2 ^ 59
def prefixEnd_8289624 : Nat := 4983230072969 + 3 ^ 40 * 8289624 * 2
def baseEnd_8289624 : Nat := 4256561557046580041676719

theorem tailTrace_8289624 : CollatzResearch.WordTrace tailWord_8289624 prefixEnd_8289624 4256561557046580041676719 := by
  unfold tailWord_8289624
  simp only [CollatzResearch.WordTrace]
  refine ⟨151173713060057738955145963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201564950746743651940194617 151173713060057738955145963)
  ·
    refine ⟨226760569590086608432718945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151173713060057738955145963 226760569590086608432718945)
    ·
      refine ⟨170070427192564956324539209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226760569590086608432718945 170070427192564956324539209)
      ·
        refine ⟨127552820394423717243404407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170070427192564956324539209 127552820394423717243404407)
        ·
          refine ⟨191329230591635575865106611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127552820394423717243404407 191329230591635575865106611)
          ·
            refine ⟨286993845887453363797659917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191329230591635575865106611 286993845887453363797659917)
            ·
              refine ⟨107622692207795011424122469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 286993845887453363797659917 107622692207795011424122469)
              ·
                refine ⟨20179254788961564642022963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107622692207795011424122469 20179254788961564642022963)
                ·
                  refine ⟨30268882183442346963034445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20179254788961564642022963 30268882183442346963034445)
                  ·
                    refine ⟨11350830818790880111137917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30268882183442346963034445 11350830818790880111137917)
                    ·
                      refine ⟨4256561557046580041676719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11350830818790880111137917 4256561557046580041676719)
                      ·
                        rfl

theorem cell23_8289624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_8289624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289624 prefixEnd_8289624 := by exact prefixLift 8289624
  have htrace : WordTrace (prefixWord ++ tailWord_8289624) baseStart_8289624 baseEnd_8289624 := by
    simpa [prefixWord, tailWord_8289624, baseEnd_8289624] using wordTrace_append hprefix tailTrace_8289624
  have hstable : (prefixWord ++ tailWord_8289624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289624).length < 2 ^ (prefixWord ++ tailWord_8289624).sum := by decide
  have hdescent : baseEnd_8289624 < baseStart_8289624 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289641 : List Nat := [1, 2, 1, 1, 1, 3, 2, 6, 2, 1, 3]
def baseStart_8289641 : Nat := 118140960795 + 8289641 * 2 ^ 59
def prefixEnd_8289641 : Nat := 4983230072969 + 3 ^ 40 * 8289641 * 2
def baseEnd_8289641 : Nat := 4256570286217706475164141

theorem tailTrace_8289641 : CollatzResearch.WordTrace tailWord_8289641 prefixEnd_8289641 4256570286217706475164141 := by
  unfold tailWord_8289641
  simp only [CollatzResearch.WordTrace]
  refine ⟨302348046161053889813660777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201565364107369259875773851 302348046161053889813660777)
  ·
    refine ⟨226761034620790417360245583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302348046161053889813660777 226761034620790417360245583)
    ·
      refine ⟨340141551931185626040368375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226761034620790417360245583 340141551931185626040368375)
      ·
        refine ⟨510212327896778439060552563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340141551931185626040368375 510212327896778439060552563)
        ·
          refine ⟨765318491845167658590828845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510212327896778439060552563 765318491845167658590828845)
          ·
            refine ⟨286994434441937871971560817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 765318491845167658590828845 286994434441937871971560817)
            ·
              refine ⟨215245825831453403978670613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286994434441937871971560817 215245825831453403978670613)
              ·
                refine ⟨10089648085849378311500185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 215245825831453403978670613 10089648085849378311500185)
                ·
                  refine ⟨7567236064387033733625139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10089648085849378311500185 7567236064387033733625139)
                  ·
                    refine ⟨11350854096580550600437709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7567236064387033733625139 11350854096580550600437709)
                    ·
                      refine ⟨4256570286217706475164141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11350854096580550600437709 4256570286217706475164141)
                      ·
                        rfl

theorem cell23_8289641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 6, 2, 1, 3].length) (baseStart_8289641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289641 prefixEnd_8289641 := by exact prefixLift 8289641
  have htrace : WordTrace (prefixWord ++ tailWord_8289641) baseStart_8289641 baseEnd_8289641 := by
    simpa [prefixWord, tailWord_8289641, baseEnd_8289641] using wordTrace_append hprefix tailTrace_8289641
  have hstable : (prefixWord ++ tailWord_8289641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289641).length < 2 ^ (prefixWord ++ tailWord_8289641).sum := by decide
  have hdescent : baseEnd_8289641 < baseStart_8289641 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289662 : List Nat := [4, 2, 3, 2, 1, 1, 2, 2, 1, 2, 3]
def baseStart_8289662 : Nat := 118140960795 + 8289662 * 2 ^ 59
def prefixEnd_8289662 : Nat := 4983230072969 + 3 ^ 40 * 8289662 * 2
def baseEnd_8289662 : Nat := 4256581069311450893001545

theorem tailTrace_8289662 : CollatzResearch.WordTrace tailWord_8289662 prefixEnd_8289662 4256581069311450893001545 := by
  unfold tailWord_8289662
  simp only [CollatzResearch.WordTrace]
  refine ⟨37793601511747226300021905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201565874729318540266783493 37793601511747226300021905)
  ·
    refine ⟨28345201133810419725016429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37793601511747226300021905 28345201133810419725016429)
    ·
      refine ⟨10629450425178907396881161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28345201133810419725016429 10629450425178907396881161)
      ·
        refine ⟨7972087818884180547660871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10629450425178907396881161 7972087818884180547660871)
        ·
          refine ⟨11958131728326270821491307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7972087818884180547660871 11958131728326270821491307)
          ·
            refine ⟨17937197592489406232236961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11958131728326270821491307 17937197592489406232236961)
            ·
              refine ⟨13452898194367054674177721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17937197592489406232236961 13452898194367054674177721)
              ·
                refine ⟨10089673645775291005633291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13452898194367054674177721 10089673645775291005633291)
                ·
                  refine ⟨15134510468662936508449937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10089673645775291005633291 15134510468662936508449937)
                  ·
                    refine ⟨11350882851497202381337453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15134510468662936508449937 11350882851497202381337453)
                    ·
                      refine ⟨4256581069311450893001545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11350882851497202381337453 4256581069311450893001545)
                      ·
                        rfl

theorem cell23_8289662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_8289662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289662 prefixEnd_8289662 := by exact prefixLift 8289662
  have htrace : WordTrace (prefixWord ++ tailWord_8289662) baseStart_8289662 baseEnd_8289662 := by
    simpa [prefixWord, tailWord_8289662, baseEnd_8289662] using wordTrace_append hprefix tailTrace_8289662
  have hstable : (prefixWord ++ tailWord_8289662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289662).length < 2 ^ (prefixWord ++ tailWord_8289662).sum := by decide
  have hdescent : baseEnd_8289662 < baseStart_8289662 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289668 : List Nat := [2, 3, 2, 1, 1, 3, 1, 4, 1, 3, 2]
def baseStart_8289668 : Nat := 118140960795 + 8289668 * 2 ^ 59
def prefixEnd_8289668 : Nat := 4983230072969 + 3 ^ 40 * 8289668 * 2
def baseEnd_8289668 : Nat := 4256584150195377869526517

theorem tailTrace_8289668 : CollatzResearch.WordTrace tailWord_8289668 prefixEnd_8289668 4256584150195377869526517 := by
  unfold tailWord_8289668
  simp only [CollatzResearch.WordTrace]
  refine ⟨151174515465978036712446829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201566020621304048949929105 151174515465978036712446829)
  ·
    refine ⟨56690443299741763767167561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151174515465978036712446829 56690443299741763767167561)
    ·
      refine ⟨42517832474806322825375671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56690443299741763767167561 42517832474806322825375671)
      ·
        refine ⟨63776748712209484238063507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42517832474806322825375671 63776748712209484238063507)
        ·
          refine ⟨95665123068314226357095261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63776748712209484238063507 95665123068314226357095261)
          ·
            refine ⟨35874421150617834883910723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95665123068314226357095261 35874421150617834883910723)
            ·
              refine ⟨53811631725926752325866085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35874421150617834883910723 53811631725926752325866085)
              ·
                refine ⟨10089680948611266061099891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53811631725926752325866085 10089680948611266061099891)
                ·
                  refine ⟨15134521422916899091649837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10089680948611266061099891 15134521422916899091649837)
                  ·
                    refine ⟨5675445533593837159368689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15134521422916899091649837 5675445533593837159368689)
                    ·
                      refine ⟨4256584150195377869526517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5675445533593837159368689 4256584150195377869526517)
                      ·
                        rfl

theorem cell23_8289668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 4, 1, 3, 2].length) (baseStart_8289668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289668 prefixEnd_8289668 := by exact prefixLift 8289668
  have htrace : WordTrace (prefixWord ++ tailWord_8289668) baseStart_8289668 baseEnd_8289668 := by
    simpa [prefixWord, tailWord_8289668, baseEnd_8289668] using wordTrace_append hprefix tailTrace_8289668
  have hstable : (prefixWord ++ tailWord_8289668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289668).length < 2 ^ (prefixWord ++ tailWord_8289668).sum := by decide
  have hdescent : baseEnd_8289668 < baseStart_8289668 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289791 : List Nat := [1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 3]
def baseStart_8289791 : Nat := 118140960795 + 8289791 * 2 ^ 59
def prefixEnd_8289791 : Nat := 4983230072969 + 3 ^ 40 * 8289791 * 2
def baseEnd_8289791 : Nat := 4256647308315880888288451

theorem tailTrace_8289791 : CollatzResearch.WordTrace tailWord_8289791 prefixEnd_8289791 4256647308315880888288451 := by
  unfold tailWord_8289791
  simp only [CollatzResearch.WordTrace]
  refine ⟨302353517110510465431621227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201569011407006976954414151 302353517110510465431621227)
  ·
    refine ⟨453530275665765698147431841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302353517110510465431621227 453530275665765698147431841)
    ·
      refine ⟨340147706749324273610573881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453530275665765698147431841 340147706749324273610573881)
      ·
        refine ⟨255110780061993205207930411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340147706749324273610573881 255110780061993205207930411)
        ·
          refine ⟨382666170092989807811895617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255110780061993205207930411 382666170092989807811895617)
          ·
            refine ⟨286999627569742355858921713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382666170092989807811895617 286999627569742355858921713)
            ·
              refine ⟨215249720677306766894191285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 286999627569742355858921713 215249720677306766894191285)
              ·
                refine ⟨20179661313497509396330433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215249720677306766894191285 20179661313497509396330433)
                ·
                  refine ⟨15134745985123132047247825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20179661313497509396330433 15134745985123132047247825)
                  ·
                    refine ⟨11351059488842349035435869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15134745985123132047247825 11351059488842349035435869)
                    ·
                      refine ⟨4256647308315880888288451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11351059488842349035435869 4256647308315880888288451)
                      ·
                        rfl

theorem cell23_8289791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 5, 2, 2, 3].length) (baseStart_8289791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289791 prefixEnd_8289791 := by exact prefixLift 8289791
  have htrace : WordTrace (prefixWord ++ tailWord_8289791) baseStart_8289791 baseEnd_8289791 := by
    simpa [prefixWord, tailWord_8289791, baseEnd_8289791] using wordTrace_append hprefix tailTrace_8289791
  have hstable : (prefixWord ++ tailWord_8289791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289791).length < 2 ^ (prefixWord ++ tailWord_8289791).sum := by decide
  have hdescent : baseEnd_8289791 < baseStart_8289791 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289811 : List Nat := [1, 1, 1, 2, 1, 6, 3, 2, 6]
def baseStart_8289811 : Nat := 118140960795 + 8289811 * 2 ^ 59
def prefixEnd_8289811 : Nat := 4983230072969 + 3 ^ 40 * 8289811 * 2
def baseEnd_8289811 : Nat := 472961953103218978893151

theorem tailTrace_8289811 : CollatzResearch.WordTrace tailWord_8289811 prefixEnd_8289811 472961953103218978893151 := by
  unfold tailWord_8289811
  simp only [CollatzResearch.WordTrace]
  refine ⟨302354246570438008847349287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201569497713625339231566191 302354246570438008847349287)
  ·
    refine ⟨453531369855657013271023931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302354246570438008847349287 453531369855657013271023931)
    ·
      refine ⟨680297054783485519906535897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453531369855657013271023931 680297054783485519906535897)
      ·
        refine ⟨510222791087614139929901923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 680297054783485519906535897 510222791087614139929901923)
        ·
          refine ⟨765334186631421209894852885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510222791087614139929901923 765334186631421209894852885)
          ·
            refine ⟨35875039998347869213821229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 765334186631421209894852885 35875039998347869213821229)
            ·
              refine ⟨13453139999380450955182961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35875039998347869213821229 13453139999380450955182961)
              ·
                refine ⟨10089854999535338216387221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13453139999380450955182961 10089854999535338216387221)
                ·
                  refine ⟨472961953103218978893151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10089854999535338216387221 472961953103218978893151)
                  ·
                    rfl

theorem cell23_8289811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 2, 6].length) (baseStart_8289811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289811 prefixEnd_8289811 := by exact prefixLift 8289811
  have htrace : WordTrace (prefixWord ++ tailWord_8289811) baseStart_8289811 baseEnd_8289811 := by
    simpa [prefixWord, tailWord_8289811, baseEnd_8289811] using wordTrace_append hprefix tailTrace_8289811
  have hstable : (prefixWord ++ tailWord_8289811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289811).length < 2 ^ (prefixWord ++ tailWord_8289811).sum := by decide
  have hdescent : baseEnd_8289811 < baseStart_8289811 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289848 : List Nat := [2, 1, 2, 1, 4, 2, 2, 1, 1, 5, 2]
def baseStart_8289848 : Nat := 118140960795 + 8289848 * 2 ^ 59
def prefixEnd_8289848 : Nat := 4983230072969 + 3 ^ 40 * 8289848 * 2
def baseEnd_8289848 : Nat := 4256676576713187165275689

theorem tailTrace_8289848 : CollatzResearch.WordTrace tailWord_8289848 prefixEnd_8289848 4256676576713187165275689 := by
  unfold tailWord_8289848
  simp only [CollatzResearch.WordTrace]
  refine ⟨151177798035651982083223099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201570397380869309444297465 151177798035651982083223099)
  ·
    refine ⟨226766697053477973124834649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151177798035651982083223099 226766697053477973124834649)
    ·
      refine ⟨170075022790108479843625987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226766697053477973124834649 170075022790108479843625987)
      ·
        refine ⟨255112534185162719765438981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170075022790108479843625987 255112534185162719765438981)
        ·
          refine ⟨47833600159718009956019809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255112534185162719765438981 47833600159718009956019809)
          ·
            refine ⟨35875200119788507467014857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47833600159718009956019809 35875200119788507467014857)
            ·
              refine ⟨26906400089841380600261143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35875200119788507467014857 26906400089841380600261143)
              ·
                refine ⟨40359600134762070900391715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26906400089841380600261143 40359600134762070900391715)
                ·
                  refine ⟨60539400202143106350587573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40359600134762070900391715 60539400202143106350587573)
                  ·
                    refine ⟨5675568768950916220367585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60539400202143106350587573 5675568768950916220367585)
                    ·
                      refine ⟨4256676576713187165275689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5675568768950916220367585 4256676576713187165275689)
                      ·
                        rfl

theorem cell23_8289848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 2, 1, 1, 5, 2].length) (baseStart_8289848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289848 prefixEnd_8289848 := by exact prefixLift 8289848
  have htrace : WordTrace (prefixWord ++ tailWord_8289848) baseStart_8289848 baseEnd_8289848 := by
    simpa [prefixWord, tailWord_8289848, baseEnd_8289848] using wordTrace_append hprefix tailTrace_8289848
  have hstable : (prefixWord ++ tailWord_8289848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289848).length < 2 ^ (prefixWord ++ tailWord_8289848).sum := by decide
  have hdescent : baseEnd_8289848 < baseStart_8289848 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289872 : List Nat := [2, 1, 1, 1, 1, 3, 7, 2, 1, 1, 3]
def baseStart_8289872 : Nat := 118140960795 + 8289872 * 2 ^ 59
def prefixEnd_8289872 : Nat := 4983230072969 + 3 ^ 40 * 8289872 * 2
def baseEnd_8289872 : Nat := 4256688900248895071375579

theorem tailTrace_8289872 : CollatzResearch.WordTrace tailWord_8289872 prefixEnd_8289872 4256688900248895071375579 := by
  unfold tailWord_8289872
  simp only [CollatzResearch.WordTrace]
  refine ⟨151178235711608508132659935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201570980948811344176879913 151178235711608508132659935)
  ·
    refine ⟨226767353567412762198989903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151178235711608508132659935 226767353567412762198989903)
    ·
      refine ⟨340151030351119143298484855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226767353567412762198989903 340151030351119143298484855)
      ·
        refine ⟨510226545526678714947727283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340151030351119143298484855 510226545526678714947727283)
        ·
          refine ⟨765339818290018072421590925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510226545526678714947727283 765339818290018072421590925)
          ·
            refine ⟨287002431858756777158096597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 765339818290018072421590925 287002431858756777158096597)
            ·
              refine ⟨6726619496689611964642889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 287002431858756777158096597 6726619496689611964642889)
              ·
                refine ⟨5044964622517208973482167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6726619496689611964642889 5044964622517208973482167)
                ·
                  refine ⟨7567446933775813460223251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5044964622517208973482167 7567446933775813460223251)
                  ·
                    refine ⟨11351170400663720190334877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7567446933775813460223251 11351170400663720190334877)
                    ·
                      refine ⟨4256688900248895071375579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11351170400663720190334877 4256688900248895071375579)
                      ·
                        rfl

theorem cell23_8289872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 1, 1, 3].length) (baseStart_8289872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289872 prefixEnd_8289872 := by exact prefixLift 8289872
  have htrace : WordTrace (prefixWord ++ tailWord_8289872) baseStart_8289872 baseEnd_8289872 := by
    simpa [prefixWord, tailWord_8289872, baseEnd_8289872] using wordTrace_append hprefix tailTrace_8289872
  have hstable : (prefixWord ++ tailWord_8289872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289872).length < 2 ^ (prefixWord ++ tailWord_8289872).sum := by decide
  have hdescent : baseEnd_8289872 < baseStart_8289872 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289891 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 6]
def baseStart_8289891 : Nat := 118140960795 + 8289891 * 2 ^ 59
def prefixEnd_8289891 : Nat := 4983230072969 + 3 ^ 40 * 8289891 * 2
def baseEnd_8289891 : Nat := 4256698656381330497037991

theorem tailTrace_8289891 : CollatzResearch.WordTrace tailWord_8289891 prefixEnd_8289891 4256698656381330497037991 := by
  unfold tailWord_8289891
  simp only [CollatzResearch.WordTrace]
  refine ⟨302357164410148182510261527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201571442940098788340174351 302357164410148182510261527)
  ·
    refine ⟨453535746615222273765392291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302357164410148182510261527 453535746615222273765392291)
    ·
      refine ⟨680303619922833410648088437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453535746615222273765392291 680303619922833410648088437)
      ·
        refine ⟨63778464367765632248258291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 680303619922833410648088437 63778464367765632248258291)
        ·
          refine ⟨95667696551648448372387437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63778464367765632248258291 95667696551648448372387437)
          ·
            refine ⟨35875386206868168139645289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95667696551648448372387437 35875386206868168139645289)
            ·
              refine ⟨26906539655151126104733967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35875386206868168139645289 26906539655151126104733967)
              ·
                refine ⟨40359809482726689157100951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26906539655151126104733967 40359809482726689157100951)
                ·
                  refine ⟨60539714224090033735651427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40359809482726689157100951 60539714224090033735651427)
                  ·
                    refine ⟨90809571336135050603477141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60539714224090033735651427 90809571336135050603477141)
                    ·
                      refine ⟨4256698656381330497037991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90809571336135050603477141 4256698656381330497037991)
                      ·
                        rfl

theorem cell23_8289891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 6].length) (baseStart_8289891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289891 prefixEnd_8289891 := by exact prefixLift 8289891
  have htrace : WordTrace (prefixWord ++ tailWord_8289891) baseStart_8289891 baseEnd_8289891 := by
    simpa [prefixWord, tailWord_8289891, baseEnd_8289891] using wordTrace_append hprefix tailTrace_8289891
  have hstable : (prefixWord ++ tailWord_8289891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289891).length < 2 ^ (prefixWord ++ tailWord_8289891).sum := by decide
  have hdescent : baseEnd_8289891 < baseStart_8289891 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289895 : List Nat := [1, 1, 5, 1, 1, 1, 2, 4, 3, 2, 2]
def baseStart_8289895 : Nat := 118140960795 + 8289895 * 2 ^ 59
def prefixEnd_8289895 : Nat := 4983230072969 + 3 ^ 40 * 8289895 * 2
def baseEnd_8289895 : Nat := 4256700710303948481387973

theorem tailTrace_8289895 : CollatzResearch.WordTrace tailWord_8289895 prefixEnd_8289895 4256700710303948481387973 := by
  unfold tailWord_8289895
  simp only [CollatzResearch.WordTrace]
  refine ⟨302357310302133691193407139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201571540201422460795604759 302357310302133691193407139)
  ·
    refine ⟨453535965453200536790110709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302357310302133691193407139 453535965453200536790110709)
    ·
      refine ⟨42518996761237550324072879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 453535965453200536790110709 42518996761237550324072879)
      ·
        refine ⟨63778495141856325486109319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42518996761237550324072879 63778495141856325486109319)
        ·
          refine ⟨95667742712784488229163979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63778495141856325486109319 95667742712784488229163979)
          ·
            refine ⟨143501614069176732343745969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95667742712784488229163979 143501614069176732343745969)
            ·
              refine ⟨107626210551882549257809477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143501614069176732343745969 107626210551882549257809477)
              ·
                refine ⟨20179914478477977985839277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107626210551882549257809477 20179914478477977985839277)
                ·
                  refine ⟨7567467929429241744689729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20179914478477977985839277 7567467929429241744689729)
                  ·
                    refine ⟨5675600947071931308517297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7567467929429241744689729 5675600947071931308517297)
                    ·
                      refine ⟨4256700710303948481387973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5675600947071931308517297 4256700710303948481387973)
                      ·
                        rfl

theorem cell23_8289895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 3, 2, 2].length) (baseStart_8289895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289895 prefixEnd_8289895 := by exact prefixLift 8289895
  have htrace : WordTrace (prefixWord ++ tailWord_8289895) baseStart_8289895 baseEnd_8289895 := by
    simpa [prefixWord, tailWord_8289895, baseEnd_8289895] using wordTrace_append hprefix tailTrace_8289895
  have hstable : (prefixWord ++ tailWord_8289895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289895).length < 2 ^ (prefixWord ++ tailWord_8289895).sum := by decide
  have hdescent : baseEnd_8289895 < baseStart_8289895 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289915 : List Nat := [1, 1, 1, 1, 1, 4, 7, 1, 1, 2, 3]
def baseStart_8289915 : Nat := 118140960795 + 8289915 * 2 ^ 59
def prefixEnd_8289915 : Nat := 4983230072969 + 3 ^ 40 * 8289915 * 2
def baseEnd_8289915 : Nat := 4256710979917038403137881

theorem tailTrace_8289915 : CollatzResearch.WordTrace tailWord_8289915 prefixEnd_8289915 4256710979917038403137881 := by
  unfold tailWord_8289915
  simp only [CollatzResearch.WordTrace]
  refine ⟨302358039762061234609135199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201572026508040823072756799 302358039762061234609135199)
  ·
    refine ⟨453537059643091851913702799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302358039762061234609135199 453537059643091851913702799)
    ·
      refine ⟨680305589464637777870554199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453537059643091851913702799 680305589464637777870554199)
      ·
        refine ⟨1020458384196956666805831299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680305589464637777870554199 1020458384196956666805831299)
        ·
          refine ⟨1530687576295435000208746949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1020458384196956666805831299 1530687576295435000208746949)
          ·
            refine ⟨287003920555394062539140053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1530687576295435000208746949 287003920555394062539140053)
            ·
              refine ⟨6726654388017048340761095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 287003920555394062539140053 6726654388017048340761095)
              ·
                refine ⟨10089981582025572511141643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6726654388017048340761095 10089981582025572511141643)
                ·
                  refine ⟨15134972373038358766712465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10089981582025572511141643 15134972373038358766712465)
                  ·
                    refine ⟨11351229279778769075034349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15134972373038358766712465 11351229279778769075034349)
                    ·
                      refine ⟨4256710979917038403137881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11351229279778769075034349 4256710979917038403137881)
                      ·
                        rfl

theorem cell23_8289915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 7, 1, 1, 2, 3].length) (baseStart_8289915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289915 prefixEnd_8289915 := by exact prefixLift 8289915
  have htrace : WordTrace (prefixWord ++ tailWord_8289915) baseStart_8289915 baseEnd_8289915 := by
    simpa [prefixWord, tailWord_8289915, baseEnd_8289915] using wordTrace_append hprefix tailTrace_8289915
  have hstable : (prefixWord ++ tailWord_8289915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289915).length < 2 ^ (prefixWord ++ tailWord_8289915).sum := by decide
  have hdescent : baseEnd_8289915 < baseStart_8289915 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289929 : List Nat := [1, 2, 1, 1, 4, 1, 6, 2, 1, 2, 2]
def baseStart_8289929 : Nat := 118140960795 + 8289929 * 2 ^ 59
def prefixEnd_8289929 : Nat := 4983230072969 + 3 ^ 40 * 8289929 * 2
def baseEnd_8289929 : Nat := 4256718168646201348362817

theorem tailTrace_8289929 : CollatzResearch.WordTrace tailWord_8289929 prefixEnd_8289929 4256718168646201348362817 := by
  unfold tailWord_8289929
  simp only [CollatzResearch.WordTrace]
  refine ⟨302358550384010515000144841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201572366922673676666763227 302358550384010515000144841)
  ·
    refine ⟨226768912788007886250108631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302358550384010515000144841 226768912788007886250108631)
    ·
      refine ⟨340153369182011829375162947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226768912788007886250108631 340153369182011829375162947)
      ·
        refine ⟨510230053773017744062744421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340153369182011829375162947 510230053773017744062744421)
        ·
          refine ⟨95668135082440827011764579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 510230053773017744062744421 95668135082440827011764579)
          ·
            refine ⟨143502202623661240517646869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95668135082440827011764579 143502202623661240517646869)
            ·
              refine ⟨6726665747984120649264697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 143502202623661240517646869 6726665747984120649264697)
              ·
                refine ⟨5044999310988090486948523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6726665747984120649264697 5044999310988090486948523)
                ·
                  refine ⟨7567498966482135730422785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5044999310988090486948523 7567498966482135730422785)
                  ·
                    refine ⟨5675624224861601797817089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7567498966482135730422785 5675624224861601797817089)
                    ·
                      refine ⟨4256718168646201348362817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5675624224861601797817089 4256718168646201348362817)
                      ·
                        rfl

theorem cell23_8289929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 2, 1, 2, 2].length) (baseStart_8289929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289929 prefixEnd_8289929 := by exact prefixLift 8289929
  have htrace : WordTrace (prefixWord ++ tailWord_8289929) baseStart_8289929 baseEnd_8289929 := by
    simpa [prefixWord, tailWord_8289929, baseEnd_8289929] using wordTrace_append hprefix tailTrace_8289929
  have hstable : (prefixWord ++ tailWord_8289929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289929).length < 2 ^ (prefixWord ++ tailWord_8289929).sum := by decide
  have hdescent : baseEnd_8289929 < baseStart_8289929 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289955 : List Nat := [1, 1, 1, 4, 1, 1, 4, 4, 1, 3, 2]
def baseStart_8289955 : Nat := 118140960795 + 8289955 * 2 ^ 59
def prefixEnd_8289955 : Nat := 4983230072969 + 3 ^ 40 * 8289955 * 2
def baseEnd_8289955 : Nat := 4256731519143218246637697

theorem tailTrace_8289955 : CollatzResearch.WordTrace tailWord_8289955 prefixEnd_8289955 4256731519143218246637697 := by
  unfold tailWord_8289955
  simp only [CollatzResearch.WordTrace]
  refine ⟨302359498681916321440591319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201572999121277547627060879 302359498681916321440591319)
  ·
    refine ⟨453539248022874482160886979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302359498681916321440591319 453539248022874482160886979)
    ·
      refine ⟨680308872034311723241330469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453539248022874482160886979 680308872034311723241330469)
      ·
        refine ⟨127557913506433448107749463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 680308872034311723241330469 127557913506433448107749463)
        ·
          refine ⟨191336870259650172161624195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127557913506433448107749463 191336870259650172161624195)
          ·
            refine ⟨287005305389475258242436293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191336870259650172161624195 287005305389475258242436293)
            ·
              refine ⟨53813494760526610920456805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 287005305389475258242436293 53813494760526610920456805)
              ·
                refine ⟨10090030267598739547585651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53813494760526610920456805 10090030267598739547585651)
                ·
                  refine ⟨15135045401398109321378477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10090030267598739547585651 15135045401398109321378477)
                  ·
                    refine ⟨5675642025524290995516929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15135045401398109321378477 5675642025524290995516929)
                    ·
                      refine ⟨4256731519143218246637697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5675642025524290995516929 4256731519143218246637697)
                      ·
                        rfl

theorem cell23_8289955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 4, 1, 3, 2].length) (baseStart_8289955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289955 prefixEnd_8289955 := by exact prefixLift 8289955
  have htrace : WordTrace (prefixWord ++ tailWord_8289955) baseStart_8289955 baseEnd_8289955 := by
    simpa [prefixWord, tailWord_8289955, baseEnd_8289955] using wordTrace_append hprefix tailTrace_8289955
  have hstable : (prefixWord ++ tailWord_8289955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289955).length < 2 ^ (prefixWord ++ tailWord_8289955).sum := by decide
  have hdescent : baseEnd_8289955 < baseStart_8289955 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289966 : List Nat := [4, 1, 4, 1, 2, 2, 2, 1, 1, 2, 3]
def baseStart_8289966 : Nat := 118140960795 + 8289966 * 2 ^ 59
def prefixEnd_8289966 : Nat := 4983230072969 + 3 ^ 40 * 8289966 * 2
def baseEnd_8289966 : Nat := 4256737167430417703600147

theorem tailTrace_8289966 : CollatzResearch.WordTrace tailWord_8289966 prefixEnd_8289966 4256737167430417703600147 := by
  unfold tailWord_8289966
  simp only [CollatzResearch.WordTrace]
  refine ⟨37794987485609558789905219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201573266589917646879494501 37794987485609558789905219)
  ·
    refine ⟨56692481228414338184857829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37794987485609558789905219 56692481228414338184857829)
    ·
      refine ⟨10629840230327688409660843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56692481228414338184857829 10629840230327688409660843)
      ·
        refine ⟨15944760345491532614491265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10629840230327688409660843 15944760345491532614491265)
        ·
          refine ⟨11958570259118649460868449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15944760345491532614491265 11958570259118649460868449)
          ·
            refine ⟨8968927694338987095651337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11958570259118649460868449 8968927694338987095651337)
            ·
              refine ⟨6726695770754240321738503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8968927694338987095651337 6726695770754240321738503)
              ·
                refine ⟨10090043656131360482607755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6726695770754240321738503 10090043656131360482607755)
                ·
                  refine ⟨15135065484197040723911633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10090043656131360482607755 15135065484197040723911633)
                  ·
                    refine ⟨11351299113147780542933725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15135065484197040723911633 11351299113147780542933725)
                    ·
                      refine ⟨4256737167430417703600147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11351299113147780542933725 4256737167430417703600147)
                      ·
                        rfl

theorem cell23_8289966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_8289966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289966 prefixEnd_8289966 := by exact prefixLift 8289966
  have htrace : WordTrace (prefixWord ++ tailWord_8289966) baseStart_8289966 baseEnd_8289966 := by
    simpa [prefixWord, tailWord_8289966, baseEnd_8289966] using wordTrace_append hprefix tailTrace_8289966
  have hstable : (prefixWord ++ tailWord_8289966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289966).length < 2 ^ (prefixWord ++ tailWord_8289966).sum := by decide
  have hdescent : baseEnd_8289966 < baseStart_8289966 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289971 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 5]
def baseStart_8289971 : Nat := 118140960795 + 8289971 * 2 ^ 59
def prefixEnd_8289971 : Nat := 4983230072969 + 3 ^ 40 * 8289971 * 2
def baseEnd_8289971 : Nat := 4256739734833690184037623

theorem tailTrace_8289971 : CollatzResearch.WordTrace tailWord_8289971 prefixEnd_8289971 4256739734833690184037623 := by
  unfold tailWord_8289971
  simp only [CollatzResearch.WordTrace]
  refine ⟨302360082249858356173173767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201573388166572237448782511 302360082249858356173173767)
  ·
    refine ⟨453540123374787534259760651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302360082249858356173173767 453540123374787534259760651)
    ·
      refine ⟨680310185062181301389640977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453540123374787534259760651 680310185062181301389640977)
      ·
        refine ⟨510232638796635976042230733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 680310185062181301389640977 510232638796635976042230733)
        ·
          refine ⟨191337239548738491015836525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 510232638796635976042230733 191337239548738491015836525)
          ·
            refine ⟨71751464830776934130938697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191337239548738491015836525 71751464830776934130938697)
            ·
              refine ⟨53813598623082700598204023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71751464830776934130938697 53813598623082700598204023)
              ·
                refine ⟨80720397934624050897306035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53813598623082700598204023 80720397934624050897306035)
                ·
                  refine ⟨121080596901936076345959053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80720397934624050897306035 121080596901936076345959053)
                  ·
                    refine ⟨45405223838226028629734645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121080596901936076345959053 45405223838226028629734645)
                    ·
                      refine ⟨4256739734833690184037623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45405223838226028629734645 4256739734833690184037623)
                      ·
                        rfl

theorem cell23_8289971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 5].length) (baseStart_8289971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289971 prefixEnd_8289971 := by exact prefixLift 8289971
  have htrace : WordTrace (prefixWord ++ tailWord_8289971) baseStart_8289971 baseEnd_8289971 := by
    simpa [prefixWord, tailWord_8289971, baseEnd_8289971] using wordTrace_append hprefix tailTrace_8289971
  have hstable : (prefixWord ++ tailWord_8289971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289971).length < 2 ^ (prefixWord ++ tailWord_8289971).sum := by decide
  have hdescent : baseEnd_8289971 < baseStart_8289971 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8289998 : List Nat := [4, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4]
def baseStart_8289998 : Nat := 118140960795 + 8289998 * 2 ^ 59
def prefixEnd_8289998 : Nat := 4983230072969 + 3 ^ 40 * 8289998 * 2
def baseEnd_8289998 : Nat := 4256753598811361578399999

theorem tailTrace_8289998 : CollatzResearch.WordTrace tailWord_8289998 prefixEnd_8289998 4256753598811361578399999 := by
  unfold tailWord_8289998
  simp only [CollatzResearch.WordTrace]
  refine ⟨37795133377595067473050831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201574044680507026522937765 37795133377595067473050831)
  ·
    refine ⟨56692700066392601209576247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37795133377595067473050831 56692700066392601209576247)
    ·
      refine ⟨85039050099588901814364371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56692700066392601209576247 85039050099588901814364371)
      ·
        refine ⟨127558575149383352721546557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85039050099588901814364371 127558575149383352721546557)
        ·
          refine ⟨47834465681018757270579959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127558575149383352721546557 47834465681018757270579959)
          ·
            refine ⟨71751698521528135905869939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47834465681018757270579959 71751698521528135905869939)
            ·
              refine ⟨107627547782292203858804909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71751698521528135905869939 107627547782292203858804909)
              ·
                refine ⟨40360330418359576447051841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 107627547782292203858804909 40360330418359576447051841)
                ·
                  refine ⟨30270247813769682335288881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40360330418359576447051841 30270247813769682335288881)
                  ·
                    refine ⟨22702685860327261751466661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30270247813769682335288881 22702685860327261751466661)
                    ·
                      refine ⟨4256753598811361578399999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22702685860327261751466661 4256753598811361578399999)
                      ·
                        rfl

theorem cell23_8289998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_8289998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8289998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8289998 prefixEnd_8289998 := by exact prefixLift 8289998
  have htrace : WordTrace (prefixWord ++ tailWord_8289998) baseStart_8289998 baseEnd_8289998 := by
    simpa [prefixWord, tailWord_8289998, baseEnd_8289998] using wordTrace_append hprefix tailTrace_8289998
  have hstable : (prefixWord ++ tailWord_8289998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8289998).length < 2 ^ (prefixWord ++ tailWord_8289998).sum := by decide
  have hdescent : baseEnd_8289998 < baseStart_8289998 := by decide
  rcases family_descends (prefixWord ++ tailWord_8289998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290002 : List Nat := [3, 2, 2, 2, 2, 1, 3, 1, 1, 4, 2]
def baseStart_8290002 : Nat := 118140960795 + 8290002 * 2 ^ 59
def prefixEnd_8290002 : Nat := 4983230072969 + 3 ^ 40 * 8290002 * 2
def baseEnd_8290002 : Nat := 4256755652733979562749981

theorem tailTrace_8290002 : CollatzResearch.WordTrace tailWord_8290002 prefixEnd_8290002 4256755652733979562749981 := by
  unfold tailWord_8290002
  simp only [CollatzResearch.WordTrace]
  refine ⟨75590303228186512116888065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201574141941830698978368173 75590303228186512116888065)
  ·
    refine ⟨56692727421139884087666049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75590303228186512116888065 56692727421139884087666049)
    ·
      refine ⟨42519545565854913065749537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56692727421139884087666049 42519545565854913065749537)
      ·
        refine ⟨31889659174391184799312153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42519545565854913065749537 31889659174391184799312153)
        ·
          refine ⟨23917244380793388599484115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31889659174391184799312153 23917244380793388599484115)
          ·
            refine ⟨35875866571190082899226173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23917244380793388599484115 35875866571190082899226173)
            ·
              refine ⟨13453449964196281087209815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35875866571190082899226173 13453449964196281087209815)
              ·
                refine ⟨20180174946294421630814723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13453449964196281087209815 20180174946294421630814723)
                ·
                  refine ⟨30270262419441632446222085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20180174946294421630814723 30270262419441632446222085)
                  ·
                    refine ⟨5675674203645306083666641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30270262419441632446222085 5675674203645306083666641)
                    ·
                      refine ⟨4256755652733979562749981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5675674203645306083666641 4256755652733979562749981)
                      ·
                        rfl

theorem cell23_8290002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 3, 1, 1, 4, 2].length) (baseStart_8290002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290002 prefixEnd_8290002 := by exact prefixLift 8290002
  have htrace : WordTrace (prefixWord ++ tailWord_8290002) baseStart_8290002 baseEnd_8290002 := by
    simpa [prefixWord, tailWord_8290002, baseEnd_8290002] using wordTrace_append hprefix tailTrace_8290002
  have hstable : (prefixWord ++ tailWord_8290002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290002).length < 2 ^ (prefixWord ++ tailWord_8290002).sum := by decide
  have hdescent : baseEnd_8290002 < baseStart_8290002 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290036 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 4, 2, 2]
def baseStart_8290036 : Nat := 118140960795 + 8290036 * 2 ^ 59
def prefixEnd_8290036 : Nat := 4983230072969 + 3 ^ 40 * 8290036 * 2
def baseEnd_8290036 : Nat := 4256773111076232429724825

theorem tailTrace_8290036 : CollatzResearch.WordTrace tailWord_8290036 prefixEnd_8290036 4256773111076232429724825 := by
  unfold tailWord_8290036
  simp only [CollatzResearch.WordTrace]
  refine ⟨151181226497311436137144981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201574968663081914849526641 151181226497311436137144981)
  ·
    refine ⟨7086619992061473568928671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 151181226497311436137144981 7086619992061473568928671)
    ·
      refine ⟨10629929988092210353393007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7086619992061473568928671 10629929988092210353393007)
      ·
        refine ⟨15944894982138315530089511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10629929988092210353393007 15944894982138315530089511)
        ·
          refine ⟨23917342473207473295134267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15944894982138315530089511 23917342473207473295134267)
          ·
            refine ⟨35876013709811209942701401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23917342473207473295134267 35876013709811209942701401)
            ·
              refine ⟨26907010282358407457026051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35876013709811209942701401 26907010282358407457026051)
              ·
                refine ⟨40360515423537611185539077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26907010282358407457026051 40360515423537611185539077)
                ·
                  refine ⟨7567596641913302097288577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40360515423537611185539077 7567596641913302097288577)
                  ·
                    refine ⟨5675697481434976572966433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7567596641913302097288577 5675697481434976572966433)
                    ·
                      refine ⟨4256773111076232429724825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5675697481434976572966433 4256773111076232429724825)
                      ·
                        rfl

theorem cell23_8290036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 4, 2, 2].length) (baseStart_8290036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290036 prefixEnd_8290036 := by exact prefixLift 8290036
  have htrace : WordTrace (prefixWord ++ tailWord_8290036) baseStart_8290036 baseEnd_8290036 := by
    simpa [prefixWord, tailWord_8290036, baseEnd_8290036] using wordTrace_append hprefix tailTrace_8290036
  have hstable : (prefixWord ++ tailWord_8290036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290036).length < 2 ^ (prefixWord ++ tailWord_8290036).sum := by decide
  have hdescent : baseEnd_8290036 < baseStart_8290036 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290041 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 2, 2, 8]
def baseStart_8290041 : Nat := 118140960795 + 8290041 * 2 ^ 59
def prefixEnd_8290041 : Nat := 4983230072969 + 3 ^ 40 * 8290041 * 2
def baseEnd_8290041 : Nat := 4256775678479504910162301

theorem tailTrace_8290041 : CollatzResearch.WordTrace tailWord_8290041 prefixEnd_8290041 4256775678479504910162301 := by
  unfold tailWord_8290041
  simp only [CollatzResearch.WordTrace]
  refine ⟨302362635359604758128221977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201575090239736505418814651 302362635359604758128221977)
  ·
    refine ⟨226771976519703568596166483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302362635359604758128221977 226771976519703568596166483)
    ·
      refine ⟨340157964779555352894249725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226771976519703568596166483 340157964779555352894249725)
      ·
        refine ⟨127559236792333257335343647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340157964779555352894249725 127559236792333257335343647)
        ·
          refine ⟨191338855188499886003015471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127559236792333257335343647 191338855188499886003015471)
          ·
            refine ⟨287008282782749829004523207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191338855188499886003015471 287008282782749829004523207)
            ·
              refine ⟨430512424174124743506784811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287008282782749829004523207 430512424174124743506784811)
              ·
                refine ⟨645768636261187115260177217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430512424174124743506784811 645768636261187115260177217)
                ·
                  refine ⟨484326477195890336445132913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 645768636261187115260177217 484326477195890336445132913)
                  ·
                    refine ⟨363244857896917752333849685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 484326477195890336445132913 363244857896917752333849685)
                    ·
                      refine ⟨4256775678479504910162301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 363244857896917752333849685 4256775678479504910162301)
                      ·
                        rfl

theorem cell23_8290041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_8290041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290041 prefixEnd_8290041 := by exact prefixLift 8290041
  have htrace : WordTrace (prefixWord ++ tailWord_8290041) baseStart_8290041 baseEnd_8290041 := by
    simpa [prefixWord, tailWord_8290041, baseEnd_8290041] using wordTrace_append hprefix tailTrace_8290041
  have hstable : (prefixWord ++ tailWord_8290041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290041).length < 2 ^ (prefixWord ++ tailWord_8290041).sum := by decide
  have hdescent : baseEnd_8290041 < baseStart_8290041 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290145 : List Nat := [1, 2, 3, 1, 1, 1, 5, 3, 1, 5]
def baseStart_8290145 : Nat := 118140960795 + 8290145 * 2 ^ 59
def prefixEnd_8290145 : Nat := 4983230072969 + 3 ^ 40 * 8290145 * 2
def baseEnd_8290145 : Nat := 1418943026822524167753941

theorem tailTrace_8290145 : CollatzResearch.WordTrace tailWord_8290145 prefixEnd_8290145 1418943026822524167753941 := by
  unfold tailWord_8290145
  simp only [CollatzResearch.WordTrace]
  refine ⟨302366428551227983890007889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201577619034151989260005259 302366428551227983890007889)
  ·
    refine ⟨226774821413420987917505917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302366428551227983890007889 226774821413420987917505917)
    ·
      refine ⟨85040558030032870469064719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226774821413420987917505917 85040558030032870469064719)
      ·
        refine ⟨127560837045049305703597079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85040558030032870469064719 127560837045049305703597079)
        ·
          refine ⟨191341255567573958555395619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127560837045049305703597079 191341255567573958555395619)
          ·
            refine ⟨287011883351360937833093429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191341255567573958555395619 287011883351360937833093429)
            ·
              refine ⟨26907364064190087921852509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 287011883351360937833093429 26907364064190087921852509)
              ·
                refine ⟨10090261524071282970694691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26907364064190087921852509 10090261524071282970694691)
                ·
                  refine ⟨15135392286106924456042037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10090261524071282970694691 15135392286106924456042037)
                  ·
                    refine ⟨1418943026822524167753941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15135392286106924456042037 1418943026822524167753941)
                    ·
                      rfl

theorem cell23_8290145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 5, 3, 1, 5].length) (baseStart_8290145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290145 prefixEnd_8290145 := by exact prefixLift 8290145
  have htrace : WordTrace (prefixWord ++ tailWord_8290145) baseStart_8290145 baseEnd_8290145 := by
    simpa [prefixWord, tailWord_8290145, baseEnd_8290145] using wordTrace_append hprefix tailTrace_8290145
  have hstable : (prefixWord ++ tailWord_8290145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290145).length < 2 ^ (prefixWord ++ tailWord_8290145).sum := by decide
  have hdescent : baseEnd_8290145 < baseStart_8290145 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290152 : List Nat := [2, 1, 4, 2, 1, 1, 2, 1, 4, 3, 2]
def baseStart_8290152 : Nat := 118140960795 + 8290152 * 2 ^ 59
def prefixEnd_8290152 : Nat := 4983230072969 + 3 ^ 40 * 8290152 * 2
def baseEnd_8290152 : Nat := 4256832674832153975874291

theorem tailTrace_8290152 : CollatzResearch.WordTrace tailWord_8290152 prefixEnd_8290152 4256832674832153975874291 := by
  unfold tailWord_8290152
  simp only [CollatzResearch.WordTrace]
  refine ⟨151183341931101312042756355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201577789241468416057008473 151183341931101312042756355)
  ·
    refine ⟨226775012896651968064134533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151183341931101312042756355 226775012896651968064134533)
    ·
      refine ⟨42520314918122244012025225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226775012896651968064134533 42520314918122244012025225)
      ·
        refine ⟨31890236188591683009018919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42520314918122244012025225 31890236188591683009018919)
        ·
          refine ⟨47835354282887524513528379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31890236188591683009018919 47835354282887524513528379)
          ·
            refine ⟨71753031424331286770292569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47835354282887524513528379 71753031424331286770292569)
            ·
              refine ⟨53814773568248465077719427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71753031424331286770292569 53814773568248465077719427)
              ·
                refine ⟨80722160352372697616579141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53814773568248465077719427 80722160352372697616579141)
                ·
                  refine ⟨15135405066069880803108589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80722160352372697616579141 15135405066069880803108589)
                  ·
                    refine ⟨5675776899776205301165721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15135405066069880803108589 5675776899776205301165721)
                    ·
                      refine ⟨4256832674832153975874291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5675776899776205301165721 4256832674832153975874291)
                      ·
                        rfl

theorem cell23_8290152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 1, 4, 3, 2].length) (baseStart_8290152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290152 prefixEnd_8290152 := by exact prefixLift 8290152
  have htrace : WordTrace (prefixWord ++ tailWord_8290152) baseStart_8290152 baseEnd_8290152 := by
    simpa [prefixWord, tailWord_8290152, baseEnd_8290152] using wordTrace_append hprefix tailTrace_8290152
  have hstable : (prefixWord ++ tailWord_8290152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290152).length < 2 ^ (prefixWord ++ tailWord_8290152).sum := by decide
  have hdescent : baseEnd_8290152 < baseStart_8290152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290202 : List Nat := [3, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5]
def baseStart_8290202 : Nat := 118140960795 + 8290202 * 2 ^ 59
def prefixEnd_8290202 : Nat := 4983230072969 + 3 ^ 40 * 8290202 * 2
def baseEnd_8290202 : Nat := 4256858348864878780249061

theorem tailTrace_8290202 : CollatzResearch.WordTrace tailWord_8290202 prefixEnd_8290202 4256858348864878780249061 := by
  unfold tailWord_8290202
  simp only [CollatzResearch.WordTrace]
  refine ⟨75592126878005370656208215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201579005008014321749888573 75592126878005370656208215)
  ·
    refine ⟨113388190317008055984312323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75592126878005370656208215 113388190317008055984312323)
    ·
      refine ⟨170082285475512083976468485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113388190317008055984312323 170082285475512083976468485)
      ·
        refine ⟨31890428526658515745587841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170082285475512083976468485 31890428526658515745587841)
        ·
          refine ⟨23917821394993886809190881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31890428526658515745587841 23917821394993886809190881)
          ·
            refine ⟨17938366046245415106893161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23917821394993886809190881 17938366046245415106893161)
            ·
              refine ⟨13453774534684061330169871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17938366046245415106893161 13453774534684061330169871)
              ·
                refine ⟨20180661802026091995254807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13453774534684061330169871 20180661802026091995254807)
                ·
                  refine ⟨30270992703039137992882211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20180661802026091995254807 30270992703039137992882211)
                  ·
                    refine ⟨45406489054558706989323317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30270992703039137992882211 45406489054558706989323317)
                    ·
                      refine ⟨4256858348864878780249061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45406489054558706989323317 4256858348864878780249061)
                      ·
                        rfl

theorem cell23_8290202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 2, 1, 1, 1, 5].length) (baseStart_8290202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290202 prefixEnd_8290202 := by exact prefixLift 8290202
  have htrace : WordTrace (prefixWord ++ tailWord_8290202) baseStart_8290202 baseEnd_8290202 := by
    simpa [prefixWord, tailWord_8290202, baseEnd_8290202] using wordTrace_append hprefix tailTrace_8290202
  have hstable : (prefixWord ++ tailWord_8290202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290202).length < 2 ^ (prefixWord ++ tailWord_8290202).sum := by decide
  have hdescent : baseEnd_8290202 < baseStart_8290202 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290205 : List Nat := [1, 4, 2, 1, 2, 4, 9]
def baseStart_8290205 : Nat := 118140960795 + 8290205 * 2 ^ 59
def prefixEnd_8290205 : Nat := 4983230072969 + 3 ^ 40 * 8290205 * 2
def baseEnd_8290205 : Nat := 52553825793911632944587

theorem tailTrace_8290205 : CollatzResearch.WordTrace tailWord_8290205 prefixEnd_8290205 52553825793911632944587 := by
  unfold tailWord_8290205
  simp only [CollatzResearch.WordTrace]
  refine ⟨302368616931010614137192069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201579077954007076091461379 302368616931010614137192069)
  ·
    refine ⟨56694115674564490150723513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302368616931010614137192069 56694115674564490150723513)
    ·
      refine ⟨42520586755923367613042635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56694115674564490150723513 42520586755923367613042635)
      ·
        refine ⟨63780880133885051419563953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42520586755923367613042635 63780880133885051419563953)
        ·
          refine ⟨47835660100413788564672965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63780880133885051419563953 47835660100413788564672965)
          ·
            refine ⟨8969186268827585355876181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 47835660100413788564672965 8969186268827585355876181)
            ·
              refine ⟨52553825793911632944587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8969186268827585355876181 52553825793911632944587)
              ·
                rfl

theorem cell23_8290205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 9].length) (baseStart_8290205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290205 prefixEnd_8290205 := by exact prefixLift 8290205
  have htrace : WordTrace (prefixWord ++ tailWord_8290205) baseStart_8290205 baseEnd_8290205 := by
    simpa [prefixWord, tailWord_8290205, baseEnd_8290205] using wordTrace_append hprefix tailTrace_8290205
  have hstable : (prefixWord ++ tailWord_8290205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290205).length < 2 ^ (prefixWord ++ tailWord_8290205).sum := by decide
  have hdescent : baseEnd_8290205 < baseStart_8290205 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290266 : List Nat := [3, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3]
def baseStart_8290266 : Nat := 118140960795 + 8290266 * 2 ^ 59
def prefixEnd_8290266 : Nat := 4983230072969 + 3 ^ 40 * 8290266 * 2
def baseEnd_8290266 : Nat := 4256891211626766529848767

theorem tailTrace_8290266 : CollatzResearch.WordTrace tailWord_8290266 prefixEnd_8290266 4256891211626766529848767 := by
  unfold tailWord_8290266
  simp only [CollatzResearch.WordTrace]
  refine ⟨75592710445947405388790663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201580561189193081036775101 75592710445947405388790663)
  ·
    refine ⟨113389065668921108083185995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75592710445947405388790663 113389065668921108083185995)
    ·
      refine ⟨170083598503381662124778993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113389065668921108083185995 170083598503381662124778993)
      ·
        refine ⟨127562698877536246593584245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170083598503381662124778993 127562698877536246593584245)
        ·
          refine ⟨11959003019769023118148523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 127562698877536246593584245 11959003019769023118148523)
          ·
            refine ⟨17938504529653534677222785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11959003019769023118148523 17938504529653534677222785)
            ·
              refine ⟨13453878397240151007917089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17938504529653534677222785 13453878397240151007917089)
              ·
                refine ⟨10090408797930113255937817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13453878397240151007917089 10090408797930113255937817)
                ·
                  refine ⟨7567806598447584941953363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10090408797930113255937817 7567806598447584941953363)
                  ·
                    refine ⟨11351709897671377412930045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7567806598447584941953363 11351709897671377412930045)
                    ·
                      refine ⟨4256891211626766529848767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11351709897671377412930045 4256891211626766529848767)
                      ·
                        rfl

theorem cell23_8290266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 2, 2, 1, 3].length) (baseStart_8290266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290266 prefixEnd_8290266 := by exact prefixLift 8290266
  have htrace : WordTrace (prefixWord ++ tailWord_8290266) baseStart_8290266 baseEnd_8290266 := by
    simpa [prefixWord, tailWord_8290266, baseEnd_8290266] using wordTrace_append hprefix tailTrace_8290266
  have hstable : (prefixWord ++ tailWord_8290266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290266).length < 2 ^ (prefixWord ++ tailWord_8290266).sum := by decide
  have hdescent : baseEnd_8290266 < baseStart_8290266 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290317 : List Nat := [1, 7, 1, 2, 1, 2, 1, 2, 2, 1, 3]
def baseStart_8290317 : Nat := 118140960795 + 8290317 * 2 ^ 59
def prefixEnd_8290317 : Nat := 4983230072969 + 3 ^ 40 * 8290317 * 2
def baseEnd_8290317 : Nat := 4256917399140145830311033

theorem tailTrace_8290317 : CollatzResearch.WordTrace tailWord_8290317 prefixEnd_8290317 4256917399140145830311033 := by
  unfold tailWord_8290317
  simp only [CollatzResearch.WordTrace]
  refine ⟨302372701906604857265269205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201581801271069904843512803 302372701906604857265269205)
  ·
    refine ⟨7086860200936051342154747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 302372701906604857265269205 7086860200936051342154747)
    ·
      refine ⟨10630290301404077013232121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7086860200936051342154747 10630290301404077013232121)
      ·
        refine ⟨7972717726053057759924091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10630290301404077013232121 7972717726053057759924091)
        ·
          refine ⟨11959076589079586639886137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7972717726053057759924091 11959076589079586639886137)
          ·
            refine ⟨8969307441809689979914603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11959076589079586639886137 8969307441809689979914603)
            ·
              refine ⟨13453961162714534969871905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8969307441809689979914603 13453961162714534969871905)
              ·
                refine ⟨10090470872035901227403929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13453961162714534969871905 10090470872035901227403929)
                ·
                  refine ⟨7567853154026925920552947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10090470872035901227403929 7567853154026925920552947)
                  ·
                    refine ⟨11351779731040388880829421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7567853154026925920552947 11351779731040388880829421)
                    ·
                      refine ⟨4256917399140145830311033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11351779731040388880829421 4256917399140145830311033)
                      ·
                        rfl

theorem cell23_8290317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_8290317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290317 prefixEnd_8290317 := by exact prefixLift 8290317
  have htrace : WordTrace (prefixWord ++ tailWord_8290317) baseStart_8290317 baseEnd_8290317 := by
    simpa [prefixWord, tailWord_8290317, baseEnd_8290317] using wordTrace_append hprefix tailTrace_8290317
  have hstable : (prefixWord ++ tailWord_8290317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290317).length < 2 ^ (prefixWord ++ tailWord_8290317).sum := by decide
  have hdescent : baseEnd_8290317 < baseStart_8290317 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290335 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 7]
def baseStart_8290335 : Nat := 118140960795 + 8290335 * 2 ^ 59
def prefixEnd_8290335 : Nat := 4983230072969 + 3 ^ 40 * 8290335 * 2
def baseEnd_8290335 : Nat := 4256926641791926759885949

theorem tailTrace_8290335 : CollatzResearch.WordTrace tailWord_8290335 prefixEnd_8290335 4256926641791926759885949 := by
  unfold tailWord_8290335
  simp only [CollatzResearch.WordTrace]
  refine ⟨302373358420539646339424459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201582238947026430892949639 302373358420539646339424459)
  ·
    refine ⟨453560037630809469509136689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302373358420539646339424459 453560037630809469509136689)
    ·
      refine ⟨340170028223107102131852517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453560037630809469509136689 340170028223107102131852517)
      ·
        refine ⟨63781880291832581649722347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340170028223107102131852517 63781880291832581649722347)
        ·
          refine ⟨95672820437748872474583521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63781880291832581649722347 95672820437748872474583521)
          ·
            refine ⟨71754615328311654355937641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95672820437748872474583521 71754615328311654355937641)
            ·
              refine ⟨53815961496233740766953231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71754615328311654355937641 53815961496233740766953231)
              ·
                refine ⟨80723942244350611150429847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53815961496233740766953231 80723942244350611150429847)
                ·
                  refine ⟨121085913366525916725644771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80723942244350611150429847 121085913366525916725644771)
                  ·
                    refine ⟨181628870049788875088467157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 121085913366525916725644771 181628870049788875088467157)
                    ·
                      refine ⟨4256926641791926759885949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 181628870049788875088467157 4256926641791926759885949)
                      ·
                        rfl

theorem cell23_8290335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_8290335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290335 prefixEnd_8290335 := by exact prefixLift 8290335
  have htrace : WordTrace (prefixWord ++ tailWord_8290335) baseStart_8290335 baseEnd_8290335 := by
    simpa [prefixWord, tailWord_8290335, baseEnd_8290335] using wordTrace_append hprefix tailTrace_8290335
  have hstable : (prefixWord ++ tailWord_8290335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290335).length < 2 ^ (prefixWord ++ tailWord_8290335).sum := by decide
  have hdescent : baseEnd_8290335 < baseStart_8290335 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290340 : List Nat := [2, 3, 1, 4, 2, 1, 3, 1, 2, 2, 2]
def baseStart_8290340 : Nat := 118140960795 + 8290340 * 2 ^ 59
def prefixEnd_8290340 : Nat := 4983230072969 + 3 ^ 40 * 8290340 * 2
def baseEnd_8290340 : Nat := 4256929209195199240323427

theorem tailTrace_8290340 : CollatzResearch.WordTrace tailWord_8290340 prefixEnd_8290340 4256929209195199240323427 := by
  unfold tailWord_8290340
  simp only [CollatzResearch.WordTrace]
  refine ⟨151186770392760766096678237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201582360523681021462237649 151186770392760766096678237)
  ·
    refine ⟨56695038897285287286254339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151186770392760766096678237 56695038897285287286254339)
    ·
      refine ⟨85042558345927930929381509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56695038897285287286254339 85042558345927930929381509)
      ·
        refine ⟨15945479689861487049259033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85042558345927930929381509 15945479689861487049259033)
        ·
          refine ⟨11959109767396115286944275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15945479689861487049259033 11959109767396115286944275)
          ·
            refine ⟨17938664651094172930416413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11959109767396115286944275 17938664651094172930416413)
            ·
              refine ⟨6726999244160314848906155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17938664651094172930416413 6726999244160314848906155)
              ·
                refine ⟨10090498866240472273359233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6726999244160314848906155 10090498866240472273359233)
                ·
                  refine ⟨7567874149680354205019425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10090498866240472273359233 7567874149680354205019425)
                  ·
                    refine ⟨5675905612260265653764569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7567874149680354205019425 5675905612260265653764569)
                    ·
                      refine ⟨4256929209195199240323427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5675905612260265653764569 4256929209195199240323427)
                      ·
                        rfl

theorem cell23_8290340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_8290340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290340 prefixEnd_8290340 := by exact prefixLift 8290340
  have htrace : WordTrace (prefixWord ++ tailWord_8290340) baseStart_8290340 baseEnd_8290340 := by
    simpa [prefixWord, tailWord_8290340, baseEnd_8290340] using wordTrace_append hprefix tailTrace_8290340
  have hstable : (prefixWord ++ tailWord_8290340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290340).length < 2 ^ (prefixWord ++ tailWord_8290340).sum := by decide
  have hdescent : baseEnd_8290340 < baseStart_8290340 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290362 : List Nat := [3, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4]
def baseStart_8290362 : Nat := 118140960795 + 8290362 * 2 ^ 59
def prefixEnd_8290362 : Nat := 4983230072969 + 3 ^ 40 * 8290362 * 2
def baseEnd_8290362 : Nat := 4256940505769598154248325

theorem tailTrace_8290362 : CollatzResearch.WordTrace tailWord_8290362 prefixEnd_8290362 4256940505769598154248325 := by
  unfold tailWord_8290362
  simp only [CollatzResearch.WordTrace]
  refine ⟨75593585797860457487664335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201582895460961219967104893 75593585797860457487664335)
  ·
    refine ⟨113390378696790686231496503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75593585797860457487664335 113390378696790686231496503)
    ·
      refine ⟨170085568045186029347244755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113390378696790686231496503 170085568045186029347244755)
      ·
        refine ⟨255128352067779044020867133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170085568045186029347244755 255128352067779044020867133)
        ·
          refine ⟨95673132025417141507825175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255128352067779044020867133 95673132025417141507825175)
          ·
            refine ⟨143509698038125712261737763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95673132025417141507825175 143509698038125712261737763)
            ·
              refine ⟨215264547057188568392606645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143509698038125712261737763 215264547057188568392606645)
              ·
                refine ⟨20181051286611428286806873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215264547057188568392606645 20181051286611428286806873)
                ·
                  refine ⟨15135788464958571215105155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20181051286611428286806873 15135788464958571215105155)
                  ·
                    refine ⟨22703682697437856822657733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15135788464958571215105155 22703682697437856822657733)
                    ·
                      refine ⟨4256940505769598154248325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22703682697437856822657733 4256940505769598154248325)
                      ·
                        rfl

theorem cell23_8290362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 5, 2, 1, 4].length) (baseStart_8290362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290362 prefixEnd_8290362 := by exact prefixLift 8290362
  have htrace : WordTrace (prefixWord ++ tailWord_8290362) baseStart_8290362 baseEnd_8290362 := by
    simpa [prefixWord, tailWord_8290362, baseEnd_8290362] using wordTrace_append hprefix tailTrace_8290362
  have hstable : (prefixWord ++ tailWord_8290362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290362).length < 2 ^ (prefixWord ++ tailWord_8290362).sum := by decide
  have hdescent : baseEnd_8290362 < baseStart_8290362 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290389 : List Nat := [1, 3, 2, 2, 1, 3, 3, 1, 3, 4]
def baseStart_8290389 : Nat := 118140960795 + 8290389 * 2 ^ 59
def prefixEnd_8290389 : Nat := 4983230072969 + 3 ^ 40 * 8290389 * 2
def baseEnd_8290389 : Nat := 1418984789915756516203567

theorem tailTrace_8290389 : CollatzResearch.WordTrace tailWord_8290389 prefixEnd_8290389 1418984789915756516203567 := by
  unfold tailWord_8290389
  simp only [CollatzResearch.WordTrace]
  refine ⟨302375327962344013561890221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201583551974896009041260147 302375327962344013561890221)
  ·
    refine ⟨113390747985879005085708833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302375327962344013561890221 113390747985879005085708833)
    ·
      refine ⟨85043060989409253814281625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113390747985879005085708833 85043060989409253814281625)
      ·
        refine ⟨63782295742056940360711219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85043060989409253814281625 63782295742056940360711219)
        ·
          refine ⟨95673443613085410541066829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63782295742056940360711219 95673443613085410541066829)
          ·
            refine ⟨35877541354907028952900061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95673443613085410541066829 35877541354907028952900061)
            ·
              refine ⟨13454078008090135857337523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35877541354907028952900061 13454078008090135857337523)
              ·
                refine ⟨20181117012135203786006285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13454078008090135857337523 20181117012135203786006285)
                ·
                  refine ⟨7567918879550701419752357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20181117012135203786006285 7567918879550701419752357)
                  ·
                    refine ⟨1418984789915756516203567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7567918879550701419752357 1418984789915756516203567)
                    ·
                      rfl

theorem cell23_8290389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 3, 1, 3, 4].length) (baseStart_8290389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290389 prefixEnd_8290389 := by exact prefixLift 8290389
  have htrace : WordTrace (prefixWord ++ tailWord_8290389) baseStart_8290389 baseEnd_8290389 := by
    simpa [prefixWord, tailWord_8290389, baseEnd_8290389] using wordTrace_append hprefix tailTrace_8290389
  have hstable : (prefixWord ++ tailWord_8290389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290389).length < 2 ^ (prefixWord ++ tailWord_8290389).sum := by decide
  have hdescent : baseEnd_8290389 < baseStart_8290389 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290440 : List Nat := [2, 1, 3, 4, 1, 3, 2, 2, 1, 4]
def baseStart_8290440 : Nat := 118140960795 + 8290440 * 2 ^ 59
def prefixEnd_8290440 : Nat := 4983230072969 + 3 ^ 40 * 8290440 * 2
def baseEnd_8290440 : Nat := 1418993519086882949690989

theorem tailTrace_8290440 : CollatzResearch.WordTrace tailWord_8290440 prefixEnd_8290440 1418993519086882949690989 := by
  unfold tailWord_8290440
  simp only [CollatzResearch.WordTrace]
  refine ⟨151188594042579624635998387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201584792056772832847997849 151188594042579624635998387)
  ·
    refine ⟨226782891063869436953997581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151188594042579624635998387 226782891063869436953997581)
    ·
      refine ⟨85043584148951038857749093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226782891063869436953997581 85043584148951038857749093)
      ·
        refine ⟨15945672027928319785827955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85043584148951038857749093 15945672027928319785827955)
        ·
          refine ⟨23918508041892479678741933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15945672027928319785827955 23918508041892479678741933)
          ·
            refine ⟨8969440515709679879528225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23918508041892479678741933 8969440515709679879528225)
            ·
              refine ⟨6727080386782259909646169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8969440515709679879528225 6727080386782259909646169)
              ·
                refine ⟨5045310290086694932234627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6727080386782259909646169 5045310290086694932234627)
                ·
                  refine ⟨7567965435130042398351941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5045310290086694932234627 7567965435130042398351941)
                  ·
                    refine ⟨1418993519086882949690989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7567965435130042398351941 1418993519086882949690989)
                    ·
                      rfl

theorem cell23_8290440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 3, 2, 2, 1, 4].length) (baseStart_8290440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290440 prefixEnd_8290440 := by exact prefixLift 8290440
  have htrace : WordTrace (prefixWord ++ tailWord_8290440) baseStart_8290440 baseEnd_8290440 := by
    simpa [prefixWord, tailWord_8290440, baseEnd_8290440] using wordTrace_append hprefix tailTrace_8290440
  have hstable : (prefixWord ++ tailWord_8290440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290440).length < 2 ^ (prefixWord ++ tailWord_8290440).sum := by decide
  have hdescent : baseEnd_8290440 < baseStart_8290440 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290469 : List Nat := [1, 3, 1, 2, 1, 3, 2, 4, 1, 1, 4]
def baseStart_8290469 : Nat := 118140960795 + 8290469 * 2 ^ 59
def prefixEnd_8290469 : Nat := 4983230072969 + 3 ^ 40 * 8290469 * 2
def baseEnd_8290469 : Nat := 4256995448199629235610333

theorem tailTrace_8290469 : CollatzResearch.WordTrace tailWord_8290469 prefixEnd_8290469 4256995448199629235610333 := by
  unfold tailWord_8290469
  simp only [CollatzResearch.WordTrace]
  refine ⟨302378245802054187224802461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201585497201369458149868307 302378245802054187224802461)
  ·
    refine ⟨113391842175770320209300923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302378245802054187224802461 113391842175770320209300923)
    ·
      refine ⟨170087763263655480313951385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113391842175770320209300923 170087763263655480313951385)
      ·
        refine ⟨127565822447741610235463539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170087763263655480313951385 127565822447741610235463539)
        ·
          refine ⟨191348733671612415353195309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127565822447741610235463539 191348733671612415353195309)
          ·
            refine ⟨71755775126854655757448241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191348733671612415353195309 71755775126854655757448241)
            ·
              refine ⟨53816831345140991818086181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71755775126854655757448241 53816831345140991818086181)
              ·
                refine ⟨10090655877213935965891159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53816831345140991818086181 10090655877213935965891159)
                ·
                  refine ⟨15135983815820903948836739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10090655877213935965891159 15135983815820903948836739)
                  ·
                    refine ⟨22703975723731355923255109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15135983815820903948836739 22703975723731355923255109)
                    ·
                      refine ⟨4256995448199629235610333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22703975723731355923255109 4256995448199629235610333)
                      ·
                        rfl

theorem cell23_8290469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 2, 4, 1, 1, 4].length) (baseStart_8290469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290469 prefixEnd_8290469 := by exact prefixLift 8290469
  have htrace : WordTrace (prefixWord ++ tailWord_8290469) baseStart_8290469 baseEnd_8290469 := by
    simpa [prefixWord, tailWord_8290469, baseEnd_8290469] using wordTrace_append hprefix tailTrace_8290469
  have hstable : (prefixWord ++ tailWord_8290469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290469).length < 2 ^ (prefixWord ++ tailWord_8290469).sum := by decide
  have hdescent : baseEnd_8290469 < baseStart_8290469 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290496 : List Nat := [2, 1, 1, 2, 5, 1, 3, 2, 2, 4]
def baseStart_8290496 : Nat := 118140960795 + 8290496 * 2 ^ 59
def prefixEnd_8290496 : Nat := 4983230072969 + 3 ^ 40 * 8290496 * 2
def baseEnd_8290496 : Nat := 1419003104059100209990903

theorem tailTrace_8290496 : CollatzResearch.WordTrace tailWord_8290496 prefixEnd_8290496 1419003104059100209990903 := by
  unfold tailWord_8290496
  simp only [CollatzResearch.WordTrace]
  refine ⟨151189615286478185418017671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201586153715304247224023561 151189615286478185418017671)
  ·
    refine ⟨226784422929717278127026507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151189615286478185418017671 226784422929717278127026507)
    ·
      refine ⟨340176634394575917190539761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226784422929717278127026507 340176634394575917190539761)
      ·
        refine ⟨255132475795931937892904821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340176634394575917190539761 255132475795931937892904821)
        ·
          refine ⟨23918669605868619177459827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 255132475795931937892904821 23918669605868619177459827)
          ·
            refine ⟨35878004408802928766189741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23918669605868619177459827 35878004408802928766189741)
            ·
              refine ⟨13454251653301098287321153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35878004408802928766189741 13454251653301098287321153)
              ·
                refine ⟨10090688739975823715490865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13454251653301098287321153 10090688739975823715490865)
                ·
                  refine ⟨7568016554981867786618149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10090688739975823715490865 7568016554981867786618149)
                  ·
                    refine ⟨1419003104059100209990903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7568016554981867786618149 1419003104059100209990903)
                    ·
                      rfl

theorem cell23_8290496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 3, 2, 2, 4].length) (baseStart_8290496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290496 prefixEnd_8290496 := by exact prefixLift 8290496
  have htrace : WordTrace (prefixWord ++ tailWord_8290496) baseStart_8290496 baseEnd_8290496 := by
    simpa [prefixWord, tailWord_8290496, baseEnd_8290496] using wordTrace_append hprefix tailTrace_8290496
  have hstable : (prefixWord ++ tailWord_8290496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290496).length < 2 ^ (prefixWord ++ tailWord_8290496).sum := by decide
  have hdescent : baseEnd_8290496 < baseStart_8290496 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290522 : List Nat := [3, 1, 1, 2, 2, 1, 2, 2, 2, 7]
def baseStart_8290522 : Nat := 118140960795 + 8290522 * 2 ^ 59
def prefixEnd_8290522 : Nat := 4983230072969 + 3 ^ 40 * 8290522 * 2
def baseEnd_8290522 : Nat := 1419007554224772509415863

theorem tailTrace_8290522 : CollatzResearch.WordTrace tailWord_8290522 prefixEnd_8290522 1419007554224772509415863 := by
  unfold tailWord_8290522
  simp only [CollatzResearch.WordTrace]
  refine ⟨75595044717715544319120455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201586785913908118184321213 75595044717715544319120455)
  ·
    refine ⟨113392567076573316478680683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75595044717715544319120455 113392567076573316478680683)
    ·
      refine ⟨170088850614859974718021025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113392567076573316478680683 170088850614859974718021025)
      ·
        refine ⟨127566637961144981038515769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170088850614859974718021025 127566637961144981038515769)
        ·
          refine ⟨95674978470858735778886827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127566637961144981038515769 95674978470858735778886827)
          ·
            refine ⟨143512467706288103668330241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95674978470858735778886827 143512467706288103668330241)
            ·
              refine ⟨107634350779716077751247681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143512467706288103668330241 107634350779716077751247681)
              ·
                refine ⟨80725763084787058313435761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107634350779716077751247681 80725763084787058313435761)
                ·
                  refine ⟨60544322313590293735076821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80725763084787058313435761 60544322313590293735076821)
                  ·
                    refine ⟨1419007554224772509415863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 60544322313590293735076821 1419007554224772509415863)
                    ·
                      rfl

theorem cell23_8290522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 2, 2, 7].length) (baseStart_8290522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290522 prefixEnd_8290522 := by exact prefixLift 8290522
  have htrace : WordTrace (prefixWord ++ tailWord_8290522) baseStart_8290522 baseEnd_8290522 := by
    simpa [prefixWord, tailWord_8290522, baseEnd_8290522] using wordTrace_append hprefix tailTrace_8290522
  have hstable : (prefixWord ++ tailWord_8290522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290522).length < 2 ^ (prefixWord ++ tailWord_8290522).sum := by decide
  have hdescent : baseEnd_8290522 < baseStart_8290522 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290536 : List Nat := [2, 1, 4, 1, 2, 2, 1, 2, 4, 1, 3]
def baseStart_8290536 : Nat := 118140960795 + 8290536 * 2 ^ 59
def prefixEnd_8290536 : Nat := 4983230072969 + 3 ^ 40 * 8290536 * 2
def baseEnd_8290536 : Nat := 4257029851403480473472525

theorem tailTrace_8290536 : CollatzResearch.WordTrace tailWord_8290536 prefixEnd_8290536 4257029851403480473472525 := by
  unfold tailWord_8290536
  simp only [CollatzResearch.WordTrace]
  refine ⟨151190344746405728833745731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201587126328540971778327641 151190344746405728833745731)
  ·
    refine ⟨226785517119608593250618597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151190344746405728833745731 226785517119608593250618597)
    ·
      refine ⟨42522284459926611234490987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226785517119608593250618597 42522284459926611234490987)
      ·
        refine ⟨63783426689889916851736481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42522284459926611234490987 63783426689889916851736481)
        ·
          refine ⟨47837570017417437638802361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63783426689889916851736481 47837570017417437638802361)
          ·
            refine ⟨35878177513063078229101771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47837570017417437638802361 35878177513063078229101771)
            ·
              refine ⟨53817266269594617343652657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35878177513063078229101771 53817266269594617343652657)
              ·
                refine ⟨40362949702195963007739493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53817266269594617343652657 40362949702195963007739493)
                ·
                  refine ⟨7568053069161743063951155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40362949702195963007739493 7568053069161743063951155)
                  ·
                    refine ⟨11352079603742614595926733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7568053069161743063951155 11352079603742614595926733)
                    ·
                      refine ⟨4257029851403480473472525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11352079603742614595926733 4257029851403480473472525)
                      ·
                        rfl

theorem cell23_8290536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 2, 4, 1, 3].length) (baseStart_8290536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290536 prefixEnd_8290536 := by exact prefixLift 8290536
  have htrace : WordTrace (prefixWord ++ tailWord_8290536) baseStart_8290536 baseEnd_8290536 := by
    simpa [prefixWord, tailWord_8290536, baseEnd_8290536] using wordTrace_append hprefix tailTrace_8290536
  have hstable : (prefixWord ++ tailWord_8290536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290536).length < 2 ^ (prefixWord ++ tailWord_8290536).sum := by decide
  have hdescent : baseEnd_8290536 < baseStart_8290536 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290552 : List Nat := [2, 1, 2, 1, 1, 2, 1, 3, 4, 6]
def baseStart_8290552 : Nat := 118140960795 + 8290552 * 2 ^ 59
def prefixEnd_8290552 : Nat := 4983230072969 + 3 ^ 40 * 8290552 * 2
def baseEnd_8290552 : Nat := 1419012689031317470290817

theorem tailTrace_8290552 : CollatzResearch.WordTrace tailWord_8290552 prefixEnd_8290552 1419012689031317470290817 := by
  unfold tailWord_8290552
  simp only [CollatzResearch.WordTrace]
  refine ⟨151190636530376746200036955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201587515373835661600049273 151190636530376746200036955)
  ·
    refine ⟨226785954795565119300055433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151190636530376746200036955 226785954795565119300055433)
    ·
      refine ⟨170089466096673839475041575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226785954795565119300055433 170089466096673839475041575)
      ·
        refine ⟨255134199145010759212562363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170089466096673839475041575 255134199145010759212562363)
        ·
          refine ⟨382701298717516138818843545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255134199145010759212562363 382701298717516138818843545)
          ·
            refine ⟨287025974038137104114132659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382701298717516138818843545 287025974038137104114132659)
            ·
              refine ⟨430538961057205656171198989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287025974038137104114132659 430538961057205656171198989)
              ·
                refine ⟨161452110396452121064199621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 430538961057205656171198989 161452110396452121064199621)
                ·
                  refine ⟨30272270699334772699537429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161452110396452121064199621 30272270699334772699537429)
                  ·
                    refine ⟨1419012689031317470290817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30272270699334772699537429 1419012689031317470290817)
                    ·
                      rfl

theorem cell23_8290552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 3, 4, 6].length) (baseStart_8290552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290552 prefixEnd_8290552 := by exact prefixLift 8290552
  have htrace : WordTrace (prefixWord ++ tailWord_8290552) baseStart_8290552 baseEnd_8290552 := by
    simpa [prefixWord, tailWord_8290552, baseEnd_8290552] using wordTrace_append hprefix tailTrace_8290552
  have hstable : (prefixWord ++ tailWord_8290552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290552).length < 2 ^ (prefixWord ++ tailWord_8290552).sum := by decide
  have hdescent : baseEnd_8290552 < baseStart_8290552 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290636 : List Nat := [2, 2, 1, 3, 2, 1, 1, 2, 2, 5, 2]
def baseStart_8290636 : Nat := 118140960795 + 8290636 * 2 ^ 59
def prefixEnd_8290636 : Nat := 4983230072969 + 3 ^ 40 * 8290636 * 2
def baseEnd_8290636 : Nat := 4257081199468930082222065

theorem tailTrace_8290636 : CollatzResearch.WordTrace tailWord_8290636 prefixEnd_8290636 4257081199468930082222065 := by
  unfold tailWord_8290636
  simp only [CollatzResearch.WordTrace]
  refine ⟨151192168396224587373065881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201589557861632783164087841 151192168396224587373065881)
  ·
    refine ⟨113394126297168440529799411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151192168396224587373065881 113394126297168440529799411)
    ·
      refine ⟨170091189445752660794699117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113394126297168440529799411 170091189445752660794699117)
      ·
        refine ⟨63784196042157247798012169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170091189445752660794699117 63784196042157247798012169)
        ·
          refine ⟨47838147031617935848509127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63784196042157247798012169 47838147031617935848509127)
          ·
            refine ⟨71757220547426903772763691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47838147031617935848509127 71757220547426903772763691)
            ·
              refine ⟨107635830821140355659145537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71757220547426903772763691 107635830821140355659145537)
              ·
                refine ⟨80726873115855266744359153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107635830821140355659145537 80726873115855266744359153)
                ·
                  refine ⟨60545154836891450058269365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 80726873115855266744359153 60545154836891450058269365)
                  ·
                    refine ⟨5676108265958573442962753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60545154836891450058269365 5676108265958573442962753)
                    ·
                      refine ⟨4257081199468930082222065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5676108265958573442962753 4257081199468930082222065)
                      ·
                        rfl

theorem cell23_8290636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 2, 2, 5, 2].length) (baseStart_8290636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290636 prefixEnd_8290636 := by exact prefixLift 8290636
  have htrace : WordTrace (prefixWord ++ tailWord_8290636) baseStart_8290636 baseEnd_8290636 := by
    simpa [prefixWord, tailWord_8290636, baseEnd_8290636] using wordTrace_append hprefix tailTrace_8290636
  have hstable : (prefixWord ++ tailWord_8290636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290636).length < 2 ^ (prefixWord ++ tailWord_8290636).sum := by decide
  have hdescent : baseEnd_8290636 < baseStart_8290636 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290727 : List Nat := [1, 1, 6, 1, 1, 3, 3, 2, 1, 4]
def baseStart_8290727 : Nat := 118140960795 + 8290727 * 2 ^ 59
def prefixEnd_8290727 : Nat := 4983230072969 + 3 ^ 40 * 8290727 * 2
def baseEnd_8290727 : Nat := 1419042642069496408728049

theorem tailTrace_8290727 : CollatzResearch.WordTrace tailWord_8290727 prefixEnd_8290727 1419042642069496408728049 := by
  unfold tailWord_8290727
  simp only [CollatzResearch.WordTrace]
  refine ⟨302387655835119497287694435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201591770556746331525129623 302387655835119497287694435)
  ·
    refine ⟨453581483752679245931541653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302387655835119497287694435 453581483752679245931541653)
    ·
      refine ⟨21261632050906839653041015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 453581483752679245931541653 21261632050906839653041015)
      ·
        refine ⟨31892448076360259479561523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21261632050906839653041015 31892448076360259479561523)
        ·
          refine ⟨47838672114540389219342285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31892448076360259479561523 47838672114540389219342285)
          ·
            refine ⟨17939502042952645957253357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47838672114540389219342285 17939502042952645957253357)
            ·
              refine ⟨6727313266107242233970009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17939502042952645957253357 6727313266107242233970009)
              ·
                refine ⟨5045484949580431675477507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6727313266107242233970009 5045484949580431675477507)
                ·
                  refine ⟨7568227424370647513216261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5045484949580431675477507 7568227424370647513216261)
                  ·
                    refine ⟨1419042642069496408728049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7568227424370647513216261 1419042642069496408728049)
                    ·
                      rfl

theorem cell23_8290727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 3, 2, 1, 4].length) (baseStart_8290727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290727 prefixEnd_8290727 := by exact prefixLift 8290727
  have htrace : WordTrace (prefixWord ++ tailWord_8290727) baseStart_8290727 baseEnd_8290727 := by
    simpa [prefixWord, tailWord_8290727, baseEnd_8290727] using wordTrace_append hprefix tailTrace_8290727
  have hstable : (prefixWord ++ tailWord_8290727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290727).length < 2 ^ (prefixWord ++ tailWord_8290727).sum := by decide
  have hdescent : baseEnd_8290727 < baseStart_8290727 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290739 : List Nat := [1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 4]
def baseStart_8290739 : Nat := 118140960795 + 8290739 * 2 ^ 59
def prefixEnd_8290739 : Nat := 4983230072969 + 3 ^ 40 * 8290739 * 2
def baseEnd_8290739 : Nat := 4257134087976343179234091

theorem tailTrace_8290739 : CollatzResearch.WordTrace tailWord_8290739 prefixEnd_8290739 4257134087976343179234091 := by
  unfold tailWord_8290739
  simp only [CollatzResearch.WordTrace]
  refine ⟨302388093511076023337131271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201592062340717348891420847 302388093511076023337131271)
  ·
    refine ⟨453582140266614035005696907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302388093511076023337131271 453582140266614035005696907)
    ·
      refine ⟨680373210399921052508545361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453582140266614035005696907 680373210399921052508545361)
      ·
        refine ⟨510279907799940789381409021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 680373210399921052508545361 510279907799940789381409021)
        ·
          refine ⟨191354965424977796018028383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 510279907799940789381409021 191354965424977796018028383)
          ·
            refine ⟨287032448137466694027042575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191354965424977796018028383 287032448137466694027042575)
            ·
              refine ⟨430548672206200041040563863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287032448137466694027042575 430548672206200041040563863)
              ·
                refine ⟨645823008309300061560845795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 430548672206200041040563863 645823008309300061560845795)
                ·
                  refine ⟨968734512463950092341268693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 645823008309300061560845795 968734512463950092341268693)
                  ·
                    refine ⟨22704715135873830289248485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 968734512463950092341268693 22704715135873830289248485)
                    ·
                      refine ⟨4257134087976343179234091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22704715135873830289248485 4257134087976343179234091)
                      ·
                        rfl

theorem cell23_8290739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 7, 4].length) (baseStart_8290739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290739 prefixEnd_8290739 := by exact prefixLift 8290739
  have htrace : WordTrace (prefixWord ++ tailWord_8290739) baseStart_8290739 baseEnd_8290739 := by
    simpa [prefixWord, tailWord_8290739, baseEnd_8290739] using wordTrace_append hprefix tailTrace_8290739
  have hstable : (prefixWord ++ tailWord_8290739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290739).length < 2 ^ (prefixWord ++ tailWord_8290739).sum := by decide
  have hdescent : baseEnd_8290739 < baseStart_8290739 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290760 : List Nat := [2, 1, 3, 1, 3, 3, 2, 1, 2, 3, 2]
def baseStart_8290760 : Nat := 118140960795 + 8290760 * 2 ^ 59
def prefixEnd_8290760 : Nat := 4983230072969 + 3 ^ 40 * 8290760 * 2
def baseEnd_8290760 : Nat := 4257144871070087597071495

theorem tailTrace_8290760 : CollatzResearch.WordTrace tailWord_8290760 prefixEnd_8290760 4257144871070087597071495 := by
  unfold tailWord_8290760
  simp only [CollatzResearch.WordTrace]
  refine ⟨151194429721999971961822867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201592572962666629282430489 151194429721999971961822867)
  ·
    refine ⟨226791644582999957942734301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151194429721999971961822867 226791644582999957942734301)
    ·
      refine ⟨85046866718624984228525363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226791644582999957942734301 85046866718624984228525363)
      ·
        refine ⟨127570300077937476342788045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85046866718624984228525363 127570300077937476342788045)
        ·
          refine ⟨47838862529226553628545517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127570300077937476342788045 47838862529226553628545517)
          ·
            refine ⟨17939573448459957610704569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47838862529226553628545517 17939573448459957610704569)
            ·
              refine ⟨13454680086344968208028427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17939573448459957610704569 13454680086344968208028427)
              ·
                refine ⟨20182020129517452312042641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13454680086344968208028427 20182020129517452312042641)
                ·
                  refine ⟨15136515097138089234031981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20182020129517452312042641 15136515097138089234031981)
                  ·
                    refine ⟨5676193161426783462761993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15136515097138089234031981 5676193161426783462761993)
                    ·
                      refine ⟨4257144871070087597071495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5676193161426783462761993 4257144871070087597071495)
                      ·
                        rfl

theorem cell23_8290760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 1, 2, 3, 2].length) (baseStart_8290760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290760 prefixEnd_8290760 := by exact prefixLift 8290760
  have htrace : WordTrace (prefixWord ++ tailWord_8290760) baseStart_8290760 baseEnd_8290760 := by
    simpa [prefixWord, tailWord_8290760, baseEnd_8290760] using wordTrace_append hprefix tailTrace_8290760
  have hstable : (prefixWord ++ tailWord_8290760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290760).length < 2 ^ (prefixWord ++ tailWord_8290760).sum := by decide
  have hdescent : baseEnd_8290760 < baseStart_8290760 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290783 : List Nat := [1, 1, 2, 3, 3, 2, 1, 4, 2, 4]
def baseStart_8290783 : Nat := 118140960795 + 8290783 * 2 ^ 59
def prefixEnd_8290783 : Nat := 4983230072969 + 3 ^ 40 * 8290783 * 2
def baseEnd_8290783 : Nat := 1419052227041713669027963

theorem tailTrace_8290783 : CollatzResearch.WordTrace tailWord_8290783 prefixEnd_8290783 1419052227041713669027963 := by
  unfold tailWord_8290783
  simp only [CollatzResearch.WordTrace]
  refine ⟨302389698322916618851733003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201593132215277745901155335 302389698322916618851733003)
  ·
    refine ⟨453584547484374928277599505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302389698322916618851733003 453584547484374928277599505)
    ·
      refine ⟨340188410613281196208199629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453584547484374928277599505 340188410613281196208199629)
      ·
        refine ⟨127570653979980448578074861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340188410613281196208199629 127570653979980448578074861)
        ·
          refine ⟨47838995242492668216778073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 127570653979980448578074861 47838995242492668216778073)
          ·
            refine ⟨35879246431869501162583555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47838995242492668216778073 35879246431869501162583555)
            ·
              refine ⟨53818869647804251743875333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35879246431869501162583555 53818869647804251743875333)
              ·
                refine ⟨10091038058963297201976625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53818869647804251743875333 10091038058963297201976625)
                ·
                  refine ⟨7568278544222472901482469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10091038058963297201976625 7568278544222472901482469)
                  ·
                    refine ⟨1419052227041713669027963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7568278544222472901482469 1419052227041713669027963)
                    ·
                      rfl

theorem cell23_8290783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 4, 2, 4].length) (baseStart_8290783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290783 prefixEnd_8290783 := by exact prefixLift 8290783
  have htrace : WordTrace (prefixWord ++ tailWord_8290783) baseStart_8290783 baseEnd_8290783 := by
    simpa [prefixWord, tailWord_8290783, baseEnd_8290783] using wordTrace_append hprefix tailTrace_8290783
  have hstable : (prefixWord ++ tailWord_8290783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290783).length < 2 ^ (prefixWord ++ tailWord_8290783).sum := by decide
  have hdescent : baseEnd_8290783 < baseStart_8290783 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290827 : List Nat := [1, 1, 1, 1, 7, 3, 2, 1, 1, 2, 3]
def baseStart_8290827 : Nat := 118140960795 + 8290827 * 2 ^ 59
def prefixEnd_8290827 : Nat := 4983230072969 + 3 ^ 40 * 8290827 * 2
def baseEnd_8290827 : Nat := 4257179274273938834933687

theorem tailTrace_8290827 : CollatzResearch.WordTrace tailWord_8290827 prefixEnd_8290827 4257179274273938834933687 := by
  unfold tailWord_8290827
  simp only [CollatzResearch.WordTrace]
  refine ⟨302391303134757214366334735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201594202089838142910889823 302391303134757214366334735)
  ·
    refine ⟨453586954702135821549502103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302391303134757214366334735 453586954702135821549502103)
    ·
      refine ⟨680380432053203732324253155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453586954702135821549502103 680380432053203732324253155)
      ·
        refine ⟨1020570648079805598486379733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680380432053203732324253155 1020570648079805598486379733)
        ·
          refine ⟨23919624564370443714524525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 1020570648079805598486379733 23919624564370443714524525)
          ·
            refine ⟨8969859211638916392946697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23919624564370443714524525 8969859211638916392946697)
            ·
              refine ⟨6727394408729187294710023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8969859211638916392946697 6727394408729187294710023)
              ·
                refine ⟨10091091613093780942065035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6727394408729187294710023 10091091613093780942065035)
                ·
                  refine ⟨15136637419640671413097553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10091091613093780942065035 15136637419640671413097553)
                  ·
                    refine ⟨11352478064730503559823165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15136637419640671413097553 11352478064730503559823165)
                    ·
                      refine ⟨4257179274273938834933687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11352478064730503559823165 4257179274273938834933687)
                      ·
                        rfl

theorem cell23_8290827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 2, 1, 1, 2, 3].length) (baseStart_8290827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290827 prefixEnd_8290827 := by exact prefixLift 8290827
  have htrace : WordTrace (prefixWord ++ tailWord_8290827) baseStart_8290827 baseEnd_8290827 := by
    simpa [prefixWord, tailWord_8290827, baseEnd_8290827] using wordTrace_append hprefix tailTrace_8290827
  have hstable : (prefixWord ++ tailWord_8290827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290827).length < 2 ^ (prefixWord ++ tailWord_8290827).sum := by decide
  have hdescent : baseEnd_8290827 < baseStart_8290827 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290833 : List Nat := [1, 2, 2, 1, 1, 2, 2, 2, 5, 3, 2]
def baseStart_8290833 : Nat := 118140960795 + 8290833 * 2 ^ 59
def prefixEnd_8290833 : Nat := 4983230072969 + 3 ^ 40 * 8290833 * 2
def baseEnd_8290833 : Nat := 4257182355157865811458659

theorem tailTrace_8290833 : CollatzResearch.WordTrace tailWord_8290833 prefixEnd_8290833 4257182355157865811458659 := by
  unfold tailWord_8290833
  simp only [CollatzResearch.WordTrace]
  refine ⟨302391521972735477391053153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201594347981823651594035435 302391521972735477391053153)
  ·
    refine ⟨226793641479551608043289865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302391521972735477391053153 226793641479551608043289865)
    ·
      refine ⟨170095231109663706032467399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226793641479551608043289865 170095231109663706032467399)
      ·
        refine ⟨255142846664495559048701099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170095231109663706032467399 255142846664495559048701099)
        ·
          refine ⟨382714269996743338573051649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255142846664495559048701099 382714269996743338573051649)
          ·
            refine ⟨287035702497557503929788737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382714269996743338573051649 287035702497557503929788737)
            ·
              refine ⟨215276776873168127947341553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287035702497557503929788737 215276776873168127947341553)
              ·
                refine ⟨161457582654876095960506165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215276776873168127947341553 161457582654876095960506165)
                ·
                  refine ⟨15136648373894633996297453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161457582654876095960506165 15136648373894633996297453)
                  ·
                    refine ⟨5676243140210487748611545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15136648373894633996297453 5676243140210487748611545)
                    ·
                      refine ⟨4257182355157865811458659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5676243140210487748611545 4257182355157865811458659)
                      ·
                        rfl

theorem cell23_8290833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 3, 2].length) (baseStart_8290833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290833 prefixEnd_8290833 := by exact prefixLift 8290833
  have htrace : WordTrace (prefixWord ++ tailWord_8290833) baseStart_8290833 baseEnd_8290833 := by
    simpa [prefixWord, tailWord_8290833, baseEnd_8290833] using wordTrace_append hprefix tailTrace_8290833
  have hstable : (prefixWord ++ tailWord_8290833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290833).length < 2 ^ (prefixWord ++ tailWord_8290833).sum := by decide
  have hdescent : baseEnd_8290833 < baseStart_8290833 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290840 : List Nat := [2, 1, 2, 3, 3, 2, 1, 1, 4, 1, 3]
def baseStart_8290840 : Nat := 118140960795 + 8290840 * 2 ^ 59
def prefixEnd_8290840 : Nat := 4983230072969 + 3 ^ 40 * 8290840 * 2
def baseEnd_8290840 : Nat := 4257185949522447284071127

theorem tailTrace_8290840 : CollatzResearch.WordTrace tailWord_8290840 prefixEnd_8290840 4257185949522447284071127 := by
  unfold tailWord_8290840
  simp only [CollatzResearch.WordTrace]
  refine ⟨151195888641855058793278987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201594518189140078391038649 151195888641855058793278987)
  ·
    refine ⟨226793832962782588189918481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151195888641855058793278987 226793832962782588189918481)
    ·
      refine ⟨170095374722086941142438861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226793832962782588189918481 170095374722086941142438861)
      ·
        refine ⟨63785765520782602928414573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170095374722086941142438861 63785765520782602928414573)
        ·
          refine ⟨23919662070293476098155465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63785765520782602928414573 23919662070293476098155465)
          ·
            refine ⟨17939746552720107073616599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23919662070293476098155465 17939746552720107073616599)
            ·
              refine ⟨26909619829080160610424899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17939746552720107073616599 26909619829080160610424899)
              ·
                refine ⟨40364429743620240915637349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26909619829080160610424899 40364429743620240915637349)
                ·
                  refine ⟨7568330576928795171682003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40364429743620240915637349 7568330576928795171682003)
                  ·
                    refine ⟨11352495865393192757523005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7568330576928795171682003 11352495865393192757523005)
                    ·
                      refine ⟨4257185949522447284071127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11352495865393192757523005 4257185949522447284071127)
                      ·
                        rfl

theorem cell23_8290840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_8290840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290840 prefixEnd_8290840 := by exact prefixLift 8290840
  have htrace : WordTrace (prefixWord ++ tailWord_8290840) baseStart_8290840 baseEnd_8290840 := by
    simpa [prefixWord, tailWord_8290840, baseEnd_8290840] using wordTrace_append hprefix tailTrace_8290840
  have hstable : (prefixWord ++ tailWord_8290840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290840).length < 2 ^ (prefixWord ++ tailWord_8290840).sum := by decide
  have hdescent : baseEnd_8290840 < baseStart_8290840 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290861 : List Nat := [1, 5, 4, 1, 1, 1, 2, 2, 1, 2, 3]
def baseStart_8290861 : Nat := 118140960795 + 8290861 * 2 ^ 59
def prefixEnd_8290861 : Nat := 4983230072969 + 3 ^ 40 * 8290861 * 2
def baseEnd_8290861 : Nat := 4257196732616191701908531

theorem tailTrace_8290861 : CollatzResearch.WordTrace tailWord_8290861 prefixEnd_8290861 4257196732616191701908531 := by
  unfold tailWord_8290861
  simp only [CollatzResearch.WordTrace]
  refine ⟨302392543216634038173072437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201595028811089358782048291 302392543216634038173072437)
  ·
    refine ⟨28349300926559441078725541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302392543216634038173072437 28349300926559441078725541)
    ·
      refine ⟨5315493923729895202261039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28349300926559441078725541 5315493923729895202261039)
      ·
        refine ⟨7973240885594842803391559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5315493923729895202261039 7973240885594842803391559)
        ·
          refine ⟨11959861328392264205087339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7973240885594842803391559 11959861328392264205087339)
          ·
            refine ⟨17939791992588396307631009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11959861328392264205087339 17939791992588396307631009)
            ·
              refine ⟨13454843994441297230723257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17939791992588396307631009 13454843994441297230723257)
              ·
                refine ⟨10091132995830972923042443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13454843994441297230723257 10091132995830972923042443)
                ·
                  refine ⟨15136699493746459384563665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10091132995830972923042443 15136699493746459384563665)
                  ·
                    refine ⟨11352524620309844538422749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15136699493746459384563665 11352524620309844538422749)
                    ·
                      refine ⟨4257196732616191701908531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11352524620309844538422749 4257196732616191701908531)
                      ·
                        rfl

theorem cell23_8290861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_8290861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290861 prefixEnd_8290861 := by exact prefixLift 8290861
  have htrace : WordTrace (prefixWord ++ tailWord_8290861) baseStart_8290861 baseEnd_8290861 := by
    simpa [prefixWord, tailWord_8290861, baseEnd_8290861] using wordTrace_append hprefix tailTrace_8290861
  have hstable : (prefixWord ++ tailWord_8290861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290861).length < 2 ^ (prefixWord ++ tailWord_8290861).sum := by decide
  have hdescent : baseEnd_8290861 < baseStart_8290861 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290880 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 4, 2, 2]
def baseStart_8290880 : Nat := 118140960795 + 8290880 * 2 ^ 59
def prefixEnd_8290880 : Nat := 4983230072969 + 3 ^ 40 * 8290880 * 2
def baseEnd_8290880 : Nat := 4257206488748627127570943

theorem tailTrace_8290880 : CollatzResearch.WordTrace tailWord_8290880 prefixEnd_8290880 4257206488748627127570943 := by
  unfold tailWord_8290880
  simp only [CollatzResearch.WordTrace]
  refine ⟨151196618101782602209007047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201595490802376802945342729 151196618101782602209007047)
  ·
    refine ⟨226794927152673903313510571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151196618101782602209007047 226794927152673903313510571)
    ·
      refine ⟨340192390729010854970265857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226794927152673903313510571 340192390729010854970265857)
      ·
        refine ⟨255144293046758141227699393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340192390729010854970265857 255144293046758141227699393)
        ·
          refine ⟨191358219785068605920774545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255144293046758141227699393 191358219785068605920774545)
          ·
            refine ⟨143518664838801454440580909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191358219785068605920774545 143518664838801454440580909)
            ·
              refine ⟨53819499314550545415217841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143518664838801454440580909 53819499314550545415217841)
              ·
                refine ⟨40364624485912909061413381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53819499314550545415217841 40364624485912909061413381)
                ·
                  refine ⟨7568367091108670449015009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40364624485912909061413381 7568367091108670449015009)
                  ·
                    refine ⟨5676275318331502836761257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7568367091108670449015009 5676275318331502836761257)
                    ·
                      refine ⟨4257206488748627127570943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5676275318331502836761257 4257206488748627127570943)
                      ·
                        rfl

theorem cell23_8290880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 4, 2, 2].length) (baseStart_8290880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290880 prefixEnd_8290880 := by exact prefixLift 8290880
  have htrace : WordTrace (prefixWord ++ tailWord_8290880) baseStart_8290880 baseEnd_8290880 := by
    simpa [prefixWord, tailWord_8290880, baseEnd_8290880] using wordTrace_append hprefix tailTrace_8290880
  have hstable : (prefixWord ++ tailWord_8290880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290880).length < 2 ^ (prefixWord ++ tailWord_8290880).sum := by decide
  have hdescent : baseEnd_8290880 < baseStart_8290880 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290923 : List Nat := [1, 1, 1, 1, 2, 2, 1, 3, 4, 5, 2]
def baseStart_8290923 : Nat := 118140960795 + 8290923 * 2 ^ 59
def prefixEnd_8290923 : Nat := 4983230072969 + 3 ^ 40 * 8290923 * 2
def baseEnd_8290923 : Nat := 4257228568416770459333245

theorem tailTrace_8290923 : CollatzResearch.WordTrace tailWord_8290923 prefixEnd_8290923 4257228568416770459333245 := by
  unfold tailWord_8290923
  simp only [CollatzResearch.WordTrace]
  refine ⟨302394804542409422761829423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201596536361606281841219615 302394804542409422761829423)
  ·
    refine ⟨453592206813614134142744135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302394804542409422761829423 453592206813614134142744135)
    ·
      refine ⟨680388310220421201214116203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453592206813614134142744135 680388310220421201214116203)
      ·
        refine ⟨1020582465330631801821174305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680388310220421201214116203 1020582465330631801821174305)
        ·
          refine ⟨765436848997973851365880729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1020582465330631801821174305 765436848997973851365880729)
          ·
            refine ⟨574077636748480388524410547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765436848997973851365880729 574077636748480388524410547)
            ·
              refine ⟨861116455122720582786615821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574077636748480388524410547 861116455122720582786615821)
              ·
                refine ⟨322918670671020218544980933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 861116455122720582786615821 322918670671020218544980933)
                ·
                  refine ⟨60547250750816290977183925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 322918670671020218544980933 60547250750816290977183925)
                  ·
                    refine ⟨5676304757889027279110993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 60547250750816290977183925 5676304757889027279110993)
                    ·
                      refine ⟨4257228568416770459333245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5676304757889027279110993 4257228568416770459333245)
                      ·
                        rfl

theorem cell23_8290923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 3, 4, 5, 2].length) (baseStart_8290923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290923 prefixEnd_8290923 := by exact prefixLift 8290923
  have htrace : WordTrace (prefixWord ++ tailWord_8290923) baseStart_8290923 baseEnd_8290923 := by
    simpa [prefixWord, tailWord_8290923, baseEnd_8290923] using wordTrace_append hprefix tailTrace_8290923
  have hstable : (prefixWord ++ tailWord_8290923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290923).length < 2 ^ (prefixWord ++ tailWord_8290923).sum := by decide
  have hdescent : baseEnd_8290923 < baseStart_8290923 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290954 : List Nat := [3, 1, 2, 3, 3, 2, 2, 2, 5]
def baseStart_8290954 : Nat := 118140960795 + 8290954 * 2 ^ 59
def prefixEnd_8290954 : Nat := 4983230072969 + 3 ^ 40 * 8290954 * 2
def baseEnd_8290954 : Nat := 473027165146339982005067

theorem tailTrace_8290954 : CollatzResearch.WordTrace tailWord_8290954 prefixEnd_8290954 473027165146339982005067 := by
  unfold tailWord_8290954
  simp only [CollatzResearch.WordTrace]
  refine ⟨75598983801324278764051979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201597290136864743370805277 75598983801324278764051979)
  ·
    refine ⟨113398475701986418146077969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75598983801324278764051979 113398475701986418146077969)
    ·
      refine ⟨85048856776489813609558477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113398475701986418146077969 85048856776489813609558477)
      ·
        refine ⟨31893321291183680103584429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85048856776489813609558477 31893321291183680103584429)
        ·
          refine ⟨11959995484193880038844161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31893321291183680103584429 11959995484193880038844161)
          ·
            refine ⟨8969996613145410029133121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11959995484193880038844161 8969996613145410029133121)
            ·
              refine ⟨6727497459859057521849841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8969996613145410029133121 6727497459859057521849841)
              ·
                refine ⟨5045623094894293141387381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6727497459859057521849841 5045623094894293141387381)
                ·
                  refine ⟨473027165146339982005067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5045623094894293141387381 473027165146339982005067)
                  ·
                    rfl

theorem cell23_8290954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 2, 5].length) (baseStart_8290954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290954 prefixEnd_8290954 := by exact prefixLift 8290954
  have htrace : WordTrace (prefixWord ++ tailWord_8290954) baseStart_8290954 baseEnd_8290954 := by
    simpa [prefixWord, tailWord_8290954, baseEnd_8290954] using wordTrace_append hprefix tailTrace_8290954
  have hstable : (prefixWord ++ tailWord_8290954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290954).length < 2 ^ (prefixWord ++ tailWord_8290954).sum := by decide
  have hdescent : baseEnd_8290954 < baseStart_8290954 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8290980 : List Nat := [2, 3, 1, 2, 2, 1, 3, 2, 3, 4]
def baseStart_8290980 : Nat := 118140960795 + 8290980 * 2 ^ 59
def prefixEnd_8290980 : Nat := 4983230072969 + 3 ^ 40 * 8290980 * 2
def baseEnd_8290980 : Nat := 1419085945604692245440161

theorem tailTrace_8290980 : CollatzResearch.WordTrace tailWord_8290980 prefixEnd_8290980 1419085945604692245440161 := by
  unfold tailWord_8290980
  simp only [CollatzResearch.WordTrace]
  refine ⟨151198441751601460748327197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201597922335468614331102929 151198441751601460748327197)
  ·
    refine ⟨56699415656850547780622699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151198441751601460748327197 56699415656850547780622699)
    ·
      refine ⟨85049123485275821670934049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56699415656850547780622699 85049123485275821670934049)
      ·
        refine ⟨63786842613956866253200537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85049123485275821670934049 63786842613956866253200537)
        ·
          refine ⟨47840131960467649689900403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63786842613956866253200537 47840131960467649689900403)
          ·
            refine ⟨71760197940701474534850605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47840131960467649689900403 71760197940701474534850605)
            ·
              refine ⟨26910074227763052950568977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71760197940701474534850605 26910074227763052950568977)
              ·
                refine ⟨20182555670822289712926733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26910074227763052950568977 20182555670822289712926733)
                ·
                  refine ⟨7568458376558358642347525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20182555670822289712926733 7568458376558358642347525)
                  ·
                    refine ⟨1419085945604692245440161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7568458376558358642347525 1419085945604692245440161)
                    ·
                      rfl

theorem cell23_8290980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 3, 2, 3, 4].length) (baseStart_8290980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8290980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8290980 prefixEnd_8290980 := by exact prefixLift 8290980
  have htrace : WordTrace (prefixWord ++ tailWord_8290980) baseStart_8290980 baseEnd_8290980 := by
    simpa [prefixWord, tailWord_8290980, baseEnd_8290980] using wordTrace_append hprefix tailTrace_8290980
  have hstable : (prefixWord ++ tailWord_8290980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8290980).length < 2 ^ (prefixWord ++ tailWord_8290980).sum := by decide
  have hdescent : baseEnd_8290980 < baseStart_8290980 := by decide
  rcases family_descends (prefixWord ++ tailWord_8290980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291080 : List Nat := [2, 1, 3, 2, 2, 2, 2, 2, 1, 1, 5]
def baseStart_8291080 : Nat := 118140960795 + 8291080 * 2 ^ 59
def prefixEnd_8291080 : Nat := 4983230072969 + 3 ^ 40 * 8291080 * 2
def baseEnd_8291080 : Nat := 4257309184879526345070023

theorem tailTrace_8291080 : CollatzResearch.WordTrace tailWord_8291080 prefixEnd_8291080 4257309184879526345070023 := by
  unfold tailWord_8291080
  simp only [CollatzResearch.WordTrace]
  refine ⟨151200265401420319287647347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201600353868560425716863129 151200265401420319287647347)
  ·
    refine ⟨226800398102130478931471021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151200265401420319287647347 226800398102130478931471021)
    ·
      refine ⟨85050149288298929599301633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226800398102130478931471021 85050149288298929599301633)
      ·
        refine ⟨63787611966224197199476225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85050149288298929599301633 63787611966224197199476225)
        ·
          refine ⟨47840708974668147899607169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63787611966224197199476225 47840708974668147899607169)
          ·
            refine ⟨35880531731001110924705377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47840708974668147899607169 35880531731001110924705377)
            ·
              refine ⟨26910398798250833193529033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35880531731001110924705377 26910398798250833193529033)
              ·
                refine ⟨20182799098688124895146775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26910398798250833193529033 20182799098688124895146775)
                ·
                  refine ⟨30274198648032187342720163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20182799098688124895146775 30274198648032187342720163)
                  ·
                    refine ⟨45411297972048281014080245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30274198648032187342720163 45411297972048281014080245)
                    ·
                      refine ⟨4257309184879526345070023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45411297972048281014080245 4257309184879526345070023)
                      ·
                        rfl

theorem cell23_8291080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_8291080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291080 prefixEnd_8291080 := by exact prefixLift 8291080
  have htrace : WordTrace (prefixWord ++ tailWord_8291080) baseStart_8291080 baseEnd_8291080 := by
    simpa [prefixWord, tailWord_8291080, baseEnd_8291080] using wordTrace_append hprefix tailTrace_8291080
  have hstable : (prefixWord ++ tailWord_8291080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291080).length < 2 ^ (prefixWord ++ tailWord_8291080).sum := by decide
  have hdescent : baseEnd_8291080 < baseStart_8291080 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291117 : List Nat := [1, 5, 3, 2, 1, 11]
def baseStart_8291117 : Nat := 118140960795 + 8291117 * 2 ^ 59
def prefixEnd_8291117 : Nat := 4983230072969 + 3 ^ 40 * 8291117 * 2
def baseEnd_8291117 : Nat := 17519869068575072840771

theorem tailTrace_8291117 : CollatzResearch.WordTrace tailWord_8291117 prefixEnd_8291117 17519869068575072840771 := by
  unfold tailWord_8291117
  simp only [CollatzResearch.WordTrace]
  refine ⟨302401880303706593894391605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201601253535804395929594403 302401880303706593894391605)
  ·
    refine ⟨28350176278472493177599213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302401880303706593894391605 28350176278472493177599213)
    ·
      refine ⟨10631316104427184941599705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28350176278472493177599213 10631316104427184941599705)
      ·
        refine ⟨7973487078320388706199779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10631316104427184941599705 7973487078320388706199779)
        ·
          refine ⟨11960230617480583059299669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7973487078320388706199779 11960230617480583059299669)
          ·
            refine ⟨17519869068575072840771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11960230617480583059299669 17519869068575072840771)
            ·
              rfl

theorem cell23_8291117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 11].length) (baseStart_8291117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291117 prefixEnd_8291117 := by exact prefixLift 8291117
  have htrace : WordTrace (prefixWord ++ tailWord_8291117) baseStart_8291117 baseEnd_8291117 := by
    simpa [prefixWord, tailWord_8291117, baseEnd_8291117] using wordTrace_append hprefix tailTrace_8291117
  have hstable : (prefixWord ++ tailWord_8291117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291117).length < 2 ^ (prefixWord ++ tailWord_8291117).sum := by decide
  have hdescent : baseEnd_8291117 < baseStart_8291117 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291134 : List Nat := [4, 2, 1, 2, 4, 1, 1, 8]
def baseStart_8291134 : Nat := 118140960795 + 8291134 * 2 ^ 59
def prefixEnd_8291134 : Nat := 4983230072969 + 3 ^ 40 * 8291134 * 2
def baseEnd_8291134 : Nat := 157679144919809967918325

theorem tailTrace_8291134 : CollatzResearch.WordTrace tailWord_8291134 prefixEnd_8291134 157679144919809967918325 := by
  unfold tailWord_8291134
  simp only [CollatzResearch.WordTrace]
  refine ⟨37800312543080625724720057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201601666896430003865173637 37800312543080625724720057)
  ·
    refine ⟨28350234407310469293540043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37800312543080625724720057 28350234407310469293540043)
    ·
      refine ⟨42525351610965703940310065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28350234407310469293540043 42525351610965703940310065)
      ·
        refine ⟨31894013708224277955232549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42525351610965703940310065 31894013708224277955232549)
        ·
          refine ⟨5980127570292052116606103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31894013708224277955232549 5980127570292052116606103)
          ·
            refine ⟨8970191355438078174909155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5980127570292052116606103 8970191355438078174909155)
            ·
              refine ⟨13455287033157117262363733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8970191355438078174909155 13455287033157117262363733)
              ·
                refine ⟨157679144919809967918325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13455287033157117262363733 157679144919809967918325)
                ·
                  rfl

theorem cell23_8291134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 4, 1, 1, 8].length) (baseStart_8291134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291134 prefixEnd_8291134 := by exact prefixLift 8291134
  have htrace : WordTrace (prefixWord ++ tailWord_8291134) baseStart_8291134 baseEnd_8291134 := by
    simpa [prefixWord, tailWord_8291134, baseEnd_8291134] using wordTrace_append hprefix tailTrace_8291134
  have hstable : (prefixWord ++ tailWord_8291134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291134).length < 2 ^ (prefixWord ++ tailWord_8291134).sum := by decide
  have hdescent : baseEnd_8291134 < baseStart_8291134 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291154 : List Nat := [3, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2]
def baseStart_8291154 : Nat := 118140960795 + 8291154 * 2 ^ 59
def prefixEnd_8291154 : Nat := 4983230072969 + 3 ^ 40 * 8291154 * 2
def baseEnd_8291154 : Nat := 4257347182447959055544683

theorem tailTrace_8291154 : CollatzResearch.WordTrace tailWord_8291154 prefixEnd_8291154 4257347182447959055544683 := by
  unfold tailWord_8291154
  simp only [CollatzResearch.WordTrace]
  refine ⟨75600807451143137303372129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201602153203048366142325677 75600807451143137303372129)
  ·
    refine ⟨56700605588357352977529097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75600807451143137303372129 56700605588357352977529097)
    ·
      refine ⟨42525454191268014733146823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56700605588357352977529097 42525454191268014733146823)
      ·
        refine ⟨63788181286902022099720235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42525454191268014733146823 63788181286902022099720235)
        ·
          refine ⟨95682271930353033149580353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63788181286902022099720235 95682271930353033149580353)
          ·
            refine ⟨71761703947764774862185265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95682271930353033149580353 71761703947764774862185265)
            ·
              refine ⟨53821277960823581146638949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71761703947764774862185265 53821277960823581146638949)
              ·
                refine ⟨10091489617654421464994803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53821277960823581146638949 10091489617654421464994803)
                ·
                  refine ⟨15137234426481632197492205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10091489617654421464994803 15137234426481632197492205)
                  ·
                    refine ⟨5676462909930612074059577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15137234426481632197492205 5676462909930612074059577)
                    ·
                      refine ⟨4257347182447959055544683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5676462909930612074059577 4257347182447959055544683)
                      ·
                        rfl

theorem cell23_8291154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2].length) (baseStart_8291154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291154 prefixEnd_8291154 := by exact prefixLift 8291154
  have htrace : WordTrace (prefixWord ++ tailWord_8291154) baseStart_8291154 baseEnd_8291154 := by
    simpa [prefixWord, tailWord_8291154, baseEnd_8291154] using wordTrace_append hprefix tailTrace_8291154
  have hstable : (prefixWord ++ tailWord_8291154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291154).length < 2 ^ (prefixWord ++ tailWord_8291154).sum := by decide
  have hdescent : baseEnd_8291154 < baseStart_8291154 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291163 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 6]
def baseStart_8291163 : Nat := 118140960795 + 8291163 * 2 ^ 59
def prefixEnd_8291163 : Nat := 4983230072969 + 3 ^ 40 * 8291163 * 2
def baseEnd_8291163 : Nat := 4257351803773849520332141

theorem tailTrace_8291163 : CollatzResearch.WordTrace tailWord_8291163 prefixEnd_8291163 4257351803773849520332141 := by
  unfold tailWord_8291163
  simp only [CollatzResearch.WordTrace]
  refine ⟨302403558061539943750566143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201602372041026629167044095 302403558061539943750566143)
  ·
    refine ⟨453605337092309915625849215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302403558061539943750566143 453605337092309915625849215)
    ·
      refine ⟨680408005638464873438773823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453605337092309915625849215 680408005638464873438773823)
      ·
        refine ⟨1020612008457697310158160735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680408005638464873438773823 1020612008457697310158160735)
        ·
          refine ⟨1530918012686545965237241103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1020612008457697310158160735 1530918012686545965237241103)
          ·
            refine ⟨2296377019029818947855861655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1530918012686545965237241103 2296377019029818947855861655)
            ·
              refine ⟨3444565528544728421783792483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2296377019029818947855861655 3444565528544728421783792483)
              ·
                refine ⟨5166848292817092632675688725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3444565528544728421783792483 5166848292817092632675688725)
                ·
                  refine ⟨242196013725801217156672909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5166848292817092632675688725 242196013725801217156672909)
                  ·
                    refine ⟨90823505147175456433752341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 242196013725801217156672909 90823505147175456433752341)
                    ·
                      refine ⟨4257351803773849520332141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90823505147175456433752341 4257351803773849520332141)
                      ·
                        rfl

theorem cell23_8291163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 6].length) (baseStart_8291163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291163 prefixEnd_8291163 := by exact prefixLift 8291163
  have htrace : WordTrace (prefixWord ++ tailWord_8291163) baseStart_8291163 baseEnd_8291163 := by
    simpa [prefixWord, tailWord_8291163, baseEnd_8291163] using wordTrace_append hprefix tailTrace_8291163
  have hstable : (prefixWord ++ tailWord_8291163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291163).length < 2 ^ (prefixWord ++ tailWord_8291163).sum := by decide
  have hdescent : baseEnd_8291163 < baseStart_8291163 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291167 : List Nat := [1, 1, 2, 3, 1, 3, 1, 4, 1, 4, 2]
def baseStart_8291167 : Nat := 118140960795 + 8291167 * 2 ^ 59
def prefixEnd_8291167 : Nat := 4983230072969 + 3 ^ 40 * 8291167 * 2
def baseEnd_8291167 : Nat := 4257353857696467504682123

theorem tailTrace_8291167 : CollatzResearch.WordTrace tailWord_8291167 prefixEnd_8291167 4257353857696467504682123 := by
  unfold tailWord_8291167
  simp only [CollatzResearch.WordTrace]
  refine ⟨302403703953525452433711755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201602469302350301622474503 302403703953525452433711755)
  ·
    refine ⟨453605555930288178650567633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302403703953525452433711755 453605555930288178650567633)
    ·
      refine ⟨340204166947716133987925725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453605555930288178650567633 340204166947716133987925725)
      ·
        refine ⟨127576562605393550245472147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 340204166947716133987925725 127576562605393550245472147)
        ·
          refine ⟨191364843908090325368208221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127576562605393550245472147 191364843908090325368208221)
          ·
            refine ⟨71761816465533872013078083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 191364843908090325368208221 71761816465533872013078083)
            ·
              refine ⟨107642724698300808019617125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71761816465533872013078083 107642724698300808019617125)
              ·
                refine ⟨20183010880931401503678211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107642724698300808019617125 20183010880931401503678211)
                ·
                  refine ⟨30274516321397102255517317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20183010880931401503678211 30274516321397102255517317)
                  ·
                    refine ⟨5676471810261956672909497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30274516321397102255517317 5676471810261956672909497)
                    ·
                      refine ⟨4257353857696467504682123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5676471810261956672909497 4257353857696467504682123)
                      ·
                        rfl

theorem cell23_8291167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 4, 1, 4, 2].length) (baseStart_8291167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291167 prefixEnd_8291167 := by exact prefixLift 8291167
  have htrace : WordTrace (prefixWord ++ tailWord_8291167) baseStart_8291167 baseEnd_8291167 := by
    simpa [prefixWord, tailWord_8291167, baseEnd_8291167] using wordTrace_append hprefix tailTrace_8291167
  have hstable : (prefixWord ++ tailWord_8291167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291167).length < 2 ^ (prefixWord ++ tailWord_8291167).sum := by decide
  have hdescent : baseEnd_8291167 < baseStart_8291167 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291171 : List Nat := [1, 1, 1, 5, 3, 1, 4, 1, 1, 3, 2]
def baseStart_8291171 : Nat := 118140960795 + 8291171 * 2 ^ 59
def prefixEnd_8291171 : Nat := 4983230072969 + 3 ^ 40 * 8291171 * 2
def baseEnd_8291171 : Nat := 4257355911619085489032105

theorem tailTrace_8291171 : CollatzResearch.WordTrace tailWord_8291171 prefixEnd_8291171 4257355911619085489032105 := by
  unfold tailWord_8291171
  simp only [CollatzResearch.WordTrace]
  refine ⟨302403849845510961116857367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201602566563673974077904911 302403849845510961116857367)
  ·
    refine ⟨453605774768266441675286051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302403849845510961116857367 453605774768266441675286051)
    ·
      refine ⟨680408662152399662512929077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453605774768266441675286051 680408662152399662512929077)
      ·
        refine ⟨63788312076787468360587101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 680408662152399662512929077 63788312076787468360587101)
        ·
          refine ⟨23920617028795300635220163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 63788312076787468360587101 23920617028795300635220163)
          ·
            refine ⟨35880925543192950952830245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23920617028795300635220163 35880925543192950952830245)
            ·
              refine ⟨6727673539348678303655671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35880925543192950952830245 6727673539348678303655671)
              ·
                refine ⟨10091510309023017455483507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6727673539348678303655671 10091510309023017455483507)
                ·
                  refine ⟨15137265463534526183225261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10091510309023017455483507 15137265463534526183225261)
                  ·
                    refine ⟨5676474548825447318709473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15137265463534526183225261 5676474548825447318709473)
                    ·
                      refine ⟨4257355911619085489032105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5676474548825447318709473 4257355911619085489032105)
                      ·
                        rfl

theorem cell23_8291171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 4, 1, 1, 3, 2].length) (baseStart_8291171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291171 prefixEnd_8291171 := by exact prefixLift 8291171
  have htrace : WordTrace (prefixWord ++ tailWord_8291171) baseStart_8291171 baseEnd_8291171 := by
    simpa [prefixWord, tailWord_8291171, baseEnd_8291171] using wordTrace_append hprefix tailTrace_8291171
  have hstable : (prefixWord ++ tailWord_8291171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291171).length < 2 ^ (prefixWord ++ tailWord_8291171).sum := by decide
  have hdescent : baseEnd_8291171 < baseStart_8291171 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291180 : List Nat := [2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 4]
def baseStart_8291180 : Nat := 118140960795 + 8291180 * 2 ^ 59
def prefixEnd_8291180 : Nat := 4983230072969 + 3 ^ 40 * 8291180 * 2
def baseEnd_8291180 : Nat := 4257360532944975953819563

theorem tailTrace_8291180 : CollatzResearch.WordTrace tailWord_8291180 prefixEnd_8291180 4257360532944975953819563 := by
  unfold tailWord_8291180
  simp only [CollatzResearch.WordTrace]
  refine ⟨151202089051239177826967497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201602785401652237102623329 151202089051239177826967497)
  ·
    refine ⟨113401566788429383370225623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151202089051239177826967497 113401566788429383370225623)
    ·
      refine ⟨170102350182644075055338435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113401566788429383370225623 170102350182644075055338435)
      ·
        refine ⟨255153525273966112583007653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170102350182644075055338435 255153525273966112583007653)
        ·
          refine ⟨47841285988868646109313935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255153525273966112583007653 47841285988868646109313935)
          ·
            refine ⟨71761928983302969163970903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47841285988868646109313935 71761928983302969163970903)
            ·
              refine ⟨107642893474954453745956355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71761928983302969163970903 107642893474954453745956355)
              ·
                refine ⟨161464340212431680618934533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107642893474954453745956355 161464340212431680618934533)
                ·
                  refine ⟨30274563789830940116050225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161464340212431680618934533 30274563789830940116050225)
                  ·
                    refine ⟨22705922842373205087037669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30274563789830940116050225 22705922842373205087037669)
                    ·
                      refine ⟨4257360532944975953819563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22705922842373205087037669 4257360532944975953819563)
                      ·
                        rfl

theorem cell23_8291180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 4].length) (baseStart_8291180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291180 prefixEnd_8291180 := by exact prefixLift 8291180
  have htrace : WordTrace (prefixWord ++ tailWord_8291180) baseStart_8291180 baseEnd_8291180 := by
    simpa [prefixWord, tailWord_8291180, baseEnd_8291180] using wordTrace_append hprefix tailTrace_8291180
  have hstable : (prefixWord ++ tailWord_8291180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291180).length < 2 ^ (prefixWord ++ tailWord_8291180).sum := by decide
  have hdescent : baseEnd_8291180 < baseStart_8291180 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291200 : List Nat := [2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 3]
def baseStart_8291200 : Nat := 118140960795 + 8291200 * 2 ^ 59
def prefixEnd_8291200 : Nat := 4983230072969 + 3 ^ 40 * 8291200 * 2
def baseEnd_8291200 : Nat := 4257370802558065875569471

theorem tailTrace_8291200 : CollatzResearch.WordTrace tailWord_8291200 prefixEnd_8291200 4257370802558065875569471 := by
  unfold tailWord_8291200
  simp only [CollatzResearch.WordTrace]
  refine ⟨151202453781202949534831527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201603271708270599379775369 151202453781202949534831527)
  ·
    refine ⟨226803680671804424302247291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151202453781202949534831527 226803680671804424302247291)
    ·
      refine ⟨340205521007706636453370937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226803680671804424302247291 340205521007706636453370937)
      ·
        refine ⟨255154140755779977340028203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340205521007706636453370937 255154140755779977340028203)
        ·
          refine ⟨382731211133669966010042305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255154140755779977340028203 382731211133669966010042305)
          ·
            refine ⟨287048408350252474507531729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 382731211133669966010042305 287048408350252474507531729)
            ·
              refine ⟨215286306262689355880648797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287048408350252474507531729 215286306262689355880648797)
              ·
                refine ⟨80732364848508508455243299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215286306262689355880648797 80732364848508508455243299)
                ·
                  refine ⟨121098547272762762682864949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80732364848508508455243299 121098547272762762682864949)
                  ·
                    refine ⟨11352988806821509001518589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121098547272762762682864949 11352988806821509001518589)
                    ·
                      refine ⟨4257370802558065875569471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11352988806821509001518589 4257370802558065875569471)
                      ·
                        rfl

theorem cell23_8291200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 3, 1, 5, 3].length) (baseStart_8291200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291200 prefixEnd_8291200 := by exact prefixLift 8291200
  have htrace : WordTrace (prefixWord ++ tailWord_8291200) baseStart_8291200 baseEnd_8291200 := by
    simpa [prefixWord, tailWord_8291200, baseEnd_8291200] using wordTrace_append hprefix tailTrace_8291200
  have hstable : (prefixWord ++ tailWord_8291200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291200).length < 2 ^ (prefixWord ++ tailWord_8291200).sum := by decide
  have hdescent : baseEnd_8291200 < baseStart_8291200 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291252 : List Nat := [2, 5, 2, 1, 1, 3, 2, 1, 2, 2, 2]
def baseStart_8291252 : Nat := 118140960795 + 8291252 * 2 ^ 59
def prefixEnd_8291252 : Nat := 4983230072969 + 3 ^ 40 * 8291252 * 2
def baseEnd_8291252 : Nat := 4257397503552099672119233

theorem tailTrace_8291252 : CollatzResearch.WordTrace tailWord_8291252 prefixEnd_8291252 4257397503552099672119233 := by
  unfold tailWord_8291252
  simp only [CollatzResearch.WordTrace]
  refine ⟨151203402079108755975278005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201604536105478341300370673 151203402079108755975278005)
  ·
    refine ⟨14175318944916445872682313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 151203402079108755975278005 14175318944916445872682313)
    ·
      refine ⟨10631489208687334404511735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14175318944916445872682313 10631489208687334404511735)
      ·
        refine ⟨15947233813031001606767603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10631489208687334404511735 15947233813031001606767603)
        ·
          refine ⟨23920850719546502410151405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15947233813031001606767603 23920850719546502410151405)
          ·
            refine ⟨8970319019829938403806777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23920850719546502410151405 8970319019829938403806777)
            ·
              refine ⟨6727739264872453802855083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8970319019829938403806777 6727739264872453802855083)
              ·
                refine ⟨10091608897308680704282625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6727739264872453802855083 10091608897308680704282625)
                ·
                  refine ⟨7568706672981510528211969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10091608897308680704282625 7568706672981510528211969)
                  ·
                    refine ⟨5676530004736132896158977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7568706672981510528211969 5676530004736132896158977)
                    ·
                      refine ⟨4257397503552099672119233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5676530004736132896158977 4257397503552099672119233)
                      ·
                        rfl

theorem cell23_8291252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 2, 1, 2, 2, 2].length) (baseStart_8291252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291252 prefixEnd_8291252 := by exact prefixLift 8291252
  have htrace : WordTrace (prefixWord ++ tailWord_8291252) baseStart_8291252 baseEnd_8291252 := by
    simpa [prefixWord, tailWord_8291252, baseEnd_8291252] using wordTrace_append hprefix tailTrace_8291252
  have hstable : (prefixWord ++ tailWord_8291252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291252).length < 2 ^ (prefixWord ++ tailWord_8291252).sum := by decide
  have hdescent : baseEnd_8291252 < baseStart_8291252 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291320 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 1, 3, 7]
def baseStart_8291320 : Nat := 118140960795 + 8291320 * 2 ^ 59
def prefixEnd_8291320 : Nat := 4983230072969 + 3 ^ 40 * 8291320 * 2
def baseEnd_8291320 : Nat := 4257432420236605406068919

theorem tailTrace_8291320 : CollatzResearch.WordTrace tailWord_8291320 prefixEnd_8291320 4257432420236605406068919 := by
  unfold tailWord_8291320
  simp only [CollatzResearch.WordTrace]
  refine ⟨151204642160985579782015707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201606189547980773042687609 151204642160985579782015707)
  ·
    refine ⟨226806963241478369673023561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151204642160985579782015707 226806963241478369673023561)
    ·
      refine ⟨170105222431108777254767671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226806963241478369673023561 170105222431108777254767671)
      ·
        refine ⟨255157833646663165882151507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170105222431108777254767671 255157833646663165882151507)
        ·
          refine ⟨382736750469994748823227261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255157833646663165882151507 382736750469994748823227261)
          ·
            refine ⟨143526281426248030808710223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382736750469994748823227261 143526281426248030808710223)
            ·
              refine ⟨215289422139372046213065335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143526281426248030808710223 215289422139372046213065335)
              ·
                refine ⟨322934133209058069319598003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 215289422139372046213065335 322934133209058069319598003)
                ·
                  refine ⟨484401199813587103979397005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 322934133209058069319598003 484401199813587103979397005)
                  ·
                    refine ⟨181650449930095163992273877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 484401199813587103979397005 181650449930095163992273877)
                    ·
                      refine ⟨4257432420236605406068919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 181650449930095163992273877 4257432420236605406068919)
                      ·
                        rfl

theorem cell23_8291320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_8291320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291320 prefixEnd_8291320 := by exact prefixLift 8291320
  have htrace : WordTrace (prefixWord ++ tailWord_8291320) baseStart_8291320 baseEnd_8291320 := by
    simpa [prefixWord, tailWord_8291320, baseEnd_8291320] using wordTrace_append hprefix tailTrace_8291320
  have hstable : (prefixWord ++ tailWord_8291320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291320).length < 2 ^ (prefixWord ++ tailWord_8291320).sum := by decide
  have hdescent : baseEnd_8291320 < baseStart_8291320 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291324 : List Nat := [2, 2, 2, 1, 2, 3, 1, 1, 5, 1, 3]
def baseStart_8291324 : Nat := 118140960795 + 8291324 * 2 ^ 59
def prefixEnd_8291324 : Nat := 4983230072969 + 3 ^ 40 * 8291324 * 2
def baseEnd_8291324 : Nat := 4257434474159223390418901

theorem tailTrace_8291324 : CollatzResearch.WordTrace tailWord_8291324 prefixEnd_8291324 4257434474159223390418901 := by
  unfold tailWord_8291324
  simp only [CollatzResearch.WordTrace]
  refine ⟨151204715106978334123588513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201606286809304445498118017 151204715106978334123588513)
  ·
    refine ⟨113403536330233750592691385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151204715106978334123588513 113403536330233750592691385)
    ·
      refine ⟨85052652247675312944518539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113403536330233750592691385 85052652247675312944518539)
      ·
        refine ⟨127578978371512969416777809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85052652247675312944518539 127578978371512969416777809)
        ·
          refine ⟨95684233778634727062583357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127578978371512969416777809 95684233778634727062583357)
          ·
            refine ⟨35881587666988022648468759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95684233778634727062583357 35881587666988022648468759)
            ·
              refine ⟨53822381500482033972703139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35881587666988022648468759 53822381500482033972703139)
              ·
                refine ⟨80733572250723050959054709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53822381500482033972703139 80733572250723050959054709)
                ·
                  refine ⟨7568772398505286027411379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80733572250723050959054709 7568772398505286027411379)
                  ·
                    refine ⟨11353158597757929041117069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7568772398505286027411379 11353158597757929041117069)
                    ·
                      refine ⟨4257434474159223390418901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11353158597757929041117069 4257434474159223390418901)
                      ·
                        rfl

theorem cell23_8291324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 5, 1, 3].length) (baseStart_8291324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291324 prefixEnd_8291324 := by exact prefixLift 8291324
  have htrace : WordTrace (prefixWord ++ tailWord_8291324) baseStart_8291324 baseEnd_8291324 := by
    simpa [prefixWord, tailWord_8291324, baseEnd_8291324] using wordTrace_append hprefix tailTrace_8291324
  have hstable : (prefixWord ++ tailWord_8291324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291324).length < 2 ^ (prefixWord ++ tailWord_8291324).sum := by decide
  have hdescent : baseEnd_8291324 < baseStart_8291324 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291377 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 1, 1, 6]
def baseStart_8291377 : Nat := 118140960795 + 8291377 * 2 ^ 59
def prefixEnd_8291377 : Nat := 4983230072969 + 3 ^ 40 * 8291377 * 2
def baseEnd_8291377 : Nat := 4257461688633911683056157

theorem tailTrace_8291377 : CollatzResearch.WordTrace tailWord_8291377 prefixEnd_8291377 4257461688633911683056157 := by
  unfold tailWord_8291377
  simp only [CollatzResearch.WordTrace]
  refine ⟨302411363282764658298856385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201607575521843105532570923 302411363282764658298856385)
  ·
    refine ⟨226808522462073493724142289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302411363282764658298856385 226808522462073493724142289)
    ·
      refine ⟨170106391846555120293106717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226808522462073493724142289 170106391846555120293106717)
      ·
        refine ⟨63789896942458170109915019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 170106391846555120293106717 63789896942458170109915019)
        ·
          refine ⟨95684845413687255164872529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63789896942458170109915019 95684845413687255164872529)
          ·
            refine ⟨71763634060265441373654397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95684845413687255164872529 71763634060265441373654397)
            ·
              refine ⟨26911362772599540515120399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 71763634060265441373654397 26911362772599540515120399)
              ·
                refine ⟨40367044158899310772680599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26911362772599540515120399 40367044158899310772680599)
                ·
                  refine ⟨60550566238348966159020899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40367044158899310772680599 60550566238348966159020899)
                  ·
                    refine ⟨90825849357523449238531349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60550566238348966159020899 90825849357523449238531349)
                    ·
                      refine ⟨4257461688633911683056157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90825849357523449238531349 4257461688633911683056157)
                      ·
                        rfl

theorem cell23_8291377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_8291377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291377 prefixEnd_8291377 := by exact prefixLift 8291377
  have htrace : WordTrace (prefixWord ++ tailWord_8291377) baseStart_8291377 baseEnd_8291377 := by
    simpa [prefixWord, tailWord_8291377, baseEnd_8291377] using wordTrace_append hprefix tailTrace_8291377
  have hstable : (prefixWord ++ tailWord_8291377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291377).length < 2 ^ (prefixWord ++ tailWord_8291377).sum := by decide
  have hdescent : baseEnd_8291377 < baseStart_8291377 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291398 : List Nat := [6, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4]
def baseStart_8291398 : Nat := 118140960795 + 8291398 * 2 ^ 59
def prefixEnd_8291398 : Nat := 4983230072969 + 3 ^ 40 * 8291398 * 2
def baseEnd_8291398 : Nat := 4257472471727656100893561

theorem tailTrace_8291398 : CollatzResearch.WordTrace tailWord_8291398 prefixEnd_8291398 4257472471727656100893561 := by
  unfold tailWord_8291398
  simp only [CollatzResearch.WordTrace]
  refine ⟨9450379037990268090167839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 201608086143792385923580565 9450379037990268090167839)
  ·
    refine ⟨14175568556985402135251759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9450379037990268090167839 14175568556985402135251759)
    ·
      refine ⟨21263352835478103202877639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14175568556985402135251759 21263352835478103202877639)
      ·
        refine ⟨31895029253217154804316459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21263352835478103202877639 31895029253217154804316459)
        ·
          refine ⟨47842543879825732206474689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31895029253217154804316459 47842543879825732206474689)
          ·
            refine ⟨35881907909869299154856017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47842543879825732206474689 35881907909869299154856017)
            ·
              refine ⟨26911430932401974366142013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35881907909869299154856017 26911430932401974366142013)
              ·
                refine ⟨10091786599650740387303255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26911430932401974366142013 10091786599650740387303255)
                ·
                  refine ⟨15137679899476110580954883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10091786599650740387303255 15137679899476110580954883)
                  ·
                    refine ⟨22706519849214165871432325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15137679899476110580954883 22706519849214165871432325)
                    ·
                      refine ⟨4257472471727656100893561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22706519849214165871432325 4257472471727656100893561)
                      ·
                        rfl

theorem cell23_8291398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_8291398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291398 prefixEnd_8291398 := by exact prefixLift 8291398
  have htrace : WordTrace (prefixWord ++ tailWord_8291398) baseStart_8291398 baseEnd_8291398 := by
    simpa [prefixWord, tailWord_8291398, baseEnd_8291398] using wordTrace_append hprefix tailTrace_8291398
  have hstable : (prefixWord ++ tailWord_8291398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291398).length < 2 ^ (prefixWord ++ tailWord_8291398).sum := by decide
  have hdescent : baseEnd_8291398 < baseStart_8291398 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291421 : List Nat := [1, 4, 4, 1, 2, 1, 2, 8]
def baseStart_8291421 : Nat := 118140960795 + 8291421 * 2 ^ 59
def prefixEnd_8291421 : Nat := 4983230072969 + 3 ^ 40 * 8291421 * 2
def baseEnd_8291421 : Nat := 157684603028989241144665

theorem tailTrace_8291421 : CollatzResearch.WordTrace tailWord_8291421 prefixEnd_8291421 157684603028989241144665 := by
  unfold tailWord_8291421
  simp only [CollatzResearch.WordTrace]
  refine ⟨302412968094605253813458117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201608645396403502542305411 302412968094605253813458117)
  ·
    refine ⟨56702431517738485090023397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302412968094605253813458117 56702431517738485090023397)
    ·
      refine ⟨10631705909575965954379387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56702431517738485090023397 10631705909575965954379387)
      ·
        refine ⟨15947558864363948931569081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10631705909575965954379387 15947558864363948931569081)
        ·
          refine ⟨11960669148272961698676811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15947558864363948931569081 11960669148272961698676811)
          ·
            refine ⟨17941003722409442548015217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11960669148272961698676811 17941003722409442548015217)
            ·
              refine ⟨13455752791807081911011413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17941003722409442548015217 13455752791807081911011413)
              ·
                refine ⟨157684603028989241144665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13455752791807081911011413 157684603028989241144665)
                ·
                  rfl

theorem cell23_8291421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 1, 2, 8].length) (baseStart_8291421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291421 prefixEnd_8291421 := by exact prefixLift 8291421
  have htrace : WordTrace (prefixWord ++ tailWord_8291421) baseStart_8291421 baseEnd_8291421 := by
    simpa [prefixWord, tailWord_8291421, baseEnd_8291421] using wordTrace_append hprefix tailTrace_8291421
  have hstable : (prefixWord ++ tailWord_8291421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291421).length < 2 ^ (prefixWord ++ tailWord_8291421).sum := by decide
  have hdescent : baseEnd_8291421 < baseStart_8291421 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291441 : List Nat := [1, 2, 2, 2, 1, 1, 2, 6, 1, 3, 2]
def baseStart_8291441 : Nat := 118140960795 + 8291441 * 2 ^ 59
def prefixEnd_8291441 : Nat := 4983230072969 + 3 ^ 40 * 8291441 * 2
def baseEnd_8291441 : Nat := 4257494551395799432655863

theorem tailTrace_8291441 : CollatzResearch.WordTrace tailWord_8291441 prefixEnd_8291441 4257494551395799432655863 := by
  unfold tailWord_8291441
  simp only [CollatzResearch.WordTrace]
  refine ⟨302413697554532797229186177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201609131703021864819457451 302413697554532797229186177)
  ·
    refine ⟨226810273165899597921889633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302413697554532797229186177 226810273165899597921889633)
    ·
      refine ⟨170107704874424698441417225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226810273165899597921889633 170107704874424698441417225)
      ·
        refine ⟨127580778655818523831062919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170107704874424698441417225 127580778655818523831062919)
        ·
          refine ⟨191371167983727785746594379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127580778655818523831062919 191371167983727785746594379)
          ·
            refine ⟨287056751975591678619891569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191371167983727785746594379 287056751975591678619891569)
            ·
              refine ⟨215292563981693758964918677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 287056751975591678619891569 215292563981693758964918677)
              ·
                refine ⟨10091838936641894951480563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 215292563981693758964918677 10091838936641894951480563)
                ·
                  refine ⟨15137758404962842427220845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10091838936641894951480563 15137758404962842427220845)
                  ·
                    refine ⟨5676659401861065910207817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15137758404962842427220845 5676659401861065910207817)
                    ·
                      refine ⟨4257494551395799432655863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5676659401861065910207817 4257494551395799432655863)
                      ·
                        rfl

theorem cell23_8291441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 6, 1, 3, 2].length) (baseStart_8291441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291441 prefixEnd_8291441 := by exact prefixLift 8291441
  have htrace : WordTrace (prefixWord ++ tailWord_8291441) baseStart_8291441 baseEnd_8291441 := by
    simpa [prefixWord, tailWord_8291441, baseEnd_8291441] using wordTrace_append hprefix tailTrace_8291441
  have hstable : (prefixWord ++ tailWord_8291441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291441).length < 2 ^ (prefixWord ++ tailWord_8291441).sum := by decide
  have hdescent : baseEnd_8291441 < baseStart_8291441 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291467 : List Nat := [1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 4]
def baseStart_8291467 : Nat := 118140960795 + 8291467 * 2 ^ 59
def prefixEnd_8291467 : Nat := 4983230072969 + 3 ^ 40 * 8291467 * 2
def baseEnd_8291467 : Nat := 4257507901892816330930743

theorem tailTrace_8291467 : CollatzResearch.WordTrace tailWord_8291467 prefixEnd_8291467 4257507901892816330930743 := by
  unfold tailWord_8291467
  simp only [CollatzResearch.WordTrace]
  refine ⟨302414645852438603669632655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201609763901625735779755103 302414645852438603669632655)
  ·
    refine ⟨453621968778657905504448983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302414645852438603669632655 453621968778657905504448983)
    ·
      refine ⟨680432953167986858256673475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453621968778657905504448983 680432953167986858256673475)
      ·
        refine ⟨1020649429751980287385010213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680432953167986858256673475 1020649429751980287385010213)
        ·
          refine ⟨191371768078496303884689415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1020649429751980287385010213 191371768078496303884689415)
          ·
            refine ⟨287057652117744455827034123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191371768078496303884689415 287057652117744455827034123)
            ·
              refine ⟨430586478176616683740551185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 287057652117744455827034123 430586478176616683740551185)
              ·
                refine ⟨322939858632462512805413389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 430586478176616683740551185 322939858632462512805413389)
                ·
                  refine ⟨121102446987173442302030021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322939858632462512805413389 121102446987173442302030021)
                  ·
                    refine ⟨22706708810095020431630629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121102446987173442302030021 22706708810095020431630629)
                    ·
                      refine ⟨4257507901892816330930743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22706708810095020431630629 4257507901892816330930743)
                      ·
                        rfl

theorem cell23_8291467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 4].length) (baseStart_8291467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291467 prefixEnd_8291467 := by exact prefixLift 8291467
  have htrace : WordTrace (prefixWord ++ tailWord_8291467) baseStart_8291467 baseEnd_8291467 := by
    simpa [prefixWord, tailWord_8291467, baseEnd_8291467] using wordTrace_append hprefix tailTrace_8291467
  have hstable : (prefixWord ++ tailWord_8291467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291467).length < 2 ^ (prefixWord ++ tailWord_8291467).sum := by decide
  have hdescent : baseEnd_8291467 < baseStart_8291467 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291484 : List Nat := [2, 2, 3, 2, 1, 2, 1, 1, 1, 4, 4]
def baseStart_8291484 : Nat := 118140960795 + 8291484 * 2 ^ 59
def prefixEnd_8291484 : Nat := 4983230072969 + 3 ^ 40 * 8291484 * 2
def baseEnd_8291484 : Nat := 4257516631063942764418165

theorem tailTrace_8291484 : CollatzResearch.WordTrace tailWord_8291484 prefixEnd_8291484 4257516631063942764418165 := by
  unfold tailWord_8291484
  simp only [CollatzResearch.WordTrace]
  refine ⟨151207632946688507786500753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201610177262251343715334337 151207632946688507786500753)
  ·
    refine ⟨113405724710016380839875565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151207632946688507786500753 113405724710016380839875565)
    ·
      refine ⟨42527146766256142814953337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113405724710016380839875565 42527146766256142814953337)
      ·
        refine ⟨31895360074692107111215003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42527146766256142814953337 31895360074692107111215003)
        ·
          refine ⟨47843040112038160666822505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31895360074692107111215003 47843040112038160666822505)
          ·
            refine ⟨35882280084028620500116879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47843040112038160666822505 35882280084028620500116879)
            ·
              refine ⟨53823420126042930750175319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35882280084028620500116879 53823420126042930750175319)
              ·
                refine ⟨80735130189064396125262979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53823420126042930750175319 80735130189064396125262979)
                ·
                  refine ⟨121102695283596594187894469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80735130189064396125262979 121102695283596594187894469)
                  ·
                    refine ⟨22706755365674361410230213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121102695283596594187894469 22706755365674361410230213)
                    ·
                      refine ⟨4257516631063942764418165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22706755365674361410230213 4257516631063942764418165)
                      ·
                        rfl

theorem cell23_8291484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_8291484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291484 prefixEnd_8291484 := by exact prefixLift 8291484
  have htrace : WordTrace (prefixWord ++ tailWord_8291484) baseStart_8291484 baseEnd_8291484 := by
    simpa [prefixWord, tailWord_8291484, baseEnd_8291484] using wordTrace_append hprefix tailTrace_8291484
  have hstable : (prefixWord ++ tailWord_8291484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291484).length < 2 ^ (prefixWord ++ tailWord_8291484).sum := by decide
  have hdescent : baseEnd_8291484 < baseStart_8291484 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291488 : List Nat := [2, 1, 1, 4, 2, 1, 1, 5, 2, 2, 2]
def baseStart_8291488 : Nat := 118140960795 + 8291488 * 2 ^ 59
def prefixEnd_8291488 : Nat := 4983230072969 + 3 ^ 40 * 8291488 * 2
def baseEnd_8291488 : Nat := 4257518684986560748768147

theorem tailTrace_8291488 : CollatzResearch.WordTrace tailWord_8291488 prefixEnd_8291488 4257518684986560748768147 := by
  unfold tailWord_8291488
  simp only [CollatzResearch.WordTrace]
  refine ⟨151207705892681262128073559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201610274523575016170764745 151207705892681262128073559)
  ·
    refine ⟨226811558839021893192110339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151207705892681262128073559 226811558839021893192110339)
    ·
      refine ⟨340217338258532839788165509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226811558839021893192110339 340217338258532839788165509)
      ·
        refine ⟨63790750923474907460281033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340217338258532839788165509 63790750923474907460281033)
        ·
          refine ⟨47843063192606180595210775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63790750923474907460281033 47843063192606180595210775)
          ·
            refine ⟨71764594788909270892816163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47843063192606180595210775 71764594788909270892816163)
            ·
              refine ⟨107646892183363906339224245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71764594788909270892816163 107646892183363906339224245)
              ·
                refine ⟨10091896142190366219302273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107646892183363906339224245 10091896142190366219302273)
                ·
                  refine ⟨7568922106642774664476705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10091896142190366219302273 7568922106642774664476705)
                  ·
                    refine ⟨5676691579982080998357529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7568922106642774664476705 5676691579982080998357529)
                    ·
                      refine ⟨4257518684986560748768147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5676691579982080998357529 4257518684986560748768147)
                      ·
                        rfl

theorem cell23_8291488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 1, 5, 2, 2, 2].length) (baseStart_8291488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291488 prefixEnd_8291488 := by exact prefixLift 8291488
  have htrace : WordTrace (prefixWord ++ tailWord_8291488) baseStart_8291488 baseEnd_8291488 := by
    simpa [prefixWord, tailWord_8291488, baseEnd_8291488] using wordTrace_append hprefix tailTrace_8291488
  have hstable : (prefixWord ++ tailWord_8291488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291488).length < 2 ^ (prefixWord ++ tailWord_8291488).sum := by decide
  have hdescent : baseEnd_8291488 < baseStart_8291488 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291511 : List Nat := [1, 1, 3, 1, 4, 1, 4, 3, 5]
def baseStart_8291511 : Nat := 118140960795 + 8291511 * 2 ^ 59
def prefixEnd_8291511 : Nat := 4983230072969 + 3 ^ 40 * 8291511 * 2
def baseEnd_8291511 : Nat := 473058943893512684308949

theorem tailTrace_8291511 : CollatzResearch.WordTrace tailWord_8291511 prefixEnd_8291511 473058943893512684308949 := by
  unfold tailWord_8291511
  simp only [CollatzResearch.WordTrace]
  refine ⟨302416250664279199184234387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201610833776186132789489591 302416250664279199184234387)
  ·
    refine ⟨453624375996418798776351581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302416250664279199184234387 453624375996418798776351581)
    ·
      refine ⟨170109140998657049541131843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 453624375996418798776351581 170109140998657049541131843)
      ·
        refine ⟨255163711497985574311697765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170109140998657049541131843 255163711497985574311697765)
        ·
          refine ⟨47843195905872295183443331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 255163711497985574311697765 47843195905872295183443331)
          ·
            refine ⟨71764793858808442775164997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47843195905872295183443331 71764793858808442775164997)
            ·
              refine ⟨13455898848526583020343437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 71764793858808442775164997 13455898848526583020343437)
              ·
                refine ⟨5045962068197468632628789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13455898848526583020343437 5045962068197468632628789)
                ·
                  refine ⟨473058943893512684308949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5045962068197468632628789 473058943893512684308949)
                  ·
                    rfl

theorem cell23_8291511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 3, 5].length) (baseStart_8291511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291511 prefixEnd_8291511 := by exact prefixLift 8291511
  have htrace : WordTrace (prefixWord ++ tailWord_8291511) baseStart_8291511 baseEnd_8291511 := by
    simpa [prefixWord, tailWord_8291511, baseEnd_8291511] using wordTrace_append hprefix tailTrace_8291511
  have hstable : (prefixWord ++ tailWord_8291511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291511).length < 2 ^ (prefixWord ++ tailWord_8291511).sum := by decide
  have hdescent : baseEnd_8291511 < baseStart_8291511 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291547 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 9]
def baseStart_8291547 : Nat := 118140960795 + 8291547 * 2 ^ 59
def prefixEnd_8291547 : Nat := 4983230072969 + 3 ^ 40 * 8291547 * 2
def baseEnd_8291547 : Nat := 4257548980345176017930375

theorem tailTrace_8291547 : CollatzResearch.WordTrace tailWord_8291547 prefixEnd_8291547 4257548980345176017930375 := by
  unfold tailWord_8291547
  simp only [CollatzResearch.WordTrace]
  refine ⟨302417563692148777332544895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201611709128099184888363263 302417563692148777332544895)
  ·
    refine ⟨453626345538223165998817343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302417563692148777332544895 453626345538223165998817343)
    ·
      refine ⟨680439518307334748998226015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453626345538223165998817343 680439518307334748998226015)
      ·
        refine ⟨1020659277461002123497339023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680439518307334748998226015 1020659277461002123497339023)
        ·
          refine ⟨1530988916191503185246008535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1020659277461002123497339023 1530988916191503185246008535)
          ·
            refine ⟨2296483374287254777869012803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1530988916191503185246008535 2296483374287254777869012803)
            ·
              refine ⟨3444725061430882166803519205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2296483374287254777869012803 3444725061430882166803519205)
              ·
                refine ⟨645885949018290406275659851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3444725061430882166803519205 645885949018290406275659851)
                ·
                  refine ⟨968828923527435609413489777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 645885949018290406275659851 968828923527435609413489777)
                  ·
                    refine ⟨726621692645576707060117333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 968828923527435609413489777 726621692645576707060117333)
                    ·
                      refine ⟨4257548980345176017930375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 726621692645576707060117333 4257548980345176017930375)
                      ·
                        rfl

theorem cell23_8291547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 9].length) (baseStart_8291547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291547 prefixEnd_8291547 := by exact prefixLift 8291547
  have htrace : WordTrace (prefixWord ++ tailWord_8291547) baseStart_8291547 baseEnd_8291547 := by
    simpa [prefixWord, tailWord_8291547, baseEnd_8291547] using wordTrace_append hprefix tailTrace_8291547
  have hstable : (prefixWord ++ tailWord_8291547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291547).length < 2 ^ (prefixWord ++ tailWord_8291547).sum := by decide
  have hdescent : baseEnd_8291547 < baseStart_8291547 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291584 : List Nat := [2, 1, 1, 2, 1, 1, 3, 6, 6]
def baseStart_8291584 : Nat := 118140960795 + 8291584 * 2 ^ 59
def prefixEnd_8291584 : Nat := 4983230072969 + 3 ^ 40 * 8291584 * 2
def baseEnd_8291584 : Nat := 473063108792154708129745

theorem tailTrace_8291584 : CollatzResearch.WordTrace tailWord_8291584 prefixEnd_8291584 473063108792154708129745 := by
  unfold tailWord_8291584
  simp only [CollatzResearch.WordTrace]
  refine ⟨151209456596507366325820903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201612608795343155101094537 151209456596507366325820903)
  ·
    refine ⟨226814184894761049488731355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151209456596507366325820903 226814184894761049488731355)
    ·
      refine ⟨340221277342141574233097033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226814184894761049488731355 340221277342141574233097033)
      ·
        refine ⟨255165958006606180674822775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340221277342141574233097033 255165958006606180674822775)
        ·
          refine ⟨382748937009909271012234163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255165958006606180674822775 382748937009909271012234163)
          ·
            refine ⟨574123405514863906518351245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382748937009909271012234163 574123405514863906518351245)
            ·
              refine ⟨215296277068073964944381717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 574123405514863906518351245 215296277068073964944381717)
              ·
                refine ⟨10092012987565967106767893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 215296277068073964944381717 10092012987565967106767893)
                ·
                  refine ⟨473063108792154708129745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10092012987565967106767893 473063108792154708129745)
                  ·
                    rfl

theorem cell23_8291584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 6, 6].length) (baseStart_8291584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291584 prefixEnd_8291584 := by exact prefixLift 8291584
  have htrace : WordTrace (prefixWord ++ tailWord_8291584) baseStart_8291584 baseEnd_8291584 := by
    simpa [prefixWord, tailWord_8291584, baseEnd_8291584] using wordTrace_append hprefix tailTrace_8291584
  have hstable : (prefixWord ++ tailWord_8291584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291584).length < 2 ^ (prefixWord ++ tailWord_8291584).sum := by decide
  have hdescent : baseEnd_8291584 < baseStart_8291584 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291588 : List Nat := [2, 3, 2, 2, 2, 1, 3, 1, 3, 4]
def baseStart_8291588 : Nat := 118140960795 + 8291588 * 2 ^ 59
def prefixEnd_8291588 : Nat := 4983230072969 + 3 ^ 40 * 8291588 * 2
def baseEnd_8291588 : Nat := 1419190011017336785839229

theorem tailTrace_8291588 : CollatzResearch.WordTrace tailWord_8291588 prefixEnd_8291588 1419190011017336785839229 := by
  unfold tailWord_8291588
  simp only [CollatzResearch.WordTrace]
  refine ⟨151209529542500120667393709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201612706056666827556524945 151209529542500120667393709)
  ·
    refine ⟨56703573578437545250272641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151209529542500120667393709 56703573578437545250272641)
    ·
      refine ⟨42527680183828158937704481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56703573578437545250272641 42527680183828158937704481)
      ·
        refine ⟨31895760137871119203278361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42527680183828158937704481 31895760137871119203278361)
        ·
          refine ⟨23921820103403339402458771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31895760137871119203278361 23921820103403339402458771)
          ·
            refine ⟨35882730155105009103688157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23921820103403339402458771 35882730155105009103688157)
            ·
              refine ⟨13456023808164378413883059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35882730155105009103688157 13456023808164378413883059)
              ·
                refine ⟨20184035712246567620824589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13456023808164378413883059 20184035712246567620824589)
                ·
                  refine ⟨7569013392092462857809221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20184035712246567620824589 7569013392092462857809221)
                  ·
                    refine ⟨1419190011017336785839229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7569013392092462857809221 1419190011017336785839229)
                    ·
                      rfl

theorem cell23_8291588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 3, 1, 3, 4].length) (baseStart_8291588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291588 prefixEnd_8291588 := by exact prefixLift 8291588
  have htrace : WordTrace (prefixWord ++ tailWord_8291588) baseStart_8291588 baseEnd_8291588 := by
    simpa [prefixWord, tailWord_8291588, baseEnd_8291588] using wordTrace_append hprefix tailTrace_8291588
  have hstable : (prefixWord ++ tailWord_8291588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291588).length < 2 ^ (prefixWord ++ tailWord_8291588).sum := by decide
  have hdescent : baseEnd_8291588 < baseStart_8291588 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291611 : List Nat := [1, 1, 1, 1, 1, 1, 5, 3, 5, 1, 3]
def baseStart_8291611 : Nat := 118140960795 + 8291611 * 2 ^ 59
def prefixEnd_8291611 : Nat := 4983230072969 + 3 ^ 40 * 8291611 * 2
def baseEnd_8291611 : Nat := 4257581843107063767530081

theorem tailTrace_8291611 : CollatzResearch.WordTrace tailWord_8291611 prefixEnd_8291611 4257581843107063767530081 := by
  unfold tailWord_8291611
  simp only [CollatzResearch.WordTrace]
  refine ⟨302419897963916916262874687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201613265309277944175249791 302419897963916916262874687)
  ·
    refine ⟨453629846945875374394312031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302419897963916916262874687 453629846945875374394312031)
    ·
      refine ⟨680444770418813061591468047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453629846945875374394312031 680444770418813061591468047)
      ·
        refine ⟨1020667155628219592387202071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680444770418813061591468047 1020667155628219592387202071)
        ·
          refine ⟨1531000733442329388580803107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1020667155628219592387202071 1531000733442329388580803107)
          ·
            refine ⟨2296501100163494082871204661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1531000733442329388580803107 2296501100163494082871204661)
            ·
              refine ⟨215296978140327570269175437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2296501100163494082871204661 215296978140327570269175437)
              ·
                refine ⟨80736366802622838850940789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 215296978140327570269175437 80736366802622838850940789)
                ·
                  refine ⟨7569034387745891142275699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80736366802622838850940789 7569034387745891142275699)
                  ·
                    refine ⟨11353551581618836713413549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7569034387745891142275699 11353551581618836713413549)
                    ·
                      refine ⟨4257581843107063767530081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11353551581618836713413549 4257581843107063767530081)
                      ·
                        rfl

theorem cell23_8291611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 3, 5, 1, 3].length) (baseStart_8291611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291611 prefixEnd_8291611 := by exact prefixLift 8291611
  have htrace : WordTrace (prefixWord ++ tailWord_8291611) baseStart_8291611 baseEnd_8291611 := by
    simpa [prefixWord, tailWord_8291611, baseEnd_8291611] using wordTrace_append hprefix tailTrace_8291611
  have hstable : (prefixWord ++ tailWord_8291611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291611).length < 2 ^ (prefixWord ++ tailWord_8291611).sum := by decide
  have hdescent : baseEnd_8291611 < baseStart_8291611 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291651 : List Nat := [1, 1, 1, 3, 1, 3, 1, 2, 2, 6, 2]
def baseStart_8291651 : Nat := 118140960795 + 8291651 * 2 ^ 59
def prefixEnd_8291651 : Nat := 4983230072969 + 3 ^ 40 * 8291651 * 2
def baseEnd_8291651 : Nat := 4257602382333243611029897

theorem tailTrace_8291651 : CollatzResearch.WordTrace tailWord_8291651 prefixEnd_8291651 4257602382333243611029897 := by
  unfold tailWord_8291651
  simp only [CollatzResearch.WordTrace]
  refine ⟨302421356883772003094330807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201614237922514668729553871 302421356883772003094330807)
  ·
    refine ⟨453632035325658004641496211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302421356883772003094330807 453632035325658004641496211)
    ·
      refine ⟨680448052988487006962244317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453632035325658004641496211 680448052988487006962244317)
      ·
        refine ⟨255168019870682627610841619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 680448052988487006962244317 255168019870682627610841619)
        ·
          refine ⟨382752029806023941416262429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255168019870682627610841619 382752029806023941416262429)
          ·
            refine ⟨143532011177258978031098411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382752029806023941416262429 143532011177258978031098411)
            ·
              refine ⟨215298016765888467046647617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143532011177258978031098411 215298016765888467046647617)
              ·
                refine ⟨161473512574416350284985713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215298016765888467046647617 161473512574416350284985713)
                ·
                  refine ⟨121105134430812262713739285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161473512574416350284985713 121105134430812262713739285)
                  ·
                    refine ⟨5676803176444324814706529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 121105134430812262713739285 5676803176444324814706529)
                    ·
                      refine ⟨4257602382333243611029897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5676803176444324814706529 4257602382333243611029897)
                      ·
                        rfl

theorem cell23_8291651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 2, 2, 6, 2].length) (baseStart_8291651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291651 prefixEnd_8291651 := by exact prefixLift 8291651
  have htrace : WordTrace (prefixWord ++ tailWord_8291651) baseStart_8291651 baseEnd_8291651 := by
    simpa [prefixWord, tailWord_8291651, baseEnd_8291651] using wordTrace_append hprefix tailTrace_8291651
  have hstable : (prefixWord ++ tailWord_8291651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291651).length < 2 ^ (prefixWord ++ tailWord_8291651).sum := by decide
  have hdescent : baseEnd_8291651 < baseStart_8291651 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291668 : List Nat := [2, 4, 1, 1, 2, 1, 2, 4, 1, 1, 4]
def baseStart_8291668 : Nat := 118140960795 + 8291668 * 2 ^ 59
def prefixEnd_8291668 : Nat := 4983230072969 + 3 ^ 40 * 8291668 * 2
def baseEnd_8291668 : Nat := 4257611111504370044517319

theorem tailTrace_8291668 : CollatzResearch.WordTrace tailWord_8291668 prefixEnd_8291668 4257611111504370044517319 := by
  unfold tailWord_8291668
  simp only [CollatzResearch.WordTrace]
  refine ⟨151210988462355207498849829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201614651283140276665133105 151210988462355207498849829)
  ·
    refine ⟨28352060336691601406034343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151210988462355207498849829 28352060336691601406034343)
    ·
      refine ⟨42528090505037402109051515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28352060336691601406034343 42528090505037402109051515)
      ·
        refine ⟨63792135757556103163577273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42528090505037402109051515 63792135757556103163577273)
        ·
          refine ⟨47844101818167077372682955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63792135757556103163577273 47844101818167077372682955)
          ·
            refine ⟨71766152727250616059024433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47844101818167077372682955 71766152727250616059024433)
            ·
              refine ⟨53824614545437962044268325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71766152727250616059024433 53824614545437962044268325)
              ·
                refine ⟨10092115227269617883300311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53824614545437962044268325 10092115227269617883300311)
                ·
                  refine ⟨15138172840904426824950467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10092115227269617883300311 15138172840904426824950467)
                  ·
                    refine ⟨22707259261356640237425701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15138172840904426824950467 22707259261356640237425701)
                    ·
                      refine ⟨4257611111504370044517319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22707259261356640237425701 4257611111504370044517319)
                      ·
                        rfl

theorem cell23_8291668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_8291668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291668 prefixEnd_8291668 := by exact prefixLift 8291668
  have htrace : WordTrace (prefixWord ++ tailWord_8291668) baseStart_8291668 baseEnd_8291668 := by
    simpa [prefixWord, tailWord_8291668, baseEnd_8291668] using wordTrace_append hprefix tailTrace_8291668
  have hstable : (prefixWord ++ tailWord_8291668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291668).length < 2 ^ (prefixWord ++ tailWord_8291668).sum := by decide
  have hdescent : baseEnd_8291668 < baseStart_8291668 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291674 : List Nat := [3, 1, 1, 2, 1, 2, 2, 11]
def baseStart_8291674 : Nat := 118140960795 + 8291674 * 2 ^ 59
def prefixEnd_8291674 : Nat := 4983230072969 + 3 ^ 40 * 8291674 * 2
def baseEnd_8291674 : Nat := 157689414532899889668233

theorem tailTrace_8291674 : CollatzResearch.WordTrace tailWord_8291674 prefixEnd_8291674 157689414532899889668233 := by
  unfold tailWord_8291674
  simp only [CollatzResearch.WordTrace]
  refine ⟨75605548940672169505604519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201614797175125785348278717 75605548940672169505604519)
  ·
    refine ⟨113408323411008254258406779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75605548940672169505604519 113408323411008254258406779)
    ·
      refine ⟨170112485116512381387610169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113408323411008254258406779 170112485116512381387610169)
      ·
        refine ⟨127584363837384286040707627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170112485116512381387610169 127584363837384286040707627)
        ·
          refine ⟨191376545756076429061061441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127584363837384286040707627 191376545756076429061061441)
          ·
            refine ⟨143532409317057321795796081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191376545756076429061061441 143532409317057321795796081)
            ·
              refine ⟨107649306987792991346847061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143532409317057321795796081 107649306987792991346847061)
              ·
                refine ⟨157689414532899889668233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 107649306987792991346847061 157689414532899889668233)
                ·
                  rfl

theorem cell23_8291674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 11].length) (baseStart_8291674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291674 prefixEnd_8291674 := by exact prefixLift 8291674
  have htrace : WordTrace (prefixWord ++ tailWord_8291674) baseStart_8291674 baseEnd_8291674 := by
    simpa [prefixWord, tailWord_8291674, baseEnd_8291674] using wordTrace_append hprefix tailTrace_8291674
  have hstable : (prefixWord ++ tailWord_8291674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291674).length < 2 ^ (prefixWord ++ tailWord_8291674).sum := by decide
  have hdescent : baseEnd_8291674 < baseStart_8291674 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291736 : List Nat := [2, 1, 2, 5, 2, 2, 1, 3, 1, 2, 2]
def baseStart_8291736 : Nat := 118140960795 + 8291736 * 2 ^ 59
def prefixEnd_8291736 : Nat := 4983230072969 + 3 ^ 40 * 8291736 * 2
def baseEnd_8291736 : Nat := 4257646028188875778467007

theorem tailTrace_8291736 : CollatzResearch.WordTrace tailWord_8291736 prefixEnd_8291736 4257646028188875778467007 := by
  unfold tailWord_8291736
  simp only [CollatzResearch.WordTrace]
  refine ⟨151212228544232031305587531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201616304725642708407450041 151212228544232031305587531)
  ·
    refine ⟨226818342816348046958381297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151212228544232031305587531 226818342816348046958381297)
    ·
      refine ⟨170113757112261035218785973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226818342816348046958381297 170113757112261035218785973)
      ·
        refine ⟨15948164729274472051761185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 170113757112261035218785973 15948164729274472051761185)
        ·
          refine ⟨11961123546955854038820889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15948164729274472051761185 11961123546955854038820889)
          ·
            refine ⟨8970842660216890529115667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11961123546955854038820889 8970842660216890529115667)
            ·
              refine ⟨13456263990325335793673501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8970842660216890529115667 13456263990325335793673501)
              ·
                refine ⟨5046098996372000922627563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13456263990325335793673501 5046098996372000922627563)
                ·
                  refine ⟨7569148494558001383941345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5046098996372000922627563 7569148494558001383941345)
                  ·
                    refine ⟨5676861370918501037956009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7569148494558001383941345 5676861370918501037956009)
                    ·
                      refine ⟨4257646028188875778467007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5676861370918501037956009 4257646028188875778467007)
                      ·
                        rfl

theorem cell23_8291736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_8291736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291736 prefixEnd_8291736 := by exact prefixLift 8291736
  have htrace : WordTrace (prefixWord ++ tailWord_8291736) baseStart_8291736 baseEnd_8291736 := by
    simpa [prefixWord, tailWord_8291736, baseEnd_8291736] using wordTrace_append hprefix tailTrace_8291736
  have hstable : (prefixWord ++ tailWord_8291736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291736).length < 2 ^ (prefixWord ++ tailWord_8291736).sum := by decide
  have hdescent : baseEnd_8291736 < baseStart_8291736 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291761 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 1, 3, 5]
def baseStart_8291761 : Nat := 118140960795 + 8291761 * 2 ^ 59
def prefixEnd_8291761 : Nat := 4983230072969 + 3 ^ 40 * 8291761 * 2
def baseEnd_8291761 : Nat := 4257658865205238180654391

theorem tailTrace_8291761 : CollatzResearch.WordTrace tailWord_8291761 prefixEnd_8291761 4257658865205238180654391 := by
  unfold tailWord_8291761
  simp only [CollatzResearch.WordTrace]
  refine ⟨302425368913373491880835137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201616912608915661253890091 302425368913373491880835137)
  ·
    refine ⟨226819026685030118910626353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302425368913373491880835137 226819026685030118910626353)
    ·
      refine ⟨170114270013772589182969765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226819026685030118910626353 170114270013772589182969765)
      ·
        refine ⟨31896425627582360471806831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 170114270013772589182969765 31896425627582360471806831)
        ·
          refine ⟨47844638441373540707710247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31896425627582360471806831 47844638441373540707710247)
          ·
            refine ⟨71766957662060311061565371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47844638441373540707710247 71766957662060311061565371)
            ·
              refine ⟨107650436493090466592348057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71766957662060311061565371 107650436493090466592348057)
              ·
                refine ⟨80737827369817849944261043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 107650436493090466592348057 80737827369817849944261043)
                ·
                  refine ⟨121106741054726774916391565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80737827369817849944261043 121106741054726774916391565)
                  ·
                    refine ⟨45415027895522540593646837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121106741054726774916391565 45415027895522540593646837)
                    ·
                      refine ⟨4257658865205238180654391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45415027895522540593646837 4257658865205238180654391)
                      ·
                        rfl

theorem cell23_8291761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_8291761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291761 prefixEnd_8291761 := by exact prefixLift 8291761
  have htrace : WordTrace (prefixWord ++ tailWord_8291761) baseStart_8291761 baseEnd_8291761 := by
    simpa [prefixWord, tailWord_8291761, baseEnd_8291761] using wordTrace_append hprefix tailTrace_8291761
  have hstable : (prefixWord ++ tailWord_8291761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291761).length < 2 ^ (prefixWord ++ tailWord_8291761).sum := by decide
  have hdescent : baseEnd_8291761 < baseStart_8291761 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291769 : List Nat := [1, 2, 1, 4, 4, 2, 2, 1, 2, 1, 3]
def baseStart_8291769 : Nat := 118140960795 + 8291769 * 2 ^ 59
def prefixEnd_8291769 : Nat := 4983230072969 + 3 ^ 40 * 8291769 * 2
def baseEnd_8291769 : Nat := 4257662973050474149354355

theorem tailTrace_8291769 : CollatzResearch.WordTrace tailWord_8291769 prefixEnd_8291769 4257662973050474149354355 := by
  unfold tailWord_8291769
  simp only [CollatzResearch.WordTrace]
  refine ⟨302425660697344509247126361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201617107131563006164750907 302425660697344509247126361)
  ·
    refine ⟨226819245523008381935344771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302425660697344509247126361 226819245523008381935344771)
    ·
      refine ⟨340228868284512572903017157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226819245523008381935344771 340228868284512572903017157)
      ·
        refine ⟨63792912803346107419315717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 340228868284512572903017157 63792912803346107419315717)
        ·
          refine ⟨11961171150627395141121697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63792912803346107419315717 11961171150627395141121697)
          ·
            refine ⟨8970878362970546355841273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11961171150627395141121697 8970878362970546355841273)
            ·
              refine ⟨6728158772227909766880955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8970878362970546355841273 6728158772227909766880955)
              ·
                refine ⟨10092238158341864650321433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6728158772227909766880955 10092238158341864650321433)
                ·
                  refine ⟨7569178618756398487741075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10092238158341864650321433 7569178618756398487741075)
                  ·
                    refine ⟨11353767928134597731611613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7569178618756398487741075 11353767928134597731611613)
                    ·
                      refine ⟨4257662973050474149354355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11353767928134597731611613 4257662973050474149354355)
                      ·
                        rfl

theorem cell23_8291769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 1, 2, 1, 3].length) (baseStart_8291769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291769 prefixEnd_8291769 := by exact prefixLift 8291769
  have htrace : WordTrace (prefixWord ++ tailWord_8291769) baseStart_8291769 baseEnd_8291769 := by
    simpa [prefixWord, tailWord_8291769, baseEnd_8291769] using wordTrace_append hprefix tailTrace_8291769
  have hstable : (prefixWord ++ tailWord_8291769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291769).length < 2 ^ (prefixWord ++ tailWord_8291769).sum := by decide
  have hdescent : baseEnd_8291769 < baseStart_8291769 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291815 : List Nat := [1, 1, 5, 2, 1, 3, 1, 4, 5]
def baseStart_8291815 : Nat := 118140960795 + 8291815 * 2 ^ 59
def prefixEnd_8291815 : Nat := 4983230072969 + 3 ^ 40 * 8291815 * 2
def baseEnd_8291815 : Nat := 473076288128953441042127

theorem tailTrace_8291815 : CollatzResearch.WordTrace tailWord_8291815 prefixEnd_8291815 473076288128953441042127 := by
  unfold tailWord_8291815
  simp only [CollatzResearch.WordTrace]
  refine ⟨302427338455177859103300899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201618225636785239402200599 302427338455177859103300899)
  ·
    refine ⟨453641007682766788654951349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302427338455177859103300899 453641007682766788654951349)
    ·
      refine ⟨42528844470259386436401689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 453641007682766788654951349 42528844470259386436401689)
      ·
        refine ⟨31896633352694539827301267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42528844470259386436401689 31896633352694539827301267)
        ·
          refine ⟨47844950029041809740951901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31896633352694539827301267 47844950029041809740951901)
          ·
            refine ⟨17941856260890678652856963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47844950029041809740951901 17941856260890678652856963)
            ·
              refine ⟨26912784391336017979285445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17941856260890678652856963 26912784391336017979285445)
              ·
                refine ⟨5046147073375503371116021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 26912784391336017979285445 5046147073375503371116021)
                ·
                  refine ⟨473076288128953441042127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5046147073375503371116021 473076288128953441042127)
                  ·
                    rfl

theorem cell23_8291815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 4, 5].length) (baseStart_8291815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291815 prefixEnd_8291815 := by exact prefixLift 8291815
  have htrace : WordTrace (prefixWord ++ tailWord_8291815) baseStart_8291815 baseEnd_8291815 := by
    simpa [prefixWord, tailWord_8291815, baseEnd_8291815] using wordTrace_append hprefix tailTrace_8291815
  have hstable : (prefixWord ++ tailWord_8291815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291815).length < 2 ^ (prefixWord ++ tailWord_8291815).sum := by decide
  have hdescent : baseEnd_8291815 < baseStart_8291815 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291898 : List Nat := [3, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3]
def baseStart_8291898 : Nat := 118140960795 + 8291898 * 2 ^ 59
def prefixEnd_8291898 : Nat := 4983230072969 + 3 ^ 40 * 8291898 * 2
def baseEnd_8291898 : Nat := 4257729212054904144641261

theorem tailTrace_8291898 : CollatzResearch.WordTrace tailWord_8291898 prefixEnd_8291898 4257729212054904144641261 := by
  unfold tailWord_8291898
  simp only [CollatzResearch.WordTrace]
  refine ⟨75607591428469291069643087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201620243809251442852381565 75607591428469291069643087)
  ·
    refine ⟨113411387142703936604464631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75607591428469291069643087 113411387142703936604464631)
    ·
      refine ⟨170117080714055904906696947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113411387142703936604464631 170117080714055904906696947)
      ·
        refine ⟨255175621071083857360045421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170117080714055904906696947 255175621071083857360045421)
        ·
          refine ⟨95690857901656446510017033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255175621071083857360045421 95690857901656446510017033)
          ·
            refine ⟨71768143426242334882512775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95690857901656446510017033 71768143426242334882512775)
            ·
              refine ⟨107652215139363502323769163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71768143426242334882512775 107652215139363502323769163)
              ·
                refine ⟨161478322709045253485653745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107652215139363502323769163 161478322709045253485653745)
                ·
                  refine ⟨121108742031783940114240309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 161478322709045253485653745 121108742031783940114240309)
                  ·
                    refine ⟨11353944565479744385710029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 121108742031783940114240309 11353944565479744385710029)
                    ·
                      refine ⟨4257729212054904144641261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11353944565479744385710029 4257729212054904144641261)
                      ·
                        rfl

theorem cell23_8291898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 1, 2, 5, 3].length) (baseStart_8291898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291898 prefixEnd_8291898 := by exact prefixLift 8291898
  have htrace : WordTrace (prefixWord ++ tailWord_8291898) baseStart_8291898 baseEnd_8291898 := by
    simpa [prefixWord, tailWord_8291898, baseEnd_8291898] using wordTrace_append hprefix tailTrace_8291898
  have hstable : (prefixWord ++ tailWord_8291898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291898).length < 2 ^ (prefixWord ++ tailWord_8291898).sum := by decide
  have hdescent : baseEnd_8291898 < baseStart_8291898 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291918 : List Nat := [4, 1, 1, 1, 1, 2, 1, 2, 5, 5]
def baseStart_8291918 : Nat := 118140960795 + 8291918 * 2 ^ 59
def prefixEnd_8291918 : Nat := 4983230072969 + 3 ^ 40 * 8291918 * 2
def baseEnd_8291918 : Nat := 1419246493889331355463723

theorem tailTrace_8291918 : CollatzResearch.WordTrace tailWord_8291918 prefixEnd_8291918 1419246493889331355463723 := by
  unfold tailWord_8291918
  simp only [CollatzResearch.WordTrace]
  refine ⟨37803886896725588461787551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201620730115869805129533605 37803886896725588461787551)
  ·
    refine ⟨56705830345088382692681327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37803886896725588461787551 56705830345088382692681327)
    ·
      refine ⟨85058745517632574039021991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56705830345088382692681327 85058745517632574039021991)
      ·
        refine ⟨127588118276448861058532987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85058745517632574039021991 127588118276448861058532987)
        ·
          refine ⟨191382177414673291587799481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127588118276448861058532987 191382177414673291587799481)
          ·
            refine ⟨143536633061004968690849611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191382177414673291587799481 143536633061004968690849611)
            ·
              refine ⟨215304949591507453036274417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143536633061004968690849611 215304949591507453036274417)
              ·
                refine ⟨161478712193630589777205813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 215304949591507453036274417 161478712193630589777205813)
                ·
                  refine ⟨15138629268152867791613045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 161478712193630589777205813 15138629268152867791613045)
                  ·
                    refine ⟨1419246493889331355463723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15138629268152867791613045 1419246493889331355463723)
                    ·
                      rfl

theorem cell23_8291918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 2, 5, 5].length) (baseStart_8291918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291918 prefixEnd_8291918 := by exact prefixLift 8291918
  have htrace : WordTrace (prefixWord ++ tailWord_8291918) baseStart_8291918 baseEnd_8291918 := by
    simpa [prefixWord, tailWord_8291918, baseEnd_8291918] using wordTrace_append hprefix tailTrace_8291918
  have hstable : (prefixWord ++ tailWord_8291918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291918).length < 2 ^ (prefixWord ++ tailWord_8291918).sum := by decide
  have hdescent : baseEnd_8291918 < baseStart_8291918 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291948 : List Nat := [2, 2, 1, 1, 3, 1, 1, 5, 1, 6]
def baseStart_8291948 : Nat := 118140960795 + 8291948 * 2 ^ 59
def prefixEnd_8291948 : Nat := 4983230072969 + 3 ^ 40 * 8291948 * 2
def baseEnd_8291948 : Nat := 1419251628695876316338677

theorem tailTrace_8291948 : CollatzResearch.WordTrace tailWord_8291948 prefixEnd_8291948 1419251628695876316338677 := by
  unfold tailWord_8291948
  simp only [CollatzResearch.WordTrace]
  refine ⟨151216094681848011408946249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201621459575797348545261665 151216094681848011408946249)
  ·
    refine ⟨113412071011386008556709687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151216094681848011408946249 113412071011386008556709687)
    ·
      refine ⟨170118106517079012835064531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113412071011386008556709687 170118106517079012835064531)
      ·
        refine ⟨255177159775618519252596797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170118106517079012835064531 255177159775618519252596797)
        ·
          refine ⟨95691434915856944719723799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255177159775618519252596797 95691434915856944719723799)
          ·
            refine ⟨143537152373785417079585699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95691434915856944719723799 143537152373785417079585699)
            ·
              refine ⟨215305728560678125619378549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 143537152373785417079585699 215305728560678125619378549)
              ·
                refine ⟨20184912052563574276816739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 215305728560678125619378549 20184912052563574276816739)
                ·
                  refine ⟨30277368078845361415225109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20184912052563574276816739 30277368078845361415225109)
                  ·
                    refine ⟨1419251628695876316338677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30277368078845361415225109 1419251628695876316338677)
                    ·
                      rfl

theorem cell23_8291948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 6].length) (baseStart_8291948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291948 prefixEnd_8291948 := by exact prefixLift 8291948
  have htrace : WordTrace (prefixWord ++ tailWord_8291948) baseStart_8291948 baseEnd_8291948 := by
    simpa [prefixWord, tailWord_8291948, baseEnd_8291948] using wordTrace_append hprefix tailTrace_8291948
  have hstable : (prefixWord ++ tailWord_8291948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291948).length < 2 ^ (prefixWord ++ tailWord_8291948).sum := by decide
  have hdescent : baseEnd_8291948 < baseStart_8291948 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291952 : List Nat := [2, 1, 1, 1, 6, 3, 1, 2, 1, 5]
def baseStart_8291952 : Nat := 118140960795 + 8291952 * 2 ^ 59
def prefixEnd_8291952 : Nat := 4983230072969 + 3 ^ 40 * 8291952 * 2
def baseEnd_8291952 : Nat := 1419252313336748977788671

theorem tailTrace_8291952 : CollatzResearch.WordTrace tailWord_8291952 prefixEnd_8291952 1419252313336748977788671 := by
  unfold tailWord_8291952
  simp only [CollatzResearch.WordTrace]
  refine ⟨151216167627840765750519055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201621556837121021000692073 151216167627840765750519055)
  ·
    refine ⟨226824251441761148625778583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151216167627840765750519055 226824251441761148625778583)
    ·
      refine ⟨340236377162641722938667875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226824251441761148625778583 340236377162641722938667875)
      ·
        refine ⟨510354565743962584408001813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340236377162641722938667875 510354565743962584408001813)
        ·
          refine ⟨23922870269248246144125085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 510354565743962584408001813 23922870269248246144125085)
          ·
            refine ⟨8971076350968092304046907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23922870269248246144125085 8971076350968092304046907)
            ·
              refine ⟨13456614526452138456070361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8971076350968092304046907 13456614526452138456070361)
              ·
                refine ⟨10092460894839103842052771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13456614526452138456070361 10092460894839103842052771)
                ·
                  refine ⟨15138691342258655763079157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10092460894839103842052771 15138691342258655763079157)
                  ·
                    refine ⟨1419252313336748977788671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15138691342258655763079157 1419252313336748977788671)
                    ·
                      rfl

theorem cell23_8291952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 1, 2, 1, 5].length) (baseStart_8291952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291952 prefixEnd_8291952 := by exact prefixLift 8291952
  have htrace : WordTrace (prefixWord ++ tailWord_8291952) baseStart_8291952 baseEnd_8291952 := by
    simpa [prefixWord, tailWord_8291952, baseEnd_8291952] using wordTrace_append hprefix tailTrace_8291952
  have hstable : (prefixWord ++ tailWord_8291952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291952).length < 2 ^ (prefixWord ++ tailWord_8291952).sum := by decide
  have hdescent : baseEnd_8291952 < baseStart_8291952 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291965 : List Nat := [1, 4, 1, 1, 4, 2, 1, 2, 1, 6]
def baseStart_8291965 : Nat := 118140960795 + 8291965 * 2 ^ 59
def prefixEnd_8291965 : Nat := 4983230072969 + 3 ^ 40 * 8291965 * 2
def baseEnd_8291965 : Nat := 1419254538419585127501151

theorem tailTrace_8291965 : CollatzResearch.WordTrace tailWord_8291965 prefixEnd_8291965 1419254538419585127501151 := by
  unfold tailWord_8291965
  simp only [CollatzResearch.WordTrace]
  refine ⟨302432809404634434721261349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201621872936422956480840899 302432809404634434721261349)
  ·
    refine ⟨56706151763368956510236503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302432809404634434721261349 56706151763368956510236503)
    ·
      refine ⟨85059227645053434765354755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56706151763368956510236503 85059227645053434765354755)
      ·
        refine ⟨127588841467580152148032133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85059227645053434765354755 127588841467580152148032133)
        ·
          refine ⟨23922907775171278527756025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127588841467580152148032133 23922907775171278527756025)
          ·
            refine ⟨17942180831378458895817019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23922907775171278527756025 17942180831378458895817019)
            ·
              refine ⟨26913271247067688343725529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17942180831378458895817019 26913271247067688343725529)
              ·
                refine ⟨20184953435300766257794147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26913271247067688343725529 20184953435300766257794147)
                ·
                  refine ⟨30277430152951149386691221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20184953435300766257794147 30277430152951149386691221)
                  ·
                    refine ⟨1419254538419585127501151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30277430152951149386691221 1419254538419585127501151)
                    ·
                      rfl

theorem cell23_8291965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_8291965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291965 prefixEnd_8291965 := by exact prefixLift 8291965
  have htrace : WordTrace (prefixWord ++ tailWord_8291965) baseStart_8291965 baseEnd_8291965 := by
    simpa [prefixWord, tailWord_8291965, baseEnd_8291965] using wordTrace_append hprefix tailTrace_8291965
  have hstable : (prefixWord ++ tailWord_8291965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291965).length < 2 ^ (prefixWord ++ tailWord_8291965).sum := by decide
  have hdescent : baseEnd_8291965 < baseStart_8291965 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291975 : List Nat := [1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 5]
def baseStart_8291975 : Nat := 118140960795 + 8291975 * 2 ^ 59
def prefixEnd_8291975 : Nat := 4983230072969 + 3 ^ 40 * 8291975 * 2
def baseEnd_8291975 : Nat := 4257768750065300343378407

theorem tailTrace_8291975 : CollatzResearch.WordTrace tailWord_8291975 prefixEnd_8291975 4257768750065300343378407 := by
  unfold tailWord_8291975
  simp only [CollatzResearch.WordTrace]
  refine ⟨302433174134598206429125379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201622116089732137619416919 302433174134598206429125379)
  ·
    refine ⟨453649761201897309643688069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302433174134598206429125379 453649761201897309643688069)
    ·
      refine ⟨85059330225355745558191513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 453649761201897309643688069 85059330225355745558191513)
      ·
        refine ⟨63794497669016809168643635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85059330225355745558191513 63794497669016809168643635)
        ·
          refine ⟨95691746503525213752965453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63794497669016809168643635 95691746503525213752965453)
          ·
            refine ⟨35884404938821955157362045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95691746503525213752965453 35884404938821955157362045)
            ·
              refine ⟨13456651852058233184010767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35884404938821955157362045 13456651852058233184010767)
              ·
                refine ⟨20184977778087349776016151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13456651852058233184010767 20184977778087349776016151)
                ·
                  refine ⟨30277466667131024664024227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20184977778087349776016151 30277466667131024664024227)
                  ·
                    refine ⟨45416200000696536996036341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30277466667131024664024227 45416200000696536996036341)
                    ·
                      refine ⟨4257768750065300343378407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45416200000696536996036341 4257768750065300343378407)
                      ·
                        rfl

theorem cell23_8291975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_8291975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291975 prefixEnd_8291975 := by exact prefixLift 8291975
  have htrace : WordTrace (prefixWord ++ tailWord_8291975) baseStart_8291975 baseEnd_8291975 := by
    simpa [prefixWord, tailWord_8291975, baseEnd_8291975] using wordTrace_append hprefix tailTrace_8291975
  have hstable : (prefixWord ++ tailWord_8291975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291975).length < 2 ^ (prefixWord ++ tailWord_8291975).sum := by decide
  have hdescent : baseEnd_8291975 < baseStart_8291975 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291978 : List Nat := [3, 1, 2, 3, 2, 12]
def baseStart_8291978 : Nat := 118140960795 + 8291978 * 2 ^ 59
def prefixEnd_8291978 : Nat := 4983230072969 + 3 ^ 40 * 8291978 * 2
def baseEnd_8291978 : Nat := 17521688438301497249551

theorem tailTrace_8291978 : CollatzResearch.WordTrace tailWord_8291978 prefixEnd_8291978 17521688438301497249551 := by
  unfold tailWord_8291978
  simp only [CollatzResearch.WordTrace]
  refine ⟨75608320888396834485371147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201622189035724891960989725 75608320888396834485371147)
  ·
    refine ⟨113412481332595251728056721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75608320888396834485371147 113412481332595251728056721)
    ·
      refine ⟨85059360999446438796042541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113412481332595251728056721 85059360999446438796042541)
      ·
        refine ⟨31897260374792414548515953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85059360999446438796042541 31897260374792414548515953)
        ·
          refine ⟨23922945281094310911386965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31897260374792414548515953 23922945281094310911386965)
          ·
            refine ⟨17521688438301497249551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 23922945281094310911386965 17521688438301497249551)
            ·
              rfl

theorem cell23_8291978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 12].length) (baseStart_8291978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291978 prefixEnd_8291978 := by exact prefixLift 8291978
  have htrace : WordTrace (prefixWord ++ tailWord_8291978) baseStart_8291978 baseEnd_8291978 := by
    simpa [prefixWord, tailWord_8291978, baseEnd_8291978] using wordTrace_append hprefix tailTrace_8291978
  have hstable : (prefixWord ++ tailWord_8291978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291978).length < 2 ^ (prefixWord ++ tailWord_8291978).sum := by decide
  have hdescent : baseEnd_8291978 < baseStart_8291978 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8291982 : List Nat := [4, 1, 1, 3, 1, 2, 1, 4, 2, 4]
def baseStart_8291982 : Nat := 118140960795 + 8291982 * 2 ^ 59
def prefixEnd_8291982 : Nat := 4983230072969 + 3 ^ 40 * 8291982 * 2
def baseEnd_8291982 : Nat := 1419257448143293938663625

theorem tailTrace_8291982 : CollatzResearch.WordTrace tailWord_8291982 prefixEnd_8291982 1419257448143293938663625 := by
  unfold tailWord_8291982
  simp only [CollatzResearch.WordTrace]
  refine ⟨37804178680696605828078775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201622286297048564416420133 37804178680696605828078775)
  ·
    refine ⟨56706268021044908742118163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37804178680696605828078775 56706268021044908742118163)
    ·
      refine ⟨85059402031567363113177245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56706268021044908742118163 85059402031567363113177245)
      ·
        refine ⟨31897275761837761167441467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85059402031567363113177245 31897275761837761167441467)
        ·
          refine ⟨47845913642756641751162201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31897275761837761167441467 47845913642756641751162201)
          ·
            refine ⟨35884435232067481313371651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47845913642756641751162201 35884435232067481313371651)
            ·
              refine ⟨53826652848101221970057477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35884435232067481313371651 53826652848101221970057477)
              ·
                refine ⟨10092497409018979119385777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 53826652848101221970057477 10092497409018979119385777)
                ·
                  refine ⟨7569373056764234339539333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10092497409018979119385777 7569373056764234339539333)
                  ·
                    refine ⟨1419257448143293938663625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7569373056764234339539333 1419257448143293938663625)
                    ·
                      rfl

theorem cell23_8291982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 4, 2, 4].length) (baseStart_8291982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8291982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8291982 prefixEnd_8291982 := by exact prefixLift 8291982
  have htrace : WordTrace (prefixWord ++ tailWord_8291982) baseStart_8291982 baseEnd_8291982 := by
    simpa [prefixWord, tailWord_8291982, baseEnd_8291982] using wordTrace_append hprefix tailTrace_8291982
  have hstable : (prefixWord ++ tailWord_8291982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8291982).length < 2 ^ (prefixWord ++ tailWord_8291982).sum := by decide
  have hdescent : baseEnd_8291982 < baseStart_8291982 := by decide
  rcases family_descends (prefixWord ++ tailWord_8291982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292005 : List Nat := [1, 3, 1, 2, 1, 2, 3, 3, 1, 3, 3]
def baseStart_8292005 : Nat := 118140960795 + 8292005 * 2 ^ 59
def prefixEnd_8292005 : Nat := 4983230072969 + 3 ^ 40 * 8292005 * 2
def baseEnd_8292005 : Nat := 4257784154484935226003269

theorem tailTrace_8292005 : CollatzResearch.WordTrace tailWord_8292005 prefixEnd_8292005 4257784154484935226003269 := by
  unfold tailWord_8292005
  simp only [CollatzResearch.WordTrace]
  refine ⟨302434268324489521552717469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201622845549659681035144979 302434268324489521552717469)
  ·
    refine ⟨113412850621683570582269051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302434268324489521552717469 113412850621683570582269051)
    ·
      refine ⟨170119275932525355873403577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113412850621683570582269051 170119275932525355873403577)
      ·
        refine ⟨127589456949394016905052683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170119275932525355873403577 127589456949394016905052683)
        ·
          refine ⟨191384185424091025357579025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127589456949394016905052683 191384185424091025357579025)
          ·
            refine ⟨143538139068068269018184269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 191384185424091025357579025 143538139068068269018184269)
            ·
              refine ⟨53826802150525600881819101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143538139068068269018184269 53826802150525600881819101)
              ·
                refine ⟨20185050806447100330682163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53826802150525600881819101 20185050806447100330682163)
                ·
                  refine ⟨30277576209670650496023245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20185050806447100330682163 30277576209670650496023245)
                  ·
                    refine ⟨11354091078626493936008717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30277576209670650496023245 11354091078626493936008717)
                    ·
                      refine ⟨4257784154484935226003269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11354091078626493936008717 4257784154484935226003269)
                      ·
                        rfl

theorem cell23_8292005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 1, 3, 3].length) (baseStart_8292005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292005 prefixEnd_8292005 := by exact prefixLift 8292005
  have htrace : WordTrace (prefixWord ++ tailWord_8292005) baseStart_8292005 baseEnd_8292005 := by
    simpa [prefixWord, tailWord_8292005, baseEnd_8292005] using wordTrace_append hprefix tailTrace_8292005
  have hstable : (prefixWord ++ tailWord_8292005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292005).length < 2 ^ (prefixWord ++ tailWord_8292005).sum := by decide
  have hdescent : baseEnd_8292005 < baseStart_8292005 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292048 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 5]
def baseStart_8292048 : Nat := 118140960795 + 8292048 * 2 ^ 59
def prefixEnd_8292048 : Nat := 4983230072969 + 3 ^ 40 * 8292048 * 2
def baseEnd_8292048 : Nat := 4257806234153078557765571

theorem tailTrace_8292048 : CollatzResearch.WordTrace tailWord_8292048 prefixEnd_8292048 4257806234153078557765571 := by
  unfold tailWord_8292048
  simp only [CollatzResearch.WordTrace]
  refine ⟨151217918331666869948266399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201623891108889159931021865 151217918331666869948266399)
  ·
    refine ⟨226826877497500304922399599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151217918331666869948266399 226826877497500304922399599)
    ·
      refine ⟨340240316246250457383599399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226826877497500304922399599 340240316246250457383599399)
      ·
        refine ⟨510360474369375686075399099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340240316246250457383599399 510360474369375686075399099)
        ·
          refine ⟨765540711554063529113098649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510360474369375686075399099 765540711554063529113098649)
          ·
            refine ⟨574155533665547646834823987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765540711554063529113098649 574155533665547646834823987)
            ·
              refine ⟨861233300498321470252235981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574155533665547646834823987 861233300498321470252235981)
              ·
                refine ⟨322962487686870551344588493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 861233300498321470252235981 322962487686870551344588493)
                ·
                  refine ⟨121110932882576456754220685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 322962487686870551344588493 121110932882576456754220685)
                  ·
                    refine ⟨45416599830966171282832757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121110932882576456754220685 45416599830966171282832757)
                    ·
                      refine ⟨4257806234153078557765571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45416599830966171282832757 4257806234153078557765571)
                      ·
                        rfl

theorem cell23_8292048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 3, 3, 5].length) (baseStart_8292048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292048 prefixEnd_8292048 := by exact prefixLift 8292048
  have htrace : WordTrace (prefixWord ++ tailWord_8292048) baseStart_8292048 baseEnd_8292048 := by
    simpa [prefixWord, tailWord_8292048, baseEnd_8292048] using wordTrace_append hprefix tailTrace_8292048
  have hstable : (prefixWord ++ tailWord_8292048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292048).length < 2 ^ (prefixWord ++ tailWord_8292048).sum := by decide
  have hdescent : baseEnd_8292048 < baseStart_8292048 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292095 : List Nat := [1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 3]
def baseStart_8292095 : Nat := 118140960795 + 8292095 * 2 ^ 59
def prefixEnd_8292095 : Nat := 4983230072969 + 3 ^ 40 * 8292095 * 2
def baseEnd_8292095 : Nat := 4257830367743839873877855

theorem tailTrace_8292095 : CollatzResearch.WordTrace tailWord_8292095 prefixEnd_8292095 4257830367743839873877855 := by
  unfold tailWord_8292095
  simp only [CollatzResearch.WordTrace]
  refine ⟨302437550894163466923493739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201625033929442311282329159 302437550894163466923493739)
  ·
    refine ⟨453656326341245200385240609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302437550894163466923493739 453656326341245200385240609)
    ·
      refine ⟨340242244755933900288930457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453656326341245200385240609 340242244755933900288930457)
      ·
        refine ⟨255181683566950425216697843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340242244755933900288930457 255181683566950425216697843)
        ·
          refine ⟨382772525350425637825046765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255181683566950425216697843 382772525350425637825046765)
          ·
            refine ⟨143539697006409614184392537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 382772525350425637825046765 143539697006409614184392537)
            ·
              refine ⟨107654772754807210638294403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 143539697006409614184392537 107654772754807210638294403)
              ·
                refine ⟨161482159132210815957441605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 107654772754807210638294403 161482159132210815957441605)
                ·
                  refine ⟨30277904837289527992020301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 161482159132210815957441605 30277904837289527992020301)
                  ·
                    refine ⟨11354214313983572997007613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30277904837289527992020301 11354214313983572997007613)
                    ·
                      refine ⟨4257830367743839873877855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11354214313983572997007613 4257830367743839873877855)
                      ·
                        rfl

theorem cell23_8292095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 3].length) (baseStart_8292095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292095 prefixEnd_8292095 := by exact prefixLift 8292095
  have htrace : WordTrace (prefixWord ++ tailWord_8292095) baseStart_8292095 baseEnd_8292095 := by
    simpa [prefixWord, tailWord_8292095, baseEnd_8292095] using wordTrace_append hprefix tailTrace_8292095
  have hstable : (prefixWord ++ tailWord_8292095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292095).length < 2 ^ (prefixWord ++ tailWord_8292095).sum := by decide
  have hdescent : baseEnd_8292095 < baseStart_8292095 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292132 : List Nat := [2, 3, 1, 3, 2, 1, 1, 3, 2, 5]
def baseStart_8292132 : Nat := 118140960795 + 8292132 * 2 ^ 59
def prefixEnd_8292132 : Nat := 4983230072969 + 3 ^ 40 * 8292132 * 2
def baseEnd_8292132 : Nat := 1419283122176018743038395

theorem tailTrace_8292132 : CollatzResearch.WordTrace tailWord_8292132 prefixEnd_8292132 1419283122176018743038395 := by
  unfold tailWord_8292132
  simp only [CollatzResearch.WordTrace]
  refine ⟨151219450197514711121295325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201625933596686281495060433 151219450197514711121295325)
  ·
    refine ⟨56707293824068016670485747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 151219450197514711121295325 56707293824068016670485747)
    ·
      refine ⟨85060940736102025005728621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56707293824068016670485747 85060940736102025005728621)
      ·
        refine ⟨31897852776038259377148233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85060940736102025005728621 31897852776038259377148233)
        ·
          refine ⟨23923389582028694532861175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31897852776038259377148233 23923389582028694532861175)
          ·
            refine ⟨35885084373043041799291763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23923389582028694532861175 35885084373043041799291763)
            ·
              refine ⟨53827626559564562698937645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35885084373043041799291763 53827626559564562698937645)
              ·
                refine ⟨20185359959836711012101617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53827626559564562698937645 20185359959836711012101617)
                ·
                  refine ⟨15139019969877533259076213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20185359959836711012101617 15139019969877533259076213)
                  ·
                    refine ⟨1419283122176018743038395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15139019969877533259076213 1419283122176018743038395)
                    ·
                      rfl

theorem cell23_8292132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 1, 3, 2, 5].length) (baseStart_8292132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292132 prefixEnd_8292132 := by exact prefixLift 8292132
  have htrace : WordTrace (prefixWord ++ tailWord_8292132) baseStart_8292132 baseEnd_8292132 := by
    simpa [prefixWord, tailWord_8292132, baseEnd_8292132] using wordTrace_append hprefix tailTrace_8292132
  have hstable : (prefixWord ++ tailWord_8292132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292132).length < 2 ^ (prefixWord ++ tailWord_8292132).sum := by decide
  have hdescent : baseEnd_8292132 < baseStart_8292132 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292152 : List Nat := [2, 1, 2, 1, 3, 3, 2, 2, 2, 1, 4]
def baseStart_8292152 : Nat := 118140960795 + 8292152 * 2 ^ 59
def prefixEnd_8292152 : Nat := 4983230072969 + 3 ^ 40 * 8292152 * 2
def baseEnd_8292152 : Nat := 4257859636141146150865093

theorem tailTrace_8292152 : CollatzResearch.WordTrace tailWord_8292152 prefixEnd_8292152 4257859636141146150865093 := by
  unfold tailWord_8292152
  simp only [CollatzResearch.WordTrace]
  refine ⟨151219814927478482829159355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201626419903304643772212473 151219814927478482829159355)
  ·
    refine ⟨226829722391217724243739033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151219814927478482829159355 226829722391217724243739033)
    ·
      refine ⟨170122291793413293182804275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 226829722391217724243739033 170122291793413293182804275)
      ·
        refine ⟨255183437690119939774206413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170122291793413293182804275 255183437690119939774206413)
        ·
          refine ⟨95693789133794977415327405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 255183437690119939774206413 95693789133794977415327405)
          ·
            refine ⟨35885170925173116530747777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 95693789133794977415327405 35885170925173116530747777)
            ·
              refine ⟨26913878193879837398060833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 35885170925173116530747777 26913878193879837398060833)
              ·
                refine ⟨20185408645409878048545625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26913878193879837398060833 20185408645409878048545625)
                ·
                  refine ⟨15139056484057408536409219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20185408645409878048545625 15139056484057408536409219)
                  ·
                    refine ⟨22708584726086112804613829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15139056484057408536409219 22708584726086112804613829)
                    ·
                      refine ⟨4257859636141146150865093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22708584726086112804613829 4257859636141146150865093)
                      ·
                        rfl

theorem cell23_8292152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2, 2, 2, 1, 4].length) (baseStart_8292152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292152 prefixEnd_8292152 := by exact prefixLift 8292152
  have htrace : WordTrace (prefixWord ++ tailWord_8292152) baseStart_8292152 baseEnd_8292152 := by
    simpa [prefixWord, tailWord_8292152, baseEnd_8292152] using wordTrace_append hprefix tailTrace_8292152
  have hstable : (prefixWord ++ tailWord_8292152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292152).length < 2 ^ (prefixWord ++ tailWord_8292152).sum := by decide
  have hdescent : baseEnd_8292152 < baseStart_8292152 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292153 : List Nat := [1, 2, 1, 7, 1, 2, 2, 2, 5]
def baseStart_8292153 : Nat := 118140960795 + 8292153 * 2 ^ 59
def prefixEnd_8292153 : Nat := 4983230072969 + 3 ^ 40 * 8292153 * 2
def baseEnd_8292153 : Nat := 473095572180200071883621

theorem tailTrace_8292153 : CollatzResearch.WordTrace tailWord_8292153 prefixEnd_8292153 473095572180200071883621 := by
  unfold tailWord_8292153
  simp only [CollatzResearch.WordTrace]
  refine ⟨302439666327953342829105113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201626444218635561886070075 302439666327953342829105113)
  ·
    refine ⟨226829749745965007121828835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302439666327953342829105113 226829749745965007121828835)
    ·
      refine ⟨340244624618947510682743253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226829749745965007121828835 340244624618947510682743253)
      ·
        refine ⟨7974483389506582281626795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 340244624618947510682743253 7974483389506582281626795)
        ·
          refine ⟨11961725084259873422440193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7974483389506582281626795 11961725084259873422440193)
          ·
            refine ⟨8971293813194905066830145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11961725084259873422440193 8971293813194905066830145)
            ·
              refine ⟨6728470359896178800122609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8971293813194905066830145 6728470359896178800122609)
              ·
                refine ⟨5046352769922134100091957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6728470359896178800122609 5046352769922134100091957)
                ·
                  refine ⟨473095572180200071883621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5046352769922134100091957 473095572180200071883621)
                  ·
                    rfl

theorem cell23_8292153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 2, 5].length) (baseStart_8292153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292153 prefixEnd_8292153 := by exact prefixLift 8292153
  have htrace : WordTrace (prefixWord ++ tailWord_8292153) baseStart_8292153 baseEnd_8292153 := by
    simpa [prefixWord, tailWord_8292153, baseEnd_8292153] using wordTrace_append hprefix tailTrace_8292153
  have hstable : (prefixWord ++ tailWord_8292153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292153).length < 2 ^ (prefixWord ++ tailWord_8292153).sum := by decide
  have hdescent : baseEnd_8292153 < baseStart_8292153 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292253 : List Nat := [1, 4, 2, 1, 2, 2, 3, 3, 1, 1, 3]
def baseStart_8292253 : Nat := 118140960795 + 8292253 * 2 ^ 59
def prefixEnd_8292253 : Nat := 4983230072969 + 3 ^ 40 * 8292253 * 2
def baseEnd_8292253 : Nat := 4257911497687250255702129

theorem tailTrace_8292253 : CollatzResearch.WordTrace tailWord_8292253 prefixEnd_8292253 4257911497687250255702129 := by
  unfold tailWord_8292253
  simp only [CollatzResearch.WordTrace]
  refine ⟨302443313627591059907745413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201628875751727373271830275 302443313627591059907745413)
  ·
    refine ⟨56708121305173323732702265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302443313627591059907745413 56708121305173323732702265)
    ·
      refine ⟨42531090978879992799526699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56708121305173323732702265 42531090978879992799526699)
      ·
        refine ⟨63796636468319989199290049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42531090978879992799526699 63796636468319989199290049)
        ·
          refine ⟨47847477351239991899467537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63796636468319989199290049 47847477351239991899467537)
          ·
            refine ⟨35885608013429993924600653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 47847477351239991899467537 35885608013429993924600653)
            ·
              refine ⟨13457103005036247721725245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35885608013429993924600653 13457103005036247721725245)
              ·
                refine ⟨5046413626888592895646967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13457103005036247721725245 5046413626888592895646967)
                ·
                  refine ⟨7569620440332889343470451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5046413626888592895646967 7569620440332889343470451)
                  ·
                    refine ⟨11354430660499334015205677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7569620440332889343470451 11354430660499334015205677)
                    ·
                      refine ⟨4257911497687250255702129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11354430660499334015205677 4257911497687250255702129)
                      ·
                        rfl

theorem cell23_8292253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_8292253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292253 prefixEnd_8292253 := by exact prefixLift 8292253
  have htrace : WordTrace (prefixWord ++ tailWord_8292253) baseStart_8292253 baseEnd_8292253 := by
    simpa [prefixWord, tailWord_8292253, baseEnd_8292253] using wordTrace_append hprefix tailTrace_8292253
  have hstable : (prefixWord ++ tailWord_8292253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292253).length < 2 ^ (prefixWord ++ tailWord_8292253).sum := by decide
  have hdescent : baseEnd_8292253 < baseStart_8292253 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292286 : List Nat := [4, 2, 1, 1, 1, 4, 1, 3, 2, 4]
def baseStart_8292286 : Nat := 118140960795 + 8292286 * 2 ^ 59
def prefixEnd_8292286 : Nat := 4983230072969 + 3 ^ 40 * 8292286 * 2
def baseEnd_8292286 : Nat := 1419309480849616208863159

theorem tailTrace_8292286 : CollatzResearch.WordTrace tailWord_8292286 prefixEnd_8292286 1419309480849616208863159 := by
  unfold tailWord_8292286
  simp only [CollatzResearch.WordTrace]
  refine ⟨37805564654558938317962089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201629678157647671029131141 37805564654558938317962089)
  ·
    refine ⟨28354173490919203738471567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 37805564654558938317962089 28354173490919203738471567)
    ·
      refine ⟨42531260236378805607707351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28354173490919203738471567 42531260236378805607707351)
      ·
        refine ⟨63796890354568208411561027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42531260236378805607707351 63796890354568208411561027)
        ·
          refine ⟨95695335531852312617341541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 63796890354568208411561027 95695335531852312617341541)
          ·
            refine ⟨17942875412222308615751539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95695335531852312617341541 17942875412222308615751539)
            ·
              refine ⟨26914313118333462923627309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17942875412222308615751539 26914313118333462923627309)
              ·
                refine ⟨10092867419375048596360241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26914313118333462923627309 10092867419375048596360241)
                ·
                  refine ⟨7569650564531286447270181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10092867419375048596360241 7569650564531286447270181)
                  ·
                    refine ⟨1419309480849616208863159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 7569650564531286447270181 1419309480849616208863159)
                    ·
                      rfl

theorem cell23_8292286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4, 1, 3, 2, 4].length) (baseStart_8292286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292286 prefixEnd_8292286 := by exact prefixLift 8292286
  have htrace : WordTrace (prefixWord ++ tailWord_8292286) baseStart_8292286 baseEnd_8292286 := by
    simpa [prefixWord, tailWord_8292286, baseEnd_8292286] using wordTrace_append hprefix tailTrace_8292286
  have hstable : (prefixWord ++ tailWord_8292286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292286).length < 2 ^ (prefixWord ++ tailWord_8292286).sum := by decide
  have hdescent : baseEnd_8292286 < baseStart_8292286 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292296 : List Nat := [2, 1, 3, 1, 4, 1, 3, 2, 1, 2, 3]
def baseStart_8292296 : Nat := 118140960795 + 8292296 * 2 ^ 59
def prefixEnd_8292296 : Nat := 4983230072969 + 3 ^ 40 * 8292296 * 2
def baseEnd_8292296 : Nat := 4257933577355393587464431

theorem tailTrace_8292296 : CollatzResearch.WordTrace tailWord_8292296 prefixEnd_8292296 4257933577355393587464431 := by
  unfold tailWord_8292296
  simp only [CollatzResearch.WordTrace]
  refine ⟨151222440983217639125780371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201629921310956852167707161 151222440983217639125780371)
  ·
    refine ⟨226833661474826458688670557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151222440983217639125780371 226833661474826458688670557)
    ·
      refine ⟨85062623053059922008251459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 226833661474826458688670557 85062623053059922008251459)
      ·
        refine ⟨127593934579589883012377189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85062623053059922008251459 127593934579589883012377189)
        ·
          refine ⟨23923862733673103064820723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 127593934579589883012377189 23923862733673103064820723)
          ·
            refine ⟨35885794100509654597231085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23923862733673103064820723 35885794100509654597231085)
            ·
              refine ⟨13457172787691120473961657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35885794100509654597231085 13457172787691120473961657)
              ·
                refine ⟨10092879590768340355471243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13457172787691120473961657 10092879590768340355471243)
                ·
                  refine ⟨15139319386152510533206865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10092879590768340355471243 15139319386152510533206865)
                  ·
                    refine ⟨11354489539614382899905149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15139319386152510533206865 11354489539614382899905149)
                    ·
                      refine ⟨4257933577355393587464431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11354489539614382899905149 4257933577355393587464431)
                      ·
                        rfl

theorem cell23_8292296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 2, 1, 2, 3].length) (baseStart_8292296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292296 prefixEnd_8292296 := by exact prefixLift 8292296
  have htrace : WordTrace (prefixWord ++ tailWord_8292296) baseStart_8292296 baseEnd_8292296 := by
    simpa [prefixWord, tailWord_8292296, baseEnd_8292296] using wordTrace_append hprefix tailTrace_8292296
  have hstable : (prefixWord ++ tailWord_8292296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292296).length < 2 ^ (prefixWord ++ tailWord_8292296).sum := by decide
  have hdescent : baseEnd_8292296 < baseStart_8292296 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292306 : List Nat := [3, 2, 2, 3, 2, 1, 1, 2, 1, 2, 4]
def baseStart_8292306 : Nat := 118140960795 + 8292306 * 2 ^ 59
def prefixEnd_8292306 : Nat := 4983230072969 + 3 ^ 40 * 8292306 * 2
def baseEnd_8292306 : Nat := 4257938712161938548339385

theorem tailTrace_8292306 : CollatzResearch.WordTrace tailWord_8292306 prefixEnd_8292306 4257938712161938548339385 := by
  unfold tailWord_8292306
  simp only [CollatzResearch.WordTrace]
  refine ⟨75611311674099762489856193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201630164464266033306283181 75611311674099762489856193)
  ·
    refine ⟨56708483755574821867392145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75611311674099762489856193 56708483755574821867392145)
    ·
      refine ⟨42531362816681116400544109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 56708483755574821867392145 42531362816681116400544109)
      ·
        refine ⟨15949261056255418650204041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42531362816681116400544109 15949261056255418650204041)
        ·
          refine ⟨11961945792191563987653031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15949261056255418650204041 11961945792191563987653031)
          ·
            refine ⟨17942918688287345981479547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11961945792191563987653031 17942918688287345981479547)
            ·
              refine ⟨26914378032431018972219321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17942918688287345981479547 26914378032431018972219321)
              ·
                refine ⟨20185783524323264229164491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26914378032431018972219321 20185783524323264229164491)
                ·
                  refine ⟨30278675286484896343746737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20185783524323264229164491 30278675286484896343746737)
                  ·
                    refine ⟨22709006464863672257810053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30278675286484896343746737 22709006464863672257810053)
                    ·
                      refine ⟨4257938712161938548339385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22709006464863672257810053 4257938712161938548339385)
                      ·
                        rfl

theorem cell23_8292306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_8292306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292306 prefixEnd_8292306 := by exact prefixLift 8292306
  have htrace : WordTrace (prefixWord ++ tailWord_8292306) baseStart_8292306 baseEnd_8292306 := by
    simpa [prefixWord, tailWord_8292306, baseEnd_8292306] using wordTrace_append hprefix tailTrace_8292306
  have hstable : (prefixWord ++ tailWord_8292306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292306).length < 2 ^ (prefixWord ++ tailWord_8292306).sum := by decide
  have hdescent : baseEnd_8292306 < baseStart_8292306 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292309 : List Nat := [1, 3, 2, 3, 2, 1, 1, 1, 3, 3, 3]
def baseStart_8292309 : Nat := 118140960795 + 8292309 * 2 ^ 59
def prefixEnd_8292309 : Nat := 4983230072969 + 3 ^ 40 * 8292309 * 2
def baseEnd_8292309 : Nat := 4257940252603902036601871

theorem tailTrace_8292309 : CollatzResearch.WordTrace tailWord_8292309 prefixEnd_8292309 4257940252603902036601871 := by
  unfold tailWord_8292309
  simp only [CollatzResearch.WordTrace]
  refine ⟨302445356115388181471783981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201630237410258787647855987 302445356115388181471783981)
  ·
    refine ⟨113417008543270568051918993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302445356115388181471783981 113417008543270568051918993)
    ·
      refine ⟨85062756407452926038939245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113417008543270568051918993 85062756407452926038939245)
      ·
        refine ⟨31898533652794847264602217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85062756407452926038939245 31898533652794847264602217)
        ·
          refine ⟨23923900239596135448451663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31898533652794847264602217 23923900239596135448451663)
          ·
            refine ⟨35885850359394203172677495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23923900239596135448451663 35885850359394203172677495)
            ·
              refine ⟨53828775539091304759016243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35885850359394203172677495 53828775539091304759016243)
              ·
                refine ⟨80743163308636957138524365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53828775539091304759016243 80743163308636957138524365)
                ·
                  refine ⟨30278686240738858926946637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 80743163308636957138524365 30278686240738858926946637)
                  ·
                    refine ⟨11354507340277072097604989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30278686240738858926946637 11354507340277072097604989)
                    ·
                      refine ⟨4257940252603902036601871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11354507340277072097604989 4257940252603902036601871)
                      ·
                        rfl

theorem cell23_8292309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_8292309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292309 prefixEnd_8292309 := by exact prefixLift 8292309
  have htrace : WordTrace (prefixWord ++ tailWord_8292309) baseStart_8292309 baseEnd_8292309 := by
    simpa [prefixWord, tailWord_8292309, baseEnd_8292309] using wordTrace_append hprefix tailTrace_8292309
  have hstable : (prefixWord ++ tailWord_8292309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292309).length < 2 ^ (prefixWord ++ tailWord_8292309).sum := by decide
  have hdescent : baseEnd_8292309 < baseStart_8292309 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292310 : List Nat := [5, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4]
def baseStart_8292310 : Nat := 118140960795 + 8292310 * 2 ^ 59
def prefixEnd_8292310 : Nat := 4983230072969 + 3 ^ 40 * 8292310 * 2
def baseEnd_8292310 : Nat := 4257940766084556532689367

theorem tailTrace_8292310 : CollatzResearch.WordTrace tailWord_8292310 prefixEnd_8292310 4257940766084556532689367 := by
  unfold tailWord_8292310
  simp only [CollatzResearch.WordTrace]
  refine ⟨18902837036774034915160649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 201630261725589705761713589 18902837036774034915160649)
  ·
    refine ⟨14177127777580526186370487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 18902837036774034915160649 14177127777580526186370487)
    ·
      refine ⟨21265691666370789279555731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14177127777580526186370487 21265691666370789279555731)
      ·
        refine ⟨31898537499556183919333597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21265691666370789279555731 31898537499556183919333597)
        ·
          refine ⟨11961951562333568969750099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 31898537499556183919333597 11961951562333568969750099)
          ·
            refine ⟨17942927343500353454625149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11961951562333568969750099 17942927343500353454625149)
            ·
              refine ⟨6728597753812632545484431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17942927343500353454625149 6728597753812632545484431)
              ·
                refine ⟨10092896630718948818226647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6728597753812632545484431 10092896630718948818226647)
                ·
                  refine ⟨15139344946078423227339971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10092896630718948818226647 15139344946078423227339971)
                  ·
                    refine ⟨22709017419117634841009957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15139344946078423227339971 22709017419117634841009957)
                    ·
                      refine ⟨4257940766084556532689367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22709017419117634841009957 4257940766084556532689367)
                      ·
                        rfl

theorem cell23_8292310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_8292310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292310 prefixEnd_8292310 := by exact prefixLift 8292310
  have htrace : WordTrace (prefixWord ++ tailWord_8292310) baseStart_8292310 baseEnd_8292310 := by
    simpa [prefixWord, tailWord_8292310, baseEnd_8292310] using wordTrace_append hprefix tailTrace_8292310
  have hstable : (prefixWord ++ tailWord_8292310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292310).length < 2 ^ (prefixWord ++ tailWord_8292310).sum := by decide
  have hdescent : baseEnd_8292310 < baseStart_8292310 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292313 : List Nat := [1, 2, 1, 2, 6, 1, 3, 1, 1, 2, 3]
def baseStart_8292313 : Nat := 118140960795 + 8292313 * 2 ^ 59
def prefixEnd_8292313 : Nat := 4983230072969 + 3 ^ 40 * 8292313 * 2
def baseEnd_8292313 : Nat := 4257942306526520020951853

theorem tailTrace_8292313 : CollatzResearch.WordTrace tailWord_8292313 prefixEnd_8292313 4257942306526520020951853 := by
  unfold tailWord_8292313
  simp only [CollatzResearch.WordTrace]
  refine ⟨302445502007373690154929593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201630334671582460103286395 302445502007373690154929593)
  ·
    refine ⟨226834126505530267616197195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302445502007373690154929593 226834126505530267616197195)
    ·
      refine ⟨340251189758295401424295793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226834126505530267616197195 340251189758295401424295793)
      ·
        refine ⟨255188392318721551068221845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340251189758295401424295793 255188392318721551068221845)
        ·
          refine ⟨11961955889940072706322899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 255188392318721551068221845 11961955889940072706322899)
          ·
            refine ⟨17942933834910109059484349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11961955889940072706322899 17942933834910109059484349)
            ·
              refine ⟨6728600188091290897306631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17942933834910109059484349 6728600188091290897306631)
              ·
                refine ⟨10092900282136936345959947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6728600188091290897306631 10092900282136936345959947)
                ·
                  refine ⟨15139350423205404518939921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10092900282136936345959947 15139350423205404518939921)
                  ·
                    refine ⟨11354512817404053389204941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15139350423205404518939921 11354512817404053389204941)
                    ·
                      refine ⟨4257942306526520020951853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11354512817404053389204941 4257942306526520020951853)
                      ·
                        rfl

theorem cell23_8292313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 3, 1, 1, 2, 3].length) (baseStart_8292313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292313 prefixEnd_8292313 := by exact prefixLift 8292313
  have htrace : WordTrace (prefixWord ++ tailWord_8292313) baseStart_8292313 baseEnd_8292313 := by
    simpa [prefixWord, tailWord_8292313, baseEnd_8292313] using wordTrace_append hprefix tailTrace_8292313
  have hstable : (prefixWord ++ tailWord_8292313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292313).length < 2 ^ (prefixWord ++ tailWord_8292313).sum := by decide
  have hdescent : baseEnd_8292313 < baseStart_8292313 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292316 : List Nat := [2, 2, 6, 1, 1, 11]
def baseStart_8292316 : Nat := 118140960795 + 8292316 * 2 ^ 59
def prefixEnd_8292316 : Nat := 4983230072969 + 3 ^ 40 * 8292316 * 2
def baseEnd_8292316 : Nat := 17522402662421742836273

theorem tailTrace_8292316 : CollatzResearch.WordTrace tailWord_8292316 prefixEnd_8292316 17522402662421742836273 := by
  unfold tailWord_8292316
  simp only [CollatzResearch.WordTrace]
  refine ⟨151222805713181410833644401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201630407617575214444859201 151222805713181410833644401)
  ·
    refine ⟨113417104284886058125233301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151222805713181410833644401 113417104284886058125233301)
    ·
      refine ⟨5316426763354033974620311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 113417104284886058125233301 5316426763354033974620311)
      ·
        refine ⟨7974640145031050961930467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5316426763354033974620311 7974640145031050961930467)
        ·
          refine ⟨11961960217546576442895701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7974640145031050961930467 11961960217546576442895701)
          ·
            refine ⟨17522402662421742836273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 11961960217546576442895701 17522402662421742836273)
            ·
              rfl

theorem cell23_8292316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 11].length) (baseStart_8292316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292316 prefixEnd_8292316 := by exact prefixLift 8292316
  have htrace : WordTrace (prefixWord ++ tailWord_8292316) baseStart_8292316 baseEnd_8292316 := by
    simpa [prefixWord, tailWord_8292316, baseEnd_8292316] using wordTrace_append hprefix tailTrace_8292316
  have hstable : (prefixWord ++ tailWord_8292316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292316).length < 2 ^ (prefixWord ++ tailWord_8292316).sum := by decide
  have hdescent : baseEnd_8292316 < baseStart_8292316 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292333 : List Nat := [1, 5, 1, 4, 2, 1, 1, 8]
def baseStart_8292333 : Nat := 118140960795 + 8292333 * 2 ^ 59
def prefixEnd_8292333 : Nat := 4983230072969 + 3 ^ 40 * 8292333 * 2
def baseEnd_8292333 : Nat := 157701947264429997877843

theorem tailTrace_8292333 : CollatzResearch.WordTrace tailWord_8292333 prefixEnd_8292333 157701947264429997877843 := by
  unfold tailWord_8292333
  simp only [CollatzResearch.WordTrace]
  refine ⟨302446231467301233570657653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201630820978200822380438435 302446231467301233570657653)
  ·
    refine ⟨28354334200059490647249155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 302446231467301233570657653 28354334200059490647249155)
    ·
      refine ⟨42531501300089235970873733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28354334200059490647249155 42531501300089235970873733)
      ·
        refine ⟨7974656493766731744538825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42531501300089235970873733 7974656493766731744538825)
        ·
          refine ⟨5980992370325048808404119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7974656493766731744538825 5980992370325048808404119)
          ·
            refine ⟨8971488555487573212606179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5980992370325048808404119 8971488555487573212606179)
            ·
              refine ⟨13457232833231359818909269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8971488555487573212606179 13457232833231359818909269)
              ·
                refine ⟨157701947264429997877843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13457232833231359818909269 157701947264429997877843)
                ·
                  rfl

theorem cell23_8292333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 2, 1, 1, 8].length) (baseStart_8292333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292333 prefixEnd_8292333 := by exact prefixLift 8292333
  have htrace : WordTrace (prefixWord ++ tailWord_8292333) baseStart_8292333 baseEnd_8292333 := by
    simpa [prefixWord, tailWord_8292333, baseEnd_8292333] using wordTrace_append hprefix tailTrace_8292333
  have hstable : (prefixWord ++ tailWord_8292333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292333).length < 2 ^ (prefixWord ++ tailWord_8292333).sum := by decide
  have hdescent : baseEnd_8292333 < baseStart_8292333 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292352 : List Nat := [2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 5]
def baseStart_8292352 : Nat := 118140960795 + 8292352 * 2 ^ 59
def prefixEnd_8292352 : Nat := 4983230072969 + 3 ^ 40 * 8292352 * 2
def baseEnd_8292352 : Nat := 4257962332272045368364173

theorem tailTrace_8292352 : CollatzResearch.WordTrace tailWord_8292352 prefixEnd_8292352 4257962332272045368364173 := by
  unfold tailWord_8292352
  simp only [CollatzResearch.WordTrace]
  refine ⟨151223462227116199907799655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201631282969488266543732873 151223462227116199907799655)
  ·
    refine ⟨226835193340674299861699483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151223462227116199907799655 226835193340674299861699483)
    ·
      refine ⟨340252790011011449792549225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226835193340674299861699483 340252790011011449792549225)
      ·
        refine ⟨255189592508258587344411919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 340252790011011449792549225 255189592508258587344411919)
        ·
          refine ⟨382784388762387881016617879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 255189592508258587344411919 382784388762387881016617879)
          ·
            refine ⟨574176583143581821524926819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 382784388762387881016617879 574176583143581821524926819)
            ·
              refine ⟨861264874715372732287390229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 574176583143581821524926819 861264874715372732287390229)
              ·
                refine ⟨40371791002283096825971417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 861264874715372732287390229 40371791002283096825971417)
                ·
                  refine ⟨30278843251712322619478563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40371791002283096825971417 30278843251712322619478563)
                  ·
                    refine ⟨45418264877568483929217845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30278843251712322619478563 45418264877568483929217845)
                    ·
                      refine ⟨4257962332272045368364173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45418264877568483929217845 4257962332272045368364173)
                      ·
                        rfl

theorem cell23_8292352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 5].length) (baseStart_8292352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292352 prefixEnd_8292352 := by exact prefixLift 8292352
  have htrace : WordTrace (prefixWord ++ tailWord_8292352) baseStart_8292352 baseEnd_8292352 := by
    simpa [prefixWord, tailWord_8292352, baseEnd_8292352] using wordTrace_append hprefix tailTrace_8292352
  have hstable : (prefixWord ++ tailWord_8292352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292352).length < 2 ^ (prefixWord ++ tailWord_8292352).sum := by decide
  have hdescent : baseEnd_8292352 < baseStart_8292352 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292366 : List Nat := [4, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2]
def baseStart_8292366 : Nat := 118140960795 + 8292366 * 2 ^ 59
def prefixEnd_8292366 : Nat := 4983230072969 + 3 ^ 40 * 8292366 * 2
def baseEnd_8292366 : Nat := 4257969521001208313589109

theorem tailTrace_8292366 : CollatzResearch.WordTrace tailWord_8292366 prefixEnd_8292366 4257969521001208313589109 := by
  unfold tailWord_8292366
  simp only [CollatzResearch.WordTrace]
  refine ⟨37805929384522710025826119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 201631623384121120137739301 37805929384522710025826119)
  ·
    refine ⟨56708894076784065038739179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 37805929384522710025826119 56708894076784065038739179)
    ·
      refine ⟨85063341115176097558108769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56708894076784065038739179 85063341115176097558108769)
      ·
        refine ⟨63797505836382073168581577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85063341115176097558108769 63797505836382073168581577)
        ·
          refine ⟨47848129377286554876436183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63797505836382073168581577 47848129377286554876436183)
          ·
            refine ⟨71772194065929832314654275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47848129377286554876436183 71772194065929832314654275)
            ·
              refine ⟨107658291098894748471981413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 71772194065929832314654275 107658291098894748471981413)
              ·
                refine ⟨20185929581042765338496515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107658291098894748471981413 20185929581042765338496515)
                ·
                  refine ⟨30278894371564148007744773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20185929581042765338496515 30278894371564148007744773)
                  ·
                    refine ⟨5677292694668277751452145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30278894371564148007744773 5677292694668277751452145)
                    ·
                      refine ⟨4257969521001208313589109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5677292694668277751452145 4257969521001208313589109)
                      ·
                        rfl

theorem cell23_8292366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2].length) (baseStart_8292366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292366 prefixEnd_8292366 := by exact prefixLift 8292366
  have htrace : WordTrace (prefixWord ++ tailWord_8292366) baseStart_8292366 baseEnd_8292366 := by
    simpa [prefixWord, tailWord_8292366, baseEnd_8292366] using wordTrace_append hprefix tailTrace_8292366
  have hstable : (prefixWord ++ tailWord_8292366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292366).length < 2 ^ (prefixWord ++ tailWord_8292366).sum := by decide
  have hdescent : baseEnd_8292366 < baseStart_8292366 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292389 : List Nat := [1, 3, 1, 2, 2, 4, 2, 1, 7]
def baseStart_8292389 : Nat := 118140960795 + 8292389 * 2 ^ 59
def prefixEnd_8292389 : Nat := 4983230072969 + 3 ^ 40 * 8292389 * 2
def baseEnd_8292389 : Nat := 473109036784029080400167

theorem tailTrace_8292389 : CollatzResearch.WordTrace tailWord_8292389 prefixEnd_8292389 473109036784029080400167 := by
  unfold tailWord_8292389
  simp only [CollatzResearch.WordTrace]
  refine ⟨302448273955098355134696221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201632182636732236756464147 302448273955098355134696221)
  ·
    refine ⟨113418102733161883175511083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302448273955098355134696221 113418102733161883175511083)
    ·
      refine ⟨170127154099742824763266625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 113418102733161883175511083 170127154099742824763266625)
      ·
        refine ⟨127595365574807118572449969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170127154099742824763266625 127595365574807118572449969)
        ·
          refine ⟨95696524181105338929337477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127595365574807118572449969 95696524181105338929337477)
          ·
            refine ⟨17943098283957251049250777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 95696524181105338929337477 17943098283957251049250777)
            ·
              refine ⟨13457323712967938286938083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17943098283957251049250777 13457323712967938286938083)
              ·
                refine ⟨20185985569451907430407125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13457323712967938286938083 20185985569451907430407125)
                ·
                  refine ⟨473109036784029080400167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20185985569451907430407125 473109036784029080400167)
                  ·
                    rfl

theorem cell23_8292389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 1, 7].length) (baseStart_8292389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292389 prefixEnd_8292389 := by exact prefixLift 8292389
  have htrace : WordTrace (prefixWord ++ tailWord_8292389) baseStart_8292389 baseEnd_8292389 := by
    simpa [prefixWord, tailWord_8292389, baseEnd_8292389] using wordTrace_append hprefix tailTrace_8292389
  have hstable : (prefixWord ++ tailWord_8292389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292389).length < 2 ^ (prefixWord ++ tailWord_8292389).sum := by decide
  have hdescent : baseEnd_8292389 < baseStart_8292389 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292400 : List Nat := [2, 1, 1, 1, 2, 6, 3, 1, 2, 2, 2]
def baseStart_8292400 : Nat := 118140960795 + 8292400 * 2 ^ 59
def prefixEnd_8292400 : Nat := 4983230072969 + 3 ^ 40 * 8292400 * 2
def baseEnd_8292400 : Nat := 4257986979343461180563953

theorem tailTrace_8292400 : CollatzResearch.WordTrace tailWord_8292400 prefixEnd_8292400 4257986979343461180563953 := by
  unfold tailWord_8292400
  simp only [CollatzResearch.WordTrace]
  refine ⟨151224337579029252006673327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201632450105372336008897769 151224337579029252006673327)
  ·
    refine ⟨226836506368543878010009991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151224337579029252006673327 226836506368543878010009991)
    ·
      refine ⟨340254759552815817015014987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226836506368543878010009991 340254759552815817015014987)
      ·
        refine ⟨510382139329223725522522481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340254759552815817015014987 510382139329223725522522481)
        ·
          refine ⟨382786604496917794141891861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 510382139329223725522522481 382786604496917794141891861)
          ·
            refine ⟨17943122085793021600401181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 382786604496917794141891861 17943122085793021600401181)
            ·
              refine ⟨6728670782172383100150443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17943122085793021600401181 6728670782172383100150443)
              ·
                refine ⟨10093006173258574650225665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6728670782172383100150443 10093006173258574650225665)
                ·
                  refine ⟨7569754629943930987669249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10093006173258574650225665 7569754629943930987669249)
                  ·
                    refine ⟨5677315972457948240751937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7569754629943930987669249 5677315972457948240751937)
                    ·
                      refine ⟨4257986979343461180563953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5677315972457948240751937 4257986979343461180563953)
                      ·
                        rfl

theorem cell23_8292400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 3, 1, 2, 2, 2].length) (baseStart_8292400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292400 prefixEnd_8292400 := by exact prefixLift 8292400
  have htrace : WordTrace (prefixWord ++ tailWord_8292400) baseStart_8292400 baseEnd_8292400 := by
    simpa [prefixWord, tailWord_8292400, baseEnd_8292400] using wordTrace_append hprefix tailTrace_8292400
  have hstable : (prefixWord ++ tailWord_8292400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292400).length < 2 ^ (prefixWord ++ tailWord_8292400).sum := by decide
  have hdescent : baseEnd_8292400 < baseStart_8292400 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292439 : List Nat := [1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 4]
def baseStart_8292439 : Nat := 118140960795 + 8292439 * 2 ^ 59
def prefixEnd_8292439 : Nat := 4983230072969 + 3 ^ 40 * 8292439 * 2
def baseEnd_8292439 : Nat := 4258007005088986527976273

theorem tailTrace_8292439 : CollatzResearch.WordTrace tailWord_8292439 prefixEnd_8292439 4258007005088986527976273 := by
  unfold tailWord_8292439
  simp only [CollatzResearch.WordTrace]
  refine ⟨302450097604917213674016371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201633398403278142449344247 302450097604917213674016371)
  ·
    refine ⟨453675146407375820511024557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302450097604917213674016371 453675146407375820511024557)
    ·
      refine ⟨170128179902765932691634209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 453675146407375820511024557 170128179902765932691634209)
      ·
        refine ⟨127596134927074449518725657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 170128179902765932691634209 127596134927074449518725657)
        ·
          refine ⟨95697101195305837139044243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127596134927074449518725657 95697101195305837139044243)
          ·
            refine ⟨143545651792958755708566365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 95697101195305837139044243 143545651792958755708566365)
            ·
              refine ⟨53829619422359533390712387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 143545651792958755708566365 53829619422359533390712387)
              ·
                refine ⟨80744429133539300086068581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53829619422359533390712387 80744429133539300086068581)
                ·
                  refine ⟨15139580462538618766137859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 80744429133539300086068581 15139580462538618766137859)
                  ·
                    refine ⟨22709370693807928149206789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15139580462538618766137859 22709370693807928149206789)
                    ·
                      refine ⟨4258007005088986527976273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22709370693807928149206789 4258007005088986527976273)
                      ·
                        rfl

theorem cell23_8292439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_8292439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292439 prefixEnd_8292439 := by exact prefixLift 8292439
  have htrace : WordTrace (prefixWord ++ tailWord_8292439) baseStart_8292439 baseEnd_8292439 := by
    simpa [prefixWord, tailWord_8292439, baseEnd_8292439] using wordTrace_append hprefix tailTrace_8292439
  have hstable : (prefixWord ++ tailWord_8292439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292439).length < 2 ^ (prefixWord ++ tailWord_8292439).sum := by decide
  have hdescent : baseEnd_8292439 < baseStart_8292439 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292476 : List Nat := [2, 2, 2, 1, 1, 4, 1, 3, 2, 2, 3]
def baseStart_8292476 : Nat := 118140960795 + 8292476 * 2 ^ 59
def prefixEnd_8292476 : Nat := 4983230072969 + 3 ^ 40 * 8292476 * 2
def baseEnd_8292476 : Nat := 4258026003873202883213603

theorem tailTrace_8292476 : CollatzResearch.WordTrace tailWord_8292476 prefixEnd_8292476 4258026003873202883213603 := by
  unfold tailWord_8292476
  simp only [CollatzResearch.WordTrace]
  refine ⟨151225723552891584496556641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201634298070522112662075521 151225723552891584496556641)
  ·
    refine ⟨113419292664668688372417481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151225723552891584496556641 113419292664668688372417481)
    ·
      refine ⟨85064469498501516279313111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113419292664668688372417481 85064469498501516279313111)
      ·
        refine ⟨127596704247752274418969667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85064469498501516279313111 127596704247752274418969667)
        ·
          refine ⟨191395056371628411628454501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127596704247752274418969667 191395056371628411628454501)
          ·
            refine ⟨35886573069680327180335219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 191395056371628411628454501 35886573069680327180335219)
            ·
              refine ⟨53829859604520490770502829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35886573069680327180335219 53829859604520490770502829)
              ·
                refine ⟨20186197351695184038938561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 53829859604520490770502829 20186197351695184038938561)
                ·
                  refine ⟨15139648013771388029203921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20186197351695184038938561 15139648013771388029203921)
                  ·
                    refine ⟨11354736010328541021902941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15139648013771388029203921 11354736010328541021902941)
                    ·
                      refine ⟨4258026003873202883213603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11354736010328541021902941 4258026003873202883213603)
                      ·
                        rfl

theorem cell23_8292476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 3, 2, 2, 3].length) (baseStart_8292476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292476 prefixEnd_8292476 := by exact prefixLift 8292476
  have htrace : WordTrace (prefixWord ++ tailWord_8292476) baseStart_8292476 baseEnd_8292476 := by
    simpa [prefixWord, tailWord_8292476, baseEnd_8292476] using wordTrace_append hprefix tailTrace_8292476
  have hstable : (prefixWord ++ tailWord_8292476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292476).length < 2 ^ (prefixWord ++ tailWord_8292476).sum := by decide
  have hdescent : baseEnd_8292476 < baseStart_8292476 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292539 : List Nat := [1, 1, 1, 1, 1, 2, 5, 4, 1, 6]
def baseStart_8292539 : Nat := 118140960795 + 8292539 * 2 ^ 59
def prefixEnd_8292539 : Nat := 4983230072969 + 3 ^ 40 * 8292539 * 2
def baseEnd_8292539 : Nat := 1419352784384812045575271

theorem tailTrace_8292539 : CollatzResearch.WordTrace tailWord_8292539 prefixEnd_8292539 1419352784384812045575271 := by
  unfold tailWord_8292539
  simp only [CollatzResearch.WordTrace]
  refine ⟨302453744904554930752656671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201635829936369953835104447 302453744904554930752656671)
  ·
    refine ⟨453680617356832396128985007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302453744904554930752656671 453680617356832396128985007)
    ·
      refine ⟨680520926035248594193477511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453680617356832396128985007 680520926035248594193477511)
      ·
        refine ⟨1020781389052872891290216267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 680520926035248594193477511 1020781389052872891290216267)
        ·
          refine ⟨1531172083579309336935324401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1020781389052872891290216267 1531172083579309336935324401)
          ·
            refine ⟨1148379062684482002701493301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1531172083579309336935324401 1148379062684482002701493301)
            ·
              refine ⟨107660537126670187753264997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1148379062684482002701493301 107660537126670187753264997)
              ·
                refine ⟨20186350711250660203737187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 107660537126670187753264997 20186350711250660203737187)
                ·
                  refine ⟨30279526066875990305605781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20186350711250660203737187 30279526066875990305605781)
                  ·
                    refine ⟨1419352784384812045575271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30279526066875990305605781 1419352784384812045575271)
                    ·
                      rfl

theorem cell23_8292539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 5, 4, 1, 6].length) (baseStart_8292539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292539 prefixEnd_8292539 := by exact prefixLift 8292539
  have htrace : WordTrace (prefixWord ++ tailWord_8292539) baseStart_8292539 baseEnd_8292539 := by
    simpa [prefixWord, tailWord_8292539, baseEnd_8292539] using wordTrace_append hprefix tailTrace_8292539
  have hstable : (prefixWord ++ tailWord_8292539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292539).length < 2 ^ (prefixWord ++ tailWord_8292539).sum := by decide
  have hdescent : baseEnd_8292539 < baseStart_8292539 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292559 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 6]
def baseStart_8292559 : Nat := 118140960795 + 8292559 * 2 ^ 59
def prefixEnd_8292559 : Nat := 4983230072969 + 3 ^ 40 * 8292559 * 2
def baseEnd_8292559 : Nat := 4258068622767526058475721

theorem tailTrace_8292559 : CollatzResearch.WordTrace tailWord_8292559 prefixEnd_8292559 4258068622767526058475721 := by
  unfold tailWord_8292559
  simp only [CollatzResearch.WordTrace]
  refine ⟨302454474364482474168384731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201636316242988316112256487 302454474364482474168384731)
  ·
    refine ⟨453681711546723711252577097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302454474364482474168384731 453681711546723711252577097)
    ·
      refine ⟨340261283660042783439432823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453681711546723711252577097 340261283660042783439432823)
      ·
        refine ⟨510391925490064175159149235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340261283660042783439432823 510391925490064175159149235)
        ·
          refine ⟨765587888235096262738723853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510391925490064175159149235 765587888235096262738723853)
          ·
            refine ⟨287095458088161098527021445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 765587888235096262738723853 287095458088161098527021445)
            ·
              refine ⟨53830398391530205973816521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 287095458088161098527021445 53830398391530205973816521)
              ·
                refine ⟨40372798793647654480362391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53830398391530205973816521 40372798793647654480362391)
                ·
                  refine ⟨60559198190471481720543587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40372798793647654480362391 60559198190471481720543587)
                  ·
                    refine ⟨90838797285707222580815381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 60559198190471481720543587 90838797285707222580815381)
                    ·
                      refine ⟨4258068622767526058475721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 90838797285707222580815381 4258068622767526058475721)
                      ·
                        rfl

theorem cell23_8292559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 1, 1, 6].length) (baseStart_8292559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292559 prefixEnd_8292559 := by exact prefixLift 8292559
  have htrace : WordTrace (prefixWord ++ tailWord_8292559) baseStart_8292559 baseEnd_8292559 := by
    simpa [prefixWord, tailWord_8292559, baseEnd_8292559] using wordTrace_append hprefix tailTrace_8292559
  have hstable : (prefixWord ++ tailWord_8292559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292559).length < 2 ^ (prefixWord ++ tailWord_8292559).sum := by decide
  have hdescent : baseEnd_8292559 < baseStart_8292559 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292573 : List Nat := [1, 4, 3, 2, 1, 1, 3, 1, 1, 6]
def baseStart_8292573 : Nat := 118140960795 + 8292573 * 2 ^ 59
def prefixEnd_8292573 : Nat := 4983230072969 + 3 ^ 40 * 8292573 * 2
def baseEnd_8292573 : Nat := 1419358603832229667900219

theorem tailTrace_8292573 : CollatzResearch.WordTrace tailWord_8292573 prefixEnd_8292573 1419358603832229667900219 := by
  unfold tailWord_8292573
  simp only [CollatzResearch.WordTrace]
  refine ⟨302454984986431754559394373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201636656657621169706262915 302454984986431754559394373)
  ·
    refine ⟨56710309684955953979886445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302454984986431754559394373 56710309684955953979886445)
    ·
      refine ⟨21266366131858482742457417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 56710309684955953979886445 21266366131858482742457417)
      ·
        refine ⟨15949774598893862056843063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21266366131858482742457417 15949774598893862056843063)
        ·
          refine ⟨23924661898340793085264595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15949774598893862056843063 23924661898340793085264595)
          ·
            refine ⟨35886992847511189627896893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23924661898340793085264595 35886992847511189627896893)
            ·
              refine ⟨13457622317816696110461335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35886992847511189627896893 13457622317816696110461335)
              ·
                refine ⟨20186433476725044165692003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13457622317816696110461335 20186433476725044165692003)
                ·
                  refine ⟨30279650215087566248538005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20186433476725044165692003 30279650215087566248538005)
                  ·
                    refine ⟨1419358603832229667900219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 30279650215087566248538005 1419358603832229667900219)
                    ·
                      rfl

theorem cell23_8292573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_8292573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292573 prefixEnd_8292573 := by exact prefixLift 8292573
  have htrace : WordTrace (prefixWord ++ tailWord_8292573) baseStart_8292573 baseEnd_8292573 := by
    simpa [prefixWord, tailWord_8292573, baseEnd_8292573] using wordTrace_append hprefix tailTrace_8292573
  have hstable : (prefixWord ++ tailWord_8292573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292573).length < 2 ^ (prefixWord ++ tailWord_8292573).sum := by decide
  have hdescent : baseEnd_8292573 < baseStart_8292573 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292640 : List Nat := [2, 1, 1, 5, 2, 2, 1, 1, 3, 3, 2]
def baseStart_8292640 : Nat := 118140960795 + 8292640 * 2 ^ 59
def prefixEnd_8292640 : Nat := 4983230072969 + 3 ^ 40 * 8292640 * 2
def baseEnd_8292640 : Nat := 4258110214700540241562849

theorem tailTrace_8292640 : CollatzResearch.WordTrace tailWord_8292640 prefixEnd_8292640 4258110214700540241562849 := by
  unfold tailWord_8292640
  simp only [CollatzResearch.WordTrace]
  refine ⟨151228714338594512501041687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201638285784792683334722249 151228714338594512501041687)
  ·
    refine ⟨226843071507891768751562531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151228714338594512501041687 226843071507891768751562531)
    ·
      refine ⟨340264607261837653127343797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226843071507891768751562531 340264607261837653127343797)
      ·
        refine ⟨31899806930797279980688481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 340264607261837653127343797 31899806930797279980688481)
        ·
          refine ⟨23924855198097959985516361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31899806930797279980688481 23924855198097959985516361)
          ·
            refine ⟨17943641398573469989137271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23924855198097959985516361 17943641398573469989137271)
            ·
              refine ⟨26915462097860204983705907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17943641398573469989137271 26915462097860204983705907)
              ·
                refine ⟨40373193146790307475558861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26915462097860204983705907 40373193146790307475558861)
                ·
                  refine ⟨15139947430046365303334573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40373193146790307475558861 15139947430046365303334573)
                  ·
                    refine ⟨5677480286267386988750465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15139947430046365303334573 5677480286267386988750465)
                    ·
                      refine ⟨4258110214700540241562849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5677480286267386988750465 4258110214700540241562849)
                      ·
                        rfl

theorem cell23_8292640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_8292640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292640 prefixEnd_8292640 := by exact prefixLift 8292640
  have htrace : WordTrace (prefixWord ++ tailWord_8292640) baseStart_8292640 baseEnd_8292640 := by
    simpa [prefixWord, tailWord_8292640, baseEnd_8292640] using wordTrace_append hprefix tailTrace_8292640
  have hstable : (prefixWord ++ tailWord_8292640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292640).length < 2 ^ (prefixWord ++ tailWord_8292640).sum := by decide
  have hdescent : baseEnd_8292640 < baseStart_8292640 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292649 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 10]
def baseStart_8292649 : Nat := 118140960795 + 8292649 * 2 ^ 59
def prefixEnd_8292649 : Nat := 4983230072969 + 3 ^ 40 * 8292649 * 2
def baseEnd_8292649 : Nat := 4258114836026430706350307

theorem tailTrace_8292649 : CollatzResearch.WordTrace tailWord_8292649 prefixEnd_8292649 4258114836026430706350307 := by
  unfold tailWord_8292649
  simp only [CollatzResearch.WordTrace]
  refine ⟨302457756934156419539161001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201638504622770946359440667 302457756934156419539161001)
  ·
    refine ⟨226843317700617314654370751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 302457756934156419539161001 226843317700617314654370751)
    ·
      refine ⟨340264976550925971981556127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 226843317700617314654370751 340264976550925971981556127)
      ·
        refine ⟨510397464826388957972334191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340264976550925971981556127 510397464826388957972334191)
        ·
          refine ⟨765596197239583436958501287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510397464826388957972334191 765596197239583436958501287)
          ·
            refine ⟨1148394295859375155437751931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 765596197239583436958501287 1148394295859375155437751931)
            ·
              refine ⟨1722591443789062733156627897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1148394295859375155437751931 1722591443789062733156627897)
              ·
                refine ⟨1291943582841797049867470923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1722591443789062733156627897 1291943582841797049867470923)
                ·
                  refine ⟨1937915374262695574801206385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1291943582841797049867470923 1937915374262695574801206385)
                  ·
                    refine ⟨1453436530697021681100904789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1937915374262695574801206385 1453436530697021681100904789)
                    ·
                      refine ⟨4258114836026430706350307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 1453436530697021681100904789 4258114836026430706350307)
                      ·
                        rfl

theorem cell23_8292649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 2, 10].length) (baseStart_8292649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292649 prefixEnd_8292649 := by exact prefixLift 8292649
  have htrace : WordTrace (prefixWord ++ tailWord_8292649) baseStart_8292649 baseEnd_8292649 := by
    simpa [prefixWord, tailWord_8292649, baseEnd_8292649] using wordTrace_append hprefix tailTrace_8292649
  have hstable : (prefixWord ++ tailWord_8292649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292649).length < 2 ^ (prefixWord ++ tailWord_8292649).sum := by decide
  have hdescent : baseEnd_8292649 < baseStart_8292649 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292693 : List Nat := [1, 3, 2, 2, 4, 1, 1, 2, 7]
def baseStart_8292693 : Nat := 118140960795 + 8292693 * 2 ^ 59
def prefixEnd_8292693 : Nat := 4983230072969 + 3 ^ 40 * 8292693 * 2
def baseEnd_8292693 : Nat := 473126381019469837133345

theorem tailTrace_8292693 : CollatzResearch.WordTrace tailWord_8292693 prefixEnd_8292693 473126381019469837133345 := by
  unfold tailWord_8292693
  simp only [CollatzResearch.WordTrace]
  refine ⟨302459361745997015053762733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201639574497331343369175155 302459361745997015053762733)
  ·
    refine ⟨113422260654748880645161025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 302459361745997015053762733 113422260654748880645161025)
    ·
      refine ⟨85066695491061660483870769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113422260654748880645161025 85066695491061660483870769)
      ·
        refine ⟨63800021618296245362903077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85066695491061660483870769 63800021618296245362903077)
        ·
          refine ⟨11962504053430546005544327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 63800021618296245362903077 11962504053430546005544327)
          ·
            refine ⟨17943756080145819008316491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11962504053430546005544327 17943756080145819008316491)
            ·
              refine ⟨26915634120218728512474737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17943756080145819008316491 26915634120218728512474737)
              ·
                refine ⟨20186725590164046384356053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26915634120218728512474737 20186725590164046384356053)
                ·
                  refine ⟨473126381019469837133345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 20186725590164046384356053 473126381019469837133345)
                  ·
                    rfl

theorem cell23_8292693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 2, 7].length) (baseStart_8292693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292693 prefixEnd_8292693 := by exact prefixLift 8292693
  have htrace : WordTrace (prefixWord ++ tailWord_8292693) baseStart_8292693 baseEnd_8292693 := by
    simpa [prefixWord, tailWord_8292693, baseEnd_8292693] using wordTrace_append hprefix tailTrace_8292693
  have hstable : (prefixWord ++ tailWord_8292693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292693).length < 2 ^ (prefixWord ++ tailWord_8292693).sum := by decide
  have hdescent : baseEnd_8292693 < baseStart_8292693 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292738 : List Nat := [3, 4, 2, 1, 2, 1, 3, 1, 2, 2, 2]
def baseStart_8292738 : Nat := 118140960795 + 8292738 * 2 ^ 59
def prefixEnd_8292738 : Nat := 4983230072969 + 3 ^ 40 * 8292738 * 2
def baseEnd_8292738 : Nat := 4258160535804680858137399

theorem tailTrace_8292738 : CollatzResearch.WordTrace tailWord_8292738 prefixEnd_8292738 4258160535804680858137399 := by
  unfold tailWord_8292738
  simp only [CollatzResearch.WordTrace]
  refine ⟨75615250757708496934787717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201640668687222658492767245 75615250757708496934787717)
  ·
    refine ⟨14177859517070343175272697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 75615250757708496934787717 14177859517070343175272697)
    ·
      refine ⟨10633394637802757381454523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14177859517070343175272697 10633394637802757381454523)
      ·
        refine ⟨15950091956704136072181785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10633394637802757381454523 15950091956704136072181785)
        ·
          refine ⟨11962568967528102054136339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15950091956704136072181785 11962568967528102054136339)
          ·
            refine ⟨17943853451292153081204509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11962568967528102054136339 17943853451292153081204509)
            ·
              refine ⟨6728945044234557405451691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17943853451292153081204509 6728945044234557405451691)
              ·
                refine ⟨10093417566351836108177537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6728945044234557405451691 10093417566351836108177537)
                ·
                  refine ⟨7570063174763877081133153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10093417566351836108177537 7570063174763877081133153)
                  ·
                    refine ⟨5677547381072907810849865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7570063174763877081133153 5677547381072907810849865)
                    ·
                      refine ⟨4258160535804680858137399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5677547381072907810849865 4258160535804680858137399)
                      ·
                        rfl

theorem cell23_8292738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 3, 1, 2, 2, 2].length) (baseStart_8292738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292738 prefixEnd_8292738 := by exact prefixLift 8292738
  have htrace : WordTrace (prefixWord ++ tailWord_8292738) baseStart_8292738 baseEnd_8292738 := by
    simpa [prefixWord, tailWord_8292738, baseEnd_8292738] using wordTrace_append hprefix tailTrace_8292738
  have hstable : (prefixWord ++ tailWord_8292738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292738).length < 2 ^ (prefixWord ++ tailWord_8292738).sum := by decide
  have hdescent : baseEnd_8292738 < baseStart_8292738 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292810 : List Nat := [3, 1, 2, 1, 2, 2, 2, 1, 5, 1, 3]
def baseStart_8292810 : Nat := 118140960795 + 8292810 * 2 ^ 59
def prefixEnd_8292810 : Nat := 4983230072969 + 3 ^ 40 * 8292810 * 2
def baseEnd_8292810 : Nat := 4258197506411804576437067

theorem tailTrace_8292810 : CollatzResearch.WordTrace tailWord_8292810 prefixEnd_8292810 4258197506411804576437067 := by
  unfold tailWord_8292810
  simp only [CollatzResearch.WordTrace]
  refine ⟨75615907271643286008942971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201642419391048762690514589 75615907271643286008942971)
  ·
    refine ⟨113423860907464929013414457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75615907271643286008942971 113423860907464929013414457)
    ·
      refine ⟨85067895680598696760060843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 113423860907464929013414457 85067895680598696760060843)
      ·
        refine ⟨127601843520898045140091265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85067895680598696760060843 127601843520898045140091265)
        ·
          refine ⟨95701382640673533855068449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 127601843520898045140091265 95701382640673533855068449)
          ·
            refine ⟨71776036980505150391301337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 95701382640673533855068449 71776036980505150391301337)
            ·
              refine ⟨53832027735378862793476003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71776036980505150391301337 53832027735378862793476003)
              ·
                refine ⟨80748041603068294190214005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53832027735378862793476003 80748041603068294190214005)
                ·
                  refine ⟨7570128900287652580332563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 80748041603068294190214005 7570128900287652580332563)
                  ·
                    refine ⟨11355193350431478870498845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7570128900287652580332563 11355193350431478870498845)
                    ·
                      refine ⟨4258197506411804576437067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11355193350431478870498845 4258197506411804576437067)
                      ·
                        rfl

theorem cell23_8292810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_8292810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292810 prefixEnd_8292810 := by exact prefixLift 8292810
  have htrace : WordTrace (prefixWord ++ tailWord_8292810) baseStart_8292810 baseEnd_8292810 := by
    simpa [prefixWord, tailWord_8292810, baseEnd_8292810] using wordTrace_append hprefix tailTrace_8292810
  have hstable : (prefixWord ++ tailWord_8292810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292810).length < 2 ^ (prefixWord ++ tailWord_8292810).sum := by decide
  have hdescent : baseEnd_8292810 < baseStart_8292810 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292834 : List Nat := [3, 3, 3, 2, 1, 1, 2, 2, 6]
def baseStart_8292834 : Nat := 118140960795 + 8292834 * 2 ^ 59
def prefixEnd_8292834 : Nat := 4983230072969 + 3 ^ 40 * 8292834 * 2
def baseEnd_8292834 : Nat := 473134425549723609170773

theorem tailTrace_8292834 : CollatzResearch.WordTrace tailWord_8292834 prefixEnd_8292834 473134425549723609170773 := by
  unfold tailWord_8292834
  simp only [CollatzResearch.WordTrace]
  refine ⟨75616126109621549033661389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201643002958990797423097037 75616126109621549033661389)
  ·
    refine ⟨28356047291108080887623021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75616126109621549033661389 28356047291108080887623021)
    ·
      refine ⟨10633517734165530332858633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28356047291108080887623021 10633517734165530332858633)
      ·
        refine ⟨7975138300624147749643975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10633517734165530332858633 7975138300624147749643975)
        ·
          refine ⟨11962707450936221624465963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7975138300624147749643975 11962707450936221624465963)
          ·
            refine ⟨17944061176404332436698945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11962707450936221624465963 17944061176404332436698945)
            ·
              refine ⟨13458045882303249327524209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17944061176404332436698945 13458045882303249327524209)
              ·
                refine ⟨10093534411727436995643157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13458045882303249327524209 10093534411727436995643157)
                ·
                  refine ⟨473134425549723609170773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10093534411727436995643157 473134425549723609170773)
                  ·
                    rfl

theorem cell23_8292834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 2, 6].length) (baseStart_8292834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292834 prefixEnd_8292834 := by exact prefixLift 8292834
  have htrace : WordTrace (prefixWord ++ tailWord_8292834) baseStart_8292834 baseEnd_8292834 := by
    simpa [prefixWord, tailWord_8292834, baseEnd_8292834] using wordTrace_append hprefix tailTrace_8292834
  have hstable : (prefixWord ++ tailWord_8292834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292834).length < 2 ^ (prefixWord ++ tailWord_8292834).sum := by decide
  have hdescent : baseEnd_8292834 < baseStart_8292834 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292867 : List Nat := [1, 1, 1, 3, 2, 1, 5, 2, 3, 2, 2]
def baseStart_8292867 : Nat := 118140960795 + 8292867 * 2 ^ 59
def prefixEnd_8292867 : Nat := 4983230072969 + 3 ^ 40 * 8292867 * 2
def baseEnd_8292867 : Nat := 4258226774809110853424305

theorem tailTrace_8292867 : CollatzResearch.WordTrace tailWord_8292867 prefixEnd_8292867 4258226774809110853424305 := by
  unfold tailWord_8292867
  simp only [CollatzResearch.WordTrace]
  refine ⟨302465708047366642770596855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201643805364911095180397903 302465708047366642770596855)
  ·
    refine ⟨453698562071049964155895283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302465708047366642770596855 453698562071049964155895283)
    ·
      refine ⟨680547843106574946233842925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453698562071049964155895283 680547843106574946233842925)
      ·
        refine ⟨255205441164965604837691097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 680547843106574946233842925 255205441164965604837691097)
        ·
          refine ⟨191404080873724203628268323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 255205441164965604837691097 191404080873724203628268323)
          ·
            refine ⟨287106121310586305442402485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191404080873724203628268323 287106121310586305442402485)
            ·
              refine ⟨26916198872867466135225233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 287106121310586305442402485 26916198872867466135225233)
              ·
                refine ⟨20187149154650599601418925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26916198872867466135225233 20187149154650599601418925)
                ·
                  refine ⟨7570180932993974850532097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20187149154650599601418925 7570180932993974850532097)
                  ·
                    refine ⟨5677635699745481137899073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7570180932993974850532097 5677635699745481137899073)
                    ·
                      refine ⟨4258226774809110853424305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5677635699745481137899073 4258226774809110853424305)
                      ·
                        rfl

theorem cell23_8292867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 5, 2, 3, 2, 2].length) (baseStart_8292867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292867 prefixEnd_8292867 := by exact prefixLift 8292867
  have htrace : WordTrace (prefixWord ++ tailWord_8292867) baseStart_8292867 baseEnd_8292867 := by
    simpa [prefixWord, tailWord_8292867, baseEnd_8292867] using wordTrace_append hprefix tailTrace_8292867
  have hstable : (prefixWord ++ tailWord_8292867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292867).length < 2 ^ (prefixWord ++ tailWord_8292867).sum := by decide
  have hdescent : baseEnd_8292867 < baseStart_8292867 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292871 : List Nat := [1, 1, 4, 3, 4, 1, 1, 1, 2, 3, 2]
def baseStart_8292871 : Nat := 118140960795 + 8292871 * 2 ^ 59
def prefixEnd_8292871 : Nat := 4983230072969 + 3 ^ 40 * 8292871 * 2
def baseEnd_8292871 : Nat := 4258228828731728837774287

theorem tailTrace_8292871 : CollatzResearch.WordTrace tailWord_8292871 prefixEnd_8292871 4258228828731728837774287 := by
  unfold tailWord_8292871
  simp only [CollatzResearch.WordTrace]
  refine ⟨302465853939352151453742467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201643902626234767635828311 302465853939352151453742467)
  ·
    refine ⟨453698780909028227180613701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302465853939352151453742467 453698780909028227180613701)
    ·
      refine ⟨85068521420442792596365069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 453698780909028227180613701 85068521420442792596365069)
      ·
        refine ⟨31900695532666047223636901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 85068521420442792596365069 31900695532666047223636901)
        ·
          refine ⟨5981380412374883854431919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 31900695532666047223636901 5981380412374883854431919)
          ·
            refine ⟨8972070618562325781647879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5981380412374883854431919 8972070618562325781647879)
            ·
              refine ⟨13458105927843488672471819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8972070618562325781647879 13458105927843488672471819)
              ·
                refine ⟨20187158891765233008707729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13458105927843488672471819 20187158891765233008707729)
                ·
                  refine ⟨15140369168823924756530797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20187158891765233008707729 15140369168823924756530797)
                  ·
                    refine ⟨5677638438308971783699049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15140369168823924756530797 5677638438308971783699049)
                    ·
                      refine ⟨4258228828731728837774287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5677638438308971783699049 4258228828731728837774287)
                      ·
                        rfl

theorem cell23_8292871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_8292871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292871 prefixEnd_8292871 := by exact prefixLift 8292871
  have htrace : WordTrace (prefixWord ++ tailWord_8292871) baseStart_8292871 baseEnd_8292871 := by
    simpa [prefixWord, tailWord_8292871, baseEnd_8292871] using wordTrace_append hprefix tailTrace_8292871
  have hstable : (prefixWord ++ tailWord_8292871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292871).length < 2 ^ (prefixWord ++ tailWord_8292871).sum := by decide
  have hdescent : baseEnd_8292871 < baseStart_8292871 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292884 : List Nat := [2, 4, 3, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_8292884 : Nat := 118140960795 + 8292884 * 2 ^ 59
def prefixEnd_8292884 : Nat := 4983230072969 + 3 ^ 40 * 8292884 * 2
def baseEnd_8292884 : Nat := 4258235503980237286911727

theorem tailTrace_8292884 : CollatzResearch.WordTrace tailWord_8292884 prefixEnd_8292884 4258235503980237286911727 := by
  unfold tailWord_8292884
  simp only [CollatzResearch.WordTrace]
  refine ⟨151233164044152527336982853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201644218725536703115977137 151233164044152527336982853)
  ·
    refine ⟨28356218258278598875684285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 151233164044152527336982853 28356218258278598875684285)
    ·
      refine ⟨10633581846854474578381607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28356218258278598875684285 10633581846854474578381607)
      ·
        refine ⟨15950372770281711867572411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10633581846854474578381607 15950372770281711867572411)
        ·
          refine ⟨23925559155422567801358617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15950372770281711867572411 23925559155422567801358617)
          ·
            refine ⟨17944169366566925851018963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23925559155422567801358617 17944169366566925851018963)
            ·
              refine ⟨26916254049850388776528445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17944169366566925851018963 26916254049850388776528445)
              ·
                refine ⟨10093595268693895791198167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26916254049850388776528445 10093595268693895791198167)
                ·
                  refine ⟨15140392903040843686797251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10093595268693895791198167 15140392903040843686797251)
                  ·
                    refine ⟨22710589354561265530195877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15140392903040843686797251 22710589354561265530195877)
                    ·
                      refine ⟨4258235503980237286911727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22710589354561265530195877 4258235503980237286911727)
                      ·
                        rfl

theorem cell23_8292884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_8292884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292884 prefixEnd_8292884 := by exact prefixLift 8292884
  have htrace : WordTrace (prefixWord ++ tailWord_8292884) baseStart_8292884 baseEnd_8292884 := by
    simpa [prefixWord, tailWord_8292884, baseEnd_8292884] using wordTrace_append hprefix tailTrace_8292884
  have hstable : (prefixWord ++ tailWord_8292884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292884).length < 2 ^ (prefixWord ++ tailWord_8292884).sum := by decide
  have hdescent : baseEnd_8292884 < baseStart_8292884 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292943 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 5]
def baseStart_8292943 : Nat := 118140960795 + 8292943 * 2 ^ 59
def prefixEnd_8292943 : Nat := 4983230072969 + 3 ^ 40 * 8292943 * 2
def baseEnd_8292943 : Nat := 4258265799338852556073955

theorem tailTrace_8292943 : CollatzResearch.WordTrace tailWord_8292943 prefixEnd_8292943 4258265799338852556073955 := by
  unfold tailWord_8292943
  simp only [CollatzResearch.WordTrace]
  refine ⟨302468479995091307750363483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201645653330060871833575655 302468479995091307750363483)
  ·
    refine ⟨453702719992636961625545225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302468479995091307750363483 453702719992636961625545225)
    ·
      refine ⟨340277039994477721219158919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 453702719992636961625545225 340277039994477721219158919)
      ·
        refine ⟨510415559991716581828738379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 340277039994477721219158919 510415559991716581828738379)
        ·
          refine ⟨765623339987574872743107569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 510415559991716581828738379 765623339987574872743107569)
          ·
            refine ⟨574217504990681154557330677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 765623339987574872743107569 574217504990681154557330677)
            ·
              refine ⟨53832891092876358239749751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 574217504990681154557330677 53832891092876358239749751)
              ·
                refine ⟨80749336639314537359624627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53832891092876358239749751 80749336639314537359624627)
                ·
                  refine ⟨121124004958971806039436941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80749336639314537359624627 121124004958971806039436941)
                  ·
                    refine ⟨45421501859614427264788853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 121124004958971806039436941 45421501859614427264788853)
                    ·
                      refine ⟨4258265799338852556073955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 45421501859614427264788853 4258265799338852556073955)
                      ·
                        rfl

theorem cell23_8292943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_8292943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292943 prefixEnd_8292943 := by exact prefixLift 8292943
  have htrace : WordTrace (prefixWord ++ tailWord_8292943) baseStart_8292943 baseEnd_8292943 := by
    simpa [prefixWord, tailWord_8292943, baseEnd_8292943] using wordTrace_append hprefix tailTrace_8292943
  have hstable : (prefixWord ++ tailWord_8292943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292943).length < 2 ^ (prefixWord ++ tailWord_8292943).sum := by decide
  have hdescent : baseEnd_8292943 < baseStart_8292943 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292968 : List Nat := [2, 1, 4, 3, 2, 2, 2, 1, 2, 1, 3]
def baseStart_8292968 : Nat := 118140960795 + 8292968 * 2 ^ 59
def prefixEnd_8292968 : Nat := 4983230072969 + 3 ^ 40 * 8292968 * 2
def baseEnd_8292968 : Nat := 4258278636355214958261341

theorem tailTrace_8292968 : CollatzResearch.WordTrace tailWord_8292968 prefixEnd_8292968 4258278636355214958261341 := by
  unfold tailWord_8292968
  simp only [CollatzResearch.WordTrace]
  refine ⟨151234695910000368510011779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201646261213333824680015705 151234695910000368510011779)
  ·
    refine ⟨226852043865000552765017669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 151234695910000368510011779 226852043865000552765017669)
    ·
      refine ⟨42534758224687603643440813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 226852043865000552765017669 42534758224687603643440813)
      ·
        refine ⟨15950534334257851366290305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42534758224687603643440813 15950534334257851366290305)
        ·
          refine ⟨11962900750693388524717729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15950534334257851366290305 11962900750693388524717729)
          ·
            refine ⟨8972175563020041393538297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11962900750693388524717729 8972175563020041393538297)
            ·
              refine ⟨6729131672265031045153723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8972175563020041393538297 6729131672265031045153723)
              ·
                refine ⟨10093697508397546567730585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6729131672265031045153723 10093697508397546567730585)
                ·
                  refine ⟨7570273131298159925797939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10093697508397546567730585 7570273131298159925797939)
                  ·
                    refine ⟨11355409696947239888696909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7570273131298159925797939 11355409696947239888696909)
                    ·
                      refine ⟨4258278636355214958261341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11355409696947239888696909 4258278636355214958261341)
                      ·
                        rfl

theorem cell23_8292968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_8292968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292968 prefixEnd_8292968 := by exact prefixLift 8292968
  have htrace : WordTrace (prefixWord ++ tailWord_8292968) baseStart_8292968 baseEnd_8292968 := by
    simpa [prefixWord, tailWord_8292968, baseEnd_8292968] using wordTrace_append hprefix tailTrace_8292968
  have hstable : (prefixWord ++ tailWord_8292968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292968).length < 2 ^ (prefixWord ++ tailWord_8292968).sum := by decide
  have hdescent : baseEnd_8292968 < baseStart_8292968 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292970 : List Nat := [3, 1, 3, 2, 1, 1, 2, 1, 1, 4, 4]
def baseStart_8292970 : Nat := 118140960795 + 8292970 * 2 ^ 59
def prefixEnd_8292970 : Nat := 4983230072969 + 3 ^ 40 * 8292970 * 2
def baseEnd_8292970 : Nat := 4258279663316523950436331

theorem tailTrace_8292970 : CollatzResearch.WordTrace tailWord_8292970 prefixEnd_8292970 4258279663316523950436331 := by
  unfold tailWord_8292970
  simp only [CollatzResearch.WordTrace]
  refine ⟨75617366191498372840399091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201646309843995660907730909 75617366191498372840399091)
  ·
    refine ⟨113426049287247559260598637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 75617366191498372840399091 113426049287247559260598637)
    ·
      refine ⟨42534768482717834722724489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 113426049287247559260598637 42534768482717834722724489)
      ·
        refine ⟨31901076362038376042043367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42534768482717834722724489 31901076362038376042043367)
        ·
          refine ⟨47851614543057564063065051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31901076362038376042043367 47851614543057564063065051)
          ·
            refine ⟨71777421814586346094597577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 47851614543057564063065051 71777421814586346094597577)
            ·
              refine ⟨53833066360939759570948183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 71777421814586346094597577 53833066360939759570948183)
              ·
                refine ⟨80749599541409639356422275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 53833066360939759570948183 80749599541409639356422275)
                ·
                  refine ⟨121124399312114459034633413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 80749599541409639356422275 121124399312114459034633413)
                  ·
                    refine ⟨22710824871021461068993765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 121124399312114459034633413 22710824871021461068993765)
                    ·
                      refine ⟨4258279663316523950436331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22710824871021461068993765 4258279663316523950436331)
                      ·
                        rfl

theorem cell23_8292970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_8292970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292970 prefixEnd_8292970 := by exact prefixLift 8292970
  have htrace : WordTrace (prefixWord ++ tailWord_8292970) baseStart_8292970 baseEnd_8292970 := by
    simpa [prefixWord, tailWord_8292970, baseEnd_8292970] using wordTrace_append hprefix tailTrace_8292970
  have hstable : (prefixWord ++ tailWord_8292970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292970).length < 2 ^ (prefixWord ++ tailWord_8292970).sum := by decide
  have hdescent : baseEnd_8292970 < baseStart_8292970 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8292978 : List Nat := [3, 2, 1, 2, 5, 1, 1, 2, 1, 3, 2]
def baseStart_8292978 : Nat := 118140960795 + 8292978 * 2 ^ 59
def prefixEnd_8292978 : Nat := 4983230072969 + 3 ^ 40 * 8292978 * 2
def baseEnd_8292978 : Nat := 4258283771161759919136295

theorem tailTrace_8292978 : CollatzResearch.WordTrace tailWord_8292978 prefixEnd_8292978 4258283771161759919136295 := by
  unfold tailWord_8292978
  simp only [CollatzResearch.WordTrace]
  refine ⟨75617439137491127181971897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201646504366643005818591725 75617439137491127181971897)
  ·
    refine ⟨56713079353118345386478923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75617439137491127181971897 56713079353118345386478923)
    ·
      refine ⟨85069619029677518079718385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56713079353118345386478923 85069619029677518079718385)
      ·
        refine ⟨63802214272258138559788789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85069619029677518079718385 63802214272258138559788789)
        ·
          refine ⟨5981457588024200489980199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 63802214272258138559788789 5981457588024200489980199)
          ·
            refine ⟨8972186382036300734970299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5981457588024200489980199 8972186382036300734970299)
            ·
              refine ⟨13458279573054451102455449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8972186382036300734970299 13458279573054451102455449)
              ·
                refine ⟨10093709679790838326841587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13458279573054451102455449 10093709679790838326841587)
                ·
                  refine ⟨15140564519686257490262381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10093709679790838326841587 15140564519686257490262381)
                  ·
                    refine ⟨5677711694882346558848393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15140564519686257490262381 5677711694882346558848393)
                    ·
                      refine ⟨4258283771161759919136295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 5677711694882346558848393 4258283771161759919136295)
                      ·
                        rfl

theorem cell23_8292978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 2, 1, 3, 2].length) (baseStart_8292978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8292978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8292978 prefixEnd_8292978 := by exact prefixLift 8292978
  have htrace : WordTrace (prefixWord ++ tailWord_8292978) baseStart_8292978 baseEnd_8292978 := by
    simpa [prefixWord, tailWord_8292978, baseEnd_8292978] using wordTrace_append hprefix tailTrace_8292978
  have hstable : (prefixWord ++ tailWord_8292978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8292978).length < 2 ^ (prefixWord ++ tailWord_8292978).sum := by decide
  have hdescent : baseEnd_8292978 < baseStart_8292978 := by decide
  rcases family_descends (prefixWord ++ tailWord_8292978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293047 : List Nat := [1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 4]
def baseStart_8293047 : Nat := 118140960795 + 8293047 * 2 ^ 59
def prefixEnd_8293047 : Nat := 4983230072969 + 3 ^ 40 * 8293047 * 2
def baseEnd_8293047 : Nat := 4258319201326920149173477

theorem tailTrace_8293047 : CollatzResearch.WordTrace tailWord_8293047 prefixEnd_8293047 4258319201326920149173477 := by
  unfold tailWord_8293047
  simp only [CollatzResearch.WordTrace]
  refine ⟨302472273186714533512149395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201648182124476355674766263 302472273186714533512149395)
  ·
    refine ⟨453708409780071800268224093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302472273186714533512149395 453708409780071800268224093)
    ·
      refine ⟨170140653667526925100584035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 453708409780071800268224093 170140653667526925100584035)
      ·
        refine ⟨255210980501290387650876053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 170140653667526925100584035 255210980501290387650876053)
        ·
          refine ⟨11963014710997986921134815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 255210980501290387650876053 11963014710997986921134815)
          ·
            refine ⟨17944522066496980381702223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11963014710997986921134815 17944522066496980381702223)
            ·
              refine ⟨26916783099745470572553335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17944522066496980381702223 26916783099745470572553335)
              ·
                refine ⟨40375174649618205858830003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26916783099745470572553335 40375174649618205858830003)
                ·
                  refine ⟨60562761974427308788245005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40375174649618205858830003 60562761974427308788245005)
                  ·
                    refine ⟨22711035740410240795591877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 60562761974427308788245005 22711035740410240795591877)
                    ·
                      refine ⟨4258319201326920149173477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22711035740410240795591877 4258319201326920149173477)
                      ·
                        rfl

theorem cell23_8293047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 6, 1, 1, 1, 1, 3, 4].length) (baseStart_8293047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293047 prefixEnd_8293047 := by exact prefixLift 8293047
  have htrace : WordTrace (prefixWord ++ tailWord_8293047) baseStart_8293047 baseEnd_8293047 := by
    simpa [prefixWord, tailWord_8293047, baseEnd_8293047] using wordTrace_append hprefix tailTrace_8293047
  have hstable : (prefixWord ++ tailWord_8293047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293047).length < 2 ^ (prefixWord ++ tailWord_8293047).sum := by decide
  have hdescent : baseEnd_8293047 < baseStart_8293047 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293084 : List Nat := [2, 2, 5, 1, 1, 1, 1, 2, 1, 4, 3]
def baseStart_8293084 : Nat := 118140960795 + 8293084 * 2 ^ 59
def prefixEnd_8293084 : Nat := 4983230072969 + 3 ^ 40 * 8293084 * 2
def baseEnd_8293084 : Nat := 4258338200111136504410807

theorem tailTrace_8293084 : CollatzResearch.WordTrace tailWord_8293084 prefixEnd_8293084 4258338200111136504410807 := by
  unfold tailWord_8293084
  simp only [CollatzResearch.WordTrace]
  refine ⟨151236811343790244415623153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 201649081791720325887497537 151236811343790244415623153)
  ·
    refine ⟨113427608507842683311717365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 151236811343790244415623153 113427608507842683311717365)
    ·
      refine ⟨10633838297610251560473503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 113427608507842683311717365 10633838297610251560473503)
      ·
        refine ⟨15950757446415377340710255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10633838297610251560473503 15950757446415377340710255)
        ·
          refine ⟨23926136169623066011065383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15950757446415377340710255 23926136169623066011065383)
          ·
            refine ⟨35889204254434599016598075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23926136169623066011065383 35889204254434599016598075)
            ·
              refine ⟨53833806381651898524897113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35889204254434599016598075 53833806381651898524897113)
              ·
                refine ⟨40375354786238923893672835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53833806381651898524897113 40375354786238923893672835)
                ·
                  refine ⟨60563032179358385840509253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40375354786238923893672835 60563032179358385840509253)
                  ·
                    refine ⟨11355568533629697345095485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 60563032179358385840509253 11355568533629697345095485)
                    ·
                      refine ⟨4258338200111136504410807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 11355568533629697345095485 4258338200111136504410807)
                      ·
                        rfl

theorem cell23_8293084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_8293084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293084 prefixEnd_8293084 := by exact prefixLift 8293084
  have htrace : WordTrace (prefixWord ++ tailWord_8293084) baseStart_8293084 baseEnd_8293084 := by
    simpa [prefixWord, tailWord_8293084, baseEnd_8293084] using wordTrace_append hprefix tailTrace_8293084
  have hstable : (prefixWord ++ tailWord_8293084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293084).length < 2 ^ (prefixWord ++ tailWord_8293084).sum := by decide
  have hdescent : baseEnd_8293084 < baseStart_8293084 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293117 : List Nat := [1, 4, 1, 1, 1, 1, 3, 5, 1, 5]
def baseStart_8293117 : Nat := 118140960795 + 8293117 * 2 ^ 59
def prefixEnd_8293117 : Nat := 4983230072969 + 3 ^ 40 * 8293117 * 2
def baseEnd_8293117 : Nat := 1419451714990911625099385

theorem tailTrace_8293117 : CollatzResearch.WordTrace tailWord_8293117 prefixEnd_8293117 1419451714990911625099385 := by
  unfold tailWord_8293117
  simp only [CollatzResearch.WordTrace]
  refine ⟨302474826296460935467197605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201649884197640623644798403 302474826296460935467197605)
  ·
    refine ⟨56714029930586425400099551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 302474826296460935467197605 56714029930586425400099551)
    ·
      refine ⟨85071044895879638100149327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 56714029930586425400099551 85071044895879638100149327)
      ·
        refine ⟨127606567343819457150223991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85071044895879638100149327 127606567343819457150223991)
        ·
          refine ⟨191409851015729185725335987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 127606567343819457150223991 191409851015729185725335987)
          ·
            refine ⟨287114776523593778588003981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 191409851015729185725335987 287114776523593778588003981)
            ·
              refine ⟨107668041196347666970501493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 287114776523593778588003981 107668041196347666970501493)
              ·
                refine ⟨10093878862157593778484515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 107668041196347666970501493 10093878862157593778484515)
                ·
                  refine ⟨15140818293236390667726773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10093878862157593778484515 15140818293236390667726773)
                  ·
                    refine ⟨1419451714990911625099385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 15140818293236390667726773 1419451714990911625099385)
                    ·
                      rfl

theorem cell23_8293117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_8293117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293117 prefixEnd_8293117 := by exact prefixLift 8293117
  have htrace : WordTrace (prefixWord ++ tailWord_8293117) baseStart_8293117 baseEnd_8293117 := by
    simpa [prefixWord, tailWord_8293117, baseEnd_8293117] using wordTrace_append hprefix tailTrace_8293117
  have hstable : (prefixWord ++ tailWord_8293117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293117).length < 2 ^ (prefixWord ++ tailWord_8293117).sum := by decide
  have hdescent : baseEnd_8293117 < baseStart_8293117 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293138 : List Nat := [3, 2, 4, 1, 2, 2, 2, 1, 6]
def baseStart_8293138 : Nat := 118140960795 + 8293138 * 2 ^ 59
def prefixEnd_8293138 : Nat := 4983230072969 + 3 ^ 40 * 8293138 * 2
def baseEnd_8293138 : Nat := 473151769785164365903951

theorem tailTrace_8293138 : CollatzResearch.WordTrace tailWord_8293138 prefixEnd_8293138 473151769785164365903951 := by
  unfold tailWord_8293138
  simp only [CollatzResearch.WordTrace]
  refine ⟨75618898057346214013428017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201650394819589904035808045 75618898057346214013428017)
  ·
    refine ⟨56714173543009660510071013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 75618898057346214013428017 56714173543009660510071013)
    ·
      refine ⟨10633907539314311345638315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 56714173543009660510071013 10633907539314311345638315)
      ·
        refine ⟨15950861308971467018457473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10633907539314311345638315 15950861308971467018457473)
        ·
          refine ⟨11963145981728600263843105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15950861308971467018457473 11963145981728600263843105)
          ·
            refine ⟨8972359486296450197882329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11963145981728600263843105 8972359486296450197882329)
            ·
              refine ⟨6729269614722337648411747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8972359486296450197882329 6729269614722337648411747)
              ·
                refine ⟨10093904422083506472617621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6729269614722337648411747 10093904422083506472617621)
                ·
                  refine ⟨473151769785164365903951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 10093904422083506472617621 473151769785164365903951)
                  ·
                    rfl

theorem cell23_8293138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_8293138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293138 prefixEnd_8293138 := by exact prefixLift 8293138
  have htrace : WordTrace (prefixWord ++ tailWord_8293138) baseStart_8293138 baseEnd_8293138 := by
    simpa [prefixWord, tailWord_8293138, baseEnd_8293138] using wordTrace_append hprefix tailTrace_8293138
  have hstable : (prefixWord ++ tailWord_8293138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293138).length < 2 ^ (prefixWord ++ tailWord_8293138).sum := by decide
  have hdescent : baseEnd_8293138 < baseStart_8293138 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293154 : List Nat := [3, 3, 1, 1, 2, 3, 1, 1, 3, 1, 4]
def baseStart_8293154 : Nat := 118140960795 + 8293154 * 2 ^ 59
def prefixEnd_8293154 : Nat := 4983230072969 + 3 ^ 40 * 8293154 * 2
def baseEnd_8293154 : Nat := 4258374143756951230535485

theorem tailTrace_8293154 : CollatzResearch.WordTrace tailWord_8293154 prefixEnd_8293154 4258374143756951230535485 := by
  unfold tailWord_8293154
  simp only [CollatzResearch.WordTrace]
  refine ⟨75619043949331722696573629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 201650783864884593857529677 75619043949331722696573629)
  ·
    refine ⟨28357141480999396011215111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 75619043949331722696573629 28357141480999396011215111)
    ·
      refine ⟨42535712221499094016822667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28357141480999396011215111 42535712221499094016822667)
      ·
        refine ⟨63803568332248641025234001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42535712221499094016822667 63803568332248641025234001)
        ·
          refine ⟨47852676249186480768925501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 63803568332248641025234001 47852676249186480768925501)
          ·
            refine ⟨17944753593444930288347063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47852676249186480768925501 17944753593444930288347063)
            ·
              refine ⟨26917130390167395432520595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17944753593444930288347063 26917130390167395432520595)
              ·
                refine ⟨40375695585251093148780893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 26917130390167395432520595 40375695585251093148780893)
                ·
                  refine ⟨15140885844469159930792835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40375695585251093148780893 15140885844469159930792835)
                  ·
                    refine ⟨22711328766703739896189253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15140885844469159930792835 22711328766703739896189253)
                    ·
                      refine ⟨4258374143756951230535485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22711328766703739896189253 4258374143756951230535485)
                      ·
                        rfl

theorem cell23_8293154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_8293154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293154 prefixEnd_8293154 := by exact prefixLift 8293154
  have htrace : WordTrace (prefixWord ++ tailWord_8293154) baseStart_8293154 baseEnd_8293154 := by
    simpa [prefixWord, tailWord_8293154, baseEnd_8293154] using wordTrace_append hprefix tailTrace_8293154
  have hstable : (prefixWord ++ tailWord_8293154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293154).length < 2 ^ (prefixWord ++ tailWord_8293154).sum := by decide
  have hdescent : baseEnd_8293154 < baseStart_8293154 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_8293171 : List Nat := [1, 1, 1, 2, 6, 2, 3, 1, 1, 1, 4]
def baseStart_8293171 : Nat := 118140960795 + 8293171 * 2 ^ 59
def prefixEnd_8293171 : Nat := 4983230072969 + 3 ^ 40 * 8293171 * 2
def baseEnd_8293171 : Nat := 4258382872928077664022907

theorem tailTrace_8293171 : CollatzResearch.WordTrace tailWord_8293171 prefixEnd_8293171 4258382872928077664022907 := by
  unfold tailWord_8293171
  simp only [CollatzResearch.WordTrace]
  refine ⟨302476795838265302689663367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 201651197225510201793108911 302476795838265302689663367)
  ·
    refine ⟨453715193757397954034495051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 302476795838265302689663367 453715193757397954034495051)
    ·
      refine ⟨680572790636096931051742577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 453715193757397954034495051 680572790636096931051742577)
      ·
        refine ⟨510429592977072698288806933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 680572790636096931051742577 510429592977072698288806933)
        ·
          refine ⟨23926387170800282732287825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 510429592977072698288806933 23926387170800282732287825)
          ·
            refine ⟨17944790378100212049215869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23926387170800282732287825 17944790378100212049215869)
            ·
              refine ⟨6729296391787579518455951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17944790378100212049215869 6729296391787579518455951)
              ·
                refine ⟨10093944587681369277683927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6729296391787579518455951 10093944587681369277683927)
                ·
                  refine ⟨15140916881522053916525891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10093944587681369277683927 15140916881522053916525891)
                  ·
                    refine ⟨22711375322283080874788837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15140916881522053916525891 22711375322283080874788837)
                    ·
                      refine ⟨4258382872928077664022907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 22711375322283080874788837 4258382872928077664022907)
                      ·
                        rfl

theorem cell23_8293171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 3, 1, 1, 1, 4].length) (baseStart_8293171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_8293171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_8293171 prefixEnd_8293171 := by exact prefixLift 8293171
  have htrace : WordTrace (prefixWord ++ tailWord_8293171) baseStart_8293171 baseEnd_8293171 := by
    simpa [prefixWord, tailWord_8293171, baseEnd_8293171] using wordTrace_append hprefix tailTrace_8293171
  have hstable : (prefixWord ++ tailWord_8293171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_8293171).length < 2 ^ (prefixWord ++ tailWord_8293171).sum := by decide
  have hdescent : baseEnd_8293171 < baseStart_8293171 := by decide
  rcases family_descends (prefixWord ++ tailWord_8293171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
