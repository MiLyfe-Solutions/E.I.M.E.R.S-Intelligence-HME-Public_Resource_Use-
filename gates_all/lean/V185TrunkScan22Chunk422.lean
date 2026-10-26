import V185TrunkScan22Chunk421

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_3761783 : List Nat := [1, 1, 3, 1, 1, 3, 1, 3, 8]
def baseStart_3761783 : Nat := 118140960795 + 3761783 * 2 ^ 59
def prefixEnd_3761783 : Nat := 4983230072969 + 3 ^ 40 * 3761783 * 2
def baseEnd_3761783 : Nat := 429245065980524608980529

theorem tailTrace_3761783 : CollatzResearch.WordTrace tailWord_3761783 prefixEnd_3761783 429245065980524608980529 := by
  unfold tailWord_3761783
  simp only [CollatzResearch.WordTrace]
  refine ⟨137203497730710127232546003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91468998487140084821697335 137203497730710127232546003)
  ·
    refine ⟨205805246596065190848819005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137203497730710127232546003 205805246596065190848819005)
    ·
      refine ⟨77176967473524446568307127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205805246596065190848819005 77176967473524446568307127)
      ·
        refine ⟨115765451210286669852460691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77176967473524446568307127 115765451210286669852460691)
        ·
          refine ⟨173648176815430004778691037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115765451210286669852460691 173648176815430004778691037)
          ·
            refine ⟨65118066305786251792009139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173648176815430004778691037 65118066305786251792009139)
            ·
              refine ⟨97677099458679377688013709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65118066305786251792009139 97677099458679377688013709)
              ·
                refine ⟨36628912297004766633005141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97677099458679377688013709 36628912297004766633005141)
                ·
                  refine ⟨429245065980524608980529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36628912297004766633005141 429245065980524608980529)
                  ·
                    rfl

theorem cell22_3761783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 3, 8].length) (baseStart_3761783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761783 prefixEnd_3761783 := by exact prefixLift 3761783
  have htrace : WordTrace (prefixWord ++ tailWord_3761783) baseStart_3761783 baseEnd_3761783 := by
    simpa [prefixWord, tailWord_3761783, baseEnd_3761783] using wordTrace_append hprefix tailTrace_3761783
  have hstable : (prefixWord ++ tailWord_3761783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761783).length < 2 ^ (prefixWord ++ tailWord_3761783).sum := by decide
  have hdescent : baseEnd_3761783 < baseStart_3761783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761785 : List Nat := [1, 2, 1, 3, 3, 1, 3, 1, 3, 4]
def baseStart_3761785 : Nat := 118140960795 + 3761785 * 2 ^ 59
def prefixEnd_3761785 : Nat := 4983230072969 + 3 ^ 40 * 3761785 * 2
def baseEnd_3761785 : Nat := 1287735882582446488391581

theorem tailTrace_3761785 : CollatzResearch.WordTrace tailWord_3761785 prefixEnd_3761785 1287735882582446488391581 := by
  unfold tailWord_3761785
  simp only [CollatzResearch.WordTrace]
  refine ⟨137203570676702881574118809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91469047117801921049412539 137203570676702881574118809)
  ·
    refine ⟨102902678007527161180589107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137203570676702881574118809 102902678007527161180589107)
    ·
      refine ⟨154354017011290741770883661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102902678007527161180589107 154354017011290741770883661)
      ·
        refine ⟨57882756379234028164081373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154354017011290741770883661 57882756379234028164081373)
        ·
          refine ⟨21706033642212760561530515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57882756379234028164081373 21706033642212760561530515)
          ·
            refine ⟨32559050463319140842295773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21706033642212760561530515 32559050463319140842295773)
            ·
              refine ⟨12209643923744677815860915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32559050463319140842295773 12209643923744677815860915)
              ·
                refine ⟨18314465885617016723791373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12209643923744677815860915 18314465885617016723791373)
                ·
                  refine ⟨6867924707106381271421765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18314465885617016723791373 6867924707106381271421765)
                  ·
                    refine ⟨1287735882582446488391581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6867924707106381271421765 1287735882582446488391581)
                    ·
                      rfl

theorem cell22_3761785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 3, 1, 3, 4].length) (baseStart_3761785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761785 prefixEnd_3761785 := by exact prefixLift 3761785
  have htrace : WordTrace (prefixWord ++ tailWord_3761785) baseStart_3761785 baseEnd_3761785 := by
    simpa [prefixWord, tailWord_3761785, baseEnd_3761785] using wordTrace_append hprefix tailTrace_3761785
  have hstable : (prefixWord ++ tailWord_3761785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761785).length < 2 ^ (prefixWord ++ tailWord_3761785).sum := by decide
  have hdescent : baseEnd_3761785 < baseStart_3761785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761810 : List Nat := [3, 2, 3, 1, 4, 1, 2, 2, 1, 3]
def baseStart_3761810 : Nat := 118140960795 + 3761810 * 2 ^ 59
def prefixEnd_3761810 : Nat := 4983230072969 + 3 ^ 40 * 3761810 * 2
def baseEnd_3761810 : Nat := 1287744440593354756516505

theorem tailTrace_3761810 : CollatzResearch.WordTrace tailWord_3761810 prefixEnd_3761810 1287744440593354756516505 := by
  unfold tailWord_3761810
  simp only [CollatzResearch.WordTrace]
  refine ⟨34301120625403077710944721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91469655001074873895852589 34301120625403077710944721)
  ·
    refine ⟨25725840469052308283208541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34301120625403077710944721 25725840469052308283208541)
    ·
      refine ⟨9647190175894615606203203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25725840469052308283208541 9647190175894615606203203)
      ·
        refine ⟨14470785263841923409304805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9647190175894615606203203 14470785263841923409304805)
        ·
          refine ⟨2713272236970360639244651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14470785263841923409304805 2713272236970360639244651)
          ·
            refine ⟨4069908355455540958866977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2713272236970360639244651 4069908355455540958866977)
            ·
              refine ⟨3052431266591655719150233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4069908355455540958866977 3052431266591655719150233)
              ·
                refine ⟨2289323449943741789362675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3052431266591655719150233 2289323449943741789362675)
                ·
                  refine ⟨3433985174915612684044013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2289323449943741789362675 3433985174915612684044013)
                  ·
                    refine ⟨1287744440593354756516505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3433985174915612684044013 1287744440593354756516505)
                    ·
                      rfl

theorem cell22_3761810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_3761810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761810 prefixEnd_3761810 := by exact prefixLift 3761810
  have htrace : WordTrace (prefixWord ++ tailWord_3761810) baseStart_3761810 baseEnd_3761810 := by
    simpa [prefixWord, tailWord_3761810, baseEnd_3761810] using wordTrace_append hprefix tailTrace_3761810
  have hstable : (prefixWord ++ tailWord_3761810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761810).length < 2 ^ (prefixWord ++ tailWord_3761810).sum := by decide
  have hdescent : baseEnd_3761810 < baseStart_3761810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761847 : List Nat := [1, 1, 3, 1, 5, 1, 3, 1, 2, 4]
def baseStart_3761847 : Nat := 118140960795 + 3761847 * 2 ^ 59
def prefixEnd_3761847 : Nat := 4983230072969 + 3 ^ 40 * 3761847 * 2
def baseEnd_3761847 : Nat := 1287757106449498993341391

theorem tailTrace_3761847 : CollatzResearch.WordTrace tailWord_3761847 prefixEnd_3761847 1287757106449498993341391 := by
  unfold tailWord_3761847
  simp only [CollatzResearch.WordTrace]
  refine ⟨137205832002478266162875795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91470554668318844108583863 137205832002478266162875795)
  ·
    refine ⟨205808748003717399244313693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137205832002478266162875795 205808748003717399244313693)
    ·
      refine ⟨77178280501394024716617635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205808748003717399244313693 77178280501394024716617635)
      ·
        refine ⟨115767420752091037074926453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77178280501394024716617635 115767420752091037074926453)
        ·
          refine ⟨10853195695508534725774355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115767420752091037074926453 10853195695508534725774355)
          ·
            refine ⟨16279793543262802088661533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10853195695508534725774355 16279793543262802088661533)
            ·
              refine ⟨6104922578723550783248075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16279793543262802088661533 6104922578723550783248075)
              ·
                refine ⟨9157383868085326174872113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6104922578723550783248075 9157383868085326174872113)
                ·
                  refine ⟨6868037901063994631154085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9157383868085326174872113 6868037901063994631154085)
                  ·
                    refine ⟨1287757106449498993341391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6868037901063994631154085 1287757106449498993341391)
                    ·
                      rfl

theorem cell22_3761847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_3761847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761847 prefixEnd_3761847 := by exact prefixLift 3761847
  have htrace : WordTrace (prefixWord ++ tailWord_3761847) baseStart_3761847 baseEnd_3761847 := by
    simpa [prefixWord, tailWord_3761847, baseEnd_3761847] using wordTrace_append hprefix tailTrace_3761847
  have hstable : (prefixWord ++ tailWord_3761847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761847).length < 2 ^ (prefixWord ++ tailWord_3761847).sum := by decide
  have hdescent : baseEnd_3761847 < baseStart_3761847 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761866 : List Nat := [3, 1, 2, 1, 5, 2, 1, 2, 2, 3]
def baseStart_3761866 : Nat := 118140960795 + 3761866 * 2 ^ 59
def prefixEnd_3761866 : Nat := 4983230072969 + 3 ^ 40 * 3761866 * 2
def baseEnd_3761866 : Nat := 1287763610537789277116333

theorem tailTrace_3761866 : CollatzResearch.WordTrace tailWord_3761866 prefixEnd_3761866 1287763610537789277116333 := by
  unfold tailWord_3761866
  simp only [CollatzResearch.WordTrace]
  refine ⟨34301631247352358101954363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91471016659606288271878301 34301631247352358101954363)
  ·
    refine ⟨51452446871028537152931545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34301631247352358101954363 51452446871028537152931545)
    ·
      refine ⟨38589335153271402864698659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51452446871028537152931545 38589335153271402864698659)
      ·
        refine ⟨57884002729907104297047989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38589335153271402864698659 57884002729907104297047989)
        ·
          refine ⟨5426625255928791027848249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57884002729907104297047989 5426625255928791027848249)
          ·
            refine ⟨4069968941946593270886187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5426625255928791027848249 4069968941946593270886187)
            ·
              refine ⟨6104953412919889906329281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4069968941946593270886187 6104953412919889906329281)
              ·
                refine ⟨4578715059689917429746961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6104953412919889906329281 4578715059689917429746961)
                ·
                  refine ⟨3434036294767438072310221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4578715059689917429746961 3434036294767438072310221)
                  ·
                    refine ⟨1287763610537789277116333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3434036294767438072310221 1287763610537789277116333)
                    ·
                      rfl

theorem cell22_3761866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 2, 1, 2, 2, 3].length) (baseStart_3761866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761866 prefixEnd_3761866 := by exact prefixLift 3761866
  have htrace : WordTrace (prefixWord ++ tailWord_3761866) baseStart_3761866 baseEnd_3761866 := by
    simpa [prefixWord, tailWord_3761866, baseEnd_3761866] using wordTrace_append hprefix tailTrace_3761866
  have hstable : (prefixWord ++ tailWord_3761866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761866).length < 2 ^ (prefixWord ++ tailWord_3761866).sum := by decide
  have hdescent : baseEnd_3761866 < baseStart_3761866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761935 : List Nat := [1, 1, 2, 1, 1, 1, 4, 5, 6]
def baseStart_3761935 : Nat := 118140960795 + 3761935 * 2 ^ 59
def prefixEnd_3761935 : Nat := 4983230072969 + 3 ^ 40 * 3761935 * 2
def baseEnd_3761935 : Nat := 429262410215965365713707

theorem tailTrace_3761935 : CollatzResearch.WordTrace tailWord_3761935 prefixEnd_3761935 429262410215965365713707 := by
  unfold tailWord_3761935
  simp only [CollatzResearch.WordTrace]
  refine ⟨137209041626159457192079259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91472694417439638128052839 137209041626159457192079259)
  ·
    refine ⟨205813562439239185788118889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137209041626159457192079259 205813562439239185788118889)
    ·
      refine ⟨154360171829429389341089167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205813562439239185788118889 154360171829429389341089167)
      ·
        refine ⟨231540257744144084011633751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154360171829429389341089167 231540257744144084011633751)
        ·
          refine ⟨347310386616216126017450627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231540257744144084011633751 347310386616216126017450627)
          ·
            refine ⟨520965579924324189026175941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347310386616216126017450627 520965579924324189026175941)
            ·
              refine ⟨97681046235810785442407989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 520965579924324189026175941 97681046235810785442407989)
              ·
                refine ⟨9157598084607261135225749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97681046235810785442407989 9157598084607261135225749)
                ·
                  refine ⟨429262410215965365713707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9157598084607261135225749 429262410215965365713707)
                  ·
                    rfl

theorem cell22_3761935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 5, 6].length) (baseStart_3761935 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761935 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761935 prefixEnd_3761935 := by exact prefixLift 3761935
  have htrace : WordTrace (prefixWord ++ tailWord_3761935) baseStart_3761935 baseEnd_3761935 := by
    simpa [prefixWord, tailWord_3761935, baseEnd_3761935] using wordTrace_append hprefix tailTrace_3761935
  have hstable : (prefixWord ++ tailWord_3761935).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761935).length < 2 ^ (prefixWord ++ tailWord_3761935).sum := by decide
  have hdescent : baseEnd_3761935 < baseStart_3761935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3761971 : List Nat := [1, 1, 1, 2, 7, 1, 3, 1, 1, 4]
def baseStart_3761971 : Nat := 118140960795 + 3761971 * 2 ^ 59
def prefixEnd_3761971 : Nat := 4983230072969 + 3 ^ 40 * 3761971 * 2
def baseEnd_3761971 : Nat := 1287799554183604003241011

theorem tailTrace_3761971 : CollatzResearch.WordTrace tailWord_3761971 prefixEnd_3761971 1287799554183604003241011 := by
  unfold tailWord_3761971
  simp only [CollatzResearch.WordTrace]
  refine ⟨137210354654029035340389767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91473569769352690226926511 137210354654029035340389767)
  ·
    refine ⟨205815531981043553010584651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137210354654029035340389767 205815531981043553010584651)
    ·
      refine ⟨308723297971565329515876977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205815531981043553010584651 308723297971565329515876977)
      ·
        refine ⟨231542473478673997136907733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308723297971565329515876977 231542473478673997136907733)
        ·
          refine ⟨5426776722156421807896275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 231542473478673997136907733 5426776722156421807896275)
          ·
            refine ⟨8140165083234632711844413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5426776722156421807896275 8140165083234632711844413)
            ·
              refine ⟨3052561906212987266941655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8140165083234632711844413 3052561906212987266941655)
              ·
                refine ⟨4578842859319480900412483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3052561906212987266941655 4578842859319480900412483)
                ·
                  refine ⟨6868264288979221350618725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4578842859319480900412483 6868264288979221350618725)
                  ·
                    refine ⟨1287799554183604003241011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6868264288979221350618725 1287799554183604003241011)
                    ·
                      rfl

theorem cell22_3761971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 3, 1, 1, 4].length) (baseStart_3761971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3761971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3761971 prefixEnd_3761971 := by exact prefixLift 3761971
  have htrace : WordTrace (prefixWord ++ tailWord_3761971) baseStart_3761971 baseEnd_3761971 := by
    simpa [prefixWord, tailWord_3761971, baseEnd_3761971] using wordTrace_append hprefix tailTrace_3761971
  have hstable : (prefixWord ++ tailWord_3761971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3761971).length < 2 ^ (prefixWord ++ tailWord_3761971).sum := by decide
  have hdescent : baseEnd_3761971 < baseStart_3761971 := by decide
  rcases family_descends (prefixWord ++ tailWord_3761971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762057 : List Nat := [1, 2, 1, 1, 5, 1, 1, 3, 2, 5]
def baseStart_3762057 : Nat := 118140960795 + 3762057 * 2 ^ 59
def prefixEnd_3762057 : Nat := 4983230072969 + 3 ^ 40 * 3762057 * 2
def baseEnd_3762057 : Nat := 1287828993741128445590747

theorem tailTrace_3762057 : CollatzResearch.WordTrace tailWord_3762057 prefixEnd_3762057 1287828993741128445590747 := by
  unfold tailWord_3762057
  simp only [CollatzResearch.WordTrace]
  refine ⟨137213491331717472028020425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91475660887811648018680283 137213491331717472028020425)
  ·
    refine ⟨102910118498788104021015319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137213491331717472028020425 102910118498788104021015319)
    ·
      refine ⟨154365177748182156031522979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102910118498788104021015319 154365177748182156031522979)
      ·
        refine ⟨231547766622273234047284469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154365177748182156031522979 231547766622273234047284469)
        ·
          refine ⟨21707603120838115691932919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 231547766622273234047284469 21707603120838115691932919)
          ·
            refine ⟨32561404681257173537899379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21707603120838115691932919 32561404681257173537899379)
            ·
              refine ⟨48842107021885760306849069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32561404681257173537899379 48842107021885760306849069)
              ·
                refine ⟨18315790133207160115068401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48842107021885760306849069 18315790133207160115068401)
                ·
                  refine ⟨13736842599905370086301301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18315790133207160115068401 13736842599905370086301301)
                  ·
                    refine ⟨1287828993741128445590747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13736842599905370086301301 1287828993741128445590747)
                    ·
                      rfl

theorem cell22_3762057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_3762057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3762057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3762057 prefixEnd_3762057 := by exact prefixLift 3762057
  have htrace : WordTrace (prefixWord ++ tailWord_3762057) baseStart_3762057 baseEnd_3762057 := by
    simpa [prefixWord, tailWord_3762057, baseEnd_3762057] using wordTrace_append hprefix tailTrace_3762057
  have hstable : (prefixWord ++ tailWord_3762057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762057).length < 2 ^ (prefixWord ++ tailWord_3762057).sum := by decide
  have hdescent : baseEnd_3762057 < baseStart_3762057 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762117 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 1, 6]
def baseStart_3762117 : Nat := 118140960795 + 3762117 * 2 ^ 59
def prefixEnd_3762117 : Nat := 4983230072969 + 3 ^ 40 * 3762117 * 2
def baseEnd_3762117 : Nat := 1287849532967308289090563

theorem tailTrace_3762117 : CollatzResearch.WordTrace tailWord_3762117 prefixEnd_3762117 1287849532967308289090563 := by
  unfold tailWord_3762117
  simp only [CollatzResearch.WordTrace]
  refine ⟨137215679711500102275204605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91477119807666734850136403 137215679711500102275204605)
  ·
    refine ⟨51455879891812538353201727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137215679711500102275204605 51455879891812538353201727)
    ·
      refine ⟨77183819837718807529802591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51455879891812538353201727 77183819837718807529802591)
      ·
        refine ⟨115775729756578211294703887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77183819837718807529802591 115775729756578211294703887)
        ·
          refine ⟨173663594634867316942055831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115775729756578211294703887 173663594634867316942055831)
          ·
            refine ⟨260495391952300975413083747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173663594634867316942055831 260495391952300975413083747)
            ·
              refine ⟨390743087928451463119625621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260495391952300975413083747 390743087928451463119625621)
              ·
                refine ⟨18316082246646162333732451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 390743087928451463119625621 18316082246646162333732451)
                ·
                  refine ⟨27474123369969243500598677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18316082246646162333732451 27474123369969243500598677)
                  ·
                    refine ⟨1287849532967308289090563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27474123369969243500598677 1287849532967308289090563)
                    ·
                      rfl

theorem cell22_3762117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_3762117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3762117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3762117 prefixEnd_3762117 := by exact prefixLift 3762117
  have htrace : WordTrace (prefixWord ++ tailWord_3762117) baseStart_3762117 baseEnd_3762117 := by
    simpa [prefixWord, tailWord_3762117, baseEnd_3762117] using wordTrace_append hprefix tailTrace_3762117
  have hstable : (prefixWord ++ tailWord_3762117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762117).length < 2 ^ (prefixWord ++ tailWord_3762117).sum := by decide
  have hdescent : baseEnd_3762117 < baseStart_3762117 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762181 : List Nat := [1, 3, 1, 1, 2, 5, 1, 2, 3, 3]
def baseStart_3762181 : Nat := 118140960795 + 3762181 * 2 ^ 59
def prefixEnd_3762181 : Nat := 4983230072969 + 3 ^ 40 * 3762181 * 2
def baseEnd_3762181 : Nat := 1287871441475233455490367

theorem tailTrace_3762181 : CollatzResearch.WordTrace tailWord_3762181 prefixEnd_3762181 1287871441475233455490367 := by
  unfold tailWord_3762181
  simp only [CollatzResearch.WordTrace]
  refine ⟨137218013983268241205534397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91478675988845494137022931 137218013983268241205534397)
  ·
    refine ⟨51456755243725590452075399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137218013983268241205534397 51456755243725590452075399)
    ·
      refine ⟨77185132865588385678113099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51456755243725590452075399 77185132865588385678113099)
      ·
        refine ⟨115777699298382578517169649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77185132865588385678113099 115777699298382578517169649)
        ·
          refine ⟨86833274473786933887877237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115777699298382578517169649 86833274473786933887877237)
          ·
            refine ⟨8140619481917525051988491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86833274473786933887877237 8140619481917525051988491)
            ·
              refine ⟨12210929222876287577982737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8140619481917525051988491 12210929222876287577982737)
              ·
                refine ⟨9158196917157215683487053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12210929222876287577982737 9158196917157215683487053)
                ·
                  refine ⟨3434323843933955881307645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9158196917157215683487053 3434323843933955881307645)
                  ·
                    refine ⟨1287871441475233455490367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3434323843933955881307645 1287871441475233455490367)
                    ·
                      rfl

theorem cell22_3762181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 2, 3, 3].length) (baseStart_3762181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3762181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3762181 prefixEnd_3762181 := by exact prefixLift 3762181
  have htrace : WordTrace (prefixWord ++ tailWord_3762181) baseStart_3762181 baseEnd_3762181 := by
    simpa [prefixWord, tailWord_3762181, baseEnd_3762181] using wordTrace_append hprefix tailTrace_3762181
  have hstable : (prefixWord ++ tailWord_3762181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762181).length < 2 ^ (prefixWord ++ tailWord_3762181).sum := by decide
  have hdescent : baseEnd_3762181 < baseStart_3762181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762215 : List Nat := [1, 1, 7, 1, 2, 1, 2, 1, 3, 3]
def baseStart_3762215 : Nat := 118140960795 + 3762215 * 2 ^ 59
def prefixEnd_3762215 : Nat := 4983230072969 + 3 ^ 40 * 3762215 * 2
def baseEnd_3762215 : Nat := 1287883080370068700140263

theorem tailTrace_3762215 : CollatzResearch.WordTrace tailWord_3762215 prefixEnd_3762215 1287883080370068700140263 := by
  unfold tailWord_3762215
  simp only [CollatzResearch.WordTrace]
  refine ⟨137219254065145065012272099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91479502710096710008181399 137219254065145065012272099)
  ·
    refine ⟨205828881097717597518408149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137219254065145065012272099 205828881097717597518408149)
    ·
      refine ⟨4824114400727756191837691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 205828881097717597518408149 4824114400727756191837691)
      ·
        refine ⟨7236171601091634287756537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4824114400727756191837691 7236171601091634287756537)
        ·
          refine ⟨5427128700818725715817403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7236171601091634287756537 5427128700818725715817403)
          ·
            refine ⟨8140693051228088573726105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5427128700818725715817403 8140693051228088573726105)
            ·
              refine ⟨6105519788421066430294579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8140693051228088573726105 6105519788421066430294579)
              ·
                refine ⟨9158279682631599645441869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6105519788421066430294579 9158279682631599645441869)
                ·
                  refine ⟨3434354880986849867040701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9158279682631599645441869 3434354880986849867040701)
                  ·
                    refine ⟨1287883080370068700140263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3434354880986849867040701 1287883080370068700140263)
                    ·
                      rfl

theorem cell22_3762215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_3762215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3762215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3762215 prefixEnd_3762215 := by exact prefixLift 3762215
  have htrace : WordTrace (prefixWord ++ tailWord_3762215) baseStart_3762215 baseEnd_3762215 := by
    simpa [prefixWord, tailWord_3762215, baseEnd_3762215] using wordTrace_append hprefix tailTrace_3762215
  have hstable : (prefixWord ++ tailWord_3762215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762215).length < 2 ^ (prefixWord ++ tailWord_3762215).sum := by decide
  have hdescent : baseEnd_3762215 < baseStart_3762215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762239 : List Nat := [1, 1, 2, 2, 3, 1, 4, 2, 6]
def baseStart_3762239 : Nat := 118140960795 + 3762239 * 2 ^ 59
def prefixEnd_3762239 : Nat := 4983230072969 + 3 ^ 40 * 3762239 * 2
def baseEnd_3762239 : Nat := 429297098686846879180063

theorem tailTrace_3762239 : CollatzResearch.WordTrace tailWord_3762239 prefixEnd_3762239 429297098686846879180063 := by
  unfold tailWord_3762239
  simp only [CollatzResearch.WordTrace]
  refine ⟨137220129417058117111145771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91480086278038744740763847 137220129417058117111145771)
  ·
    refine ⟨205830194125587175666718657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137220129417058117111145771 205830194125587175666718657)
    ·
      refine ⟨154372645594190381750038993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205830194125587175666718657 154372645594190381750038993)
      ·
        refine ⟨115779484195642786312529245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154372645594190381750038993 115779484195642786312529245)
        ·
          refine ⟨43417306573366044867198467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115779484195642786312529245 43417306573366044867198467)
          ·
            refine ⟨65125959860049067300797701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43417306573366044867198467 65125959860049067300797701)
            ·
              refine ⟨12211117473759200118899569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65125959860049067300797701 12211117473759200118899569)
              ·
                refine ⟨9158338105319400089174677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12211117473759200118899569 9158338105319400089174677)
                ·
                  refine ⟨429297098686846879180063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9158338105319400089174677 429297098686846879180063)
                  ·
                    rfl

theorem cell22_3762239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 2, 6].length) (baseStart_3762239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3762239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3762239 prefixEnd_3762239 := by exact prefixLift 3762239
  have htrace : WordTrace (prefixWord ++ tailWord_3762239) baseStart_3762239 baseEnd_3762239 := by
    simpa [prefixWord, tailWord_3762239, baseEnd_3762239] using wordTrace_append hprefix tailTrace_3762239
  have hstable : (prefixWord ++ tailWord_3762239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762239).length < 2 ^ (prefixWord ++ tailWord_3762239).sum := by decide
  have hdescent : baseEnd_3762239 < baseStart_3762239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762284 : List Nat := [2, 2, 1, 1, 3, 3, 1, 9]
def baseStart_3762284 : Nat := 118140960795 + 3762284 * 2 ^ 59
def prefixEnd_3762284 : Nat := 4983230072969 + 3 ^ 40 * 3762284 * 2
def baseEnd_3762284 : Nat := 143100744497797280018339

theorem tailTrace_3762284 : CollatzResearch.WordTrace tailWord_3762284 prefixEnd_3762284 143100744497797280018339 := by
  unfold tailWord_3762284
  simp only [CollatzResearch.WordTrace]
  refine ⟨68610885350947544898266953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91481180467930059864355937 68610885350947544898266953)
  ·
    refine ⟨51458164013210658673700215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68610885350947544898266953 51458164013210658673700215)
    ·
      refine ⟨77187246019815988010550323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51458164013210658673700215 77187246019815988010550323)
      ·
        refine ⟨115780869029723982015825485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77187246019815988010550323 115780869029723982015825485)
        ·
          refine ⟨43417825886146493255934557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115780869029723982015825485 43417825886146493255934557)
          ·
            refine ⟨16281684707304934970975459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43417825886146493255934557 16281684707304934970975459)
            ·
              refine ⟨24422527060957402456463189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16281684707304934970975459 24422527060957402456463189)
              ·
                refine ⟨143100744497797280018339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24422527060957402456463189 143100744497797280018339)
                ·
                  rfl

theorem cell22_3762284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 9].length) (baseStart_3762284 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3762284 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3762284 prefixEnd_3762284 := by exact prefixLift 3762284
  have htrace : WordTrace (prefixWord ++ tailWord_3762284) baseStart_3762284 baseEnd_3762284 := by
    simpa [prefixWord, tailWord_3762284, baseEnd_3762284] using wordTrace_append hprefix tailTrace_3762284
  have hstable : (prefixWord ++ tailWord_3762284).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762284).length < 2 ^ (prefixWord ++ tailWord_3762284).sum := by decide
  have hdescent : baseEnd_3762284 < baseStart_3762284 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762286 : List Nat := [4, 1, 2, 2, 1, 1, 1, 2, 4, 4]
def baseStart_3762286 : Nat := 118140960795 + 3762286 * 2 ^ 59
def prefixEnd_3762286 : Nat := 4983230072969 + 3 ^ 40 * 3762286 * 2
def baseEnd_3762286 : Nat := 1287907385121048181615045

theorem tailTrace_3762286 : CollatzResearch.WordTrace tailWord_3762286 prefixEnd_3762286 1287907385121048181615045 := by
  unfold tailWord_3762286
  simp only [CollatzResearch.WordTrace]
  refine ⟨17152730455985980517263339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91481229098591896092071141 17152730455985980517263339)
  ·
    refine ⟨25729095683978970775895009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17152730455985980517263339 25729095683978970775895009)
    ·
      refine ⟨19296821762984228081921257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25729095683978970775895009 19296821762984228081921257)
      ·
        refine ⟨14472616322238171061440943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19296821762984228081921257 14472616322238171061440943)
        ·
          refine ⟨21708924483357256592161415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14472616322238171061440943 21708924483357256592161415)
          ·
            refine ⟨32563386725035884888242123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21708924483357256592161415 32563386725035884888242123)
            ·
              refine ⟨48845080087553827332363185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32563386725035884888242123 48845080087553827332363185)
              ·
                refine ⟨36633810065665370499272389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48845080087553827332363185 36633810065665370499272389)
                ·
                  refine ⟨6868839387312256968613573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36633810065665370499272389 6868839387312256968613573)
                  ·
                    refine ⟨1287907385121048181615045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6868839387312256968613573 1287907385121048181615045)
                    ·
                      rfl

theorem cell22_3762286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_3762286 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3762286 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3762286 prefixEnd_3762286 := by exact prefixLift 3762286
  have htrace : WordTrace (prefixWord ++ tailWord_3762286) baseStart_3762286 baseEnd_3762286 := by
    simpa [prefixWord, tailWord_3762286, baseEnd_3762286] using wordTrace_append hprefix tailTrace_3762286
  have hstable : (prefixWord ++ tailWord_3762286).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762286).length < 2 ^ (prefixWord ++ tailWord_3762286).sum := by decide
  have hdescent : baseEnd_3762286 < baseStart_3762286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762288 : List Nat := [2, 1, 1, 1, 5, 3, 1, 3, 2, 3]
def baseStart_3762288 : Nat := 118140960795 + 3762288 * 2 ^ 59
def prefixEnd_3762288 : Nat := 4983230072969 + 3 ^ 40 * 3762288 * 2
def baseEnd_3762288 : Nat := 1287908069761920843065039

theorem tailTrace_3762288 : CollatzResearch.WordTrace tailWord_3762288 prefixEnd_3762288 1287908069761920843065039 := by
  unfold tailWord_3762288
  simp only [CollatzResearch.WordTrace]
  refine ⟨68610958296940299239839759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91481277729253732319786345 68610958296940299239839759)
  ·
    refine ⟨102916437445410448859759639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68610958296940299239839759 102916437445410448859759639)
    ·
      refine ⟨154374656168115673289639459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102916437445410448859759639 154374656168115673289639459)
      ·
        refine ⟨231561984252173509934459189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154374656168115673289639459 231561984252173509934459189)
        ·
          refine ⟨21708936023641266556355549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 231561984252173509934459189 21708936023641266556355549)
          ·
            refine ⟨8140851008865474958633331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21708936023641266556355549 8140851008865474958633331)
            ·
              refine ⟨12211276513298212437949997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8140851008865474958633331 12211276513298212437949997)
              ·
                refine ⟨4579228692486829664231249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12211276513298212437949997 4579228692486829664231249)
                ·
                  refine ⟨3434421519365122248173437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4579228692486829664231249 3434421519365122248173437)
                  ·
                    refine ⟨1287908069761920843065039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3434421519365122248173437 1287908069761920843065039)
                    ·
                      rfl

theorem cell22_3762288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 1, 3, 2, 3].length) (baseStart_3762288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3762288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3762288 prefixEnd_3762288 := by exact prefixLift 3762288
  have htrace : WordTrace (prefixWord ++ tailWord_3762288) baseStart_3762288 baseEnd_3762288 := by
    simpa [prefixWord, tailWord_3762288, baseEnd_3762288] using wordTrace_append hprefix tailTrace_3762288
  have hstable : (prefixWord ++ tailWord_3762288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762288).length < 2 ^ (prefixWord ++ tailWord_3762288).sum := by decide
  have hdescent : baseEnd_3762288 < baseStart_3762288 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762324 : List Nat := [2, 4, 2, 3, 1, 2, 2, 2, 4]
def baseStart_3762324 : Nat := 118140960795 + 3762324 * 2 ^ 59
def prefixEnd_3762324 : Nat := 4983230072969 + 3 ^ 40 * 3762324 * 2
def baseEnd_3762324 : Nat := 429306797765876249721643

theorem tailTrace_3762324 : CollatzResearch.WordTrace tailWord_3762324 prefixEnd_3762324 429306797765876249721643 := by
  unfold tailWord_3762324
  simp only [CollatzResearch.WordTrace]
  refine ⟨68611614810875088313995013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91482153081166784418660017 68611614810875088313995013)
  ·
    refine ⟨12864677777039079058874065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68611614810875088313995013 12864677777039079058874065)
    ·
      refine ⟨9648508332779309294155549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12864677777039079058874065 9648508332779309294155549)
      ·
        refine ⟨3618190624792240985308331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9648508332779309294155549 3618190624792240985308331)
        ·
          refine ⟨5427285937188361477962497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3618190624792240985308331 5427285937188361477962497)
          ·
            refine ⟨4070464452891271108471873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5427285937188361477962497 4070464452891271108471873)
            ·
              refine ⟨3052848339668453331353905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4070464452891271108471873 3052848339668453331353905)
              ·
                refine ⟨2289636254751339998515429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3052848339668453331353905 2289636254751339998515429)
                ·
                  refine ⟨429306797765876249721643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2289636254751339998515429 429306797765876249721643)
                  ·
                    rfl

theorem cell22_3762324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_3762324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3762324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3762324 prefixEnd_3762324 := by exact prefixLift 3762324
  have htrace : WordTrace (prefixWord ++ tailWord_3762324) baseStart_3762324 baseEnd_3762324 := by
    simpa [prefixWord, tailWord_3762324, baseEnd_3762324] using wordTrace_append hprefix tailTrace_3762324
  have hstable : (prefixWord ++ tailWord_3762324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762324).length < 2 ^ (prefixWord ++ tailWord_3762324).sum := by decide
  have hdescent : baseEnd_3762324 < baseStart_3762324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762329 : List Nat := [1, 2, 1, 2, 1, 2, 1, 5, 7]
def baseStart_3762329 : Nat := 118140960795 + 3762329 * 2 ^ 59
def prefixEnd_3762329 : Nat := 4983230072969 + 3 ^ 40 * 3762329 * 2
def baseEnd_3762329 : Nat := 429307368299936800929971

theorem tailTrace_3762329 : CollatzResearch.WordTrace tailWord_3762329 prefixEnd_3762329 429307368299936800929971 := by
  unfold tailWord_3762329
  simp only [CollatzResearch.WordTrace]
  refine ⟨137223411986732062481922041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91482274657821374987948027 137223411986732062481922041)
  ·
    refine ⟨102917558990049046861441531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137223411986732062481922041 102917558990049046861441531)
    ·
      refine ⟨154376338485073570292162297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102917558990049046861441531 154376338485073570292162297)
      ·
        refine ⟨115782253863805177719121723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154376338485073570292162297 115782253863805177719121723)
        ·
          refine ⟨173673380795707766578682585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115782253863805177719121723 173673380795707766578682585)
          ·
            refine ⟨130255035596780824934011939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173673380795707766578682585 130255035596780824934011939)
            ·
              refine ⟨195382553395171237401017909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130255035596780824934011939 195382553395171237401017909)
              ·
                refine ⟨18317114380797303506345429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 195382553395171237401017909 18317114380797303506345429)
                ·
                  refine ⟨429307368299936800929971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18317114380797303506345429 429307368299936800929971)
                  ·
                    rfl

theorem cell22_3762329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 5, 7].length) (baseStart_3762329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3762329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3762329 prefixEnd_3762329 := by exact prefixLift 3762329
  have htrace : WordTrace (prefixWord ++ tailWord_3762329) baseStart_3762329 baseEnd_3762329 := by
    simpa [prefixWord, tailWord_3762329, baseEnd_3762329] using wordTrace_append hprefix tailTrace_3762329
  have hstable : (prefixWord ++ tailWord_3762329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762329).length < 2 ^ (prefixWord ++ tailWord_3762329).sum := by decide
  have hdescent : baseEnd_3762329 < baseStart_3762329 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762513 : List Nat := [1, 2, 2, 1, 4, 3, 1, 1, 2, 5]
def baseStart_3762513 : Nat := 118140960795 + 3762513 * 2 ^ 59
def prefixEnd_3762513 : Nat := 4983230072969 + 3 ^ 40 * 3762513 * 2
def baseEnd_3762513 : Nat := 1287985091860095256189349

theorem tailTrace_3762513 : CollatzResearch.WordTrace tailWord_3762513 prefixEnd_3762513 1287985091860095256189349 := by
  unfold tailWord_3762513
  simp only [CollatzResearch.WordTrace]
  refine ⟨137230123018065461906620193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91486748678710307937746795 137230123018065461906620193)
  ·
    refine ⟨102922592263549096429965145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137230123018065461906620193 102922592263549096429965145)
    ·
      refine ⟨77191944197661822322473859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102922592263549096429965145 77191944197661822322473859)
      ·
        refine ⟨115787916296492733483710789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77191944197661822322473859 115787916296492733483710789)
        ·
          refine ⟨21710234305592387528195773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115787916296492733483710789 21710234305592387528195773)
          ·
            refine ⟨8141337864597145323073415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21710234305592387528195773 8141337864597145323073415)
            ·
              refine ⟨12212006796895717984610123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8141337864597145323073415 12212006796895717984610123)
              ·
                refine ⟨18318010195343576976915185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12212006796895717984610123 18318010195343576976915185)
                ·
                  refine ⟨13738507646507682732686389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18318010195343576976915185 13738507646507682732686389)
                  ·
                    refine ⟨1287985091860095256189349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13738507646507682732686389 1287985091860095256189349)
                    ·
                      rfl

theorem cell22_3762513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_3762513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3762513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3762513 prefixEnd_3762513 := by exact prefixLift 3762513
  have htrace : WordTrace (prefixWord ++ tailWord_3762513) baseStart_3762513 baseEnd_3762513 := by
    simpa [prefixWord, tailWord_3762513, baseEnd_3762513] using wordTrace_append hprefix tailTrace_3762513
  have hstable : (prefixWord ++ tailWord_3762513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762513).length < 2 ^ (prefixWord ++ tailWord_3762513).sum := by decide
  have hdescent : baseEnd_3762513 < baseStart_3762513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762648 : List Nat := [2, 1, 2, 2, 2, 1, 1, 2, 4, 5]
def baseStart_3762648 : Nat := 118140960795 + 3762648 * 2 ^ 59
def prefixEnd_3762648 : Nat := 4983230072969 + 3 ^ 40 * 3762648 * 2
def baseEnd_3762648 : Nat := 1288031305118999904063935

theorem tailTrace_3762648 : CollatzResearch.WordTrace tailWord_3762648 prefixEnd_3762648 1288031305118999904063935 := by
  unfold tailWord_3762648
  simp only [CollatzResearch.WordTrace]
  refine ⟨68617523436288189981392299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91490031248384253308523065 68617523436288189981392299)
  ·
    refine ⟨102926285154432284972088449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68617523436288189981392299 102926285154432284972088449)
    ·
      refine ⟨77194713865824213729066337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102926285154432284972088449 77194713865824213729066337)
      ·
        refine ⟨57896035399368160296799753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77194713865824213729066337 57896035399368160296799753)
        ·
          refine ⟨43422026549526120222599815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57896035399368160296799753 43422026549526120222599815)
          ·
            refine ⟨65133039824289180333899723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43422026549526120222599815 65133039824289180333899723)
            ·
              refine ⟨97699559736433770500849585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65133039824289180333899723 97699559736433770500849585)
              ·
                refine ⟨73274669802325327875637189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97699559736433770500849585 73274669802325327875637189)
                ·
                  refine ⟨13739000587935998976681973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 73274669802325327875637189 13739000587935998976681973)
                  ·
                    refine ⟨1288031305118999904063935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13739000587935998976681973 1288031305118999904063935)
                    ·
                      rfl

theorem cell22_3762648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 2, 4, 5].length) (baseStart_3762648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3762648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3762648 prefixEnd_3762648 := by exact prefixLift 3762648
  have htrace : WordTrace (prefixWord ++ tailWord_3762648) baseStart_3762648 baseEnd_3762648 := by
    simpa [prefixWord, tailWord_3762648, baseEnd_3762648] using wordTrace_append hprefix tailTrace_3762648
  have hstable : (prefixWord ++ tailWord_3762648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762648).length < 2 ^ (prefixWord ++ tailWord_3762648).sum := by decide
  have hdescent : baseEnd_3762648 < baseStart_3762648 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762712 : List Nat := [2, 1, 2, 3, 3, 1, 1, 5, 4]
def baseStart_3762712 : Nat := 118140960795 + 3762712 * 2 ^ 59
def prefixEnd_3762712 : Nat := 4983230072969 + 3 ^ 40 * 3762712 * 2
def baseEnd_3762712 : Nat := 429351071208975023487913

theorem tailTrace_3762712 : CollatzResearch.WordTrace tailWord_3762712 prefixEnd_3762712 429351071208975023487913 := by
  unfold tailWord_3762712
  simp only [CollatzResearch.WordTrace]
  refine ⟨68618690572172259446557195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91491587429563012595409593 68618690572172259446557195)
  ·
    refine ⟨102928035858258389169835793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68618690572172259446557195 102928035858258389169835793)
    ·
      refine ⟨77196026893693791877376845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102928035858258389169835793 77196026893693791877376845)
      ·
        refine ⟨28948510085135171954016317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77196026893693791877376845 28948510085135171954016317)
        ·
          refine ⟨10855691281925689482756119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28948510085135171954016317 10855691281925689482756119)
          ·
            refine ⟨16283536922888534224134179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10855691281925689482756119 16283536922888534224134179)
            ·
              refine ⟨24425305384332801336201269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16283536922888534224134179 24425305384332801336201269)
              ·
                refine ⟨2289872379781200125268869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24425305384332801336201269 2289872379781200125268869)
                ·
                  refine ⟨429351071208975023487913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2289872379781200125268869 429351071208975023487913)
                  ·
                    rfl

theorem cell22_3762712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 5, 4].length) (baseStart_3762712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3762712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3762712 prefixEnd_3762712 := by exact prefixLift 3762712
  have htrace : WordTrace (prefixWord ++ tailWord_3762712) baseStart_3762712 baseEnd_3762712 := by
    simpa [prefixWord, tailWord_3762712, baseEnd_3762712] using wordTrace_append hprefix tailTrace_3762712
  have hstable : (prefixWord ++ tailWord_3762712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762712).length < 2 ^ (prefixWord ++ tailWord_3762712).sum := by decide
  have hdescent : baseEnd_3762712 < baseStart_3762712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762725 : List Nat := [1, 3, 1, 2, 2, 1, 2, 4, 2, 4]
def baseStart_3762725 : Nat := 118140960795 + 3762725 * 2 ^ 59
def prefixEnd_3762725 : Nat := 4983230072969 + 3 ^ 40 * 3762725 * 2
def baseEnd_3762725 : Nat := 1288057663792597369888699

theorem tailTrace_3762725 : CollatzResearch.WordTrace tailWord_3762725 prefixEnd_3762725 1288057663792597369888699 := by
  unfold tailWord_3762725
  simp only [CollatzResearch.WordTrace]
  refine ⟨137237855293297422113337629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91491903528864948075558419 137237855293297422113337629)
  ·
    refine ⟨51464195734986533292501611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137237855293297422113337629 51464195734986533292501611)
    ·
      refine ⟨77196293602479799938752417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51464195734986533292501611 77196293602479799938752417)
      ·
        refine ⟨57897220201859849954064313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77196293602479799938752417 57897220201859849954064313)
        ·
          refine ⟨43422915151394887465548235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57897220201859849954064313 43422915151394887465548235)
          ·
            refine ⟨65134372727092331198322353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43422915151394887465548235 65134372727092331198322353)
            ·
              refine ⟨48850779545319248398741765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65134372727092331198322353 48850779545319248398741765)
              ·
                refine ⟨9159521164747359074764081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48850779545319248398741765 9159521164747359074764081)
                ·
                  refine ⟨6869640873560519306073061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9159521164747359074764081 6869640873560519306073061)
                  ·
                    refine ⟨1288057663792597369888699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6869640873560519306073061 1288057663792597369888699)
                    ·
                      rfl

theorem cell22_3762725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 4, 2, 4].length) (baseStart_3762725 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3762725 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3762725 prefixEnd_3762725 := by exact prefixLift 3762725
  have htrace : WordTrace (prefixWord ++ tailWord_3762725) baseStart_3762725 baseEnd_3762725 := by
    simpa [prefixWord, tailWord_3762725, baseEnd_3762725] using wordTrace_append hprefix tailTrace_3762725
  have hstable : (prefixWord ++ tailWord_3762725).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762725).length < 2 ^ (prefixWord ++ tailWord_3762725).sum := by decide
  have hdescent : baseEnd_3762725 < baseStart_3762725 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762742 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_3762742 : Nat := 118140960795 + 3762742 * 2 ^ 59
def prefixEnd_3762742 : Nat := 4983230072969 + 3 ^ 40 * 3762742 * 2
def baseEnd_3762742 : Nat := 1288063483240014992213647

theorem tailTrace_3762742 : CollatzResearch.WordTrace tailWord_3762742 prefixEnd_3762742 1288063483240014992213647 := by
  unfold tailWord_3762742
  simp only [CollatzResearch.WordTrace]
  refine ⟨8577404708389739626044155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91492316889490556011137653 8577404708389739626044155)
  ·
    refine ⟨12866107062584609439066233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8577404708389739626044155 12866107062584609439066233)
    ·
      refine ⟨9649580296938457079299675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12866107062584609439066233 9649580296938457079299675)
      ·
        refine ⟨14474370445407685618949513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9649580296938457079299675 14474370445407685618949513)
        ·
          refine ⟨10855777834055764214212135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14474370445407685618949513 10855777834055764214212135)
          ·
            refine ⟨16283666751083646321318203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10855777834055764214212135 16283666751083646321318203)
            ·
              refine ⟨24425500126625469481977305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16283666751083646321318203 24425500126625469481977305)
              ·
                refine ⟨18319125094969102111482979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24425500126625469481977305 18319125094969102111482979)
                ·
                  refine ⟨27478687642453653167224469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18319125094969102111482979 27478687642453653167224469)
                  ·
                    refine ⟨1288063483240014992213647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27478687642453653167224469 1288063483240014992213647)
                    ·
                      rfl

theorem cell22_3762742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_3762742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3762742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3762742 prefixEnd_3762742 := by exact prefixLift 3762742
  have htrace : WordTrace (prefixWord ++ tailWord_3762742) baseStart_3762742 baseEnd_3762742 := by
    simpa [prefixWord, tailWord_3762742, baseEnd_3762742] using wordTrace_append hprefix tailTrace_3762742
  have hstable : (prefixWord ++ tailWord_3762742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762742).length < 2 ^ (prefixWord ++ tailWord_3762742).sum := by decide
  have hdescent : baseEnd_3762742 < baseStart_3762742 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762744 : List Nat := [2, 1, 2, 1, 4, 1, 5, 1, 2, 3]
def baseStart_3762744 : Nat := 118140960795 + 3762744 * 2 ^ 59
def prefixEnd_3762744 : Nat := 4983230072969 + 3 ^ 40 * 3762744 * 2
def baseEnd_3762744 : Nat := 1288064167880887653663641

theorem tailTrace_3762744 : CollatzResearch.WordTrace tailWord_3762744 prefixEnd_3762744 1288064167880887653663641 := by
  unfold tailWord_3762744
  simp only [CollatzResearch.WordTrace]
  refine ⟨68619274140114294179139643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91492365520152392238852857 68619274140114294179139643)
  ·
    refine ⟨102928911210171441268709465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68619274140114294179139643 102928911210171441268709465)
    ·
      refine ⟨77196683407628580951532099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102928911210171441268709465 77196683407628580951532099)
      ·
        refine ⟨115795025111442871427298149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77196683407628580951532099 115795025111442871427298149)
        ·
          refine ⟨21711567208395538392618403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115795025111442871427298149 21711567208395538392618403)
          ·
            refine ⟨32567350812593307588927605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21711567208395538392618403 32567350812593307588927605)
            ·
              refine ⟨3053189138680622586461963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32567350812593307588927605 3053189138680622586461963)
              ·
                refine ⟨4579783708020933879692945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3053189138680622586461963 4579783708020933879692945)
                ·
                  refine ⟨3434837781015700409769709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4579783708020933879692945 3434837781015700409769709)
                  ·
                    refine ⟨1288064167880887653663641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3434837781015700409769709 1288064167880887653663641)
                    ·
                      rfl

theorem cell22_3762744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 5, 1, 2, 3].length) (baseStart_3762744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3762744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3762744 prefixEnd_3762744 := by exact prefixLift 3762744
  have htrace : WordTrace (prefixWord ++ tailWord_3762744) baseStart_3762744 baseEnd_3762744 := by
    simpa [prefixWord, tailWord_3762744, baseEnd_3762744] using wordTrace_append hprefix tailTrace_3762744
  have hstable : (prefixWord ++ tailWord_3762744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762744).length < 2 ^ (prefixWord ++ tailWord_3762744).sum := by decide
  have hdescent : baseEnd_3762744 < baseStart_3762744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762757 : List Nat := [1, 3, 1, 1, 1, 7, 2, 6]
def baseStart_3762757 : Nat := 118140960795 + 3762757 * 2 ^ 59
def prefixEnd_3762757 : Nat := 4983230072969 + 3 ^ 40 * 3762757 * 2
def baseEnd_3762757 : Nat := 143118735338506661454289

theorem tailTrace_3762757 : CollatzResearch.WordTrace tailWord_3762757 prefixEnd_3762757 143118735338506661454289 := by
  unfold tailWord_3762757
  simp only [CollatzResearch.WordTrace]
  refine ⟨137239022429181491578502525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91492681619454327719001683 137239022429181491578502525)
  ·
    refine ⟨51464633410943059341938447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137239022429181491578502525 51464633410943059341938447)
    ·
      refine ⟨77196950116414589012907671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51464633410943059341938447 77196950116414589012907671)
      ·
        refine ⟨115795425174621883519361507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77196950116414589012907671 115795425174621883519361507)
        ·
          refine ⟨173693137761932825279042261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115795425174621883519361507 173693137761932825279042261)
          ·
            refine ⟨4070932916295300592477553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 173693137761932825279042261 4070932916295300592477553)
            ·
              refine ⟨3053199687221475444358165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4070932916295300592477553 3053199687221475444358165)
              ·
                refine ⟨143118735338506661454289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3053199687221475444358165 143118735338506661454289)
                ·
                  rfl

theorem cell22_3762757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 2, 6].length) (baseStart_3762757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3762757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3762757 prefixEnd_3762757 := by exact prefixLift 3762757
  have htrace : WordTrace (prefixWord ++ tailWord_3762757) baseStart_3762757 baseEnd_3762757 := by
    simpa [prefixWord, tailWord_3762757, baseEnd_3762757] using wordTrace_append hprefix tailTrace_3762757
  have hstable : (prefixWord ++ tailWord_3762757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762757).length < 2 ^ (prefixWord ++ tailWord_3762757).sum := by decide
  have hdescent : baseEnd_3762757 < baseStart_3762757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762785 : List Nat := [1, 2, 3, 1, 1, 4, 2, 1, 7]
def baseStart_3762785 : Nat := 118140960795 + 3762785 * 2 ^ 59
def prefixEnd_3762785 : Nat := 4983230072969 + 3 ^ 40 * 3762785 * 2
def baseEnd_3762785 : Nat := 429359401006259071129505

theorem tailTrace_3762785 : CollatzResearch.WordTrace tailWord_3762785 prefixEnd_3762785 429359401006259071129505 := by
  unfold tailWord_3762785
  simp only [CollatzResearch.WordTrace]
  refine ⟨137240043673080052360521809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91493362448720034907014539 137240043673080052360521809)
  ·
    refine ⟨102930032754810039270391357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137240043673080052360521809 102930032754810039270391357)
    ·
      refine ⟨38598762283053764726396759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102930032754810039270391357 38598762283053764726396759)
      ·
        refine ⟨57898143424580647089595139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38598762283053764726396759 57898143424580647089595139)
        ·
          refine ⟨86847215136870970634392709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57898143424580647089595139 86847215136870970634392709)
          ·
            refine ⟨16283852838163306993948633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86847215136870970634392709 16283852838163306993948633)
            ·
              refine ⟨12212889628622480245461475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16283852838163306993948633 12212889628622480245461475)
              ·
                refine ⟨18319334442933720368192213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12212889628622480245461475 18319334442933720368192213)
                ·
                  refine ⟨429359401006259071129505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18319334442933720368192213 429359401006259071129505)
                  ·
                    rfl

theorem cell22_3762785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 1, 7].length) (baseStart_3762785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3762785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3762785 prefixEnd_3762785 := by exact prefixLift 3762785
  have htrace : WordTrace (prefixWord ++ tailWord_3762785) baseStart_3762785 baseEnd_3762785 := by
    simpa [prefixWord, tailWord_3762785, baseEnd_3762785] using wordTrace_append hprefix tailTrace_3762785
  have hstable : (prefixWord ++ tailWord_3762785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762785).length < 2 ^ (prefixWord ++ tailWord_3762785).sum := by decide
  have hdescent : baseEnd_3762785 < baseStart_3762785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762877 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 1, 6]
def baseStart_3762877 : Nat := 118140960795 + 3762877 * 2 ^ 59
def prefixEnd_3762877 : Nat := 4983230072969 + 3 ^ 40 * 3762877 * 2
def baseEnd_3762877 : Nat := 1288109696498919640088233

theorem tailTrace_3762877 : CollatzResearch.WordTrace tailWord_3762877 prefixEnd_3762877 1288109696498919640088233 := by
  unfold tailWord_3762877
  simp only [CollatzResearch.WordTrace]
  refine ⟨137243399188746752072870885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91495599459164501381913923 137243399188746752072870885)
  ·
    refine ⟨25733137347890016013663291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137243399188746752072870885 25733137347890016013663291)
    ·
      refine ⟨38599706021835024020494937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25733137347890016013663291 38599706021835024020494937)
      ·
        refine ⟨28949779516376268015371203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38599706021835024020494937 28949779516376268015371203)
        ·
          refine ⟨43424669274564402023056805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28949779516376268015371203 43424669274564402023056805)
          ·
            refine ⟨8142125488980825379323151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43424669274564402023056805 8142125488980825379323151)
            ·
              refine ⟨12213188233471238068984727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8142125488980825379323151 12213188233471238068984727)
              ·
                refine ⟨18319782350206857103477091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12213188233471238068984727 18319782350206857103477091)
                ·
                  refine ⟨27479673525310285655215637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18319782350206857103477091 27479673525310285655215637)
                  ·
                    refine ⟨1288109696498919640088233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27479673525310285655215637 1288109696498919640088233)
                    ·
                      rfl

theorem cell22_3762877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_3762877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3762877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3762877 prefixEnd_3762877 := by exact prefixLift 3762877
  have htrace : WordTrace (prefixWord ++ tailWord_3762877) baseStart_3762877 baseEnd_3762877 := by
    simpa [prefixWord, tailWord_3762877, baseEnd_3762877] using wordTrace_append hprefix tailTrace_3762877
  have hstable : (prefixWord ++ tailWord_3762877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762877).length < 2 ^ (prefixWord ++ tailWord_3762877).sum := by decide
  have hdescent : baseEnd_3762877 < baseStart_3762877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762892 : List Nat := [2, 2, 1, 5, 1, 2, 9]
def baseStart_3762892 : Nat := 118140960795 + 3762892 * 2 ^ 59
def prefixEnd_3762892 : Nat := 4983230072969 + 3 ^ 40 * 3762892 * 2
def baseEnd_3762892 : Nat := 47707956715017207443081

theorem tailTrace_3762892 : CollatzResearch.WordTrace tailWord_3762892 prefixEnd_3762892 47707956715017207443081 := by
  unfold tailWord_3762892
  simp only [CollatzResearch.WordTrace]
  refine ⟨68621973141846204817333465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91495964189128273089777953 68621973141846204817333465)
  ·
    refine ⟨51466479856384653613000099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68621973141846204817333465 51466479856384653613000099)
    ·
      refine ⟨77199719784576980419500149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51466479856384653613000099 77199719784576980419500149)
      ·
        refine ⟨7237473729804091914328139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77199719784576980419500149 7237473729804091914328139)
        ·
          refine ⟨10856210594706137871492209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7237473729804091914328139 10856210594706137871492209)
          ·
            refine ⟨8142157946029603403619157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10856210594706137871492209 8142157946029603403619157)
            ·
              refine ⟨47707956715017207443081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8142157946029603403619157 47707956715017207443081)
              ·
                rfl

theorem cell22_3762892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 9].length) (baseStart_3762892 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3762892 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3762892 prefixEnd_3762892 := by exact prefixLift 3762892
  have htrace : WordTrace (prefixWord ++ tailWord_3762892) baseStart_3762892 baseEnd_3762892 := by
    simpa [prefixWord, tailWord_3762892, baseEnd_3762892] using wordTrace_append hprefix tailTrace_3762892
  have hstable : (prefixWord ++ tailWord_3762892).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762892).length < 2 ^ (prefixWord ++ tailWord_3762892).sum := by decide
  have hdescent : baseEnd_3762892 < baseStart_3762892 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762932 : List Nat := [2, 6, 1, 1, 3, 1, 1, 3, 4]
def baseStart_3762932 : Nat := 118140960795 + 3762932 * 2 ^ 59
def prefixEnd_3762932 : Nat := 4983230072969 + 3 ^ 40 * 3762932 * 2
def baseEnd_3762932 : Nat := 429376174707639276654355

theorem tailTrace_3762932 : CollatzResearch.WordTrace tailWord_3762932 prefixEnd_3762932 429376174707639276654355 := by
  unfold tailWord_3762932
  simp only [CollatzResearch.WordTrace]
  refine ⟨68622702601773748233061525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91496936802364997644082033 68622702601773748233061525)
  ·
    refine ⟨3216689184458144448424759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68622702601773748233061525 3216689184458144448424759)
    ·
      refine ⟨4825033776687216672637139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3216689184458144448424759 4825033776687216672637139)
      ·
        refine ⟨7237550665030825008955709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4825033776687216672637139 7237550665030825008955709)
        ·
          refine ⟨2714081499386559378358391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7237550665030825008955709 2714081499386559378358391)
          ·
            refine ⟨4071122249079839067537587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2714081499386559378358391 4071122249079839067537587)
            ·
              refine ⟨6106683373619758601306381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4071122249079839067537587 6106683373619758601306381)
              ·
                refine ⟨2290006265107409475489893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6106683373619758601306381 2290006265107409475489893)
                ·
                  refine ⟨429376174707639276654355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2290006265107409475489893 429376174707639276654355)
                  ·
                    rfl

theorem cell22_3762932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_3762932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3762932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3762932 prefixEnd_3762932 := by exact prefixLift 3762932
  have htrace : WordTrace (prefixWord ++ tailWord_3762932) baseStart_3762932 baseEnd_3762932 := by
    simpa [prefixWord, tailWord_3762932, baseEnd_3762932] using wordTrace_append hprefix tailTrace_3762932
  have hstable : (prefixWord ++ tailWord_3762932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762932).length < 2 ^ (prefixWord ++ tailWord_3762932).sum := by decide
  have hdescent : baseEnd_3762932 < baseStart_3762932 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762984 : List Nat := [2, 1, 5, 1, 1, 1, 3, 1, 3, 4]
def baseStart_3762984 : Nat := 118140960795 + 3762984 * 2 ^ 59
def prefixEnd_3762984 : Nat := 4983230072969 + 3 ^ 40 * 3762984 * 2
def baseEnd_3762984 : Nat := 1288146324785607027662905

theorem tailTrace_3762984 : CollatzResearch.WordTrace tailWord_3762984 prefixEnd_3762984 1288146324785607027662905 := by
  unfold tailWord_3762984
  simp only [CollatzResearch.WordTrace]
  refine ⟨68623650899679554673508003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91498201199572739564677337 68623650899679554673508003)
  ·
    refine ⟨102935476349519332010262005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68623650899679554673508003 102935476349519332010262005)
    ·
      refine ⟨9650200907767437375962063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102935476349519332010262005 9650200907767437375962063)
      ·
        refine ⟨14475301361651156063943095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9650200907767437375962063 14475301361651156063943095)
        ·
          refine ⟨21712952042476734095914643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14475301361651156063943095 21712952042476734095914643)
          ·
            refine ⟨32569428063715101143871965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21712952042476734095914643 32569428063715101143871965)
            ·
              refine ⟨12213535523893162928951987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32569428063715101143871965 12213535523893162928951987)
              ·
                refine ⟨18320303285839744393427981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12213535523893162928951987 18320303285839744393427981)
                ·
                  refine ⟨6870113732189904147535493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18320303285839744393427981 6870113732189904147535493)
                  ·
                    refine ⟨1288146324785607027662905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6870113732189904147535493 1288146324785607027662905)
                    ·
                      rfl

theorem cell22_3762984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_3762984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3762984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3762984 prefixEnd_3762984 := by exact prefixLift 3762984
  have htrace : WordTrace (prefixWord ++ tailWord_3762984) baseStart_3762984 baseEnd_3762984 := by
    simpa [prefixWord, tailWord_3762984, baseEnd_3762984] using wordTrace_append hprefix tailTrace_3762984
  have hstable : (prefixWord ++ tailWord_3762984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762984).length < 2 ^ (prefixWord ++ tailWord_3762984).sum := by decide
  have hdescent : baseEnd_3762984 < baseStart_3762984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3762999 : List Nat := [1, 1, 3, 1, 2, 1, 4, 5, 4]
def baseStart_3762999 : Nat := 118140960795 + 3762999 * 2 ^ 59
def prefixEnd_3762999 : Nat := 4983230072969 + 3 ^ 40 * 3762999 * 2
def baseEnd_3762999 : Nat := 429383819864050662845953

theorem tailTrace_3762999 : CollatzResearch.WordTrace tailWord_3762999 prefixEnd_3762999 429383819864050662845953 := by
  unfold tailWord_3762999
  simp only [CollatzResearch.WordTrace]
  refine ⟨137247848894304766908812051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91498565929536511272541367 137247848894304766908812051)
  ·
    refine ⟨205871773341457150363218077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137247848894304766908812051 205871773341457150363218077)
    ·
      refine ⟨77201915003046431386206779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205871773341457150363218077 77201915003046431386206779)
      ·
        refine ⟨115802872504569647079310169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77201915003046431386206779 115802872504569647079310169)
        ·
          refine ⟨86852154378427235309482627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115802872504569647079310169 86852154378427235309482627)
          ·
            refine ⟨130278231567640852964223941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86852154378427235309482627 130278231567640852964223941)
            ·
              refine ⟨24427168418932659930791989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130278231567640852964223941 24427168418932659930791989)
              ·
                refine ⟨2290047039274936868511749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24427168418932659930791989 2290047039274936868511749)
                ·
                  refine ⟨429383819864050662845953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2290047039274936868511749 429383819864050662845953)
                  ·
                    rfl

theorem cell22_3762999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 5, 4].length) (baseStart_3762999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3762999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3762999 prefixEnd_3762999 := by exact prefixLift 3762999
  have htrace : WordTrace (prefixWord ++ tailWord_3762999) baseStart_3762999 baseEnd_3762999 := by
    simpa [prefixWord, tailWord_3762999, baseEnd_3762999] using wordTrace_append hprefix tailTrace_3762999
  have hstable : (prefixWord ++ tailWord_3762999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3762999).length < 2 ^ (prefixWord ++ tailWord_3762999).sum := by decide
  have hdescent : baseEnd_3762999 < baseStart_3762999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3762999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763009 : List Nat := [1, 2, 5, 3, 2, 1, 2, 2, 1, 3]
def baseStart_3763009 : Nat := 118140960795 + 3763009 * 2 ^ 59
def prefixEnd_3763009 : Nat := 4983230072969 + 3 ^ 40 * 3763009 * 2
def baseEnd_3763009 : Nat := 1288154882796515295787829

theorem tailTrace_3763009 : CollatzResearch.WordTrace tailWord_3763009 prefixEnd_3763009 1288154882796515295787829 := by
  unfold tailWord_3763009
  simp only [CollatzResearch.WordTrace]
  refine ⟨137248213624268538616676081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91498809082845692411117387 137248213624268538616676081)
  ·
    refine ⟨102936160218201403962507061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137248213624268538616676081 102936160218201403962507061)
    ·
      refine ⟨9650265020456381621485037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102936160218201403962507061 9650265020456381621485037)
      ·
        refine ⟨3618849382671143108056889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9650265020456381621485037 3618849382671143108056889)
        ·
          refine ⟨2714137037003357331042667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3618849382671143108056889 2714137037003357331042667)
          ·
            refine ⟨4071205555505035996564001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2714137037003357331042667 4071205555505035996564001)
            ·
              refine ⟨3053404166628776997423001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4071205555505035996564001 3053404166628776997423001)
              ·
                refine ⟨2290053124971582748067251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3053404166628776997423001 2290053124971582748067251)
                ·
                  refine ⟨3435079687457374122100877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2290053124971582748067251 3435079687457374122100877)
                  ·
                    refine ⟨1288154882796515295787829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3435079687457374122100877 1288154882796515295787829)
                    ·
                      rfl

theorem cell22_3763009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_3763009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763009 prefixEnd_3763009 := by exact prefixLift 3763009
  have htrace : WordTrace (prefixWord ++ tailWord_3763009) baseStart_3763009 baseEnd_3763009 := by
    simpa [prefixWord, tailWord_3763009, baseEnd_3763009] using wordTrace_append hprefix tailTrace_3763009
  have hstable : (prefixWord ++ tailWord_3763009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763009).length < 2 ^ (prefixWord ++ tailWord_3763009).sum := by decide
  have hdescent : baseEnd_3763009 < baseStart_3763009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763031 : List Nat := [1, 1, 3, 2, 4, 1, 2, 3, 2, 3]
def baseStart_3763031 : Nat := 118140960795 + 3763031 * 2 ^ 59
def prefixEnd_3763031 : Nat := 4983230072969 + 3 ^ 40 * 3763031 * 2
def baseEnd_3763031 : Nat := 1288162413846114571737761

theorem tailTrace_3763031 : CollatzResearch.WordTrace tailWord_3763031 prefixEnd_3763031 1288162413846114571737761 := by
  unfold tailWord_3763031
  simp only [CollatzResearch.WordTrace]
  refine ⟨137249016030188836373976947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91499344020125890915984631 137249016030188836373976947)
  ·
    refine ⟨205873524045283254560965421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137249016030188836373976947 205873524045283254560965421)
    ·
      refine ⟨77202571516981220460362033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205873524045283254560965421 77202571516981220460362033)
      ·
        refine ⟨57901928637735915345271525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77202571516981220460362033 57901928637735915345271525)
        ·
          refine ⟨10856611619575484127238411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57901928637735915345271525 10856611619575484127238411)
          ·
            refine ⟨16284917429363226190857617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10856611619575484127238411 16284917429363226190857617)
            ·
              refine ⟨12213688072022419643143213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16284917429363226190857617 12213688072022419643143213)
              ·
                refine ⟨4580133027008407366178705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12213688072022419643143213 4580133027008407366178705)
                ·
                  refine ⟨3435099770256305524634029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4580133027008407366178705 3435099770256305524634029)
                  ·
                    refine ⟨1288162413846114571737761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3435099770256305524634029 1288162413846114571737761)
                    ·
                      rfl

theorem cell22_3763031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 2, 3, 2, 3].length) (baseStart_3763031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763031 prefixEnd_3763031 := by exact prefixLift 3763031
  have htrace : WordTrace (prefixWord ++ tailWord_3763031) baseStart_3763031 baseEnd_3763031 := by
    simpa [prefixWord, tailWord_3763031, baseEnd_3763031] using wordTrace_append hprefix tailTrace_3763031
  have hstable : (prefixWord ++ tailWord_3763031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763031).length < 2 ^ (prefixWord ++ tailWord_3763031).sum := by decide
  have hdescent : baseEnd_3763031 < baseStart_3763031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763183 : List Nat := [1, 1, 2, 1, 4, 4, 2, 2, 2, 3]
def baseStart_3763183 : Nat := 118140960795 + 3763183 * 2 ^ 59
def prefixEnd_3763183 : Nat := 4983230072969 + 3 ^ 40 * 3763183 * 2
def baseEnd_3763183 : Nat := 1288214446552436841937295

theorem tailTrace_3763183 : CollatzResearch.WordTrace tailWord_3763183 prefixEnd_3763183 1288214446552436841937295 := by
  unfold tailWord_3763183
  simp only [CollatzResearch.WordTrace]
  refine ⟨137254559925638166333510203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91503039950425444222340135 137254559925638166333510203)
  ·
    refine ⟨205881839888457249500265305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137254559925638166333510203 205881839888457249500265305)
    ·
      refine ⟨154411379916342937125198979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205881839888457249500265305 154411379916342937125198979)
      ·
        refine ⟨231617069874514405687798469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154411379916342937125198979 231617069874514405687798469)
        ·
          refine ⟨43428200601471451066462213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231617069874514405687798469 43428200601471451066462213)
          ·
            refine ⟨8142787612775897074961665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43428200601471451066462213 8142787612775897074961665)
            ·
              refine ⟨6107090709581922806221249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8142787612775897074961665 6107090709581922806221249)
              ·
                refine ⟨4580318032186442104665937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6107090709581922806221249 4580318032186442104665937)
                ·
                  refine ⟨3435238524139831578499453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4580318032186442104665937 3435238524139831578499453)
                  ·
                    refine ⟨1288214446552436841937295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3435238524139831578499453 1288214446552436841937295)
                    ·
                      rfl

theorem cell22_3763183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 2, 2, 2, 3].length) (baseStart_3763183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763183 prefixEnd_3763183 := by exact prefixLift 3763183
  have htrace : WordTrace (prefixWord ++ tailWord_3763183) baseStart_3763183 baseEnd_3763183 := by
    simpa [prefixWord, tailWord_3763183, baseEnd_3763183] using wordTrace_append hprefix tailTrace_3763183
  have hstable : (prefixWord ++ tailWord_3763183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763183).length < 2 ^ (prefixWord ++ tailWord_3763183).sum := by decide
  have hdescent : baseEnd_3763183 < baseStart_3763183 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763185 : List Nat := [1, 2, 2, 2, 4, 3, 2, 2, 4]
def baseStart_3763185 : Nat := 118140960795 + 3763185 * 2 ^ 59
def prefixEnd_3763185 : Nat := 4983230072969 + 3 ^ 40 * 3763185 * 2
def baseEnd_3763185 : Nat := 429405043731103167795763

theorem tailTrace_3763185 : CollatzResearch.WordTrace tailWord_3763185 prefixEnd_3763185 429405043731103167795763 := by
  unfold tailWord_3763185
  simp only [CollatzResearch.WordTrace]
  refine ⟨137254632871630920675083009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91503088581087280450055339 137254632871630920675083009)
  ·
    refine ⟨102940974653723190506312257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137254632871630920675083009 102940974653723190506312257)
    ·
      refine ⟨77205730990292392879734193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102940974653723190506312257 77205730990292392879734193)
      ·
        refine ⟨57904298242719294659800645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77205730990292392879734193 57904298242719294659800645)
        ·
          refine ⟨10857055920509867748712621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57904298242719294659800645 10857055920509867748712621)
          ·
            refine ⟨4071395970191200405767233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10857055920509867748712621 4071395970191200405767233)
            ·
              refine ⟨3053546977643400304325425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4071395970191200405767233 3053546977643400304325425)
              ·
                refine ⟨2290160233232550228244069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3053546977643400304325425 2290160233232550228244069)
                ·
                  refine ⟨429405043731103167795763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2290160233232550228244069 429405043731103167795763)
                  ·
                    rfl

theorem cell22_3763185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 2, 2, 4].length) (baseStart_3763185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763185 prefixEnd_3763185 := by exact prefixLift 3763185
  have htrace : WordTrace (prefixWord ++ tailWord_3763185) baseStart_3763185 baseEnd_3763185 := by
    simpa [prefixWord, tailWord_3763185, baseEnd_3763185] using wordTrace_append hprefix tailTrace_3763185
  have hstable : (prefixWord ++ tailWord_3763185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763185).length < 2 ^ (prefixWord ++ tailWord_3763185).sum := by decide
  have hdescent : baseEnd_3763185 < baseStart_3763185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763196 : List Nat := [2, 2, 2, 1, 2, 5, 1, 7]
def baseStart_3763196 : Nat := 118140960795 + 3763196 * 2 ^ 59
def prefixEnd_3763196 : Nat := 4983230072969 + 3 ^ 40 * 3763196 * 2
def baseEnd_3763196 : Nat := 143135432968678793484695

theorem tailTrace_3763196 : CollatzResearch.WordTrace tailWord_3763196 prefixEnd_3763196 143135432968678793484695 := by
  unfold tailWord_3763196
  simp only [CollatzResearch.WordTrace]
  refine ⟨68627517037295534776866721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91503356049727379702488961 68627517037295534776866721)
  ·
    refine ⟨51470637777971651082650041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68627517037295534776866721 51470637777971651082650041)
    ·
      refine ⟨38602978333478738311987531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51470637777971651082650041 38602978333478738311987531)
      ·
        refine ⟨57904467500218107467981297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38602978333478738311987531 57904467500218107467981297)
        ·
          refine ⟨43428350625163580600985973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57904467500218107467981297 43428350625163580600985973)
          ·
            refine ⟨4071407871109085681342435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43428350625163580600985973 4071407871109085681342435)
            ·
              refine ⟨6107111806663628522013653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4071407871109085681342435 6107111806663628522013653)
              ·
                refine ⟨143135432968678793484695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6107111806663628522013653 143135432968678793484695)
                ·
                  rfl

theorem cell22_3763196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 7].length) (baseStart_3763196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763196 prefixEnd_3763196 := by exact prefixLift 3763196
  have htrace : WordTrace (prefixWord ++ tailWord_3763196) baseStart_3763196 baseEnd_3763196 := by
    simpa [prefixWord, tailWord_3763196, baseEnd_3763196] using wordTrace_append hprefix tailTrace_3763196
  have hstable : (prefixWord ++ tailWord_3763196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763196).length < 2 ^ (prefixWord ++ tailWord_3763196).sum := by decide
  have hdescent : baseEnd_3763196 < baseStart_3763196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763211 : List Nat := [1, 1, 1, 1, 6, 2, 1, 1, 5, 3]
def baseStart_3763211 : Nat := 118140960795 + 3763211 * 2 ^ 59
def prefixEnd_3763211 : Nat := 4983230072969 + 3 ^ 40 * 3763211 * 2
def baseEnd_3763211 : Nat := 1288224031524654102237209

theorem tailTrace_3763211 : CollatzResearch.WordTrace tailWord_3763211 prefixEnd_3763211 1288224031524654102237209 := by
  unfold tailWord_3763211
  simp only [CollatzResearch.WordTrace]
  refine ⟨137255581169536727115529487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91503720779691151410352991 137255581169536727115529487)
  ·
    refine ⟨205883371754305090673294231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137255581169536727115529487 205883371754305090673294231)
    ·
      refine ⟨308825057631457636009941347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205883371754305090673294231 308825057631457636009941347)
      ·
        refine ⟨463237586447186454014912021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308825057631457636009941347 463237586447186454014912021)
        ·
          refine ⟨21714261864711865031949001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 463237586447186454014912021 21714261864711865031949001)
          ·
            refine ⟨16285696398533898773961751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21714261864711865031949001 16285696398533898773961751)
            ·
              refine ⟨24428544597800848160942627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16285696398533898773961751 24428544597800848160942627)
              ·
                refine ⟨36642816896701272241413941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24428544597800848160942627 36642816896701272241413941)
                ·
                  refine ⟨3435264084065744272632557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36642816896701272241413941 3435264084065744272632557)
                  ·
                    refine ⟨1288224031524654102237209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3435264084065744272632557 1288224031524654102237209)
                    ·
                      rfl

theorem cell22_3763211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 1, 5, 3].length) (baseStart_3763211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763211 prefixEnd_3763211 := by exact prefixLift 3763211
  have htrace : WordTrace (prefixWord ++ tailWord_3763211) baseStart_3763211 baseEnd_3763211 := by
    simpa [prefixWord, tailWord_3763211, baseEnd_3763211] using wordTrace_append hprefix tailTrace_3763211
  have hstable : (prefixWord ++ tailWord_3763211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763211).length < 2 ^ (prefixWord ++ tailWord_3763211).sum := by decide
  have hdescent : baseEnd_3763211 < baseStart_3763211 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763256 : List Nat := [2, 1, 2, 1, 5, 1, 2, 1, 2, 5]
def baseStart_3763256 : Nat := 118140960795 + 3763256 * 2 ^ 59
def prefixEnd_3763256 : Nat := 4983230072969 + 3 ^ 40 * 3763256 * 2
def baseEnd_3763256 : Nat := 1288239435944288984862071

theorem tailTrace_3763256 : CollatzResearch.WordTrace tailWord_3763256 prefixEnd_3763256 1288239435944288984862071 := by
  unfold tailWord_3763256
  simp only [CollatzResearch.WordTrace]
  refine ⟨68628611227186849900458811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91504814969582466533945081 68628611227186849900458811)
  ·
    refine ⟨102942916840780274850688217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68628611227186849900458811 102942916840780274850688217)
    ·
      refine ⟨77207187630585206138016163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102942916840780274850688217 77207187630585206138016163)
      ·
        refine ⟨115810781445877809207024245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77207187630585206138016163 115810781445877809207024245)
        ·
          refine ⟨10857260760551044613158523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115810781445877809207024245 10857260760551044613158523)
          ·
            refine ⟨16285891140826566919737785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10857260760551044613158523 16285891140826566919737785)
            ·
              refine ⟨12214418355619925189803339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16285891140826566919737785 12214418355619925189803339)
              ·
                refine ⟨18321627533429887784705009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12214418355619925189803339 18321627533429887784705009)
                ·
                  refine ⟨13741220650072415838528757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18321627533429887784705009 13741220650072415838528757)
                  ·
                    refine ⟨1288239435944288984862071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13741220650072415838528757 1288239435944288984862071)
                    ·
                      rfl

theorem cell22_3763256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 1, 2, 5].length) (baseStart_3763256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763256 prefixEnd_3763256 := by exact prefixLift 3763256
  have htrace : WordTrace (prefixWord ++ tailWord_3763256) baseStart_3763256 baseEnd_3763256 := by
    simpa [prefixWord, tailWord_3763256, baseEnd_3763256] using wordTrace_append hprefix tailTrace_3763256
  have hstable : (prefixWord ++ tailWord_3763256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763256).length < 2 ^ (prefixWord ++ tailWord_3763256).sum := by decide
  have hdescent : baseEnd_3763256 < baseStart_3763256 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763303 : List Nat := [1, 1, 5, 1, 1, 5, 1, 1, 6]
def baseStart_3763303 : Nat := 118140960795 + 3763303 * 2 ^ 59
def prefixEnd_3763303 : Nat := 4983230072969 + 3 ^ 40 * 3763303 * 2
def baseEnd_3763303 : Nat := 429418508334932176312309

theorem tailTrace_3763303 : CollatzResearch.WordTrace tailWord_3763303 prefixEnd_3763303 429418508334932176312309 := by
  unfold tailWord_3763303
  simp only [CollatzResearch.WordTrace]
  refine ⟨137258936685203426827878563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91505957790135617885252375 137258936685203426827878563)
  ·
    refine ⟨205888405027805140241817845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137258936685203426827878563 205888405027805140241817845)
    ·
      refine ⟨19302037971356731897670423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205888405027805140241817845 19302037971356731897670423)
      ·
        refine ⟨28953056957035097846505635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19302037971356731897670423 28953056957035097846505635)
        ·
          refine ⟨43429585435552646769758453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28953056957035097846505635 43429585435552646769758453)
          ·
            refine ⟨4071523634583060634664855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43429585435552646769758453 4071523634583060634664855)
            ·
              refine ⟨6107285451874590951997283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4071523634583060634664855 6107285451874590951997283)
              ·
                refine ⟨9160928177811886427995925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6107285451874590951997283 9160928177811886427995925)
                ·
                  refine ⟨429418508334932176312309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9160928177811886427995925 429418508334932176312309)
                  ·
                    rfl

theorem cell22_3763303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 6].length) (baseStart_3763303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763303 prefixEnd_3763303 := by exact prefixLift 3763303
  have htrace : WordTrace (prefixWord ++ tailWord_3763303) baseStart_3763303 baseEnd_3763303 := by
    simpa [prefixWord, tailWord_3763303, baseEnd_3763303] using wordTrace_append hprefix tailTrace_3763303
  have hstable : (prefixWord ++ tailWord_3763303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763303).length < 2 ^ (prefixWord ++ tailWord_3763303).sum := by decide
  have hdescent : baseEnd_3763303 < baseStart_3763303 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763318 : List Nat := [5, 1, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_3763318 : Nat := 118140960795 + 3763318 * 2 ^ 59
def prefixEnd_3763318 : Nat := 4983230072969 + 3 ^ 40 * 3763318 * 2
def baseEnd_3763318 : Nat := 1288260659811341489811881

theorem tailTrace_3763318 : CollatzResearch.WordTrace tailWord_3763318 prefixEnd_3763318 1288260659811341489811881 := by
  unfold tailWord_3763318
  simp only [CollatzResearch.WordTrace]
  refine ⟨8578717736259317774354663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91506322520099389593116405 8578717736259317774354663)
  ·
    refine ⟨12868076604388976661531995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8578717736259317774354663 12868076604388976661531995)
    ·
      refine ⟨19302114906583464992297993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12868076604388976661531995 19302114906583464992297993)
      ·
        refine ⟨14476586179937598744223495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19302114906583464992297993 14476586179937598744223495)
        ·
          refine ⟨21714879269906398116335243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14476586179937598744223495 21714879269906398116335243)
          ·
            refine ⟨32572318904859597174502865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21714879269906398116335243 32572318904859597174502865)
            ·
              refine ⟨24429239178644697880877149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32572318904859597174502865 24429239178644697880877149)
              ·
                refine ⟨9160964691991761705328931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24429239178644697880877149 9160964691991761705328931)
                ·
                  refine ⟨13741447037987642557993397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9160964691991761705328931 13741447037987642557993397)
                  ·
                    refine ⟨1288260659811341489811881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13741447037987642557993397 1288260659811341489811881)
                    ·
                      rfl

theorem cell22_3763318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_3763318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763318 prefixEnd_3763318 := by exact prefixLift 3763318
  have htrace : WordTrace (prefixWord ++ tailWord_3763318) baseStart_3763318 baseEnd_3763318 := by
    simpa [prefixWord, tailWord_3763318, baseEnd_3763318] using wordTrace_append hprefix tailTrace_3763318
  have hstable : (prefixWord ++ tailWord_3763318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763318).length < 2 ^ (prefixWord ++ tailWord_3763318).sum := by decide
  have hdescent : baseEnd_3763318 < baseStart_3763318 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763361 : List Nat := [1, 2, 3, 3, 1, 1, 1, 1, 1, 8]
def baseStart_3763361 : Nat := 118140960795 + 3763361 * 2 ^ 59
def prefixEnd_3763361 : Nat := 4983230072969 + 3 ^ 40 * 3763361 * 2
def baseEnd_3763361 : Nat := 1288275379590103710986749

theorem tailTrace_3763361 : CollatzResearch.WordTrace tailWord_3763361 prefixEnd_3763361 1288275379590103710986749 := by
  unfold tailWord_3763361
  simp only [CollatzResearch.WordTrace]
  refine ⟨137261052118993302733489937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91507368079328868488993291 137261052118993302733489937)
  ·
    refine ⟨102945789089244977050117453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137261052118993302733489937 102945789089244977050117453)
    ·
      refine ⟨38604670908466866393794045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102945789089244977050117453 38604670908466866393794045)
      ·
        refine ⟨14476751590675074897672767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38604670908466866393794045 14476751590675074897672767)
        ·
          refine ⟨21715127386012612346509151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14476751590675074897672767 21715127386012612346509151)
          ·
            refine ⟨32572691079018918519763727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21715127386012612346509151 32572691079018918519763727)
            ·
              refine ⟨48859036618528377779645591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32572691079018918519763727 48859036618528377779645591)
              ·
                refine ⟨73288554927792566669468387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48859036618528377779645591 73288554927792566669468387)
                ·
                  refine ⟨109932832391688850004202581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73288554927792566669468387 109932832391688850004202581)
                  ·
                    refine ⟨1288275379590103710986749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109932832391688850004202581 1288275379590103710986749)
                    ·
                      rfl

theorem cell22_3763361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 1, 1, 8].length) (baseStart_3763361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763361 prefixEnd_3763361 := by exact prefixLift 3763361
  have htrace : WordTrace (prefixWord ++ tailWord_3763361) baseStart_3763361 baseEnd_3763361 := by
    simpa [prefixWord, tailWord_3763361, baseEnd_3763361] using wordTrace_append hprefix tailTrace_3763361
  have hstable : (prefixWord ++ tailWord_3763361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763361).length < 2 ^ (prefixWord ++ tailWord_3763361).sum := by decide
  have hdescent : baseEnd_3763361 < baseStart_3763361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763414 : List Nat := [5, 2, 1, 2, 2, 1, 2, 1, 3, 3]
def baseStart_3763414 : Nat := 118140960795 + 3763414 * 2 ^ 59
def prefixEnd_3763414 : Nat := 4983230072969 + 3 ^ 40 * 3763414 * 2
def baseEnd_3763414 : Nat := 1288293522573229239411587

theorem tailTrace_3763414 : CollatzResearch.WordTrace tailWord_3763414 prefixEnd_3763414 1288293522573229239411587 := by
  unfold tailWord_3763414
  simp only [CollatzResearch.WordTrace]
  refine ⟨8578936574237580799073081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91508656791867528523446197 8578936574237580799073081)
  ·
    refine ⟨6434202430678185599304811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8578936574237580799073081 6434202430678185599304811)
    ·
      refine ⟨9651303646017278398957217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6434202430678185599304811 9651303646017278398957217)
      ·
        refine ⟨7238477734512958799217913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9651303646017278398957217 7238477734512958799217913)
        ·
          refine ⟨5428858300884719099413435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7238477734512958799217913 5428858300884719099413435)
          ·
            refine ⟨8143287451327078649120153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5428858300884719099413435 8143287451327078649120153)
            ·
              refine ⟨6107465588495308986840115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8143287451327078649120153 6107465588495308986840115)
              ·
                refine ⟨9161198382742963480260173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6107465588495308986840115 9161198382742963480260173)
                ·
                  refine ⟨3435449393528611305097565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9161198382742963480260173 3435449393528611305097565)
                  ·
                    refine ⟨1288293522573229239411587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3435449393528611305097565 1288293522573229239411587)
                    ·
                      rfl

theorem cell22_3763414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 1, 3, 3].length) (baseStart_3763414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763414 prefixEnd_3763414 := by exact prefixLift 3763414
  have htrace : WordTrace (prefixWord ++ tailWord_3763414) baseStart_3763414 baseEnd_3763414 := by
    simpa [prefixWord, tailWord_3763414, baseEnd_3763414] using wordTrace_append hprefix tailTrace_3763414
  have hstable : (prefixWord ++ tailWord_3763414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763414).length < 2 ^ (prefixWord ++ tailWord_3763414).sum := by decide
  have hdescent : baseEnd_3763414 < baseStart_3763414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763438 : List Nat := [4, 1, 2, 1, 1, 1, 4, 2, 6]
def baseStart_3763438 : Nat := 118140960795 + 3763438 * 2 ^ 59
def prefixEnd_3763438 : Nat := 4983230072969 + 3 ^ 40 * 3763438 * 2
def baseEnd_3763438 : Nat := 429433912754567058937171

theorem tailTrace_3763438 : CollatzResearch.WordTrace tailWord_3763438 prefixEnd_3763438 429433912754567058937171 := by
  unfold tailWord_3763438
  simp only [CollatzResearch.WordTrace]
  refine ⟨17157982567464293110505371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91509240359809563256028645 17157982567464293110505371)
  ·
    refine ⟨25736973851196439665758057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17157982567464293110505371 25736973851196439665758057)
    ·
      refine ⟨19302730388397329749318543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25736973851196439665758057 19302730388397329749318543)
      ·
        refine ⟨28954095582595994623977815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19302730388397329749318543 28954095582595994623977815)
        ·
          refine ⟨43431143373893991935966723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28954095582595994623977815 43431143373893991935966723)
          ·
            refine ⟨65146715060840987903950085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43431143373893991935966723 65146715060840987903950085)
            ·
              refine ⟨12215009073907685231990641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65146715060840987903950085 12215009073907685231990641)
              ·
                refine ⟨9161256805430763923992981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12215009073907685231990641 9161256805430763923992981)
                ·
                  refine ⟨429433912754567058937171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9161256805430763923992981 429433912754567058937171)
                  ·
                    rfl

theorem cell22_3763438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_3763438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763438 prefixEnd_3763438 := by exact prefixLift 3763438
  have htrace : WordTrace (prefixWord ++ tailWord_3763438) baseStart_3763438 baseEnd_3763438 := by
    simpa [prefixWord, tailWord_3763438, baseEnd_3763438] using wordTrace_append hprefix tailTrace_3763438
  have hstable : (prefixWord ++ tailWord_3763438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763438).length < 2 ^ (prefixWord ++ tailWord_3763438).sum := by decide
  have hdescent : baseEnd_3763438 < baseStart_3763438 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763455 : List Nat := [1, 1, 2, 2, 1, 5, 3, 3, 4]
def baseStart_3763455 : Nat := 118140960795 + 3763455 * 2 ^ 59
def prefixEnd_3763455 : Nat := 4983230072969 + 3 ^ 40 * 3763455 * 2
def baseEnd_3763455 : Nat := 429435852570372933045487

theorem tailTrace_3763455 : CollatzResearch.WordTrace tailWord_3763455 prefixEnd_3763455 429435852570372933045487 := by
  unfold tailWord_3763455
  simp only [CollatzResearch.WordTrace]
  refine ⟨137264480580652756787411819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91509653720435171191607879 137264480580652756787411819)
  ·
    refine ⟨205896720870979135181117729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137264480580652756787411819 205896720870979135181117729)
    ·
      refine ⟨154422540653234351385838297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205896720870979135181117729 154422540653234351385838297)
      ·
        refine ⟨115816905489925763539378723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154422540653234351385838297 115816905489925763539378723)
        ·
          refine ⟨173725358234888645309068085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115816905489925763539378723 173725358234888645309068085)
          ·
            refine ⟨16286752334520810497725133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173725358234888645309068085 16286752334520810497725133)
            ·
              refine ⟨6107532125445303936646925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16286752334520810497725133 6107532125445303936646925)
              ·
                refine ⟨2290324547041988976242597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6107532125445303936646925 2290324547041988976242597)
                ·
                  refine ⟨429435852570372933045487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2290324547041988976242597 429435852570372933045487)
                  ·
                    rfl

theorem cell22_3763455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 3, 3, 4].length) (baseStart_3763455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763455 prefixEnd_3763455 := by exact prefixLift 3763455
  have htrace : WordTrace (prefixWord ++ tailWord_3763455) baseStart_3763455 baseEnd_3763455 := by
    simpa [prefixWord, tailWord_3763455, baseEnd_3763455] using wordTrace_append hprefix tailTrace_3763455
  have hstable : (prefixWord ++ tailWord_3763455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763455).length < 2 ^ (prefixWord ++ tailWord_3763455).sum := by decide
  have hdescent : baseEnd_3763455 < baseStart_3763455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763468 : List Nat := [2, 2, 1, 2, 2, 3, 1, 1, 4, 4]
def baseStart_3763468 : Nat := 118140960795 + 3763468 * 2 ^ 59
def prefixEnd_3763468 : Nat := 4983230072969 + 3 ^ 40 * 3763468 * 2
def baseEnd_3763468 : Nat := 1288312007876791098561421

theorem tailTrace_3763468 : CollatzResearch.WordTrace tailWord_3763468 prefixEnd_3763468 1288312007876791098561421 := by
  unfold tailWord_3763468
  simp only [CollatzResearch.WordTrace]
  refine ⟨68632477364802830003817529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91509969819737106671756705 68632477364802830003817529)
  ·
    refine ⟨51474358023602122502863147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68632477364802830003817529 51474358023602122502863147)
    ·
      refine ⟨77211537035403183754294721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51474358023602122502863147 77211537035403183754294721)
      ·
        refine ⟨57908652776552387815721041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77211537035403183754294721 57908652776552387815721041)
        ·
          refine ⟨43431489582414290861790781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57908652776552387815721041 43431489582414290861790781)
          ·
            refine ⟨16286808593405359073171543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43431489582414290861790781 16286808593405359073171543)
            ·
              refine ⟨24430212890108038609757315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16286808593405359073171543 24430212890108038609757315)
              ·
                refine ⟨36645319335162057914635973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24430212890108038609757315 36645319335162057914635973)
                ·
                  refine ⟨6870997375342885858994245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36645319335162057914635973 6870997375342885858994245)
                  ·
                    refine ⟨1288312007876791098561421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6870997375342885858994245 1288312007876791098561421)
                    ·
                      rfl

theorem cell22_3763468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 1, 1, 4, 4].length) (baseStart_3763468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763468 prefixEnd_3763468 := by exact prefixLift 3763468
  have htrace : WordTrace (prefixWord ++ tailWord_3763468) baseStart_3763468 baseEnd_3763468 := by
    simpa [prefixWord, tailWord_3763468, baseEnd_3763468] using wordTrace_append hprefix tailTrace_3763468
  have hstable : (prefixWord ++ tailWord_3763468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763468).length < 2 ^ (prefixWord ++ tailWord_3763468).sum := by decide
  have hdescent : baseEnd_3763468 < baseStart_3763468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763470 : List Nat := [4, 1, 1, 2, 1, 3, 2, 1, 4, 3]
def baseStart_3763470 : Nat := 118140960795 + 3763470 * 2 ^ 59
def prefixEnd_3763470 : Nat := 4983230072969 + 3 ^ 40 * 3763470 * 2
def baseEnd_3763470 : Nat := 1288312692517663760011415

theorem tailTrace_3763470 : CollatzResearch.WordTrace tailWord_3763470 prefixEnd_3763470 1288312692517663760011415 := by
  unfold tailWord_3763470
  simp only [CollatzResearch.WordTrace]
  refine ⟨17158128459449801793650983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91510018450398942899471909 17158128459449801793650983)
  ·
    refine ⟨25737192689174702690476475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17158128459449801793650983 25737192689174702690476475)
    ·
      refine ⟨38605789033762054035714713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25737192689174702690476475 38605789033762054035714713)
      ·
        refine ⟨28954341775321540526786035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38605789033762054035714713 28954341775321540526786035)
        ·
          refine ⟨43431512662982310790179053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28954341775321540526786035 43431512662982310790179053)
          ·
            refine ⟨16286817248618366546317145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43431512662982310790179053 16286817248618366546317145)
            ·
              refine ⟨12215112936463774909737859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16286817248618366546317145 12215112936463774909737859)
              ·
                refine ⟨18322669404695662364606789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12215112936463774909737859 18322669404695662364606789)
                ·
                  refine ⟨3435500513380436693363773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18322669404695662364606789 3435500513380436693363773)
                  ·
                    refine ⟨1288312692517663760011415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3435500513380436693363773 1288312692517663760011415)
                    ·
                      rfl

theorem cell22_3763470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 3, 2, 1, 4, 3].length) (baseStart_3763470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763470 prefixEnd_3763470 := by exact prefixLift 3763470
  have htrace : WordTrace (prefixWord ++ tailWord_3763470) baseStart_3763470 baseEnd_3763470 := by
    simpa [prefixWord, tailWord_3763470, baseEnd_3763470] using wordTrace_append hprefix tailTrace_3763470
  have hstable : (prefixWord ++ tailWord_3763470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763470).length < 2 ^ (prefixWord ++ tailWord_3763470).sum := by decide
  have hdescent : baseEnd_3763470 < baseStart_3763470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763487 : List Nat := [1, 1, 2, 4, 4, 1, 1, 3, 2, 3]
def baseStart_3763487 : Nat := 118140960795 + 3763487 * 2 ^ 59
def prefixEnd_3763487 : Nat := 4983230072969 + 3 ^ 40 * 3763487 * 2
def baseEnd_3763487 : Nat := 1288318511965081382336363

theorem tailTrace_3763487 : CollatzResearch.WordTrace tailWord_3763487 prefixEnd_3763487 1288318511965081382336363 := by
  unfold tailWord_3763487
  simp only [CollatzResearch.WordTrace]
  refine ⟨137265647716536826252576715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91510431811024550835051143 137265647716536826252576715)
  ·
    refine ⟨205898471574805239378865073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137265647716536826252576715 205898471574805239378865073)
    ·
      refine ⟨154423853681103929534148805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205898471574805239378865073 154423853681103929534148805)
      ·
        refine ⟨28954472565206986787652901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154423853681103929534148805 28954472565206986787652901)
        ·
          refine ⟨5428963605976310022684919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28954472565206986787652901 5428963605976310022684919)
          ·
            refine ⟨8143445408964465034027379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5428963605976310022684919 8143445408964465034027379)
            ·
              refine ⟨12215168113446697551041069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8143445408964465034027379 12215168113446697551041069)
              ·
                refine ⟨4580688042542511581640401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12215168113446697551041069 4580688042542511581640401)
                ·
                  refine ⟨3435516031906883686230301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4580688042542511581640401 3435516031906883686230301)
                  ·
                    refine ⟨1288318511965081382336363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3435516031906883686230301 1288318511965081382336363)
                    ·
                      rfl

theorem cell22_3763487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 1, 3, 2, 3].length) (baseStart_3763487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763487 prefixEnd_3763487 := by exact prefixLift 3763487
  have htrace : WordTrace (prefixWord ++ tailWord_3763487) baseStart_3763487 baseEnd_3763487 := by
    simpa [prefixWord, tailWord_3763487, baseEnd_3763487] using wordTrace_append hprefix tailTrace_3763487
  have hstable : (prefixWord ++ tailWord_3763487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763487).length < 2 ^ (prefixWord ++ tailWord_3763487).sum := by decide
  have hdescent : baseEnd_3763487 < baseStart_3763487 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763543 : List Nat := [1, 1, 3, 2, 3, 2, 1, 1, 1, 7]
def baseStart_3763543 : Nat := 118140960795 + 3763543 * 2 ^ 59
def prefixEnd_3763543 : Nat := 4983230072969 + 3 ^ 40 * 3763543 * 2
def baseEnd_3763543 : Nat := 1288337681909515902936191

theorem tailTrace_3763543 : CollatzResearch.WordTrace tailWord_3763543 prefixEnd_3763543 1288337681909515902936191 := by
  unfold tailWord_3763543
  simp only [CollatzResearch.WordTrace]
  refine ⟨137267690204333947816615283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91511793469555965211076855 137267690204333947816615283)
  ·
    refine ⟨205901535306500921724922925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137267690204333947816615283 205901535306500921724922925)
    ·
      refine ⟨77213075739937845646846097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205901535306500921724922925 77213075739937845646846097)
      ·
        refine ⟨57909806804953384235134573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77213075739937845646846097 57909806804953384235134573)
        ·
          refine ⟨21716177551857519088175465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57909806804953384235134573 21716177551857519088175465)
          ·
            refine ⟨16287133163893139316131599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21716177551857519088175465 16287133163893139316131599)
            ·
              refine ⟨24430699745839708974197399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16287133163893139316131599 24430699745839708974197399)
              ·
                refine ⟨36646049618759563461296099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24430699745839708974197399 36646049618759563461296099)
                ·
                  refine ⟨54969074428139345191944149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36646049618759563461296099 54969074428139345191944149)
                  ·
                    refine ⟨1288337681909515902936191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54969074428139345191944149 1288337681909515902936191)
                    ·
                      rfl

theorem cell22_3763543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 1, 1, 7].length) (baseStart_3763543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763543 prefixEnd_3763543 := by exact prefixLift 3763543
  have htrace : WordTrace (prefixWord ++ tailWord_3763543) baseStart_3763543 baseEnd_3763543 := by
    simpa [prefixWord, tailWord_3763543, baseEnd_3763543] using wordTrace_append hprefix tailTrace_3763543
  have hstable : (prefixWord ++ tailWord_3763543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763543).length < 2 ^ (prefixWord ++ tailWord_3763543).sum := by decide
  have hdescent : baseEnd_3763543 < baseStart_3763543 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763575 : List Nat := [1, 1, 3, 1, 1, 2, 5, 3, 1, 4]
def baseStart_3763575 : Nat := 118140960795 + 3763575 * 2 ^ 59
def prefixEnd_3763575 : Nat := 4983230072969 + 3 ^ 40 * 3763575 * 2
def baseEnd_3763575 : Nat := 1288348636163478486136093

theorem tailTrace_3763575 : CollatzResearch.WordTrace tailWord_3763575 prefixEnd_3763575 1288348636163478486136093 := by
  unfold tailWord_3763575
  simp only [CollatzResearch.WordTrace]
  refine ⟨137268857340218017281780179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91512571560145344854520119 137268857340218017281780179)
  ·
    refine ⟨205903286010327025922670269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137268857340218017281780179 205903286010327025922670269)
    ·
      refine ⟨77213732253872634721001351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 205903286010327025922670269 77213732253872634721001351)
      ·
        refine ⟨115820598380808952081502027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77213732253872634721001351 115820598380808952081502027)
        ·
          refine ⟨173730897571213428122253041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115820598380808952081502027 173730897571213428122253041)
          ·
            refine ⟨130298173178410071091689781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173730897571213428122253041 130298173178410071091689781)
            ·
              refine ⟨12215453735475944164845917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130298173178410071091689781 12215453735475944164845917)
              ·
                refine ⟨4580795150803479061817219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12215453735475944164845917 4580795150803479061817219)
                ·
                  refine ⟨6871192726205218592725829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4580795150803479061817219 6871192726205218592725829)
                  ·
                    refine ⟨1288348636163478486136093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6871192726205218592725829 1288348636163478486136093)
                    ·
                      rfl

theorem cell22_3763575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_3763575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763575 prefixEnd_3763575 := by exact prefixLift 3763575
  have htrace : WordTrace (prefixWord ++ tailWord_3763575) baseStart_3763575 baseEnd_3763575 := by
    simpa [prefixWord, tailWord_3763575, baseEnd_3763575] using wordTrace_append hprefix tailTrace_3763575
  have hstable : (prefixWord ++ tailWord_3763575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763575).length < 2 ^ (prefixWord ++ tailWord_3763575).sum := by decide
  have hdescent : baseEnd_3763575 < baseStart_3763575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763605 : List Nat := [1, 3, 2, 1, 1, 2, 5, 1, 1, 5]
def baseStart_3763605 : Nat := 118140960795 + 3763605 * 2 ^ 59
def prefixEnd_3763605 : Nat := 4983230072969 + 3 ^ 40 * 3763605 * 2
def baseEnd_3763605 : Nat := 1288358905776568407886001

theorem tailTrace_3763605 : CollatzResearch.WordTrace tailWord_3763605 prefixEnd_3763605 1288358905776568407886001 := by
  unfold tailWord_3763605
  simp only [CollatzResearch.WordTrace]
  refine ⟨137269951530109332405372269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91513301020072888270248179 137269951530109332405372269)
  ·
    refine ⟨51476231823790999652014601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137269951530109332405372269 51476231823790999652014601)
    ·
      refine ⟨38607173867843249739010951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51476231823790999652014601 38607173867843249739010951)
      ·
        refine ⟨57910760801764874608516427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38607173867843249739010951 57910760801764874608516427)
        ·
          refine ⟨86866141202647311912774641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57910760801764874608516427 86866141202647311912774641)
          ·
            refine ⟨65149605901985483934580981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86866141202647311912774641 65149605901985483934580981)
            ·
              refine ⟨6107775553311139118866967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65149605901985483934580981 6107775553311139118866967)
              ·
                refine ⟨9161663329966708678300451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6107775553311139118866967 9161663329966708678300451)
                ·
                  refine ⟨13742494994950063017450677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9161663329966708678300451 13742494994950063017450677)
                  ·
                    refine ⟨1288358905776568407886001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13742494994950063017450677 1288358905776568407886001)
                    ·
                      rfl

theorem cell22_3763605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_3763605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763605 prefixEnd_3763605 := by exact prefixLift 3763605
  have htrace : WordTrace (prefixWord ++ tailWord_3763605) baseStart_3763605 baseEnd_3763605 := by
    simpa [prefixWord, tailWord_3763605, baseEnd_3763605] using wordTrace_append hprefix tailTrace_3763605
  have hstable : (prefixWord ++ tailWord_3763605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763605).length < 2 ^ (prefixWord ++ tailWord_3763605).sum := by decide
  have hdescent : baseEnd_3763605 < baseStart_3763605 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763620 : List Nat := [2, 3, 1, 2, 1, 1, 1, 5, 2, 4]
def baseStart_3763620 : Nat := 118140960795 + 3763620 * 2 ^ 59
def prefixEnd_3763620 : Nat := 4983230072969 + 3 ^ 40 * 3763620 * 2
def baseEnd_3763620 : Nat := 1288364040583113368760955

theorem tailTrace_3763620 : CollatzResearch.WordTrace tailWord_3763620 prefixEnd_3763620 1288364040583113368760955 := by
  unfold tailWord_3763620
  simp only [CollatzResearch.WordTrace]
  refine ⟨68635249312527494983584157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91513665750036659978112209 68635249312527494983584157)
  ·
    refine ⟨25738218492197810618844059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68635249312527494983584157 25738218492197810618844059)
    ·
      refine ⟨38607327738296715928266089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25738218492197810618844059 38607327738296715928266089)
      ·
        refine ⟨28955495803722536946199567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38607327738296715928266089 28955495803722536946199567)
        ·
          refine ⟨43433243705583805419299351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28955495803722536946199567 43433243705583805419299351)
          ·
            refine ⟨65149865558375708128949027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43433243705583805419299351 65149865558375708128949027)
            ·
              refine ⟨97724798337563562193423541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65149865558375708128949027 97724798337563562193423541)
              ·
                refine ⟨9161699844146583955633457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97724798337563562193423541 9161699844146583955633457)
                ·
                  refine ⟨6871274883109937966725093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9161699844146583955633457 6871274883109937966725093)
                  ·
                    refine ⟨1288364040583113368760955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6871274883109937966725093 1288364040583113368760955)
                    ·
                      rfl

theorem cell22_3763620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_3763620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763620 prefixEnd_3763620 := by exact prefixLift 3763620
  have htrace : WordTrace (prefixWord ++ tailWord_3763620) baseStart_3763620 baseEnd_3763620 := by
    simpa [prefixWord, tailWord_3763620, baseEnd_3763620] using wordTrace_append hprefix tailTrace_3763620
  have hstable : (prefixWord ++ tailWord_3763620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763620).length < 2 ^ (prefixWord ++ tailWord_3763620).sum := by decide
  have hdescent : baseEnd_3763620 < baseStart_3763620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763637 : List Nat := [1, 3, 3, 2, 2, 2, 1, 2, 2, 4]
def baseStart_3763637 : Nat := 118140960795 + 3763637 * 2 ^ 59
def prefixEnd_3763637 : Nat := 4983230072969 + 3 ^ 40 * 3763637 * 2
def baseEnd_3763637 : Nat := 1288369860030530991085903

theorem tailTrace_3763637 : CollatzResearch.WordTrace tailWord_3763637 prefixEnd_3763637 1288369860030530991085903 := by
  unfold tailWord_3763637
  simp only [CollatzResearch.WordTrace]
  refine ⟨137271118665993401870537165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91514079110662267913691443 137271118665993401870537165)
  ·
    refine ⟨51476669499747525701451437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137271118665993401870537165 51476669499747525701451437)
    ·
      refine ⟨19303751062405322138044289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51476669499747525701451437 19303751062405322138044289)
      ·
        refine ⟨14477813296803991603533217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19303751062405322138044289 14477813296803991603533217)
        ·
          refine ⟨10858359972602993702649913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14477813296803991603533217 10858359972602993702649913)
          ·
            refine ⟨8143769979452245276987435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10858359972602993702649913 8143769979452245276987435)
            ·
              refine ⟨12215654969178367915481153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8143769979452245276987435 12215654969178367915481153)
              ·
                refine ⟨9161741226883775936610865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12215654969178367915481153 9161741226883775936610865)
                ·
                  refine ⟨6871305920162831952458149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9161741226883775936610865 6871305920162831952458149)
                  ·
                    refine ⟨1288369860030530991085903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6871305920162831952458149 1288369860030530991085903)
                    ·
                      rfl

theorem cell22_3763637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_3763637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763637 prefixEnd_3763637 := by exact prefixLift 3763637
  have htrace : WordTrace (prefixWord ++ tailWord_3763637) baseStart_3763637 baseEnd_3763637 := by
    simpa [prefixWord, tailWord_3763637, baseEnd_3763637] using wordTrace_append hprefix tailTrace_3763637
  have hstable : (prefixWord ++ tailWord_3763637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763637).length < 2 ^ (prefixWord ++ tailWord_3763637).sum := by decide
  have hdescent : baseEnd_3763637 < baseStart_3763637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763652 : List Nat := [2, 3, 3, 2, 1, 2, 2, 7]
def baseStart_3763652 : Nat := 118140960795 + 3763652 * 2 ^ 59
def prefixEnd_3763652 : Nat := 4983230072969 + 3 ^ 40 * 3763652 * 2
def baseEnd_3763652 : Nat := 143152777204119550217873

theorem tailTrace_3763652 : CollatzResearch.WordTrace tailWord_3763652 prefixEnd_3763652 143152777204119550217873 := by
  unfold tailWord_3763652
  simp only [CollatzResearch.WordTrace]
  refine ⟨68635832880469529716166605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91514443840626039621555473 68635832880469529716166605)
  ·
    refine ⟨25738437330176073643562477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68635832880469529716166605 25738437330176073643562477)
    ·
      refine ⟨9651913998816027616335929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25738437330176073643562477 9651913998816027616335929)
      ·
        refine ⟨7238935499112020712251947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9651913998816027616335929 7238935499112020712251947)
        ·
          refine ⟨10858403248668031068377921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7238935499112020712251947 10858403248668031068377921)
          ·
            refine ⟨8143802436501023301283441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10858403248668031068377921 8143802436501023301283441)
            ·
              refine ⟨6107851827375767475962581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8143802436501023301283441 6107851827375767475962581)
              ·
                refine ⟨143152777204119550217873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6107851827375767475962581 143152777204119550217873)
                ·
                  rfl

theorem cell22_3763652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 7].length) (baseStart_3763652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763652 prefixEnd_3763652 := by exact prefixLift 3763652
  have htrace : WordTrace (prefixWord ++ tailWord_3763652) baseStart_3763652 baseEnd_3763652 := by
    simpa [prefixWord, tailWord_3763652, baseEnd_3763652] using wordTrace_append hprefix tailTrace_3763652
  have hstable : (prefixWord ++ tailWord_3763652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763652).length < 2 ^ (prefixWord ++ tailWord_3763652).sum := by decide
  have hdescent : baseEnd_3763652 < baseStart_3763652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763697 : List Nat := [1, 2, 2, 2, 3, 3, 2, 2, 5]
def baseStart_3763697 : Nat := 118140960795 + 3763697 * 2 ^ 59
def prefixEnd_3763697 : Nat := 4983230072969 + 3 ^ 40 * 3763697 * 2
def baseEnd_3763697 : Nat := 429463466418903611528573

theorem tailTrace_3763697 : CollatzResearch.WordTrace tailWord_3763697 prefixEnd_3763697 429463466418903611528573 := by
  unfold tailWord_3763697
  simp only [CollatzResearch.WordTrace]
  refine ⟨137273307045776032117721345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91515538030517354745147563 137273307045776032117721345)
  ·
    refine ⟨102954980284332024088291009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137273307045776032117721345 102954980284332024088291009)
    ·
      refine ⟨77216235213249018066218257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102954980284332024088291009 77216235213249018066218257)
      ·
        refine ⟨57912176409936763549663693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77216235213249018066218257 57912176409936763549663693)
        ·
          refine ⟨21717066153726286331123885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57912176409936763549663693 21717066153726286331123885)
          ·
            refine ⟨8143899807647357374171457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21717066153726286331123885 8143899807647357374171457)
            ·
              refine ⟨6107924855735518030628593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8143899807647357374171457 6107924855735518030628593)
              ·
                refine ⟨4580943641801638522971445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6107924855735518030628593 4580943641801638522971445)
                ·
                  refine ⟨429463466418903611528573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4580943641801638522971445 429463466418903611528573)
                  ·
                    rfl

theorem cell22_3763697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 2, 2, 5].length) (baseStart_3763697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763697 prefixEnd_3763697 := by exact prefixLift 3763697
  have htrace : WordTrace (prefixWord ++ tailWord_3763697) baseStart_3763697 baseEnd_3763697 := by
    simpa [prefixWord, tailWord_3763697, baseEnd_3763697] using wordTrace_append hprefix tailTrace_3763697
  have hstable : (prefixWord ++ tailWord_3763697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763697).length < 2 ^ (prefixWord ++ tailWord_3763697).sum := by decide
  have hdescent : baseEnd_3763697 < baseStart_3763697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763714 : List Nat := [3, 4, 1, 2, 1, 1, 2, 3, 5]
def baseStart_3763714 : Nat := 118140960795 + 3763714 * 2 ^ 59
def prefixEnd_3763714 : Nat := 4983230072969 + 3 ^ 40 * 3763714 * 2
def baseEnd_3763714 : Nat := 429465406234709485636889

theorem tailTrace_3763714 : CollatzResearch.WordTrace tailWord_3763714 prefixEnd_3763714 429465406234709485636889 := by
  unfold tailWord_3763714
  simp only [CollatzResearch.WordTrace]
  refine ⟨34318481771678611005272549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91515951391142962680726797 34318481771678611005272549)
  ·
    refine ⟨6434715332189739563488603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34318481771678611005272549 6434715332189739563488603)
    ·
      refine ⟨9652072998284609345232905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6434715332189739563488603 9652072998284609345232905)
      ·
        refine ⟨7239054748713457008924679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9652072998284609345232905 7239054748713457008924679)
        ·
          refine ⟨10858582123070185513387019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7239054748713457008924679 10858582123070185513387019)
          ·
            refine ⟨16287873184605278270080529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10858582123070185513387019 16287873184605278270080529)
            ·
              refine ⟨12215904888453958702560397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16287873184605278270080529 12215904888453958702560397)
              ·
                refine ⟨4580964333170234513460149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12215904888453958702560397 4580964333170234513460149)
                ·
                  refine ⟨429465406234709485636889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4580964333170234513460149 429465406234709485636889)
                  ·
                    rfl

theorem cell22_3763714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_3763714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763714 prefixEnd_3763714 := by exact prefixLift 3763714
  have htrace : WordTrace (prefixWord ++ tailWord_3763714) baseStart_3763714 baseEnd_3763714 := by
    simpa [prefixWord, tailWord_3763714, baseEnd_3763714] using wordTrace_append hprefix tailTrace_3763714
  have hstable : (prefixWord ++ tailWord_3763714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763714).length < 2 ^ (prefixWord ++ tailWord_3763714).sum := by decide
  have hdescent : baseEnd_3763714 < baseStart_3763714 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763744 : List Nat := [2, 1, 1, 6, 1, 2, 1, 3, 1, 4]
def baseStart_3763744 : Nat := 118140960795 + 3763744 * 2 ^ 59
def prefixEnd_3763744 : Nat := 4983230072969 + 3 ^ 40 * 3763744 * 2
def baseEnd_3763744 : Nat := 1288406488317218378660575

theorem tailTrace_3763744 : CollatzResearch.WordTrace tailWord_3763744 prefixEnd_3763744 1288406488317218378660575 := by
  unfold tailWord_3763744
  simp only [CollatzResearch.WordTrace]
  refine ⟨68637510638302879572341143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91516680851070506096454857 68637510638302879572341143)
  ·
    refine ⟨102956265957454319358511715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68637510638302879572341143 102956265957454319358511715)
    ·
      refine ⟨154434398936181479037767573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102956265957454319358511715 154434398936181479037767573)
      ·
        refine ⟨7239112450133506829895355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 154434398936181479037767573 7239112450133506829895355)
        ·
          refine ⟨10858668675200260244843033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7239112450133506829895355 10858668675200260244843033)
          ·
            refine ⟨8144001506400195183632275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10858668675200260244843033 8144001506400195183632275)
            ·
              refine ⟨12216002259600292775448413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8144001506400195183632275 12216002259600292775448413)
              ·
                refine ⟨4581000847350109790793155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12216002259600292775448413 4581000847350109790793155)
                ·
                  refine ⟨6871501271025164686189733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4581000847350109790793155 6871501271025164686189733)
                  ·
                    refine ⟨1288406488317218378660575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6871501271025164686189733 1288406488317218378660575)
                    ·
                      rfl

theorem cell22_3763744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 2, 1, 3, 1, 4].length) (baseStart_3763744 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763744 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763744 prefixEnd_3763744 := by exact prefixLift 3763744
  have htrace : WordTrace (prefixWord ++ tailWord_3763744) baseStart_3763744 baseEnd_3763744 := by
    simpa [prefixWord, tailWord_3763744, baseEnd_3763744] using wordTrace_append hprefix tailTrace_3763744
  have hstable : (prefixWord ++ tailWord_3763744).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763744).length < 2 ^ (prefixWord ++ tailWord_3763744).sum := by decide
  have hdescent : baseEnd_3763744 < baseStart_3763744 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763770 : List Nat := [3, 1, 1, 1, 3, 2, 2, 9]
def baseStart_3763770 : Nat := 118140960795 + 3763770 * 2 ^ 59
def prefixEnd_3763770 : Nat := 4983230072969 + 3 ^ 40 * 3763770 * 2
def baseEnd_3763770 : Nat := 143157265405395886390055

theorem tailTrace_3763770 : CollatzResearch.WordTrace tailWord_3763770 prefixEnd_3763770 143157265405395886390055 := by
  unfold tailWord_3763770
  simp only [CollatzResearch.WordTrace]
  refine ⟨34318992393627891396282191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91517313049674377056752509 34318992393627891396282191)
  ·
    refine ⟨51478488590441837094423287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34318992393627891396282191 51478488590441837094423287)
    ·
      refine ⟨77217732885662755641634931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51478488590441837094423287 77217732885662755641634931)
      ·
        refine ⟨115826599328494133462452397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77217732885662755641634931 115826599328494133462452397)
        ·
          refine ⟨43434974748185300048419649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115826599328494133462452397 43434974748185300048419649)
          ·
            refine ⟨32576231061138975036314737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43434974748185300048419649 32576231061138975036314737)
            ·
              refine ⟨24432173295854231277236053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32576231061138975036314737 24432173295854231277236053)
              ·
                refine ⟨143157265405395886390055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24432173295854231277236053 143157265405395886390055)
                ·
                  rfl

theorem cell22_3763770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 9].length) (baseStart_3763770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763770 prefixEnd_3763770 := by exact prefixLift 3763770
  have htrace : WordTrace (prefixWord ++ tailWord_3763770) baseStart_3763770 baseEnd_3763770 := by
    simpa [prefixWord, tailWord_3763770, baseEnd_3763770] using wordTrace_append hprefix tailTrace_3763770
  have hstable : (prefixWord ++ tailWord_3763770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763770).length < 2 ^ (prefixWord ++ tailWord_3763770).sum := by decide
  have hdescent : baseEnd_3763770 < baseStart_3763770 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763800 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 1, 8]
def baseStart_3763800 : Nat := 118140960795 + 3763800 * 2 ^ 59
def prefixEnd_3763800 : Nat := 4983230072969 + 3 ^ 40 * 3763800 * 2
def baseEnd_3763800 : Nat := 1288425658261652899260403

theorem tailTrace_3763800 : CollatzResearch.WordTrace tailWord_3763800 prefixEnd_3763800 1288425658261652899260403 := by
  unfold tailWord_3763800
  simp only [CollatzResearch.WordTrace]
  refine ⟨68638531882201440354360427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91518042509601920472480569 68638531882201440354360427)
  ·
    refine ⟨102957797823302160531540641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68638531882201440354360427 102957797823302160531540641)
    ·
      refine ⟨77218348367476620398655481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102957797823302160531540641 77218348367476620398655481)
      ·
        refine ⟨57913761275607465298991611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77218348367476620398655481 57913761275607465298991611)
        ·
          refine ⟨86870641913411197948487417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57913761275607465298991611 86870641913411197948487417)
          ·
            refine ⟨65152981435058398461365563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86870641913411197948487417 65152981435058398461365563)
            ·
              refine ⟨97729472152587597692048345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65152981435058398461365563 97729472152587597692048345)
              ·
                refine ⟨73297104114440698269036259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97729472152587597692048345 73297104114440698269036259)
                ·
                  refine ⟨109945656171661047403554389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73297104114440698269036259 109945656171661047403554389)
                  ·
                    refine ⟨1288425658261652899260403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 109945656171661047403554389 1288425658261652899260403)
                    ·
                      rfl

theorem cell22_3763800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 1, 8].length) (baseStart_3763800 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763800 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763800 prefixEnd_3763800 := by exact prefixLift 3763800
  have htrace : WordTrace (prefixWord ++ tailWord_3763800) baseStart_3763800 baseEnd_3763800 := by
    simpa [prefixWord, tailWord_3763800, baseEnd_3763800] using wordTrace_append hprefix tailTrace_3763800
  have hstable : (prefixWord ++ tailWord_3763800).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763800).length < 2 ^ (prefixWord ++ tailWord_3763800).sum := by decide
  have hdescent : baseEnd_3763800 < baseStart_3763800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763802 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 5, 3]
def baseStart_3763802 : Nat := 118140960795 + 3763802 * 2 ^ 59
def prefixEnd_3763802 : Nat := 4983230072969 + 3 ^ 40 * 3763802 * 2
def baseEnd_3763802 : Nat := 1288426342902525560710397

theorem tailTrace_3763802 : CollatzResearch.WordTrace tailWord_3763802 prefixEnd_3763802 1288426342902525560710397 := by
  unfold tailWord_3763802
  simp only [CollatzResearch.WordTrace]
  refine ⟨34319284177598908762573415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91518091140263756700195773 34319284177598908762573415)
  ·
    refine ⟨51478926266398363143860123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34319284177598908762573415 51478926266398363143860123)
    ·
      refine ⟨77218389399597544715790185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51478926266398363143860123 77218389399597544715790185)
      ·
        refine ⟨57913792049698158536842639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77218389399597544715790185 57913792049698158536842639)
        ·
          refine ⟨86870688074547237805263959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57913792049698158536842639 86870688074547237805263959)
          ·
            refine ⟨130306032111820856707895939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86870688074547237805263959 130306032111820856707895939)
            ·
              refine ⟨195459048167731285061843909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130306032111820856707895939 195459048167731285061843909)
              ·
                refine ⟨36648571531449615949095733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195459048167731285061843909 36648571531449615949095733)
                ·
                  refine ⟨3435803581073401495227725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36648571531449615949095733 3435803581073401495227725)
                  ·
                    refine ⟨1288426342902525560710397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3435803581073401495227725 1288426342902525560710397)
                    ·
                      rfl

theorem cell22_3763802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 5, 3].length) (baseStart_3763802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763802 prefixEnd_3763802 := by exact prefixLift 3763802
  have htrace : WordTrace (prefixWord ++ tailWord_3763802) baseStart_3763802 baseEnd_3763802 := by
    simpa [prefixWord, tailWord_3763802, baseEnd_3763802] using wordTrace_append hprefix tailTrace_3763802
  have hstable : (prefixWord ++ tailWord_3763802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763802).length < 2 ^ (prefixWord ++ tailWord_3763802).sum := by decide
  have hdescent : baseEnd_3763802 < baseStart_3763802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763870 : List Nat := [4, 3, 1, 1, 1, 2, 4, 2, 1, 3]
def baseStart_3763870 : Nat := 118140960795 + 3763870 * 2 ^ 59
def prefixEnd_3763870 : Nat := 4983230072969 + 3 ^ 40 * 3763870 * 2
def baseEnd_3763870 : Nat := 1288449620692196050010189

theorem tailTrace_3763870 : CollatzResearch.WordTrace tailWord_3763870 prefixEnd_3763870 1288449620692196050010189 := by
  unfold tailWord_3763870
  simp only [CollatzResearch.WordTrace]
  refine ⟨17159952109268660332971133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91519744582766188442512709 17159952109268660332971133)
  ·
    refine ⟨6434982040975747624864175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17159952109268660332971133 6434982040975747624864175)
    ·
      refine ⟨9652473061463621437296263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6434982040975747624864175 9652473061463621437296263)
      ·
        refine ⟨14478709592195432155944395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9652473061463621437296263 14478709592195432155944395)
        ·
          refine ⟨21718064388293148233916593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14478709592195432155944395 21718064388293148233916593)
          ·
            refine ⟨16288548291219861175437445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21718064388293148233916593 16288548291219861175437445)
            ·
              refine ⟨3054102804603723970394521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16288548291219861175437445 3054102804603723970394521)
              ·
                refine ⟨2290577103452792977795891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3054102804603723970394521 2290577103452792977795891)
                ·
                  refine ⟨3435865655179189466693837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2290577103452792977795891 3435865655179189466693837)
                  ·
                    refine ⟨1288449620692196050010189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3435865655179189466693837 1288449620692196050010189)
                    ·
                      rfl

theorem cell22_3763870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 1, 3].length) (baseStart_3763870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763870 prefixEnd_3763870 := by exact prefixLift 3763870
  have htrace : WordTrace (prefixWord ++ tailWord_3763870) baseStart_3763870 baseEnd_3763870 := by
    simpa [prefixWord, tailWord_3763870, baseEnd_3763870] using wordTrace_append hprefix tailTrace_3763870
  have hstable : (prefixWord ++ tailWord_3763870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763870).length < 2 ^ (prefixWord ++ tailWord_3763870).sum := by decide
  have hdescent : baseEnd_3763870 < baseStart_3763870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763943 : List Nat := [1, 1, 5, 4, 1, 2, 1, 1, 1, 5]
def baseStart_3763943 : Nat := 118140960795 + 3763943 * 2 ^ 59
def prefixEnd_3763943 : Nat := 4983230072969 + 3 ^ 40 * 3763943 * 2
def baseEnd_3763943 : Nat := 1288474610084048192934965

theorem tailTrace_3763943 : CollatzResearch.WordTrace tailWord_3763943 prefixEnd_3763943 1288474610084048192934965 := by
  unfold tailWord_3763943
  simp only [CollatzResearch.WordTrace]
  refine ⟨137282279402884816131176483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91521519601923210754117655 137282279402884816131176483)
  ·
    refine ⟨205923419104327224196764725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137282279402884816131176483 205923419104327224196764725)
    ·
      refine ⟨19305320541030677268446693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205923419104327224196764725 19305320541030677268446693)
      ·
        refine ⟨3619747601443251987833755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19305320541030677268446693 3619747601443251987833755)
        ·
          refine ⟨5429621402164877981750633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3619747601443251987833755 5429621402164877981750633)
          ·
            refine ⟨4072216051623658486312975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5429621402164877981750633 4072216051623658486312975)
            ·
              refine ⟨6108324077435487729469463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4072216051623658486312975 6108324077435487729469463)
              ·
                refine ⟨9162486116153231594204195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6108324077435487729469463 9162486116153231594204195)
                ·
                  refine ⟨13743729174229847391306293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9162486116153231594204195 13743729174229847391306293)
                  ·
                    refine ⟨1288474610084048192934965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13743729174229847391306293 1288474610084048192934965)
                    ·
                      rfl

theorem cell22_3763943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_3763943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763943 prefixEnd_3763943 := by exact prefixLift 3763943
  have htrace : WordTrace (prefixWord ++ tailWord_3763943) baseStart_3763943 baseEnd_3763943 := by
    simpa [prefixWord, tailWord_3763943, baseEnd_3763943] using wordTrace_append hprefix tailTrace_3763943
  have hstable : (prefixWord ++ tailWord_3763943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763943).length < 2 ^ (prefixWord ++ tailWord_3763943).sum := by decide
  have hdescent : baseEnd_3763943 < baseStart_3763943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3763967 : List Nat := [1, 1, 2, 2, 1, 3, 3, 2, 7]
def baseStart_3763967 : Nat := 118140960795 + 3763967 * 2 ^ 59
def prefixEnd_3763967 : Nat := 4983230072969 + 3 ^ 40 * 3763967 * 2
def baseEnd_3763967 : Nat := 429494275258173376778297

theorem tailTrace_3763967 : CollatzResearch.WordTrace tailWord_3763967 prefixEnd_3763967 429494275258173376778297 := by
  unfold tailWord_3763967
  simp only [CollatzResearch.WordTrace]
  refine ⟨137283154754797868230050155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91522103169865245486700103 137283154754797868230050155)
  ·
    refine ⟨205924732132196802345075233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137283154754797868230050155 205924732132196802345075233)
    ·
      refine ⟨154443549099147601758806425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205924732132196802345075233 154443549099147601758806425)
      ·
        refine ⟨115832661824360701319104819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154443549099147601758806425 115832661824360701319104819)
        ·
          refine ⟨173748992736541051978657229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115832661824360701319104819 173748992736541051978657229)
          ·
            refine ⟨65155872276202894491996461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173748992736541051978657229 65155872276202894491996461)
            ·
              refine ⟨24433452103576085434498673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65155872276202894491996461 24433452103576085434498673)
              ·
                refine ⟨18325089077682064075874005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24433452103576085434498673 18325089077682064075874005)
                ·
                  refine ⟨429494275258173376778297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18325089077682064075874005 429494275258173376778297)
                  ·
                    rfl

theorem cell22_3763967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 2, 7].length) (baseStart_3763967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3763967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3763967 prefixEnd_3763967 := by exact prefixLift 3763967
  have htrace : WordTrace (prefixWord ++ tailWord_3763967) baseStart_3763967 baseEnd_3763967 := by
    simpa [prefixWord, tailWord_3763967, baseEnd_3763967] using wordTrace_append hprefix tailTrace_3763967
  have hstable : (prefixWord ++ tailWord_3763967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3763967).length < 2 ^ (prefixWord ++ tailWord_3763967).sum := by decide
  have hdescent : baseEnd_3763967 < baseStart_3763967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3763967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764001 : List Nat := [1, 2, 3, 2, 1, 3, 4, 1, 5]
def baseStart_3764001 : Nat := 118140960795 + 3764001 * 2 ^ 59
def prefixEnd_3764001 : Nat := 4983230072969 + 3 ^ 40 * 3764001 * 2
def baseEnd_3764001 : Nat := 429498154889785124994929

theorem tailTrace_3764001 : CollatzResearch.WordTrace tailWord_3764001 prefixEnd_3764001 429498154889785124994929 := by
  unfold tailWord_3764001
  simp only [CollatzResearch.WordTrace]
  refine ⟨137284394836674692036787857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91522929891116461357858571 137284394836674692036787857)
  ·
    refine ⟨102963296127506019027590893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137284394836674692036787857 102963296127506019027590893)
    ·
      refine ⟨38611236047814757135346585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102963296127506019027590893 38611236047814757135346585)
      ·
        refine ⟨28958427035861067851509939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38611236047814757135346585 28958427035861067851509939)
        ·
          refine ⟨43437640553791601777264909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28958427035861067851509939 43437640553791601777264909)
          ·
            refine ⟨16289115207671850666474341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43437640553791601777264909 16289115207671850666474341)
            ·
              refine ⟨3054209101438471999963939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16289115207671850666474341 3054209101438471999963939)
              ·
                refine ⟨4581313652157707999945909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3054209101438471999963939 4581313652157707999945909)
                ·
                  refine ⟨429498154889785124994929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4581313652157707999945909 429498154889785124994929)
                  ·
                    rfl

theorem cell22_3764001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 4, 1, 5].length) (baseStart_3764001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764001 prefixEnd_3764001 := by exact prefixLift 3764001
  have htrace : WordTrace (prefixWord ++ tailWord_3764001) baseStart_3764001 baseEnd_3764001 := by
    simpa [prefixWord, tailWord_3764001, baseEnd_3764001] using wordTrace_append hprefix tailTrace_3764001
  have hstable : (prefixWord ++ tailWord_3764001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764001).length < 2 ^ (prefixWord ++ tailWord_3764001).sum := by decide
  have hdescent : baseEnd_3764001 < baseStart_3764001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764076 : List Nat := [2, 2, 1, 1, 4, 2, 3, 1, 2, 4]
def baseStart_3764076 : Nat := 118140960795 + 3764076 * 2 ^ 59
def prefixEnd_3764076 : Nat := 4983230072969 + 3 ^ 40 * 3764076 * 2
def baseEnd_3764076 : Nat := 1288520138702080179359557

theorem tailTrace_3764076 : CollatzResearch.WordTrace tailWord_3764076 prefixEnd_3764076 1288520138702080179359557 := by
  unfold tailWord_3764076
  simp only [CollatzResearch.WordTrace]
  refine ⟨68643565155701489922884041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91524753540935319897178721 68643565155701489922884041)
  ·
    refine ⟨51482673866776117442163031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68643565155701489922884041 51482673866776117442163031)
    ·
      refine ⟨77224010800164176163244547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51482673866776117442163031 77224010800164176163244547)
      ·
        refine ⟨115836016200246264244866821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77224010800164176163244547 115836016200246264244866821)
        ·
          refine ⟨21719253037546174545912529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115836016200246264244866821 21719253037546174545912529)
          ·
            refine ⟨16289439778159630909434397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21719253037546174545912529 16289439778159630909434397)
            ·
              refine ⟨6108539916809861591037899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16289439778159630909434397 6108539916809861591037899)
              ·
                refine ⟨9162809875214792386556849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6108539916809861591037899 9162809875214792386556849)
                ·
                  refine ⟨6872107406411094289917637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9162809875214792386556849 6872107406411094289917637)
                  ·
                    refine ⟨1288520138702080179359557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6872107406411094289917637 1288520138702080179359557)
                    ·
                      rfl

theorem cell22_3764076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_3764076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764076 prefixEnd_3764076 := by exact prefixLift 3764076
  have htrace : WordTrace (prefixWord ++ tailWord_3764076) baseStart_3764076 baseEnd_3764076 := by
    simpa [prefixWord, tailWord_3764076, baseEnd_3764076] using wordTrace_append hprefix tailTrace_3764076
  have hstable : (prefixWord ++ tailWord_3764076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764076).length < 2 ^ (prefixWord ++ tailWord_3764076).sum := by decide
  have hdescent : baseEnd_3764076 < baseStart_3764076 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764142 : List Nat := [4, 1, 5, 1, 2, 1, 8]
def baseStart_3764142 : Nat := 118140960795 + 3764142 * 2 ^ 59
def prefixEnd_3764142 : Nat := 4983230072969 + 3 ^ 40 * 3764142 * 2
def baseEnd_3764142 : Nat := 47723804883365852118865

theorem tailTrace_3764142 : CollatzResearch.WordTrace tailWord_3764142 prefixEnd_3764142 47723804883365852118865 := by
  unfold tailWord_3764142
  simp only [CollatzResearch.WordTrace]
  refine ⟨17161192191145484139708835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91526358352775915411780453 17161192191145484139708835)
  ·
    refine ⟨25741788286718226209563253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17161192191145484139708835 25741788286718226209563253)
    ·
      refine ⟨2413292651879833707146555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25741788286718226209563253 2413292651879833707146555)
      ·
        refine ⟨3619938977819750560719833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2413292651879833707146555 3619938977819750560719833)
        ·
          refine ⟨2714954233364812920539875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3619938977819750560719833 2714954233364812920539875)
          ·
            refine ⟨4072431350047219380809813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2714954233364812920539875 4072431350047219380809813)
            ·
              refine ⟨47723804883365852118865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4072431350047219380809813 47723804883365852118865)
              ·
                rfl

theorem cell22_3764142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 8].length) (baseStart_3764142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764142 prefixEnd_3764142 := by exact prefixLift 3764142
  have htrace : WordTrace (prefixWord ++ tailWord_3764142) baseStart_3764142 baseEnd_3764142 := by
    simpa [prefixWord, tailWord_3764142, baseEnd_3764142] using wordTrace_append hprefix tailTrace_3764142
  have hstable : (prefixWord ++ tailWord_3764142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764142).length < 2 ^ (prefixWord ++ tailWord_3764142).sum := by decide
  have hdescent : baseEnd_3764142 < baseStart_3764142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764157 : List Nat := [1, 4, 1, 2, 3, 2, 3, 2, 1, 3]
def baseStart_3764157 : Nat := 118140960795 + 3764157 * 2 ^ 59
def prefixEnd_3764157 : Nat := 4983230072969 + 3 ^ 40 * 3764157 * 2
def baseEnd_3764157 : Nat := 1288547866657422968084309

theorem tailTrace_3764157 : CollatzResearch.WordTrace tailWord_3764157 prefixEnd_3764157 1288547866657422968084309 := by
  unfold tailWord_3764157
  simp only [CollatzResearch.WordTrace]
  refine ⟨137290084624109530679466725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91526723082739687119644483 137290084624109530679466725)
  ·
    refine ⟨25741890867020537002400011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137290084624109530679466725 25741890867020537002400011)
    ·
      refine ⟨38612836300530805503600017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25741890867020537002400011 38612836300530805503600017)
      ·
        refine ⟨28959627225398104127700013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38612836300530805503600017 28959627225398104127700013)
        ·
          refine ⟨10859860209524289047887505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28959627225398104127700013 10859860209524289047887505)
          ·
            refine ⟨8144895157143216785915629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10859860209524289047887505 8144895157143216785915629)
            ·
              refine ⟨3054335683928706294718361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8144895157143216785915629 3054335683928706294718361)
              ·
                refine ⟨2290751762946529721038771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3054335683928706294718361 2290751762946529721038771)
                ·
                  refine ⟨3436127644419794581558157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2290751762946529721038771 3436127644419794581558157)
                  ·
                    refine ⟨1288547866657422968084309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3436127644419794581558157 1288547866657422968084309)
                    ·
                      rfl

theorem cell22_3764157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_3764157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764157 prefixEnd_3764157 := by exact prefixLift 3764157
  have htrace : WordTrace (prefixWord ++ tailWord_3764157) baseStart_3764157 baseEnd_3764157 := by
    simpa [prefixWord, tailWord_3764157, baseEnd_3764157] using wordTrace_append hprefix tailTrace_3764157
  have hstable : (prefixWord ++ tailWord_3764157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764157).length < 2 ^ (prefixWord ++ tailWord_3764157).sum := by decide
  have hdescent : baseEnd_3764157 < baseStart_3764157 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764196 : List Nat := [2, 3, 1, 1, 1, 1, 5, 2, 1, 5]
def baseStart_3764196 : Nat := 118140960795 + 3764196 * 2 ^ 59
def prefixEnd_3764196 : Nat := 4983230072969 + 3 ^ 40 * 3764196 * 2
def baseEnd_3764196 : Nat := 1288561217154439866359189

theorem tailTrace_3764196 : CollatzResearch.WordTrace tailWord_3764196 prefixEnd_3764196 1288561217154439866359189 := by
  unfold tailWord_3764196
  simp only [CollatzResearch.WordTrace]
  refine ⟨68645753535484120170068221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91527671380645493560090961 68645753535484120170068221)
  ·
    refine ⟨25742157575806545063775583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68645753535484120170068221 25742157575806545063775583)
    ·
      refine ⟨38613236363709817595663375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25742157575806545063775583 38613236363709817595663375)
      ·
        refine ⟨57919854545564726393495063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38613236363709817595663375 57919854545564726393495063)
        ·
          refine ⟨86879781818347089590242595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57919854545564726393495063 86879781818347089590242595)
          ·
            refine ⟨130319672727520634385363893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86879781818347089590242595 130319672727520634385363893)
            ·
              refine ⟨12217469318205059473627865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130319672727520634385363893 12217469318205059473627865)
              ·
                refine ⟨9163101988653794605220899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12217469318205059473627865 9163101988653794605220899)
                ·
                  refine ⟨13744652982980691907831349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9163101988653794605220899 13744652982980691907831349)
                  ·
                    refine ⟨1288561217154439866359189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13744652982980691907831349 1288561217154439866359189)
                    ·
                      rfl

theorem cell22_3764196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_3764196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764196 prefixEnd_3764196 := by exact prefixLift 3764196
  have htrace : WordTrace (prefixWord ++ tailWord_3764196) baseStart_3764196 baseEnd_3764196 := by
    simpa [prefixWord, tailWord_3764196, baseEnd_3764196] using wordTrace_append hprefix tailTrace_3764196
  have hstable : (prefixWord ++ tailWord_3764196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764196).length < 2 ^ (prefixWord ++ tailWord_3764196).sum := by decide
  have hdescent : baseEnd_3764196 < baseStart_3764196 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764209 : List Nat := [1, 2, 2, 2, 15]
def baseStart_3764209 : Nat := 118140960795 + 3764209 * 2 ^ 59
def prefixEnd_3764209 : Nat := 4983230072969 + 3 ^ 40 * 3764209 * 2
def baseEnd_3764209 : Nat := 5302739371687704385943

theorem tailTrace_3764209 : CollatzResearch.WordTrace tailWord_3764209 prefixEnd_3764209 5302739371687704385943 := by
  unfold tailWord_3764209
  simp only [CollatzResearch.WordTrace]
  refine ⟨137291981219921143560359681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91527987479947429040239787 137291981219921143560359681)
  ·
    refine ⟨102968985914940857670269761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137291981219921143560359681 102968985914940857670269761)
    ·
      refine ⟨77226739436205643252702321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102968985914940857670269761 77226739436205643252702321)
      ·
        refine ⟨57920054577154232439526741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77226739436205643252702321 57920054577154232439526741)
        ·
          refine ⟨5302739371687704385943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 15 57920054577154232439526741 5302739371687704385943)
          ·
            rfl

theorem cell22_3764209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 15].length) (baseStart_3764209 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764209 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764209 prefixEnd_3764209 := by exact prefixLift 3764209
  have htrace : WordTrace (prefixWord ++ tailWord_3764209) baseStart_3764209 baseEnd_3764209 := by
    simpa [prefixWord, tailWord_3764209, baseEnd_3764209] using wordTrace_append hprefix tailTrace_3764209
  have hstable : (prefixWord ++ tailWord_3764209).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764209).length < 2 ^ (prefixWord ++ tailWord_3764209).sum := by decide
  have hdescent : baseEnd_3764209 < baseStart_3764209 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764245 : List Nat := [1, 3, 2, 1, 5, 2, 1, 1, 2, 4]
def baseStart_3764245 : Nat := 118140960795 + 3764245 * 2 ^ 59
def prefixEnd_3764245 : Nat := 4983230072969 + 3 ^ 40 * 3764245 * 2
def baseEnd_3764245 : Nat := 1288577990855820071884039

theorem tailTrace_3764245 : CollatzResearch.WordTrace tailWord_3764245 prefixEnd_3764245 1288577990855820071884039 := by
  unfold tailWord_3764245
  simp only [CollatzResearch.WordTrace]
  refine ⟨137293294247790721708670189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91528862831860481139113459 137293294247790721708670189)
  ·
    refine ⟨51484985342921520640751321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137293294247790721708670189 51484985342921520640751321)
    ·
      refine ⟨38613739007191140480563491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51484985342921520640751321 38613739007191140480563491)
      ·
        refine ⟨57920608510786710720845237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38613739007191140480563491 57920608510786710720845237)
        ·
          refine ⟨5430057047886254130079241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57920608510786710720845237 5430057047886254130079241)
          ·
            refine ⟨4072542785914690597559431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5430057047886254130079241 4072542785914690597559431)
            ·
              refine ⟨6108814178872035896339147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4072542785914690597559431 6108814178872035896339147)
              ·
                refine ⟨9163221268308053844508721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6108814178872035896339147 9163221268308053844508721)
                ·
                  refine ⟨6872415951231040383381541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9163221268308053844508721 6872415951231040383381541)
                  ·
                    refine ⟨1288577990855820071884039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6872415951231040383381541 1288577990855820071884039)
                    ·
                      rfl

theorem cell22_3764245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 1, 2, 4].length) (baseStart_3764245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764245 prefixEnd_3764245 := by exact prefixLift 3764245
  have htrace : WordTrace (prefixWord ++ tailWord_3764245) baseStart_3764245 baseEnd_3764245 := by
    simpa [prefixWord, tailWord_3764245, baseEnd_3764245] using wordTrace_append hprefix tailTrace_3764245
  have hstable : (prefixWord ++ tailWord_3764245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764245).length < 2 ^ (prefixWord ++ tailWord_3764245).sum := by decide
  have hdescent : baseEnd_3764245 < baseStart_3764245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764258 : List Nat := [3, 3, 1, 1, 1, 2, 1, 2, 5, 3]
def baseStart_3764258 : Nat := 118140960795 + 3764258 * 2 ^ 59
def prefixEnd_3764258 : Nat := 4983230072969 + 3 ^ 40 * 3764258 * 2
def baseEnd_3764258 : Nat := 1288582441021492371308999

theorem tailTrace_3764258 : CollatzResearch.WordTrace tailWord_3764258 prefixEnd_3764258 1288582441021492371308999 := by
  unfold tailWord_3764258
  simp only [CollatzResearch.WordTrace]
  refine ⟨34323442099185906232223357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91529178931162416619262285 34323442099185906232223357)
  ·
    refine ⟨12871290787194714837083759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34323442099185906232223357 12871290787194714837083759)
    ·
      refine ⟨19306936180792072255625639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12871290787194714837083759 19306936180792072255625639)
      ·
        refine ⟨28960404271188108383438459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19306936180792072255625639 28960404271188108383438459)
        ·
          refine ⟨43440606406782162575157689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28960404271188108383438459 43440606406782162575157689)
          ·
            refine ⟨32580454805086621931368267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43440606406782162575157689 32580454805086621931368267)
            ·
              refine ⟨48870682207629932897052401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32580454805086621931368267 48870682207629932897052401)
              ·
                refine ⟨36653011655722449672789301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48870682207629932897052401 36653011655722449672789301)
                ·
                  refine ⟨3436219842723979656823997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36653011655722449672789301 3436219842723979656823997)
                  ·
                    refine ⟨1288582441021492371308999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3436219842723979656823997 1288582441021492371308999)
                    ·
                      rfl

theorem cell22_3764258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 2, 5, 3].length) (baseStart_3764258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764258 prefixEnd_3764258 := by exact prefixLift 3764258
  have htrace : WordTrace (prefixWord ++ tailWord_3764258) baseStart_3764258 baseEnd_3764258 := by
    simpa [prefixWord, tailWord_3764258, baseEnd_3764258] using wordTrace_append hprefix tailTrace_3764258
  have hstable : (prefixWord ++ tailWord_3764258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764258).length < 2 ^ (prefixWord ++ tailWord_3764258).sum := by decide
  have hdescent : baseEnd_3764258 < baseStart_3764258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764264 : List Nat := [2, 1, 5, 3, 1, 2, 1, 2, 2, 3]
def baseStart_3764264 : Nat := 118140960795 + 3764264 * 2 ^ 59
def prefixEnd_3764264 : Nat := 4983230072969 + 3 ^ 40 * 3764264 * 2
def baseEnd_3764264 : Nat := 1288584494944110355658981

theorem tailTrace_3764264 : CollatzResearch.WordTrace tailWord_3764264 prefixEnd_3764264 1288584494944110355658981 := by
  unfold tailWord_3764264
  simp only [CollatzResearch.WordTrace]
  refine ⟨68646993617360943976805923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91529324823147925302407897 68646993617360943976805923)
  ·
    refine ⟨102970490426041415965208885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68646993617360943976805923 102970490426041415965208885)
    ·
      refine ⟨9653483477441382746738333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102970490426041415965208885 9653483477441382746738333)
      ·
        refine ⟨3620056304040518530026875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9653483477441382746738333 3620056304040518530026875)
        ·
          refine ⟨5430084456060777795040313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3620056304040518530026875 5430084456060777795040313)
          ·
            refine ⟨4072563342045583346280235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5430084456060777795040313 4072563342045583346280235)
            ·
              refine ⟨6108845013068375019420353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4072563342045583346280235 6108845013068375019420353)
              ·
                refine ⟨4581633759801281264565265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6108845013068375019420353 4581633759801281264565265)
                ·
                  refine ⟨3436225319850960948423949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4581633759801281264565265 3436225319850960948423949)
                  ·
                    refine ⟨1288584494944110355658981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3436225319850960948423949 1288584494944110355658981)
                    ·
                      rfl

theorem cell22_3764264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_3764264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764264 prefixEnd_3764264 := by exact prefixLift 3764264
  have htrace : WordTrace (prefixWord ++ tailWord_3764264) baseStart_3764264 baseEnd_3764264 := by
    simpa [prefixWord, tailWord_3764264, baseEnd_3764264] using wordTrace_append hprefix tailTrace_3764264
  have hstable : (prefixWord ++ tailWord_3764264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764264).length < 2 ^ (prefixWord ++ tailWord_3764264).sum := by decide
  have hdescent : baseEnd_3764264 < baseStart_3764264 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764271 : List Nat := [1, 1, 2, 1, 2, 1, 1, 8, 5]
def baseStart_3764271 : Nat := 118140960795 + 3764271 * 2 ^ 59
def prefixEnd_3764271 : Nat := 4983230072969 + 3 ^ 40 * 3764271 * 2
def baseEnd_3764271 : Nat := 429528963729054890244653

theorem tailTrace_3764271 : CollatzResearch.WordTrace tailWord_3764271 prefixEnd_3764271 429528963729054890244653 := by
  unfold tailWord_3764271
  simp only [CollatzResearch.WordTrace]
  refine ⟨137294242545696528149116667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91529495030464352099411111 137294242545696528149116667)
  ·
    refine ⟨205941363818544792223675001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137294242545696528149116667 205941363818544792223675001)
    ·
      refine ⟨154456022863908594167756251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205941363818544792223675001 154456022863908594167756251)
      ·
        refine ⟨231684034295862891251634377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154456022863908594167756251 231684034295862891251634377)
        ·
          refine ⟨173763025721897168438725783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231684034295862891251634377 173763025721897168438725783)
          ·
            refine ⟨260644538582845752658088675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173763025721897168438725783 260644538582845752658088675)
            ·
              refine ⟨390966807874268628987133013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 260644538582845752658088675 390966807874268628987133013)
              ·
                refine ⟨4581642279776585495942965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 390966807874268628987133013 4581642279776585495942965)
                ·
                  refine ⟨429528963729054890244653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4581642279776585495942965 429528963729054890244653)
                  ·
                    rfl

theorem cell22_3764271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 8, 5].length) (baseStart_3764271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764271 prefixEnd_3764271 := by exact prefixLift 3764271
  have htrace : WordTrace (prefixWord ++ tailWord_3764271) baseStart_3764271 baseEnd_3764271 := by
    simpa [prefixWord, tailWord_3764271, baseEnd_3764271] using wordTrace_append hprefix tailTrace_3764271
  have hstable : (prefixWord ++ tailWord_3764271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764271).length < 2 ^ (prefixWord ++ tailWord_3764271).sum := by decide
  have hdescent : baseEnd_3764271 < baseStart_3764271 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764275 : List Nat := [1, 1, 1, 2, 4, 1, 4, 4, 1, 3]
def baseStart_3764275 : Nat := 118140960795 + 3764275 * 2 ^ 59
def prefixEnd_3764275 : Nat := 4983230072969 + 3 ^ 40 * 3764275 * 2
def baseEnd_3764275 : Nat := 1288588260468909993633947

theorem tailTrace_3764275 : CollatzResearch.WordTrace tailWord_3764275 prefixEnd_3764275 1288588260468909993633947 := by
  unfold tailWord_3764275
  simp only [CollatzResearch.WordTrace]
  refine ⟨137294388437682036832262279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91529592291788024554841519 137294388437682036832262279)
  ·
    refine ⟨205941582656523055248393419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137294388437682036832262279 205941582656523055248393419)
    ·
      refine ⟨308912373984784582872590129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205941582656523055248393419 308912373984784582872590129)
      ·
        refine ⟨231684280488588437154442597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 308912373984784582872590129 231684280488588437154442597)
        ·
          refine ⟨43440802591610331966457987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231684280488588437154442597 43440802591610331966457987)
          ·
            refine ⟨65161203887415497949686981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43440802591610331966457987 65161203887415497949686981)
            ·
              refine ⟨12217725728890405865566309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65161203887415497949686981 12217725728890405865566309)
              ·
                refine ⟨2290823574166951099793683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12217725728890405865566309 2290823574166951099793683)
                ·
                  refine ⟨3436235361250426649690525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2290823574166951099793683 3436235361250426649690525)
                  ·
                    refine ⟨1288588260468909993633947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3436235361250426649690525 1288588260468909993633947)
                    ·
                      rfl

theorem cell22_3764275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 4, 4, 1, 3].length) (baseStart_3764275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764275 prefixEnd_3764275 := by exact prefixLift 3764275
  have htrace : WordTrace (prefixWord ++ tailWord_3764275) baseStart_3764275 baseEnd_3764275 := by
    simpa [prefixWord, tailWord_3764275, baseEnd_3764275] using wordTrace_append hprefix tailTrace_3764275
  have hstable : (prefixWord ++ tailWord_3764275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764275).length < 2 ^ (prefixWord ++ tailWord_3764275).sum := by decide
  have hdescent : baseEnd_3764275 < baseStart_3764275 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764361 : List Nat := [1, 2, 1, 1, 4, 2, 1, 10]
def baseStart_3764361 : Nat := 118140960795 + 3764361 * 2 ^ 59
def prefixEnd_3764361 : Nat := 4983230072969 + 3 ^ 40 * 3764361 * 2
def baseEnd_3764361 : Nat := 143179744447381603998187

theorem tailTrace_3764361 : CollatzResearch.WordTrace tailWord_3764361 prefixEnd_3764361 143179744447381603998187 := by
  unfold tailWord_3764361
  simp only [CollatzResearch.WordTrace]
  refine ⟨137297525115370473519892937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91531683410246982346595291 137297525115370473519892937)
  ·
    refine ⟨102973143836527855139919703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137297525115370473519892937 102973143836527855139919703)
    ·
      refine ⟨154459715754791782709879555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102973143836527855139919703 154459715754791782709879555)
      ·
        refine ⟨231689573632187674064819333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154459715754791782709879555 231689573632187674064819333)
        ·
          refine ⟨43441795056035188887153625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231689573632187674064819333 43441795056035188887153625)
          ·
            refine ⟨32581346292026391665365219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43441795056035188887153625 32581346292026391665365219)
            ·
              refine ⟨48872019438039587498047829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32581346292026391665365219 48872019438039587498047829)
              ·
                refine ⟨143179744447381603998187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48872019438039587498047829 143179744447381603998187)
                ·
                  rfl

theorem cell22_3764361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 10].length) (baseStart_3764361 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764361 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764361 prefixEnd_3764361 := by exact prefixLift 3764361
  have htrace : WordTrace (prefixWord ++ tailWord_3764361) baseStart_3764361 baseEnd_3764361 := by
    simpa [prefixWord, tailWord_3764361, baseEnd_3764361] using wordTrace_append hprefix tailTrace_3764361
  have hstable : (prefixWord ++ tailWord_3764361).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764361).length < 2 ^ (prefixWord ++ tailWord_3764361).sum := by decide
  have hdescent : baseEnd_3764361 < baseStart_3764361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764378 : List Nat := [3, 1, 1, 5, 2, 10]
def baseStart_3764378 : Nat := 118140960795 + 3764378 * 2 ^ 59
def prefixEnd_3764378 : Nat := 4983230072969 + 3 ^ 40 * 3764378 * 2
def baseEnd_3764378 : Nat := 15908932339183358744551

theorem tailTrace_3764378 : CollatzResearch.WordTrace tailWord_3764378 prefixEnd_3764378 15908932339183358744551 := by
  unfold tailWord_3764378
  simp only [CollatzResearch.WordTrace]
  refine ⟨34324536289077221355815447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91532096770872590282174525 34324536289077221355815447)
  ·
    refine ⟨51486804433615832033723171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34324536289077221355815447 51486804433615832033723171)
    ·
      refine ⟨77230206650423748050584757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51486804433615832033723171 77230206650423748050584757)
      ·
        refine ⟨7240331873477226379742321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77230206650423748050584757 7240331873477226379742321)
        ·
          refine ⟨5430248905107919784806741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7240331873477226379742321 5430248905107919784806741)
          ·
            refine ⟨15908932339183358744551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5430248905107919784806741 15908932339183358744551)
            ·
              rfl

theorem cell22_3764378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 10].length) (baseStart_3764378 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764378 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764378 prefixEnd_3764378 := by exact prefixLift 3764378
  have htrace : WordTrace (prefixWord ++ tailWord_3764378) baseStart_3764378 baseEnd_3764378 := by
    simpa [prefixWord, tailWord_3764378, baseEnd_3764378] using wordTrace_append hprefix tailTrace_3764378
  have hstable : (prefixWord ++ tailWord_3764378).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764378).length < 2 ^ (prefixWord ++ tailWord_3764378).sum := by decide
  have hdescent : baseEnd_3764378 < baseStart_3764378 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764414 : List Nat := [4, 2, 1, 1, 5, 1, 1, 1, 2, 4]
def baseStart_3764414 : Nat := 118140960795 + 3764414 * 2 ^ 59
def prefixEnd_3764414 : Nat := 4983230072969 + 3 ^ 40 * 3764414 * 2
def baseEnd_3764414 : Nat := 1288635843009559964408521

theorem tailTrace_3764414 : CollatzResearch.WordTrace tailWord_3764414 prefixEnd_3764414 1288635843009559964408521 := by
  unfold tailWord_3764414
  simp only [CollatzResearch.WordTrace]
  refine ⟨17162432273022307946446537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91532972122785642381048197 17162432273022307946446537)
  ·
    refine ⟨12871824204766730959834903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17162432273022307946446537 12871824204766730959834903)
    ·
      refine ⟨19307736307150096439752355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12871824204766730959834903 19307736307150096439752355)
      ·
        refine ⟨28961604460725144659628533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19307736307150096439752355 28961604460725144659628533)
        ·
          refine ⟨2715150418192982311840175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28961604460725144659628533 2715150418192982311840175)
          ·
            refine ⟨4072725627289473467760263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2715150418192982311840175 4072725627289473467760263)
            ·
              refine ⟨6109088440934210201640395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4072725627289473467760263 6109088440934210201640395)
              ·
                refine ⟨9163632661401315302460593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6109088440934210201640395 9163632661401315302460593)
                ·
                  refine ⟨6872724496050986476845445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9163632661401315302460593 6872724496050986476845445)
                  ·
                    refine ⟨1288635843009559964408521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6872724496050986476845445 1288635843009559964408521)
                    ·
                      rfl

theorem cell22_3764414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_3764414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764414 prefixEnd_3764414 := by exact prefixLift 3764414
  have htrace : WordTrace (prefixWord ++ tailWord_3764414) baseStart_3764414 baseEnd_3764414 := by
    simpa [prefixWord, tailWord_3764414, baseEnd_3764414] using wordTrace_append hprefix tailTrace_3764414
  have hstable : (prefixWord ++ tailWord_3764414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764414).length < 2 ^ (prefixWord ++ tailWord_3764414).sum := by decide
  have hdescent : baseEnd_3764414 < baseStart_3764414 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764427 : List Nat := [1, 1, 1, 1, 3, 2, 6, 3, 1, 3]
def baseStart_3764427 : Nat := 118140960795 + 3764427 * 2 ^ 59
def prefixEnd_3764427 : Nat := 4983230072969 + 3 ^ 40 * 3764427 * 2
def baseEnd_3764427 : Nat := 1288640293175232263833481

theorem tailTrace_3764427 : CollatzResearch.WordTrace tailWord_3764427 prefixEnd_3764427 1288640293175232263833481 := by
  unfold tailWord_3764427
  simp only [CollatzResearch.WordTrace]
  refine ⟨137299932333131366791795535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91533288222087577861197023 137299932333131366791795535)
  ·
    refine ⟨205949898499697050187693303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137299932333131366791795535 205949898499697050187693303)
    ·
      refine ⟨308924847749545575281539955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205949898499697050187693303 308924847749545575281539955)
      ·
        refine ⟨463387271624318362922309933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 308924847749545575281539955 463387271624318362922309933)
        ·
          refine ⟨173770226859119386095866225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 463387271624318362922309933 173770226859119386095866225)
          ·
            refine ⟨130327670144339539571899669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173770226859119386095866225 130327670144339539571899669)
            ·
              refine ⟨6109109538015915917432797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 130327670144339539571899669 6109109538015915917432797)
              ·
                refine ⟨2290916076755968469037299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6109109538015915917432797 2290916076755968469037299)
                ·
                  refine ⟨3436374115133952703555949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2290916076755968469037299 3436374115133952703555949)
                  ·
                    refine ⟨1288640293175232263833481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3436374115133952703555949 1288640293175232263833481)
                    ·
                      rfl

theorem cell22_3764427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 1, 3].length) (baseStart_3764427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764427 prefixEnd_3764427 := by exact prefixLift 3764427
  have htrace : WordTrace (prefixWord ++ tailWord_3764427) baseStart_3764427 baseEnd_3764427 := by
    simpa [prefixWord, tailWord_3764427, baseEnd_3764427] using wordTrace_append hprefix tailTrace_3764427
  have hstable : (prefixWord ++ tailWord_3764427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764427).length < 2 ^ (prefixWord ++ tailWord_3764427).sum := by decide
  have hdescent : baseEnd_3764427 < baseStart_3764427 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764440 : List Nat := [2, 1, 2, 2, 4, 1, 3, 2, 5]
def baseStart_3764440 : Nat := 118140960795 + 3764440 * 2 ^ 59
def prefixEnd_3764440 : Nat := 4983230072969 + 3 ^ 40 * 3764440 * 2
def baseEnd_3764440 : Nat := 429548247780301521086147

theorem tailTrace_3764440 : CollatzResearch.WordTrace tailWord_3764440 prefixEnd_3764440 429548247780301521086147 := by
  unfold tailWord_3764440
  simp only [CollatzResearch.WordTrace]
  refine ⟨68650203241042135006009387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91533604321389513341345849 68650203241042135006009387)
  ·
    refine ⟨102975304861563202509014081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68650203241042135006009387 102975304861563202509014081)
    ·
      refine ⟨77231478646172401881760561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102975304861563202509014081 77231478646172401881760561)
      ·
        refine ⟨57923608984629301411320421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77231478646172401881760561 57923608984629301411320421)
        ·
          refine ⟨10860676684617994014622579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57923608984629301411320421 10860676684617994014622579)
          ·
            refine ⟨16291015026926991021933869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10860676684617994014622579 16291015026926991021933869)
            ·
              refine ⟨6109130635097621633225201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16291015026926991021933869 6109130635097621633225201)
              ·
                refine ⟨4581847976323216224918901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6109130635097621633225201 4581847976323216224918901)
                ·
                  refine ⟨429548247780301521086147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4581847976323216224918901 429548247780301521086147)
                  ·
                    rfl

theorem cell22_3764440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 5].length) (baseStart_3764440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764440 prefixEnd_3764440 := by exact prefixLift 3764440
  have htrace : WordTrace (prefixWord ++ tailWord_3764440) baseStart_3764440 baseEnd_3764440 := by
    simpa [prefixWord, tailWord_3764440, baseEnd_3764440] using wordTrace_append hprefix tailTrace_3764440
  have hstable : (prefixWord ++ tailWord_3764440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764440).length < 2 ^ (prefixWord ++ tailWord_3764440).sum := by decide
  have hdescent : baseEnd_3764440 < baseStart_3764440 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764455 : List Nat := [1, 1, 5, 3, 1, 1, 2, 1, 2, 5]
def baseStart_3764455 : Nat := 118140960795 + 3764455 * 2 ^ 59
def prefixEnd_3764455 : Nat := 4983230072969 + 3 ^ 40 * 3764455 * 2
def baseEnd_3764455 : Nat := 1288649878147449524133395

theorem tailTrace_3764455 : CollatzResearch.WordTrace tailWord_3764455 prefixEnd_3764455 1288649878147449524133395 := by
  unfold tailWord_3764455
  simp only [CollatzResearch.WordTrace]
  refine ⟨137300953577029927573814819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91533969051353285049209879 137300953577029927573814819)
  ·
    refine ⟨205951430365544891360722229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137300953577029927573814819 205951430365544891360722229)
    ·
      refine ⟨19307946596769833565067709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 205951430365544891360722229 19307946596769833565067709)
      ·
        refine ⟨7240479973788687586900391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19307946596769833565067709 7240479973788687586900391)
        ·
          refine ⟨10860719960683031380350587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7240479973788687586900391 10860719960683031380350587)
          ·
            refine ⟨16291079941024547070525881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10860719960683031380350587 16291079941024547070525881)
            ·
              refine ⟨12218309955768410302894411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16291079941024547070525881 12218309955768410302894411)
              ·
                refine ⟨18327464933652615454341617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12218309955768410302894411 18327464933652615454341617)
                ·
                  refine ⟨13745598700239461590756213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18327464933652615454341617 13745598700239461590756213)
                  ·
                    refine ⟨1288649878147449524133395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13745598700239461590756213 1288649878147449524133395)
                    ·
                      rfl

theorem cell22_3764455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 1, 2, 5].length) (baseStart_3764455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764455 prefixEnd_3764455 := by exact prefixLift 3764455
  have htrace : WordTrace (prefixWord ++ tailWord_3764455) baseStart_3764455 baseEnd_3764455 := by
    simpa [prefixWord, tailWord_3764455, baseEnd_3764455] using wordTrace_append hprefix tailTrace_3764455
  have hstable : (prefixWord ++ tailWord_3764455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764455).length < 2 ^ (prefixWord ++ tailWord_3764455).sum := by decide
  have hdescent : baseEnd_3764455 < baseStart_3764455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764470 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_3764470 : Nat := 118140960795 + 3764470 * 2 ^ 59
def prefixEnd_3764470 : Nat := 4983230072969 + 3 ^ 40 * 3764470 * 2
def baseEnd_3764470 : Nat := 1288655012953994485008349

theorem tailTrace_3764470 : CollatzResearch.WordTrace tailWord_3764470 prefixEnd_3764470 1288655012953994485008349 := by
  unfold tailWord_3764470
  simp only [CollatzResearch.WordTrace]
  refine ⟨8581343791998474070975679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91534333781317056757073909 8581343791998474070975679)
  ·
    refine ⟨12872015687997711106463519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8581343791998474070975679 12872015687997711106463519)
    ·
      refine ⟨19308023531996566659695279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12872015687997711106463519 19308023531996566659695279)
      ·
        refine ⟨28962035297994849989542919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19308023531996566659695279 28962035297994849989542919)
        ·
          refine ⟨43443052946992274984314379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28962035297994849989542919 43443052946992274984314379)
          ·
            refine ⟨65164579420488412476471569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43443052946992274984314379 65164579420488412476471569)
            ·
              refine ⟨48873434565366309357353677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65164579420488412476471569 48873434565366309357353677)
              ·
                refine ⟨18327537962012366009007629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48873434565366309357353677 18327537962012366009007629)
                ·
                  refine ⟨6872826735754637253377861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18327537962012366009007629 6872826735754637253377861)
                  ·
                    refine ⟨1288655012953994485008349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6872826735754637253377861 1288655012953994485008349)
                    ·
                      rfl

theorem cell22_3764470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_3764470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764470 prefixEnd_3764470 := by exact prefixLift 3764470
  have htrace : WordTrace (prefixWord ++ tailWord_3764470) baseStart_3764470 baseEnd_3764470 := by
    simpa [prefixWord, tailWord_3764470, baseEnd_3764470] using wordTrace_append hprefix tailTrace_3764470
  have hstable : (prefixWord ++ tailWord_3764470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764470).length < 2 ^ (prefixWord ++ tailWord_3764470).sum := by decide
  have hdescent : baseEnd_3764470 < baseStart_3764470 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764483 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 3, 5]
def baseStart_3764483 : Nat := 118140960795 + 3764483 * 2 ^ 59
def prefixEnd_3764483 : Nat := 4983230072969 + 3 ^ 40 * 3764483 * 2
def baseEnd_3764483 : Nat := 1288659463119666784433309

theorem tailTrace_3764483 : CollatzResearch.WordTrace tailWord_3764483 prefixEnd_3764483 1288659463119666784433309 := by
  unfold tailWord_3764483
  simp only [CollatzResearch.WordTrace]
  refine ⟨137301974820928488355834103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91534649880618992237222735 137301974820928488355834103)
  ·
    refine ⟨205952962231392732533751155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137301974820928488355834103 205952962231392732533751155)
    ·
      refine ⟨308929443347089098800626733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205952962231392732533751155 308929443347089098800626733)
      ·
        refine ⟨115848541255158412050235025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 308929443347089098800626733 115848541255158412050235025)
        ·
          refine ⟨86886405941368809037676269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115848541255158412050235025 86886405941368809037676269)
          ·
            refine ⟨32582402228013303389128601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86886405941368809037676269 32582402228013303389128601)
            ·
              refine ⟨24436801671009977541846451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32582402228013303389128601 24436801671009977541846451)
              ·
                refine ⟨36655202506514966312769677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24436801671009977541846451 36655202506514966312769677)
                ·
                  refine ⟨13745700939943112367288629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36655202506514966312769677 13745700939943112367288629)
                  ·
                    refine ⟨1288659463119666784433309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13745700939943112367288629 1288659463119666784433309)
                    ·
                      rfl

theorem cell22_3764483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 5].length) (baseStart_3764483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764483 prefixEnd_3764483 := by exact prefixLift 3764483
  have htrace : WordTrace (prefixWord ++ tailWord_3764483) baseStart_3764483 baseEnd_3764483 := by
    simpa [prefixWord, tailWord_3764483, baseEnd_3764483] using wordTrace_append hprefix tailTrace_3764483
  have hstable : (prefixWord ++ tailWord_3764483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764483).length < 2 ^ (prefixWord ++ tailWord_3764483).sum := by decide
  have hdescent : baseEnd_3764483 < baseStart_3764483 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764485 : List Nat := [1, 3, 1, 1, 2, 1, 2, 7, 4]
def baseStart_3764485 : Nat := 118140960795 + 3764485 * 2 ^ 59
def prefixEnd_3764485 : Nat := 4983230072969 + 3 ^ 40 * 3764485 * 2
def baseEnd_3764485 : Nat := 429553382586846481961101

theorem tailTrace_3764485 : CollatzResearch.WordTrace tailWord_3764485 prefixEnd_3764485 429553382586846481961101 := by
  unfold tailWord_3764485
  simp only [CollatzResearch.WordTrace]
  refine ⟨137302047766921242697406909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91534698511280828464937939 137302047766921242697406909)
  ·
    refine ⟨51488267912595466011527591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137302047766921242697406909 51488267912595466011527591)
    ·
      refine ⟨77232401868893199017291387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51488267912595466011527591 77232401868893199017291387)
      ·
        refine ⟨115848602803339798525937081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77232401868893199017291387 115848602803339798525937081)
        ·
          refine ⟨86886452102504848894452811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115848602803339798525937081 86886452102504848894452811)
          ·
            refine ⟨130329678153757273341679217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86886452102504848894452811 130329678153757273341679217)
            ·
              refine ⟨97747258615317955006259413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130329678153757273341679217 97747258615317955006259413)
              ·
                refine ⟨2290951373796514570459205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 97747258615317955006259413 2290951373796514570459205)
                ·
                  refine ⟨429553382586846481961101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2290951373796514570459205 429553382586846481961101)
                  ·
                    rfl

theorem cell22_3764485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 7, 4].length) (baseStart_3764485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764485 prefixEnd_3764485 := by exact prefixLift 3764485
  have htrace : WordTrace (prefixWord ++ tailWord_3764485) baseStart_3764485 baseEnd_3764485 := by
    simpa [prefixWord, tailWord_3764485, baseEnd_3764485] using wordTrace_append hprefix tailTrace_3764485
  have hstable : (prefixWord ++ tailWord_3764485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764485).length < 2 ^ (prefixWord ++ tailWord_3764485).sum := by decide
  have hdescent : baseEnd_3764485 < baseStart_3764485 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764513 : List Nat := [1, 2, 3, 2, 1, 1, 3, 9]
def baseStart_3764513 : Nat := 118140960795 + 3764513 * 2 ^ 59
def prefixEnd_3764513 : Nat := 4983230072969 + 3 ^ 40 * 3764513 * 2
def baseEnd_3764513 : Nat := 143185525859195189575913

theorem tailTrace_3764513 : CollatzResearch.WordTrace tailWord_3764513 prefixEnd_3764513 143185525859195189575913 := by
  unfold tailWord_3764513
  simp only [CollatzResearch.WordTrace]
  refine ⟨137303069010819803479426193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91535379340546535652950795 137303069010819803479426193)
  ·
    refine ⟨102977301758114852609569645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137303069010819803479426193 102977301758114852609569645)
    ·
      refine ⟨38616488159293069728588617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102977301758114852609569645 38616488159293069728588617)
      ·
        refine ⟨28962366119469802296441463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38616488159293069728588617 28962366119469802296441463)
        ·
          refine ⟨43443549179204703444662195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28962366119469802296441463 43443549179204703444662195)
          ·
            refine ⟨65165323768807055166993293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43443549179204703444662195 65165323768807055166993293)
            ·
              refine ⟨24436996413302645687622485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65165323768807055166993293 24436996413302645687622485)
              ·
                refine ⟨143185525859195189575913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24436996413302645687622485 143185525859195189575913)
                ·
                  rfl

theorem cell22_3764513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 9].length) (baseStart_3764513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764513 prefixEnd_3764513 := by exact prefixLift 3764513
  have htrace : WordTrace (prefixWord ++ tailWord_3764513) baseStart_3764513 baseEnd_3764513 := by
    simpa [prefixWord, tailWord_3764513, baseEnd_3764513] using wordTrace_append hprefix tailTrace_3764513
  have hstable : (prefixWord ++ tailWord_3764513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764513).length < 2 ^ (prefixWord ++ tailWord_3764513).sum := by decide
  have hdescent : baseEnd_3764513 < baseStart_3764513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764532 : List Nat := [2, 5, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_3764532 : Nat := 118140960795 + 3764532 * 2 ^ 59
def prefixEnd_3764532 : Nat := 4983230072969 + 3 ^ 40 * 3764532 * 2
def baseEnd_3764532 : Nat := 1288676236821046989958159

theorem tailTrace_3764532 : CollatzResearch.WordTrace tailWord_3764532 prefixEnd_3764532 1288676236821046989958159 := by
  unfold tailWord_3764532
  simp only [CollatzResearch.WordTrace]
  refine ⟨68651880998875484862183925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91535841331833979816245233 68651880998875484862183925)
  ·
    refine ⟨6436113843644576705829743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68651880998875484862183925 6436113843644576705829743)
    ·
      refine ⟨9654170765466865058744615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6436113843644576705829743 9654170765466865058744615)
      ·
        refine ⟨14481256148200297588116923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9654170765466865058744615 14481256148200297588116923)
        ·
          refine ⟨21721884222300446382175385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14481256148200297588116923 21721884222300446382175385)
          ·
            refine ⟨16291413166725334786631539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21721884222300446382175385 16291413166725334786631539)
            ·
              refine ⟨24437119750088002179947309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16291413166725334786631539 24437119750088002179947309)
              ·
                refine ⟨9163919906283000817480241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24437119750088002179947309 9163919906283000817480241)
                ·
                  refine ⟨6872939929712250613110181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9163919906283000817480241 6872939929712250613110181)
                  ·
                    refine ⟨1288676236821046989958159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6872939929712250613110181 1288676236821046989958159)
                    ·
                      rfl

theorem cell22_3764532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_3764532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764532 prefixEnd_3764532 := by exact prefixLift 3764532
  have htrace : WordTrace (prefixWord ++ tailWord_3764532) baseStart_3764532 baseEnd_3764532 := by
    simpa [prefixWord, tailWord_3764532, baseEnd_3764532] using wordTrace_append hprefix tailTrace_3764532
  have hstable : (prefixWord ++ tailWord_3764532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764532).length < 2 ^ (prefixWord ++ tailWord_3764532).sum := by decide
  have hdescent : baseEnd_3764532 < baseStart_3764532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764575 : List Nat := [1, 1, 2, 3, 1, 2, 4, 3, 5]
def baseStart_3764575 : Nat := 118140960795 + 3764575 * 2 ^ 59
def prefixEnd_3764575 : Nat := 4983230072969 + 3 ^ 40 * 3764575 * 2
def baseEnd_3764575 : Nat := 429563652199936403711009

theorem tailTrace_3764575 : CollatzResearch.WordTrace tailWord_3764575 prefixEnd_3764575 429563652199936403711009 := by
  unfold tailWord_3764575
  simp only [CollatzResearch.WordTrace]
  refine ⟨137305330336595188068183179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91536886891063458712122119 137305330336595188068183179)
  ·
    refine ⟨205957995504892782102274769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137305330336595188068183179 205957995504892782102274769)
    ·
      refine ⟨154468496628669586576706077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 205957995504892782102274769 154468496628669586576706077)
      ·
        refine ⟨57925686235751094966264779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154468496628669586576706077 57925686235751094966264779)
        ·
          refine ⟨86888529353626642449397169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57925686235751094966264779 86888529353626642449397169)
          ·
            refine ⟨65166397015219981837047877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86888529353626642449397169 65166397015219981837047877)
            ·
              refine ⟨12218699440353746594446477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65166397015219981837047877 12218699440353746594446477)
              ·
                refine ⟨4582012290132654972917429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12218699440353746594446477 4582012290132654972917429)
                ·
                  refine ⟨429563652199936403711009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4582012290132654972917429 429563652199936403711009)
                  ·
                    rfl

theorem cell22_3764575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 4, 3, 5].length) (baseStart_3764575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764575 prefixEnd_3764575 := by exact prefixLift 3764575
  have htrace : WordTrace (prefixWord ++ tailWord_3764575) baseStart_3764575 baseEnd_3764575 := by
    simpa [prefixWord, tailWord_3764575, baseEnd_3764575] using wordTrace_append hprefix tailTrace_3764575
  have hstable : (prefixWord ++ tailWord_3764575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764575).length < 2 ^ (prefixWord ++ tailWord_3764575).sum := by decide
  have hdescent : baseEnd_3764575 < baseStart_3764575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764609 : List Nat := [1, 2, 4, 3, 1, 3, 1, 2, 5]
def baseStart_3764609 : Nat := 118140960795 + 3764609 * 2 ^ 59
def prefixEnd_3764609 : Nat := 4983230072969 + 3 ^ 40 * 3764609 * 2
def baseEnd_3764609 : Nat := 429567531831548151927641

theorem tailTrace_3764609 : CollatzResearch.WordTrace tailWord_3764609 prefixEnd_3764609 429567531831548151927641 := by
  unfold tailWord_3764609
  simp only [CollatzResearch.WordTrace]
  refine ⟨137306570418472011874920881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91537713612314674583280587 137306570418472011874920881)
  ·
    refine ⟨102979927813854008906190661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137306570418472011874920881 102979927813854008906190661)
    ·
      refine ⟨19308736465097626669910749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102979927813854008906190661 19308736465097626669910749)
      ·
        refine ⟨7240776174411610001216531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19308736465097626669910749 7240776174411610001216531)
        ·
          refine ⟨10861164261617415001824797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7240776174411610001216531 10861164261617415001824797)
          ·
            refine ⟨4072936598106530625684299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10861164261617415001824797 4072936598106530625684299)
            ·
              refine ⟨6109404897159795938526449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4072936598106530625684299 6109404897159795938526449)
              ·
                refine ⟨4582053672869846953894837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6109404897159795938526449 4582053672869846953894837)
                ·
                  refine ⟨429567531831548151927641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4582053672869846953894837 429567531831548151927641)
                  ·
                    rfl

theorem cell22_3764609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 3, 1, 2, 5].length) (baseStart_3764609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764609 prefixEnd_3764609 := by exact prefixLift 3764609
  have htrace : WordTrace (prefixWord ++ tailWord_3764609) baseStart_3764609 baseEnd_3764609 := by
    simpa [prefixWord, tailWord_3764609, baseEnd_3764609] using wordTrace_append hprefix tailTrace_3764609
  have hstable : (prefixWord ++ tailWord_3764609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764609).length < 2 ^ (prefixWord ++ tailWord_3764609).sum := by decide
  have hdescent : baseEnd_3764609 < baseStart_3764609 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764620 : List Nat := [2, 2, 1, 2, 1, 4, 1, 3, 6]
def baseStart_3764620 : Nat := 118140960795 + 3764620 * 2 ^ 59
def prefixEnd_3764620 : Nat := 4983230072969 + 3 ^ 40 * 3764620 * 2
def baseEnd_3764620 : Nat := 429568787006481364585963

theorem tailTrace_3764620 : CollatzResearch.WordTrace tailWord_3764620 prefixEnd_3764620 429568787006481364585963 := by
  unfold tailWord_3764620
  simp only [CollatzResearch.WordTrace]
  refine ⟨68653485810716080376785657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91537981080954773835714209 68653485810716080376785657)
  ·
    refine ⟨51490114358037060282589243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68653485810716080376785657 51490114358037060282589243)
    ·
      refine ⟨77235171537055590423883865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51490114358037060282589243 77235171537055590423883865)
      ·
        refine ⟨57926378652791692817912899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77235171537055590423883865 57926378652791692817912899)
        ·
          refine ⟨86889567979187539226869349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57926378652791692817912899 86889567979187539226869349)
          ·
            refine ⟨16291793996097663605038003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86889567979187539226869349 16291793996097663605038003)
            ·
              refine ⟨24437690994146495407557005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16291793996097663605038003 24437690994146495407557005)
              ·
                refine ⟨9164134122804935777833877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24437690994146495407557005 9164134122804935777833877)
                ·
                  refine ⟨429568787006481364585963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9164134122804935777833877 429568787006481364585963)
                  ·
                    rfl

theorem cell22_3764620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_3764620 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764620 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764620 prefixEnd_3764620 := by exact prefixLift 3764620
  have htrace : WordTrace (prefixWord ++ tailWord_3764620) baseStart_3764620 baseEnd_3764620 := by
    simpa [prefixWord, tailWord_3764620, baseEnd_3764620] using wordTrace_append hprefix tailTrace_3764620
  have hstable : (prefixWord ++ tailWord_3764620).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764620).length < 2 ^ (prefixWord ++ tailWord_3764620).sum := by decide
  have hdescent : baseEnd_3764620 < baseStart_3764620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764665 : List Nat := [1, 2, 1, 4, 3, 1, 10]
def baseStart_3764665 : Nat := 118140960795 + 3764665 * 2 ^ 59
def prefixEnd_3764665 : Nat := 4983230072969 + 3 ^ 40 * 3764665 * 2
def baseEnd_3764665 : Nat := 47730435757002925051213

theorem tailTrace_3764665 : CollatzResearch.WordTrace tailWord_3764665 prefixEnd_3764665 47730435757002925051213 := by
  unfold tailWord_3764665
  simp only [CollatzResearch.WordTrace]
  refine ⟨137308612906269133438959449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91539075270846088959306299 137308612906269133438959449)
  ·
    refine ⟨102981459679701850079219587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137308612906269133438959449 102981459679701850079219587)
    ·
      refine ⟨154472189519552775118829381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102981459679701850079219587 154472189519552775118829381)
      ·
        refine ⟨28963535534916145334780509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154472189519552775118829381 28963535534916145334780509)
        ·
          refine ⟨10861325825593554500542691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28963535534916145334780509 10861325825593554500542691)
          ·
            refine ⟨16291988738390331750814037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10861325825593554500542691 16291988738390331750814037)
            ·
              refine ⟨47730435757002925051213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16291988738390331750814037 47730435757002925051213)
              ·
                rfl

theorem cell22_3764665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 10].length) (baseStart_3764665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764665 prefixEnd_3764665 := by exact prefixLift 3764665
  have htrace : WordTrace (prefixWord ++ tailWord_3764665) baseStart_3764665 baseEnd_3764665 := by
    simpa [prefixWord, tailWord_3764665, baseEnd_3764665] using wordTrace_append hprefix tailTrace_3764665
  have hstable : (prefixWord ++ tailWord_3764665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764665).length < 2 ^ (prefixWord ++ tailWord_3764665).sum := by decide
  have hdescent : baseEnd_3764665 < baseStart_3764665 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764697 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 5, 3]
def baseStart_3764697 : Nat := 118140960795 + 3764697 * 2 ^ 59
def prefixEnd_3764697 : Nat := 4983230072969 + 3 ^ 40 * 3764697 * 2
def baseEnd_3764697 : Nat := 1288732719693041559582653

theorem tailTrace_3764697 : CollatzResearch.WordTrace tailWord_3764697 prefixEnd_3764697 1288732719693041559582653 := by
  unfold tailWord_3764697
  simp only [CollatzResearch.WordTrace]
  refine ⟨137309780042153202904124345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91539853361435468602749563 137309780042153202904124345)
  ·
    refine ⟨102982335031614902178093259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137309780042153202904124345 102982335031614902178093259)
    ·
      refine ⟨154473502547422353267139889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102982335031614902178093259 154473502547422353267139889)
      ·
        refine ⟨115855126910566764950354917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154473502547422353267139889 115855126910566764950354917)
        ·
          refine ⟨21722836295731268428191547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115855126910566764950354917 21722836295731268428191547)
          ·
            refine ⟨32584254443596902642287321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21722836295731268428191547 32584254443596902642287321)
            ·
              refine ⟨24438190832697676981715491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32584254443596902642287321 24438190832697676981715491)
              ·
                refine ⟨36657286249046515472573237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24438190832697676981715491 36657286249046515472573237)
                ·
                  refine ⟨3436620585848110825553741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36657286249046515472573237 3436620585848110825553741)
                  ·
                    refine ⟨1288732719693041559582653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3436620585848110825553741 1288732719693041559582653)
                    ·
                      rfl

theorem cell22_3764697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 3].length) (baseStart_3764697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764697 prefixEnd_3764697 := by exact prefixLift 3764697
  have htrace : WordTrace (prefixWord ++ tailWord_3764697) baseStart_3764697 baseEnd_3764697 := by
    simpa [prefixWord, tailWord_3764697, baseEnd_3764697] using wordTrace_append hprefix tailTrace_3764697
  have hstable : (prefixWord ++ tailWord_3764697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764697).length < 2 ^ (prefixWord ++ tailWord_3764697).sum := by decide
  have hdescent : baseEnd_3764697 < baseStart_3764697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764757 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 3, 4]
def baseStart_3764757 : Nat := 118140960795 + 3764757 * 2 ^ 59
def prefixEnd_3764757 : Nat := 4983230072969 + 3 ^ 40 * 3764757 * 2
def baseEnd_3764757 : Nat := 1288753258919221403082469

theorem tailTrace_3764757 : CollatzResearch.WordTrace tailWord_3764757 prefixEnd_3764757 1288753258919221403082469 := by
  unfold tailWord_3764757
  simp only [CollatzResearch.WordTrace]
  refine ⟨137311968421935833151308525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91541312281290555434205683 137311968421935833151308525)
  ·
    refine ⟨51491988158225937431740697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137311968421935833151308525 51491988158225937431740697)
    ·
      refine ⟨38618991118669453073805523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51491988158225937431740697 38618991118669453073805523)
      ·
        refine ⟨57928486678004179610708285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38618991118669453073805523 57928486678004179610708285)
        ·
          refine ⟨21723182504251567354015607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57928486678004179610708285 21723182504251567354015607)
          ·
            refine ⟨32584773756377351031023411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21723182504251567354015607 32584773756377351031023411)
            ·
              refine ⟨48877160634566026546535117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32584773756377351031023411 48877160634566026546535117)
              ·
                refine ⟨18328935237962259954950669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48877160634566026546535117 18328935237962259954950669)
                ·
                  refine ⟨6873350714235847483106501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18328935237962259954950669 6873350714235847483106501)
                  ·
                    refine ⟨1288753258919221403082469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6873350714235847483106501 1288753258919221403082469)
                    ·
                      rfl

theorem cell22_3764757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_3764757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764757 prefixEnd_3764757 := by exact prefixLift 3764757
  have htrace : WordTrace (prefixWord ++ tailWord_3764757) baseStart_3764757 baseEnd_3764757 := by
    simpa [prefixWord, tailWord_3764757, baseEnd_3764757] using wordTrace_append hprefix tailTrace_3764757
  have hstable : (prefixWord ++ tailWord_3764757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764757).length < 2 ^ (prefixWord ++ tailWord_3764757).sum := by decide
  have hdescent : baseEnd_3764757 < baseStart_3764757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764789 : List Nat := [1, 3, 3, 1, 1, 2, 1, 6, 4]
def baseStart_3764789 : Nat := 118140960795 + 3764789 * 2 ^ 59
def prefixEnd_3764789 : Nat := 4983230072969 + 3 ^ 40 * 3764789 * 2
def baseEnd_3764789 : Nat := 429588071057727995427457

theorem tailTrace_3764789 : CollatzResearch.WordTrace tailWord_3764789 prefixEnd_3764789 429588071057727995427457 := by
  unfold tailWord_3764789
  simp only [CollatzResearch.WordTrace]
  refine ⟨137313135557819902616473421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91542090371879935077648947 137313135557819902616473421)
  ·
    refine ⟨51492425834182463481177533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137313135557819902616473421 51492425834182463481177533)
    ·
      refine ⟨19309659687818423805441575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51492425834182463481177533 19309659687818423805441575)
      ·
        refine ⟨28964489531727635708162363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19309659687818423805441575 28964489531727635708162363)
        ·
          refine ⟨43446734297591453562243545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28964489531727635708162363 43446734297591453562243545)
          ·
            refine ⟨32585050723193590171682659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43446734297591453562243545 32585050723193590171682659)
            ·
              refine ⟨48877576084790385257523989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32585050723193590171682659 48877576084790385257523989)
              ·
                refine ⟨2291136378974549308946437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48877576084790385257523989 2291136378974549308946437)
                ·
                  refine ⟨429588071057727995427457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2291136378974549308946437 429588071057727995427457)
                  ·
                    rfl

theorem cell22_3764789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 6, 4].length) (baseStart_3764789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764789 prefixEnd_3764789 := by exact prefixLift 3764789
  have htrace : WordTrace (prefixWord ++ tailWord_3764789) baseStart_3764789 baseEnd_3764789 := by
    simpa [prefixWord, tailWord_3764789, baseEnd_3764789] using wordTrace_append hprefix tailTrace_3764789
  have hstable : (prefixWord ++ tailWord_3764789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764789).length < 2 ^ (prefixWord ++ tailWord_3764789).sum := by decide
  have hdescent : baseEnd_3764789 < baseStart_3764789 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764806 : List Nat := [6, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_3764806 : Nat := 118140960795 + 3764806 * 2 ^ 59
def prefixEnd_3764806 : Nat := 4983230072969 + 3 ^ 40 * 3764806 * 2
def baseEnd_3764806 : Nat := 429590010873533869535773

theorem tailTrace_3764806 : CollatzResearch.WordTrace tailWord_3764806 prefixEnd_3764806 429590010873533869535773 := by
  unfold tailWord_3764806
  simp only [CollatzResearch.WordTrace]
  refine ⟨4291054862461197328745071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 91542503732505543013228181 4291054862461197328745071)
  ·
    refine ⟨6436582293691795993117607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4291054862461197328745071 6436582293691795993117607)
    ·
      refine ⟨9654873440537693989676411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6436582293691795993117607 9654873440537693989676411)
      ·
        refine ⟨14482310160806540984514617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9654873440537693989676411 14482310160806540984514617)
        ·
          refine ⟨10861732620604905738385963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14482310160806540984514617 10861732620604905738385963)
          ·
            refine ⟨16292598930907358607578945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10861732620604905738385963 16292598930907358607578945)
            ·
              refine ⟨12219449198180518955684209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16292598930907358607578945 12219449198180518955684209)
              ·
                refine ⟨9164586898635389216763157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12219449198180518955684209 9164586898635389216763157)
                ·
                  refine ⟨429590010873533869535773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9164586898635389216763157 429590010873533869535773)
                  ·
                    rfl

theorem cell22_3764806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_3764806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764806 prefixEnd_3764806 := by exact prefixLift 3764806
  have htrace : WordTrace (prefixWord ++ tailWord_3764806) baseStart_3764806 baseEnd_3764806 := by
    simpa [prefixWord, tailWord_3764806, baseEnd_3764806] using wordTrace_append hprefix tailTrace_3764806
  have hstable : (prefixWord ++ tailWord_3764806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764806).length < 2 ^ (prefixWord ++ tailWord_3764806).sum := by decide
  have hdescent : baseEnd_3764806 < baseStart_3764806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764817 : List Nat := [1, 2, 2, 1, 3, 4, 1, 8]
def baseStart_3764817 : Nat := 118140960795 + 3764817 * 2 ^ 59
def prefixEnd_3764817 : Nat := 4983230072969 + 3 ^ 40 * 3764817 * 2
def baseEnd_3764817 : Nat := 143197088682822360731365

theorem tailTrace_3764817 : CollatzResearch.WordTrace tailWord_3764817 prefixEnd_3764817 143197088682822360731365 := by
  unfold tailWord_3764817
  simp only [CollatzResearch.WordTrace]
  refine ⟨137314156801718463398492705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91542771201145642265661803 137314156801718463398492705)
  ·
    refine ⟨102985617601288847548869529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137314156801718463398492705 102985617601288847548869529)
    ·
      refine ⟨77239213200966635661652147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102985617601288847548869529 77239213200966635661652147)
      ·
        refine ⟨115858819801449953492478221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77239213200966635661652147 115858819801449953492478221)
        ·
          refine ⟨43447057425543732559679333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115858819801449953492478221 43447057425543732559679333)
          ·
            refine ⟨8146323267289449854939875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43447057425543732559679333 8146323267289449854939875)
            ·
              refine ⟨12219484900934174782409813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8146323267289449854939875 12219484900934174782409813)
              ·
                refine ⟨143197088682822360731365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12219484900934174782409813 143197088682822360731365)
                ·
                  rfl

theorem cell22_3764817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 8].length) (baseStart_3764817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764817 prefixEnd_3764817 := by exact prefixLift 3764817
  have htrace : WordTrace (prefixWord ++ tailWord_3764817) baseStart_3764817 baseEnd_3764817 := by
    simpa [prefixWord, tailWord_3764817, baseEnd_3764817] using wordTrace_append hprefix tailTrace_3764817
  have hstable : (prefixWord ++ tailWord_3764817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764817).length < 2 ^ (prefixWord ++ tailWord_3764817).sum := by decide
  have hdescent : baseEnd_3764817 < baseStart_3764817 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764896 : List Nat := [2, 1, 1, 4, 4, 1, 2, 2, 5]
def baseStart_3764896 : Nat := 118140960795 + 3764896 * 2 ^ 59
def prefixEnd_3764896 : Nat := 4983230072969 + 3 ^ 40 * 3764896 * 2
def baseEnd_3764896 : Nat := 429600280486623791285681

theorem tailTrace_3764896 : CollatzResearch.WordTrace tailWord_3764896 prefixEnd_3764896 429600280486623791285681 := by
  unfold tailWord_3764896
  simp only [CollatzResearch.WordTrace]
  refine ⟨68658519084216129945309271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91544692112288173260412361 68658519084216129945309271)
  ·
    refine ⟨102987778626324194917963907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68658519084216129945309271 102987778626324194917963907)
    ·
      refine ⟨154481667939486292376945861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102987778626324194917963907 154481667939486292376945861)
      ·
        refine ⟨28965312738653679820677349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154481667939486292376945861 28965312738653679820677349)
        ·
          refine ⟨5430996138497564966377003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28965312738653679820677349 5430996138497564966377003)
          ·
            refine ⟨8146494207746347449565505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5430996138497564966377003 8146494207746347449565505)
            ·
              refine ⟨6109870655809760587174129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8146494207746347449565505 6109870655809760587174129)
              ·
                refine ⟨4582402991857320440380597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6109870655809760587174129 4582402991857320440380597)
                ·
                  refine ⟨429600280486623791285681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4582402991857320440380597 429600280486623791285681)
                  ·
                    rfl

theorem cell22_3764896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 5].length) (baseStart_3764896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764896 prefixEnd_3764896 := by exact prefixLift 3764896
  have htrace : WordTrace (prefixWord ++ tailWord_3764896) baseStart_3764896 baseEnd_3764896 := by
    simpa [prefixWord, tailWord_3764896, baseEnd_3764896] using wordTrace_append hprefix tailTrace_3764896
  have hstable : (prefixWord ++ tailWord_3764896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764896).length < 2 ^ (prefixWord ++ tailWord_3764896).sum := by decide
  have hdescent : baseEnd_3764896 < baseStart_3764896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764924 : List Nat := [2, 2, 2, 3, 1, 1, 3, 2, 6]
def baseStart_3764924 : Nat := 118140960795 + 3764924 * 2 ^ 59
def prefixEnd_3764924 : Nat := 4983230072969 + 3 ^ 40 * 3764924 * 2
def baseEnd_3764924 : Nat := 429603475477362878052319

theorem tailTrace_3764924 : CollatzResearch.WordTrace tailWord_3764924 prefixEnd_3764924 429603475477362878052319 := by
  unfold tailWord_3764924
  simp only [CollatzResearch.WordTrace]
  refine ⟨68659029706165410336318913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91545372941553880448425217 68659029706165410336318913)
  ·
    refine ⟨51494272279624057752239185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68659029706165410336318913 51494272279624057752239185)
    ·
      refine ⟨38620704209718043314179389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51494272279624057752239185 38620704209718043314179389)
      ·
        refine ⟨14482764078644266242817271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38620704209718043314179389 14482764078644266242817271)
        ·
          refine ⟨21724146117966399364225907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14482764078644266242817271 21724146117966399364225907)
          ·
            refine ⟨32586219176949599046338861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21724146117966399364225907 32586219176949599046338861)
            ·
              refine ⟨12219832191356099642377073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32586219176949599046338861 12219832191356099642377073)
              ·
                refine ⟨9164874143517074731782805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12219832191356099642377073 9164874143517074731782805)
                ·
                  refine ⟨429603475477362878052319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9164874143517074731782805 429603475477362878052319)
                  ·
                    rfl

theorem cell22_3764924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 6].length) (baseStart_3764924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764924 prefixEnd_3764924 := by exact prefixLift 3764924
  have htrace : WordTrace (prefixWord ++ tailWord_3764924) baseStart_3764924 baseEnd_3764924 := by
    simpa [prefixWord, tailWord_3764924, baseEnd_3764924] using wordTrace_append hprefix tailTrace_3764924
  have hstable : (prefixWord ++ tailWord_3764924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764924).length < 2 ^ (prefixWord ++ tailWord_3764924).sum := by decide
  have hdescent : baseEnd_3764924 < baseStart_3764924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764926 : List Nat := [4, 2, 1, 1, 2, 1, 2, 4, 1, 4]
def baseStart_3764926 : Nat := 118140960795 + 3764926 * 2 ^ 59
def prefixEnd_3764926 : Nat := 4983230072969 + 3 ^ 40 * 3764926 * 2
def baseEnd_3764926 : Nat := 1288811111072961295606951

theorem tailTrace_3764926 : CollatzResearch.WordTrace tailWord_3764926 prefixEnd_3764926 1288811111072961295606951 := by
  unfold tailWord_3764926
  simp only [CollatzResearch.WordTrace]
  refine ⟨17164766544790446876776329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91545421572215716676140421 17164766544790446876776329)
  ·
    refine ⟨12873574908592835157582247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17164766544790446876776329 12873574908592835157582247)
    ·
      refine ⟨19310362362889252736373371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12873574908592835157582247 19310362362889252736373371)
      ·
        refine ⟨28965543544333879104560057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19310362362889252736373371 28965543544333879104560057)
        ·
          refine ⟨21724157658250409328420043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28965543544333879104560057 21724157658250409328420043)
          ·
            refine ⟨32586236487375613992630065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21724157658250409328420043 32586236487375613992630065)
            ·
              refine ⟨24439677365531710494472549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32586236487375613992630065 24439677365531710494472549)
              ·
                refine ⟨4582439506037195717713603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24439677365531710494472549 4582439506037195717713603)
                ·
                  refine ⟨6873659259055793576570405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4582439506037195717713603 6873659259055793576570405)
                  ·
                    refine ⟨1288811111072961295606951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6873659259055793576570405 1288811111072961295606951)
                    ·
                      rfl

theorem cell22_3764926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_3764926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764926 prefixEnd_3764926 := by exact prefixLift 3764926
  have htrace : WordTrace (prefixWord ++ tailWord_3764926) baseStart_3764926 baseEnd_3764926 := by
    simpa [prefixWord, tailWord_3764926, baseEnd_3764926] using wordTrace_append hprefix tailTrace_3764926
  have hstable : (prefixWord ++ tailWord_3764926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764926).length < 2 ^ (prefixWord ++ tailWord_3764926).sum := by decide
  have hdescent : baseEnd_3764926 < baseStart_3764926 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764934 : List Nat := [6, 1, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_3764934 : Nat := 118140960795 + 3764934 * 2 ^ 59
def prefixEnd_3764934 : Nat := 4983230072969 + 3 ^ 40 * 3764934 * 2
def baseEnd_3764934 : Nat := 1288813849636451941406927

theorem tailTrace_3764934 : CollatzResearch.WordTrace tailWord_3764934 prefixEnd_3764934 1288813849636451941406927 := by
  unfold tailWord_3764934
  simp only [CollatzResearch.WordTrace]
  refine ⟨4291200754446706011890683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 91545616094863061587001237 4291200754446706011890683)
  ·
    refine ⟨6436801131670059017836025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4291200754446706011890683 6436801131670059017836025)
    ·
      refine ⟨4827600848752544263377019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6436801131670059017836025 4827600848752544263377019)
      ·
        refine ⟨7241401273128816395065529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4827600848752544263377019 7241401273128816395065529)
        ·
          refine ⟨5431050954846612296299147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7241401273128816395065529 5431050954846612296299147)
          ·
            refine ⟨8146576432269918444448721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5431050954846612296299147 8146576432269918444448721)
            ·
              refine ⟨6109932324202438833336541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8146576432269918444448721 6109932324202438833336541)
              ·
                refine ⟨2291224621575914562501203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6109932324202438833336541 2291224621575914562501203)
                ·
                  refine ⟨3436836932363871843751805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2291224621575914562501203 3436836932363871843751805)
                  ·
                    refine ⟨1288813849636451941406927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3436836932363871843751805 1288813849636451941406927)
                    ·
                      rfl

theorem cell22_3764934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_3764934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764934 prefixEnd_3764934 := by exact prefixLift 3764934
  have htrace : WordTrace (prefixWord ++ tailWord_3764934) baseStart_3764934 baseEnd_3764934 := by
    simpa [prefixWord, tailWord_3764934, baseEnd_3764934] using wordTrace_append hprefix tailTrace_3764934
  have hstable : (prefixWord ++ tailWord_3764934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764934).length < 2 ^ (prefixWord ++ tailWord_3764934).sum := by decide
  have hdescent : baseEnd_3764934 < baseStart_3764934 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3764954 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 4, 4]
def baseStart_3764954 : Nat := 118140960795 + 3764954 * 2 ^ 59
def prefixEnd_3764954 : Nat := 4983230072969 + 3 ^ 40 * 3764954 * 2
def baseEnd_3764954 : Nat := 1288820696045178555906865

theorem tailTrace_3764954 : CollatzResearch.WordTrace tailWord_3764954 prefixEnd_3764954 1288820696045178555906865 := by
  unfold tailWord_3764954
  simp only [CollatzResearch.WordTrace]
  refine ⟨34329788400555533949057479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91546102401481423864153277 34329788400555533949057479)
  ·
    refine ⟨51494682600833300923586219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34329788400555533949057479 51494682600833300923586219)
    ·
      refine ⟨77242023901249951385379329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51494682600833300923586219 77242023901249951385379329)
      ·
        refine ⟨57931517925937463539034497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77242023901249951385379329 57931517925937463539034497)
        ·
          refine ⟨43448638444453097654275873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57931517925937463539034497 43448638444453097654275873)
          ·
            refine ⟨32586478833339823240706905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43448638444453097654275873 32586478833339823240706905)
            ·
              refine ⟨24439859125004867430530179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32586478833339823240706905 24439859125004867430530179)
              ·
                refine ⟨36659788687507301145795269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24439859125004867430530179 36659788687507301145795269)
                ·
                  refine ⟨6873710378907618964836613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36659788687507301145795269 6873710378907618964836613)
                  ·
                    refine ⟨1288820696045178555906865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6873710378907618964836613 1288820696045178555906865)
                    ·
                      rfl

theorem cell22_3764954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 4, 4].length) (baseStart_3764954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3764954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3764954 prefixEnd_3764954 := by exact prefixLift 3764954
  have htrace : WordTrace (prefixWord ++ tailWord_3764954) baseStart_3764954 baseEnd_3764954 := by
    simpa [prefixWord, tailWord_3764954, baseEnd_3764954] using wordTrace_append hprefix tailTrace_3764954
  have hstable : (prefixWord ++ tailWord_3764954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3764954).length < 2 ^ (prefixWord ++ tailWord_3764954).sum := by decide
  have hdescent : baseEnd_3764954 < baseStart_3764954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3764954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765029 : List Nat := [1, 3, 1, 2, 3, 1, 2, 1, 1, 7]
def baseStart_3765029 : Nat := 118140960795 + 3765029 * 2 ^ 59
def prefixEnd_3765029 : Nat := 4983230072969 + 3 ^ 40 * 3765029 * 2
def baseEnd_3765029 : Nat := 1288846370077903360281635

theorem tailTrace_3765029 : CollatzResearch.WordTrace tailWord_3765029 prefixEnd_3765029 1288846370077903360281635 := by
  unfold tailWord_3765029
  simp only [CollatzResearch.WordTrace]
  refine ⟨137321889076950423605210141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91547926051300282403473427 137321889076950423605210141)
  ·
    refine ⟨51495708403856408851953803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137321889076950423605210141 51495708403856408851953803)
    ·
      refine ⟨77243562605784613277930705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51495708403856408851953803 77243562605784613277930705)
      ·
        refine ⟨57932671954338459958448029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77243562605784613277930705 57932671954338459958448029)
        ·
          refine ⟨21724751982876922484418011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57932671954338459958448029 21724751982876922484418011)
          ·
            refine ⟨32587127974315383726627017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21724751982876922484418011 32587127974315383726627017)
            ·
              refine ⟨24440345980736537794970263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32587127974315383726627017 24440345980736537794970263)
              ·
                refine ⟨36660518971104806692455395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24440345980736537794970263 36660518971104806692455395)
                ·
                  refine ⟨54990778456657210038683093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36660518971104806692455395 54990778456657210038683093)
                  ·
                    refine ⟨1288846370077903360281635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 54990778456657210038683093 1288846370077903360281635)
                    ·
                      rfl

theorem cell22_3765029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 7].length) (baseStart_3765029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765029 prefixEnd_3765029 := by exact prefixLift 3765029
  have htrace : WordTrace (prefixWord ++ tailWord_3765029) baseStart_3765029 baseEnd_3765029 := by
    simpa [prefixWord, tailWord_3765029, baseEnd_3765029] using wordTrace_append hprefix tailTrace_3765029
  have hstable : (prefixWord ++ tailWord_3765029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765029).length < 2 ^ (prefixWord ++ tailWord_3765029).sum := by decide
  have hdescent : baseEnd_3765029 < baseStart_3765029 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765091 : List Nat := [1, 1, 1, 5, 3, 1, 1, 3, 1, 5]
def baseStart_3765091 : Nat := 118140960795 + 3765091 * 2 ^ 59
def prefixEnd_3765091 : Nat := 4983230072969 + 3 ^ 40 * 3765091 * 2
def baseEnd_3765091 : Nat := 1288867593944955865231445

theorem tailTrace_3765091 : CollatzResearch.WordTrace tailWord_3765091 prefixEnd_3765091 1288867593944955865231445 := by
  unfold tailWord_3765091
  simp only [CollatzResearch.WordTrace]
  refine ⟨137324150402725808193967127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91549433601817205462644751 137324150402725808193967127)
  ·
    refine ⟨205986225604088712290950691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137324150402725808193967127 205986225604088712290950691)
    ·
      refine ⟨308979338406133068436426037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 205986225604088712290950691 308979338406133068436426037)
      ·
        refine ⟨28966812975574975165914941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 308979338406133068436426037 28966812975574975165914941)
        ·
          refine ⟨10862554865840615687218103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28966812975574975165914941 10862554865840615687218103)
          ·
            refine ⟨16293832298760923530827155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10862554865840615687218103 16293832298760923530827155)
            ·
              refine ⟨24440748448141385296240733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16293832298760923530827155 24440748448141385296240733)
              ·
                refine ⟨9165280668053019486090275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24440748448141385296240733 9165280668053019486090275)
                ·
                  refine ⟨13747921002079529229135413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9165280668053019486090275 13747921002079529229135413)
                  ·
                    refine ⟨1288867593944955865231445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13747921002079529229135413 1288867593944955865231445)
                    ·
                      rfl

theorem cell22_3765091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 5].length) (baseStart_3765091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765091 prefixEnd_3765091 := by exact prefixLift 3765091
  have htrace : WordTrace (prefixWord ++ tailWord_3765091) baseStart_3765091 baseEnd_3765091 := by
    simpa [prefixWord, tailWord_3765091, baseEnd_3765091] using wordTrace_append hprefix tailTrace_3765091
  have hstable : (prefixWord ++ tailWord_3765091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765091).length < 2 ^ (prefixWord ++ tailWord_3765091).sum := by decide
  have hdescent : baseEnd_3765091 < baseStart_3765091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765104 : List Nat := [2, 1, 1, 1, 4, 1, 2, 10]
def baseStart_3765104 : Nat := 118140960795 + 3765104 * 2 ^ 59
def prefixEnd_3765104 : Nat := 4983230072969 + 3 ^ 40 * 3765104 * 2
def baseEnd_3765104 : Nat := 143208004901180907184045

theorem tailTrace_3765104 : CollatzResearch.WordTrace tailWord_3765104 prefixEnd_3765104 143208004901180907184045 := by
  unfold tailWord_3765104
  simp only [CollatzResearch.WordTrace]
  refine ⟨68662312275839355707095183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91549749701119140942793577 68662312275839355707095183)
  ·
    refine ⟨102993468413759033560642775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68662312275839355707095183 102993468413759033560642775)
    ·
      refine ⟨154490202620638550340964163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102993468413759033560642775 154490202620638550340964163)
      ·
        refine ⟨231735303930957825511446245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154490202620638550340964163 231735303930957825511446245)
        ·
          refine ⟨43450369487054592283396171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231735303930957825511446245 43450369487054592283396171)
          ·
            refine ⟨65175554230581888425094257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43450369487054592283396171 65175554230581888425094257)
            ·
              refine ⟨48881665672936416318820693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65175554230581888425094257 48881665672936416318820693)
              ·
                refine ⟨143208004901180907184045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48881665672936416318820693 143208004901180907184045)
                ·
                  rfl

theorem cell22_3765104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 10].length) (baseStart_3765104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765104 prefixEnd_3765104 := by exact prefixLift 3765104
  have htrace : WordTrace (prefixWord ++ tailWord_3765104) baseStart_3765104 baseEnd_3765104 := by
    simpa [prefixWord, tailWord_3765104, baseEnd_3765104] using wordTrace_append hprefix tailTrace_3765104
  have hstable : (prefixWord ++ tailWord_3765104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765104).length < 2 ^ (prefixWord ++ tailWord_3765104).sum := by decide
  have hdescent : baseEnd_3765104 < baseStart_3765104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765110 : List Nat := [5, 1, 1, 3, 1, 1, 1, 5, 4]
def baseStart_3765110 : Nat := 118140960795 + 3765110 * 2 ^ 59
def prefixEnd_3765110 : Nat := 4983230072969 + 3 ^ 40 * 3765110 * 2
def baseEnd_3765110 : Nat := 429624699344415383002129

theorem tailTrace_3765110 : CollatzResearch.WordTrace tailWord_3765110 prefixEnd_3765110 429624699344415383002129 := by
  unfold tailWord_3765110
  simp only [CollatzResearch.WordTrace]
  refine ⟨8582802711853560902431799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91549895593104649625939189 8582802711853560902431799)
  ·
    refine ⟨12874204067780341353647699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8582802711853560902431799 12874204067780341353647699)
    ·
      refine ⟨19311306101670512030471549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12874204067780341353647699 19311306101670512030471549)
      ·
        refine ⟨7241739788126442011426831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19311306101670512030471549 7241739788126442011426831)
        ·
          refine ⟨10862609682189663017140247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7241739788126442011426831 10862609682189663017140247)
          ·
            refine ⟨16293914523284494525710371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10862609682189663017140247 16293914523284494525710371)
            ·
              refine ⟨24440871784926741788565557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16293914523284494525710371 24440871784926741788565557)
              ·
                refine ⟨2291331729836882042678021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 24440871784926741788565557 2291331729836882042678021)
                ·
                  refine ⟨429624699344415383002129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2291331729836882042678021 429624699344415383002129)
                  ·
                    rfl

theorem cell22_3765110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 5, 4].length) (baseStart_3765110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765110 prefixEnd_3765110 := by exact prefixLift 3765110
  have htrace : WordTrace (prefixWord ++ tailWord_3765110) baseStart_3765110 baseEnd_3765110 := by
    simpa [prefixWord, tailWord_3765110, baseEnd_3765110] using wordTrace_append hprefix tailTrace_3765110
  have hstable : (prefixWord ++ tailWord_3765110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765110).length < 2 ^ (prefixWord ++ tailWord_3765110).sum := by decide
  have hdescent : baseEnd_3765110 < baseStart_3765110 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765125 : List Nat := [1, 3, 1, 1, 3, 5, 1, 2, 2, 3]
def baseStart_3765125 : Nat := 118140960795 + 3765125 * 2 ^ 59
def prefixEnd_3765125 : Nat := 4983230072969 + 3 ^ 40 * 3765125 * 2
def baseEnd_3765125 : Nat := 1288879232839791109881341

theorem tailTrace_3765125 : CollatzResearch.WordTrace tailWord_3765125 prefixEnd_3765125 1288879232839791109881341 := by
  unfold tailWord_3765125
  simp only [CollatzResearch.WordTrace]
  refine ⟨137325390484602632000704829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91550260323068421333803219 137325390484602632000704829)
  ·
    refine ⟨51497021431725987000264311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137325390484602632000704829 51497021431725987000264311)
    ·
      refine ⟨77245532147588980500396467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51497021431725987000264311 77245532147588980500396467)
      ·
        refine ⟨115868298221383470750594701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77245532147588980500396467 115868298221383470750594701)
        ·
          refine ⟨43450611833018801531473013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115868298221383470750594701 43450611833018801531473013)
          ·
            refine ⟨4073494859345512643575595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43450611833018801531473013 4073494859345512643575595)
            ·
              refine ⟨6110242289018268965363393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4073494859345512643575595 6110242289018268965363393)
              ·
                refine ⟨4582681716763701724022545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6110242289018268965363393 4582681716763701724022545)
                ·
                  refine ⟨3437011287572776293016909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4582681716763701724022545 3437011287572776293016909)
                  ·
                    refine ⟨1288879232839791109881341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3437011287572776293016909 1288879232839791109881341)
                    ·
                      rfl

theorem cell22_3765125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 3].length) (baseStart_3765125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765125 prefixEnd_3765125 := by exact prefixLift 3765125
  have htrace : WordTrace (prefixWord ++ tailWord_3765125) baseStart_3765125 baseEnd_3765125 := by
    simpa [prefixWord, tailWord_3765125, baseEnd_3765125] using wordTrace_append hprefix tailTrace_3765125
  have hstable : (prefixWord ++ tailWord_3765125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765125).length < 2 ^ (prefixWord ++ tailWord_3765125).sum := by decide
  have hdescent : baseEnd_3765125 < baseStart_3765125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765142 : List Nat := [5, 3, 1, 1, 1, 1, 3, 1, 1, 5]
def baseStart_3765142 : Nat := 118140960795 + 3765142 * 2 ^ 59
def prefixEnd_3765142 : Nat := 4983230072969 + 3 ^ 40 * 3765142 * 2
def baseEnd_3765142 : Nat := 1288885052287208732206289

theorem tailTrace_3765142 : CollatzResearch.WordTrace tailWord_3765142 prefixEnd_3765142 1288885052287208732206289 := by
  unfold tailWord_3765142
  simp only [CollatzResearch.WordTrace]
  refine ⟨8582875657846315244004605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91550673683694029269382453 8582875657846315244004605)
  ·
    refine ⟨3218578371692368216501727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8582875657846315244004605 3218578371692368216501727)
    ·
      refine ⟨4827867557538552324752591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3218578371692368216501727 4827867557538552324752591)
      ·
        refine ⟨7241801336307828487128887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4827867557538552324752591 7241801336307828487128887)
        ·
          refine ⟨10862702004461742730693331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7241801336307828487128887 10862702004461742730693331)
          ·
            refine ⟨16294053006692614096039997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10862702004461742730693331 16294053006692614096039997)
            ·
              refine ⟨6110269877509730286014999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16294053006692614096039997 6110269877509730286014999)
              ·
                refine ⟨9165404816264595429022499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6110269877509730286014999 9165404816264595429022499)
                ·
                  refine ⟨13748107224396893143533749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9165404816264595429022499 13748107224396893143533749)
                  ·
                    refine ⟨1288885052287208732206289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13748107224396893143533749 1288885052287208732206289)
                    ·
                      rfl

theorem cell22_3765142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_3765142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765142 prefixEnd_3765142 := by exact prefixLift 3765142
  have htrace : WordTrace (prefixWord ++ tailWord_3765142) baseStart_3765142 baseEnd_3765142 := by
    simpa [prefixWord, tailWord_3765142, baseEnd_3765142] using wordTrace_append hprefix tailTrace_3765142
  have hstable : (prefixWord ++ tailWord_3765142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765142).length < 2 ^ (prefixWord ++ tailWord_3765142).sum := by decide
  have hdescent : baseEnd_3765142 < baseStart_3765142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765174 : List Nat := [5, 1, 4, 1, 1, 1, 1, 2, 2, 4]
def baseStart_3765174 : Nat := 118140960795 + 3765174 * 2 ^ 59
def prefixEnd_3765174 : Nat := 4983230072969 + 3 ^ 40 * 3765174 * 2
def baseEnd_3765174 : Nat := 1288896006541171315406191

theorem tailTrace_3765174 : CollatzResearch.WordTrace tailWord_3765174 prefixEnd_3765174 1288896006541171315406191 := by
  unfold tailWord_3765174
  simp only [CollatzResearch.WordTrace]
  refine ⟨8582948603839069585577411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91551451774283408912825717 8582948603839069585577411)
  ·
    refine ⟨12874422905758604378366117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8582948603839069585577411 12874422905758604378366117)
    ·
      refine ⟨2413954294829738320943647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12874422905758604378366117 2413954294829738320943647)
      ·
        refine ⟨3620931442244607481415471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2413954294829738320943647 3620931442244607481415471)
        ·
          refine ⟨5431397163366911222123207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3620931442244607481415471 5431397163366911222123207)
          ·
            refine ⟨8147095745050366833184811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5431397163366911222123207 8147095745050366833184811)
            ·
              refine ⟨12220643617575550249777217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8147095745050366833184811 12220643617575550249777217)
              ·
                refine ⟨9165482713181662687332913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12220643617575550249777217 9165482713181662687332913)
                ·
                  refine ⟨6874112034886247015499685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9165482713181662687332913 6874112034886247015499685)
                  ·
                    refine ⟨1288896006541171315406191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6874112034886247015499685 1288896006541171315406191)
                    ·
                      rfl

theorem cell22_3765174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_3765174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765174 prefixEnd_3765174 := by exact prefixLift 3765174
  have htrace : WordTrace (prefixWord ++ tailWord_3765174) baseStart_3765174 baseEnd_3765174 := by
    simpa [prefixWord, tailWord_3765174, baseEnd_3765174] using wordTrace_append hprefix tailTrace_3765174
  have hstable : (prefixWord ++ tailWord_3765174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765174).length < 2 ^ (prefixWord ++ tailWord_3765174).sum := by decide
  have hdescent : baseEnd_3765174 < baseStart_3765174 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765260 : List Nat := [2, 2, 1, 2, 3, 2, 2, 3, 2, 3]
def baseStart_3765260 : Nat := 118140960795 + 3765260 * 2 ^ 59
def prefixEnd_3765260 : Nat := 4983230072969 + 3 ^ 40 * 3765260 * 2
def baseEnd_3765260 : Nat := 1288925446098695757755927

theorem tailTrace_3765260 : CollatzResearch.WordTrace tailWord_3765260 prefixEnd_3765260 1288925446098695757755927 := by
  unfold tailWord_3765260
  simp only [CollatzResearch.WordTrace]
  refine ⟨68665157169556775028434617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91553542892742366704579489 68665157169556775028434617)
  ·
    refine ⟨51498867877167581271325963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68665157169556775028434617 51498867877167581271325963)
    ·
      refine ⟨77248301815751371906988945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51498867877167581271325963 77248301815751371906988945)
      ·
        refine ⟨57936226361813528930241709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77248301815751371906988945 57936226361813528930241709)
        ·
          refine ⟨21726084885680073348840641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57936226361813528930241709 21726084885680073348840641)
          ·
            refine ⟨16294563664260055011630481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21726084885680073348840641 16294563664260055011630481)
            ·
              refine ⟨12220922748195041258722861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16294563664260055011630481 12220922748195041258722861)
              ·
                refine ⟨4582846030573140472021073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12220922748195041258722861 4582846030573140472021073)
                ·
                  refine ⟨3437134522929855354015805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4582846030573140472021073 3437134522929855354015805)
                  ·
                    refine ⟨1288925446098695757755927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3437134522929855354015805 1288925446098695757755927)
                    ·
                      rfl

theorem cell22_3765260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 2, 3, 2, 3].length) (baseStart_3765260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765260 prefixEnd_3765260 := by exact prefixLift 3765260
  have htrace : WordTrace (prefixWord ++ tailWord_3765260) baseStart_3765260 baseEnd_3765260 := by
    simpa [prefixWord, tailWord_3765260, baseEnd_3765260] using wordTrace_append hprefix tailTrace_3765260
  have hstable : (prefixWord ++ tailWord_3765260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765260).length < 2 ^ (prefixWord ++ tailWord_3765260).sum := by decide
  have hdescent : baseEnd_3765260 < baseStart_3765260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765305 : List Nat := [1, 2, 1, 5, 2, 1, 1, 3, 3, 3]
def baseStart_3765305 : Nat := 118140960795 + 3765305 * 2 ^ 59
def prefixEnd_3765305 : Nat := 4983230072969 + 3 ^ 40 * 3765305 * 2
def baseEnd_3765305 : Nat := 1288940850518330640380789

theorem tailTrace_3765305 : CollatzResearch.WordTrace tailWord_3765305 prefixEnd_3765305 1288940850518330640380789 := by
  unfold tailWord_3765305
  simp only [CollatzResearch.WordTrace]
  refine ⟨137331955623950522742257369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91554637082633681828171579 137331955623950522742257369)
  ·
    refine ⟨102998966717962892056693027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137331955623950522742257369 102998966717962892056693027)
    ·
      refine ⟨154498450076944338085039541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102998966717962892056693027 154498450076944338085039541)
      ·
        refine ⟨14484229694713531695472457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154498450076944338085039541 14484229694713531695472457)
        ·
          refine ⟨10863172271035148771604343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14484229694713531695472457 10863172271035148771604343)
          ·
            refine ⟨16294758406552723157406515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10863172271035148771604343 16294758406552723157406515)
            ·
              refine ⟨24442137609829084736109773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16294758406552723157406515 24442137609829084736109773)
              ·
                refine ⟨9165801603685906776041165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24442137609829084736109773 9165801603685906776041165)
                ·
                  refine ⟨3437175601382215041015437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9165801603685906776041165 3437175601382215041015437)
                  ·
                    refine ⟨1288940850518330640380789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3437175601382215041015437 1288940850518330640380789)
                    ·
                      rfl

theorem cell22_3765305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 3].length) (baseStart_3765305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765305 prefixEnd_3765305 := by exact prefixLift 3765305
  have htrace : WordTrace (prefixWord ++ tailWord_3765305) baseStart_3765305 baseEnd_3765305 := by
    simpa [prefixWord, tailWord_3765305, baseEnd_3765305] using wordTrace_append hprefix tailTrace_3765305
  have hstable : (prefixWord ++ tailWord_3765305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765305).length < 2 ^ (prefixWord ++ tailWord_3765305).sum := by decide
  have hdescent : baseEnd_3765305 < baseStart_3765305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765348 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 5, 4]
def baseStart_3765348 : Nat := 118140960795 + 3765348 * 2 ^ 59
def prefixEnd_3765348 : Nat := 4983230072969 + 3 ^ 40 * 3765348 * 2
def baseEnd_3765348 : Nat := 1288955570297092861555657

theorem tailTrace_3765348 : CollatzResearch.WordTrace tailWord_3765348 prefixEnd_3765348 1288955570297092861555657 := by
  unfold tailWord_3765348
  simp only [CollatzResearch.WordTrace]
  refine ⟨68666761981397370543036349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91555682641863160724048465 68666761981397370543036349)
  ·
    refine ⟨25750035743024013953638631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68666761981397370543036349 25750035743024013953638631)
    ·
      refine ⟨38625053614536020930457947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25750035743024013953638631 38625053614536020930457947)
      ·
        refine ⟨57937580421804031395686921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38625053614536020930457947 57937580421804031395686921)
        ·
          refine ⟨43453185316353023546765191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57937580421804031395686921 43453185316353023546765191)
          ·
            refine ⟨65179777974529535320147787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43453185316353023546765191 65179777974529535320147787)
            ·
              refine ⟨97769666961794302980221681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65179777974529535320147787 97769666961794302980221681)
              ·
                refine ⟨73327250221345727235166261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97769666961794302980221681 73327250221345727235166261)
                ·
                  refine ⟨6874429708251161928296837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73327250221345727235166261 6874429708251161928296837)
                  ·
                    refine ⟨1288955570297092861555657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6874429708251161928296837 1288955570297092861555657)
                    ·
                      rfl

theorem cell22_3765348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_3765348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765348 prefixEnd_3765348 := by exact prefixLift 3765348
  have htrace : WordTrace (prefixWord ++ tailWord_3765348) baseStart_3765348 baseEnd_3765348 := by
    simpa [prefixWord, tailWord_3765348, baseEnd_3765348] using wordTrace_append hprefix tailTrace_3765348
  have hstable : (prefixWord ++ tailWord_3765348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765348).length < 2 ^ (prefixWord ++ tailWord_3765348).sum := by decide
  have hdescent : baseEnd_3765348 < baseStart_3765348 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765369 : List Nat := [1, 2, 1, 3, 6, 1, 2, 1, 5]
def baseStart_3765369 : Nat := 118140960795 + 3765369 * 2 ^ 59
def prefixEnd_3765369 : Nat := 4983230072969 + 3 ^ 40 * 3765369 * 2
def baseEnd_3765369 : Nat := 429654253008751935593531

theorem tailTrace_3765369 : CollatzResearch.WordTrace tailWord_3765369 prefixEnd_3765369 429654253008751935593531 := by
  unfold tailWord_3765369
  simp only [CollatzResearch.WordTrace]
  refine ⟨137334289895718661672587161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91556193263812441115058107 137334289895718661672587161)
  ·
    refine ⟨103000717421788996254440371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137334289895718661672587161 103000717421788996254440371)
    ·
      refine ⟨154501076132683494381660557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103000717421788996254440371 154501076132683494381660557)
      ·
        refine ⟨57937903549756310393122709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154501076132683494381660557 57937903549756310393122709)
        ·
          refine ⟨2715839228894827049677627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57937903549756310393122709 2715839228894827049677627)
          ·
            refine ⟨4073758843342240574516441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2715839228894827049677627 4073758843342240574516441)
            ·
              refine ⟨3055319132506680430887331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4073758843342240574516441 3055319132506680430887331)
              ·
                refine ⟨4582978698760020646330997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3055319132506680430887331 4582978698760020646330997)
                ·
                  refine ⟨429654253008751935593531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4582978698760020646330997 429654253008751935593531)
                  ·
                    rfl

theorem cell22_3765369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 5].length) (baseStart_3765369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765369 prefixEnd_3765369 := by exact prefixLift 3765369
  have htrace : WordTrace (prefixWord ++ tailWord_3765369) baseStart_3765369 baseEnd_3765369 := by
    simpa [prefixWord, tailWord_3765369, baseEnd_3765369] using wordTrace_append hprefix tailTrace_3765369
  have hstable : (prefixWord ++ tailWord_3765369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765369).length < 2 ^ (prefixWord ++ tailWord_3765369).sum := by decide
  have hdescent : baseEnd_3765369 < baseStart_3765369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765412 : List Nat := [2, 3, 1, 2, 3, 1, 1, 4, 2, 3]
def baseStart_3765412 : Nat := 118140960795 + 3765412 * 2 ^ 59
def prefixEnd_3765412 : Nat := 4983230072969 + 3 ^ 40 * 3765412 * 2
def baseEnd_3765412 : Nat := 1288977478805018027955461

theorem tailTrace_3765412 : CollatzResearch.WordTrace tailWord_3765412 prefixEnd_3765412 1288977478805018027955461 := by
  unfold tailWord_3765412
  simp only [CollatzResearch.WordTrace]
  refine ⟨68667929117281440008201245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91557238823041920010934993 68667929117281440008201245)
  ·
    refine ⟨25750473418980540003075467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68667929117281440008201245 25750473418980540003075467)
    ·
      refine ⟨38625710128470810004613201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25750473418980540003075467 38625710128470810004613201)
      ·
        refine ⟨28969282596353107503459901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38625710128470810004613201 28969282596353107503459901)
        ·
          refine ⟨10863480973632415313797463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28969282596353107503459901 10863480973632415313797463)
          ·
            refine ⟨16295221460448622970696195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10863480973632415313797463 16295221460448622970696195)
            ·
              refine ⟨24442832190672934456044293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16295221460448622970696195 24442832190672934456044293)
              ·
                refine ⟨4583031035751175210508305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24442832190672934456044293 4583031035751175210508305)
                ·
                  refine ⟨3437273276813381407881229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4583031035751175210508305 3437273276813381407881229)
                  ·
                    refine ⟨1288977478805018027955461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3437273276813381407881229 1288977478805018027955461)
                    ·
                      rfl

theorem cell22_3765412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 2, 3].length) (baseStart_3765412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765412 prefixEnd_3765412 := by exact prefixLift 3765412
  have htrace : WordTrace (prefixWord ++ tailWord_3765412) baseStart_3765412 baseEnd_3765412 := by
    simpa [prefixWord, tailWord_3765412, baseEnd_3765412] using wordTrace_append hprefix tailTrace_3765412
  have hstable : (prefixWord ++ tailWord_3765412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765412).length < 2 ^ (prefixWord ++ tailWord_3765412).sum := by decide
  have hdescent : baseEnd_3765412 < baseStart_3765412 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765425 : List Nat := [1, 2, 2, 5, 1, 1, 3, 7]
def baseStart_3765425 : Nat := 118140960795 + 3765425 * 2 ^ 59
def prefixEnd_3765425 : Nat := 4983230072969 + 3 ^ 40 * 3765425 * 2
def baseEnd_3765425 : Nat := 143220214330076703042269

theorem tailTrace_3765425 : CollatzResearch.WordTrace tailWord_3765425 prefixEnd_3765425 143220214330076703042269 := by
  unfold tailWord_3765425
  simp only [CollatzResearch.WordTrace]
  refine ⟨137336332383515783236625729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91557554922343855491083819 137336332383515783236625729)
  ·
    refine ⟨103002249287636837427469297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137336332383515783236625729 103002249287636837427469297)
    ·
      refine ⟨77251686965727628070601973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103002249287636837427469297 77251686965727628070601973)
      ·
        refine ⟨7242345653036965131618935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77251686965727628070601973 7242345653036965131618935)
        ·
          refine ⟨10863518479555447697428403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7242345653036965131618935 10863518479555447697428403)
          ·
            refine ⟨16295277719333171546142605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10863518479555447697428403 16295277719333171546142605)
            ·
              refine ⟨6110729144749939329803477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16295277719333171546142605 6110729144749939329803477)
              ·
                refine ⟨143220214330076703042269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6110729144749939329803477 143220214330076703042269)
                ·
                  rfl

theorem cell22_3765425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 7].length) (baseStart_3765425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765425 prefixEnd_3765425 := by exact prefixLift 3765425
  have htrace : WordTrace (prefixWord ++ tailWord_3765425) baseStart_3765425 baseEnd_3765425 := by
    simpa [prefixWord, tailWord_3765425, baseEnd_3765425] using wordTrace_append hprefix tailTrace_3765425
  have hstable : (prefixWord ++ tailWord_3765425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765425).length < 2 ^ (prefixWord ++ tailWord_3765425).sum := by decide
  have hdescent : baseEnd_3765425 < baseStart_3765425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765444 : List Nat := [2, 3, 3, 1, 3, 2, 1, 1, 2, 4]
def baseStart_3765444 : Nat := 118140960795 + 3765444 * 2 ^ 59
def prefixEnd_3765444 : Nat := 4983230072969 + 3 ^ 40 * 3765444 * 2
def baseEnd_3765444 : Nat := 1288988433058980611155363

theorem tailTrace_3765444 : CollatzResearch.WordTrace tailWord_3765444 prefixEnd_3765444 1288988433058980611155363 := by
  unfold tailWord_3765444
  simp only [CollatzResearch.WordTrace]
  refine ⟨68668512685223474740783693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91558016913631299654378257 68668512685223474740783693)
  ·
    refine ⟨25750692256958803027793885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68668512685223474740783693 25750692256958803027793885)
    ·
      refine ⟨9656509596359551135422707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25750692256958803027793885 9656509596359551135422707)
      ·
        refine ⟨14484764394539326703134061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9656509596359551135422707 14484764394539326703134061)
        ·
          refine ⟨5431786647952247513675273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14484764394539326703134061 5431786647952247513675273)
          ·
            refine ⟨4073839985964185635256455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5431786647952247513675273 4073839985964185635256455)
            ·
              refine ⟨6110759978946278452884683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4073839985964185635256455 6110759978946278452884683)
              ·
                refine ⟨9166139968419417679327025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6110759978946278452884683 9166139968419417679327025)
                ·
                  refine ⟨6874604976314563259495269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9166139968419417679327025 6874604976314563259495269)
                  ·
                    refine ⟨1288988433058980611155363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6874604976314563259495269 1288988433058980611155363)
                    ·
                      rfl

theorem cell22_3765444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_3765444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765444 prefixEnd_3765444 := by exact prefixLift 3765444
  have htrace : WordTrace (prefixWord ++ tailWord_3765444) baseStart_3765444 baseEnd_3765444 := by
    simpa [prefixWord, tailWord_3765444, baseEnd_3765444] using wordTrace_append hprefix tailTrace_3765444
  have hstable : (prefixWord ++ tailWord_3765444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765444).length < 2 ^ (prefixWord ++ tailWord_3765444).sum := by decide
  have hdescent : baseEnd_3765444 < baseStart_3765444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765532 : List Nat := [2, 2, 3, 1, 1, 1, 2, 6, 4]
def baseStart_3765532 : Nat := 118140960795 + 3765532 * 2 ^ 59
def prefixEnd_3765532 : Nat := 4983230072969 + 3 ^ 40 * 3765532 * 2
def baseEnd_3765532 : Nat := 429672852419125904985031

theorem tailTrace_3765532 : CollatzResearch.WordTrace tailWord_3765532 prefixEnd_3765532 429672852419125904985031 := by
  unfold tailWord_3765532
  simp only [CollatzResearch.WordTrace]
  refine ⟨68670117497064070255385425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91560156662752093673847233 68670117497064070255385425)
  ·
    refine ⟨51502588122798052691539069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68670117497064070255385425 51502588122798052691539069)
    ·
      refine ⟨19313470546049269759327151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51502588122798052691539069 19313470546049269759327151)
      ·
        refine ⟨28970205819073904638990727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19313470546049269759327151 28970205819073904638990727)
        ·
          refine ⟨43455308728610856958486091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28970205819073904638990727 43455308728610856958486091)
          ·
            refine ⟨65182963092916285437729137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43455308728610856958486091 65182963092916285437729137)
            ·
              refine ⟨48887222319687214078296853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65182963092916285437729137 48887222319687214078296853)
              ·
                refine ⟨2291588546235338159920165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48887222319687214078296853 2291588546235338159920165)
                ·
                  refine ⟨429672852419125904985031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2291588546235338159920165 429672852419125904985031)
                  ·
                    rfl

theorem cell22_3765532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 4].length) (baseStart_3765532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765532 prefixEnd_3765532 := by exact prefixLift 3765532
  have htrace : WordTrace (prefixWord ++ tailWord_3765532) baseStart_3765532 baseEnd_3765532 := by
    simpa [prefixWord, tailWord_3765532, baseEnd_3765532] using wordTrace_append hprefix tailTrace_3765532
  have hstable : (prefixWord ++ tailWord_3765532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765532).length < 2 ^ (prefixWord ++ tailWord_3765532).sum := by decide
  have hdescent : baseEnd_3765532 < baseStart_3765532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765562 : List Nat := [3, 1, 1, 1, 4, 1, 4, 1, 2, 4]
def baseStart_3765562 : Nat := 118140960795 + 3765562 * 2 ^ 59
def prefixEnd_3765562 : Nat := 4983230072969 + 3 ^ 40 * 3765562 * 2
def baseEnd_3765562 : Nat := 1289028826870467636705001

theorem tailTrace_3765562 : CollatzResearch.WordTrace tailWord_3765562 prefixEnd_3765562 1289028826870467636705001 := by
  unfold tailWord_3765562
  simp only [CollatzResearch.WordTrace]
  refine ⟨34335332296004863908590735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91560886122679637089575293 34335332296004863908590735)
  ·
    refine ⟨51502998444007295862886103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34335332296004863908590735 51502998444007295862886103)
    ·
      refine ⟨77254497666010943794329155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51502998444007295862886103 77254497666010943794329155)
      ·
        refine ⟨115881746499016415691493733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77254497666010943794329155 115881746499016415691493733)
        ·
          refine ⟨21727827468565577942155075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115881746499016415691493733 21727827468565577942155075)
          ·
            refine ⟨32591741202848366913232613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21727827468565577942155075 32591741202848366913232613)
            ·
              refine ⟨6110951475534068796231115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32591741202848366913232613 6110951475534068796231115)
              ·
                refine ⟨9166427213301103194346673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6110951475534068796231115 9166427213301103194346673)
                ·
                  refine ⟨6874820409975827395760005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9166427213301103194346673 6874820409975827395760005)
                  ·
                    refine ⟨1289028826870467636705001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6874820409975827395760005 1289028826870467636705001)
                    ·
                      rfl

theorem cell22_3765562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 2, 4].length) (baseStart_3765562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765562 prefixEnd_3765562 := by exact prefixLift 3765562
  have htrace : WordTrace (prefixWord ++ tailWord_3765562) baseStart_3765562 baseEnd_3765562 := by
    simpa [prefixWord, tailWord_3765562, baseEnd_3765562] using wordTrace_append hprefix tailTrace_3765562
  have hstable : (prefixWord ++ tailWord_3765562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765562).length < 2 ^ (prefixWord ++ tailWord_3765562).sum := by decide
  have hdescent : baseEnd_3765562 < baseStart_3765562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765592 : List Nat := [2, 1, 2, 2, 1, 1, 4, 3, 3, 3]
def baseStart_3765592 : Nat := 118140960795 + 3765592 * 2 ^ 59
def prefixEnd_3765592 : Nat := 4983230072969 + 3 ^ 40 * 3765592 * 2
def baseEnd_3765592 : Nat := 1289039096483557558454909

theorem tailTrace_3765592 : CollatzResearch.WordTrace tailWord_3765592 prefixEnd_3765592 1289039096483557558454909 := by
  unfold tailWord_3765592
  simp only [CollatzResearch.WordTrace]
  refine ⟨68671211686955385378977515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91561615582607180505303353 68671211686955385378977515)
  ·
    refine ⟨103006817530433078068466273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68671211686955385378977515 103006817530433078068466273)
    ·
      refine ⟨77255113147824808551349705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103006817530433078068466273 77255113147824808551349705)
      ·
        refine ⟨57941334860868606413512279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77255113147824808551349705 57941334860868606413512279)
        ·
          refine ⟨86912002291302909620268419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57941334860868606413512279 86912002291302909620268419)
          ·
            refine ⟨130368003436954364430402629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86912002291302909620268419 130368003436954364430402629)
            ·
              refine ⟨24444000644428943330700493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 130368003436954364430402629 24444000644428943330700493)
              ·
                refine ⟨9166500241660853749012685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24444000644428943330700493 9166500241660853749012685)
                ·
                  refine ⟨3437437590622820155879757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9166500241660853749012685 3437437590622820155879757)
                  ·
                    refine ⟨1289039096483557558454909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3437437590622820155879757 1289039096483557558454909)
                    ·
                      rfl

theorem cell22_3765592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 3, 3].length) (baseStart_3765592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765592 prefixEnd_3765592 := by exact prefixLift 3765592
  have htrace : WordTrace (prefixWord ++ tailWord_3765592) baseStart_3765592 baseEnd_3765592 := by
    simpa [prefixWord, tailWord_3765592, baseEnd_3765592] using wordTrace_append hprefix tailTrace_3765592
  have hstable : (prefixWord ++ tailWord_3765592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765592).length < 2 ^ (prefixWord ++ tailWord_3765592).sum := by decide
  have hdescent : baseEnd_3765592 < baseStart_3765592 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765639 : List Nat := [1, 1, 4, 2, 2, 4, 1, 2, 5]
def baseStart_3765639 : Nat := 118140960795 + 3765639 * 2 ^ 59
def prefixEnd_3765639 : Nat := 4983230072969 + 3 ^ 40 * 3765639 * 2
def baseEnd_3765639 : Nat := 429685061848021700843255

theorem tailTrace_3765639 : CollatzResearch.WordTrace tailWord_3765639 prefixEnd_3765639 429685061848021700843255 := by
  unfold tailWord_3765639
  simp only [CollatzResearch.WordTrace]
  refine ⟨137344137604740497784915971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91562758403160331856610647 137344137604740497784915971)
  ·
    refine ⟨206016206407110746677373957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137344137604740497784915971 206016206407110746677373957)
    ·
      refine ⟨38628038701333265002007617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206016206407110746677373957 38628038701333265002007617)
      ·
        refine ⟨28971029025999948751505713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38628038701333265002007617 28971029025999948751505713)
        ·
          refine ⟨21728271769499961563629285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28971029025999948751505713 21728271769499961563629285)
          ·
            refine ⟨4074050956781242793180491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21728271769499961563629285 4074050956781242793180491)
            ·
              refine ⟨6111076435171864189770737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4074050956781242793180491 6111076435171864189770737)
              ·
                refine ⟨4583307326378898142328053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6111076435171864189770737 4583307326378898142328053)
                ·
                  refine ⟨429685061848021700843255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4583307326378898142328053 429685061848021700843255)
                  ·
                    rfl

theorem cell22_3765639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 5].length) (baseStart_3765639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765639 prefixEnd_3765639 := by exact prefixLift 3765639
  have htrace : WordTrace (prefixWord ++ tailWord_3765639) baseStart_3765639 baseEnd_3765639 := by
    simpa [prefixWord, tailWord_3765639, baseEnd_3765639] using wordTrace_append hprefix tailTrace_3765639
  have hstable : (prefixWord ++ tailWord_3765639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765639).length < 2 ^ (prefixWord ++ tailWord_3765639).sum := by decide
  have hdescent : baseEnd_3765639 < baseStart_3765639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765656 : List Nat := [2, 1, 2, 5, 2, 1, 3, 1, 5]
def baseStart_3765656 : Nat := 118140960795 + 3765656 * 2 ^ 59
def prefixEnd_3765656 : Nat := 4983230072969 + 3 ^ 40 * 3765656 * 2
def baseEnd_3765656 : Nat := 429687001663827574951571

theorem tailTrace_3765656 : CollatzResearch.WordTrace tailWord_3765656 prefixEnd_3765656 429687001663827574951571 := by
  unfold tailWord_3765656
  simp only [CollatzResearch.WordTrace]
  refine ⟨68672378822839454844142411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91563171763785939792189881 68672378822839454844142411)
  ·
    refine ⟨103008568234259182266213617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68672378822839454844142411 103008568234259182266213617)
    ·
      refine ⟨77256426175694386699660213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103008568234259182266213617 77256426175694386699660213)
      ·
        refine ⟨7242789953971348753093145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77256426175694386699660213 7242789953971348753093145)
        ·
          refine ⟨5432092465478511564819859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7242789953971348753093145 5432092465478511564819859)
          ·
            refine ⟨8148138698217767347229789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5432092465478511564819859 8148138698217767347229789)
            ·
              refine ⟨3055552011831662755211171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8148138698217767347229789 3055552011831662755211171)
              ·
                refine ⟨4583328017747494132816757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3055552011831662755211171 4583328017747494132816757)
                ·
                  refine ⟨429687001663827574951571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4583328017747494132816757 429687001663827574951571)
                  ·
                    rfl

theorem cell22_3765656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 5].length) (baseStart_3765656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765656 prefixEnd_3765656 := by exact prefixLift 3765656
  have htrace : WordTrace (prefixWord ++ tailWord_3765656) baseStart_3765656 baseEnd_3765656 := by
    simpa [prefixWord, tailWord_3765656, baseEnd_3765656] using wordTrace_append hprefix tailTrace_3765656
  have hstable : (prefixWord ++ tailWord_3765656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765656).length < 2 ^ (prefixWord ++ tailWord_3765656).sum := by decide
  have hdescent : baseEnd_3765656 < baseStart_3765656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765846 : List Nat := [5, 2, 2, 2, 2, 1, 1, 3, 1, 3]
def baseStart_3765846 : Nat := 118140960795 + 3765846 * 2 ^ 59
def prefixEnd_3765846 : Nat := 4983230072969 + 3 ^ 40 * 3765846 * 2
def baseEnd_3765846 : Nat := 1289126045874385562604131

theorem tailTrace_3765846 : CollatzResearch.WordTrace tailWord_3765846 prefixEnd_3765846 1289126045874385562604131 := by
  unfold tailWord_3765846
  simp only [CollatzResearch.WordTrace]
  refine ⟨8584480469686910758606337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91567791676660381425134261 8584480469686910758606337)
  ·
    refine ⟨6438360352265183068954753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8584480469686910758606337 6438360352265183068954753)
    ·
      refine ⟨4828770264198887301716065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6438360352265183068954753 4828770264198887301716065)
      ·
        refine ⟨3621577698149165476287049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4828770264198887301716065 3621577698149165476287049)
        ·
          refine ⟨2716183273611874107215287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3621577698149165476287049 2716183273611874107215287)
          ·
            refine ⟨4074274910417811160822931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2716183273611874107215287 4074274910417811160822931)
            ·
              refine ⟨6111412365626716741234397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4074274910417811160822931 6111412365626716741234397)
              ·
                refine ⟨2291779637110018777962899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6111412365626716741234397 2291779637110018777962899)
                ·
                  refine ⟨3437669455665028166944349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2291779637110018777962899 3437669455665028166944349)
                  ·
                    refine ⟨1289126045874385562604131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3437669455665028166944349 1289126045874385562604131)
                    ·
                      rfl

theorem cell22_3765846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_3765846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765846 prefixEnd_3765846 := by exact prefixLift 3765846
  have htrace : WordTrace (prefixWord ++ tailWord_3765846) baseStart_3765846 baseEnd_3765846 := by
    simpa [prefixWord, tailWord_3765846, baseEnd_3765846] using wordTrace_append hprefix tailTrace_3765846
  have hstable : (prefixWord ++ tailWord_3765846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765846).length < 2 ^ (prefixWord ++ tailWord_3765846).sum := by decide
  have hdescent : baseEnd_3765846 < baseStart_3765846 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765864 : List Nat := [2, 1, 4, 3, 1, 1, 10]
def baseStart_3765864 : Nat := 118140960795 + 3765864 * 2 ^ 59
def prefixEnd_3765864 : Nat := 4983230072969 + 3 ^ 40 * 3765864 * 2
def baseEnd_3765864 : Nat := 47745637320082945024225

theorem tailTrace_3765864 : CollatzResearch.WordTrace tailWord_3765864 prefixEnd_3765864 47745637320082945024225 := by
  unfold tailWord_3765864
  simp only [CollatzResearch.WordTrace]
  refine ⟨68676172014462680605928323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91568229352616907474571097 68676172014462680605928323)
  ·
    refine ⟨103014258021694020908892485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68676172014462680605928323 103014258021694020908892485)
    ·
      refine ⟨19315173379067628920417341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103014258021694020908892485 19315173379067628920417341)
      ·
        refine ⟨7243190017150360845156503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19315173379067628920417341 7243190017150360845156503)
        ·
          refine ⟨10864785025725541267734755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7243190017150360845156503 10864785025725541267734755)
          ·
            refine ⟨16297177538588311901602133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10864785025725541267734755 16297177538588311901602133)
            ·
              refine ⟨47745637320082945024225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16297177538588311901602133 47745637320082945024225)
              ·
                rfl

theorem cell22_3765864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 10].length) (baseStart_3765864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765864 prefixEnd_3765864 := by exact prefixLift 3765864
  have htrace : WordTrace (prefixWord ++ tailWord_3765864) baseStart_3765864 baseEnd_3765864 := by
    simpa [prefixWord, tailWord_3765864, baseEnd_3765864] using wordTrace_append hprefix tailTrace_3765864
  have hstable : (prefixWord ++ tailWord_3765864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765864).length < 2 ^ (prefixWord ++ tailWord_3765864).sum := by decide
  have hdescent : baseEnd_3765864 < baseStart_3765864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765866 : List Nat := [3, 1, 3, 2, 1, 3, 1, 2, 2, 4]
def baseStart_3765866 : Nat := 118140960795 + 3765866 * 2 ^ 59
def prefixEnd_3765866 : Nat := 4983230072969 + 3 ^ 40 * 3765866 * 2
def baseEnd_3765866 : Nat := 1289132892283112177104069

theorem tailTrace_3765866 : CollatzResearch.WordTrace tailWord_3765866 prefixEnd_3765866 1289132892283112177104069 := by
  unfold tailWord_3765866
  simp only [CollatzResearch.WordTrace]
  refine ⟨34338104243729528888357363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91568277983278743702286301 34338104243729528888357363)
  ·
    refine ⟨51507156365594293332536045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34338104243729528888357363 51507156365594293332536045)
    ·
      refine ⟨19315183637097859999701017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51507156365594293332536045 19315183637097859999701017)
      ·
        refine ⟨14486387727823394999775763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19315183637097859999701017 14486387727823394999775763)
        ·
          refine ⟨21729581591735092499663645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14486387727823394999775763 21729581591735092499663645)
          ·
            refine ⟨8148593096900659687373867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21729581591735092499663645 8148593096900659687373867)
            ·
              refine ⟨12222889645350989531060801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8148593096900659687373867 12222889645350989531060801)
              ·
                refine ⟨9167167234013242148295601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12222889645350989531060801 9167167234013242148295601)
                ·
                  refine ⟨6875375425509931611221701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9167167234013242148295601 6875375425509931611221701)
                  ·
                    refine ⟨1289132892283112177104069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6875375425509931611221701 1289132892283112177104069)
                    ·
                      rfl

theorem cell22_3765866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_3765866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765866 prefixEnd_3765866 := by exact prefixLift 3765866
  have htrace : WordTrace (prefixWord ++ tailWord_3765866) baseStart_3765866 baseEnd_3765866 := by
    simpa [prefixWord, tailWord_3765866, baseEnd_3765866] using wordTrace_append hprefix tailTrace_3765866
  have hstable : (prefixWord ++ tailWord_3765866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765866).length < 2 ^ (prefixWord ++ tailWord_3765866).sum := by decide
  have hdescent : baseEnd_3765866 < baseStart_3765866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765870 : List Nat := [4, 1, 2, 2, 3, 1, 3, 2, 4]
def baseStart_3765870 : Nat := 118140960795 + 3765870 * 2 ^ 59
def prefixEnd_3765870 : Nat := 4983230072969 + 3 ^ 40 * 3765870 * 2
def baseEnd_3765870 : Nat := 429711420521619166668019

theorem tailTrace_3765870 : CollatzResearch.WordTrace tailWord_3765870 prefixEnd_3765870 429711420521619166668019 := by
  unfold tailWord_3765870
  simp only [CollatzResearch.WordTrace]
  refine ⟨17169070358362953029571883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91568375244602416157716709 17169070358362953029571883)
  ·
    refine ⟨25753605537544429544357825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17169070358362953029571883 25753605537544429544357825)
    ·
      refine ⟨19315204153158322158268369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25753605537544429544357825 19315204153158322158268369)
      ·
        refine ⟨14486403114868741618701277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19315204153158322158268369 14486403114868741618701277)
        ·
          refine ⟨5432401168075778107012979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14486403114868741618701277 5432401168075778107012979)
          ·
            refine ⟨8148601752113667160519469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5432401168075778107012979 8148601752113667160519469)
            ·
              refine ⟨3055725657042625185194801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8148601752113667160519469 3055725657042625185194801)
              ·
                refine ⟨2291794242781968888896101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3055725657042625185194801 2291794242781968888896101)
                ·
                  refine ⟨429711420521619166668019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2291794242781968888896101 429711420521619166668019)
                  ·
                    rfl

theorem cell22_3765870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 4].length) (baseStart_3765870 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765870 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765870 prefixEnd_3765870 := by exact prefixLift 3765870
  have htrace : WordTrace (prefixWord ++ tailWord_3765870) baseStart_3765870 baseEnd_3765870 := by
    simpa [prefixWord, tailWord_3765870, baseEnd_3765870] using wordTrace_append hprefix tailTrace_3765870
  have hstable : (prefixWord ++ tailWord_3765870).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765870).length < 2 ^ (prefixWord ++ tailWord_3765870).sum := by decide
  have hdescent : baseEnd_3765870 < baseStart_3765870 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765885 : List Nat := [1, 4, 1, 1, 4, 3, 2, 1, 2, 3]
def baseStart_3765885 : Nat := 118140960795 + 3765885 * 2 ^ 59
def prefixEnd_3765885 : Nat := 4983230072969 + 3 ^ 40 * 3765885 * 2
def baseEnd_3765885 : Nat := 1289139396371402460879011

theorem tailTrace_3765885 : CollatzResearch.WordTrace tailWord_3765885 prefixEnd_3765885 1289139396371402460879011 := by
  unfold tailWord_3765885
  simp only [CollatzResearch.WordTrace]
  refine ⟨137353109961849281798371109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91568739974566187865580739 137353109961849281798371109)
  ·
    refine ⟨25753708117846740337194583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137353109961849281798371109 25753708117846740337194583)
    ·
      refine ⟨38630562176770110505791875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25753708117846740337194583 38630562176770110505791875)
      ·
        refine ⟨57945843265155165758687813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38630562176770110505791875 57945843265155165758687813)
        ·
          refine ⟨10864845612216593579753965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57945843265155165758687813 10864845612216593579753965)
          ·
            refine ⟨4074317104581222592407737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10864845612216593579753965 4074317104581222592407737)
            ·
              refine ⟨3055737828435916944305803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4074317104581222592407737 3055737828435916944305803)
              ·
                refine ⟨4583606742653875416458705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3055737828435916944305803 4583606742653875416458705)
                ·
                  refine ⟨3437705056990406562344029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4583606742653875416458705 3437705056990406562344029)
                  ·
                    refine ⟨1289139396371402460879011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3437705056990406562344029 1289139396371402460879011)
                    ·
                      rfl

theorem cell22_3765885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_3765885 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765885 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765885 prefixEnd_3765885 := by exact prefixLift 3765885
  have htrace : WordTrace (prefixWord ++ tailWord_3765885) baseStart_3765885 baseEnd_3765885 := by
    simpa [prefixWord, tailWord_3765885, baseEnd_3765885] using wordTrace_append hprefix tailTrace_3765885
  have hstable : (prefixWord ++ tailWord_3765885).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765885).length < 2 ^ (prefixWord ++ tailWord_3765885).sum := by decide
  have hdescent : baseEnd_3765885 < baseStart_3765885 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765939 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 5, 4]
def baseStart_3765939 : Nat := 118140960795 + 3765939 * 2 ^ 59
def prefixEnd_3765939 : Nat := 4983230072969 + 3 ^ 40 * 3765939 * 2
def baseEnd_3765939 : Nat := 1289157881674964320028845

theorem tailTrace_3765939 : CollatzResearch.WordTrace tailWord_3765939 prefixEnd_3765939 1289157881674964320028845 := by
  unfold tailWord_3765939
  simp only [CollatzResearch.WordTrace]
  refine ⟨137355079503653649020836871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91570053002435766013891247 137355079503653649020836871)
  ·
    refine ⟨206032619255480473531255307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137355079503653649020836871 206032619255480473531255307)
    ·
      refine ⟨309048928883220710296882961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206032619255480473531255307 309048928883220710296882961)
      ·
        refine ⟨231786696662415532722662221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309048928883220710296882961 231786696662415532722662221)
        ·
          refine ⟨86920011248405824770998333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231786696662415532722662221 86920011248405824770998333)
          ·
            refine ⟨32595004218152184289124375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86920011248405824770998333 32595004218152184289124375)
            ·
              refine ⟨48892506327228276433686563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32595004218152184289124375 48892506327228276433686563)
              ·
                refine ⟨73338759490842414650529845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48892506327228276433686563 73338759490842414650529845)
                ·
                  refine ⟨6875508702266476373487173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73338759490842414650529845 6875508702266476373487173)
                  ·
                    refine ⟨1289157881674964320028845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6875508702266476373487173 1289157881674964320028845)
                    ·
                      rfl

theorem cell22_3765939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 4].length) (baseStart_3765939 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765939 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765939 prefixEnd_3765939 := by exact prefixLift 3765939
  have htrace : WordTrace (prefixWord ++ tailWord_3765939) baseStart_3765939 baseEnd_3765939 := by
    simpa [prefixWord, tailWord_3765939, baseEnd_3765939] using wordTrace_append hprefix tailTrace_3765939
  have hstable : (prefixWord ++ tailWord_3765939).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765939).length < 2 ^ (prefixWord ++ tailWord_3765939).sum := by decide
  have hdescent : baseEnd_3765939 < baseStart_3765939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765956 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 3, 4]
def baseStart_3765956 : Nat := 118140960795 + 3765956 * 2 ^ 59
def prefixEnd_3765956 : Nat := 4983230072969 + 3 ^ 40 * 3765956 * 2
def baseEnd_3765956 : Nat := 1289163701122381942353793

theorem tailTrace_3765956 : CollatzResearch.WordTrace tailWord_3765956 prefixEnd_3765956 1289163701122381942353793 := by
  unfold tailWord_3765956
  simp only [CollatzResearch.WordTrace]
  refine ⟨68677849772296030462102861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91570466363061373949470481 68677849772296030462102861)
  ·
    refine ⟨25754193664611011423288573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68677849772296030462102861 25754193664611011423288573)
    ·
      refine ⟨9657822624229129283733215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25754193664611011423288573 9657822624229129283733215)
      ·
        refine ⟨14486733936343693925599823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9657822624229129283733215 14486733936343693925599823)
        ·
          refine ⟨21730100904515540888399735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14486733936343693925599823 21730100904515540888399735)
          ·
            refine ⟨32595151356773311332599603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21730100904515540888399735 32595151356773311332599603)
            ·
              refine ⟨48892727035159966998899405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32595151356773311332599603 48892727035159966998899405)
              ·
                refine ⟨18334772638184987624587277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48892727035159966998899405 18334772638184987624587277)
                ·
                  refine ⟨6875539739319370359220229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18334772638184987624587277 6875539739319370359220229)
                  ·
                    refine ⟨1289163701122381942353793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6875539739319370359220229 1289163701122381942353793)
                    ·
                      rfl

theorem cell22_3765956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_3765956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765956 prefixEnd_3765956 := by exact prefixLift 3765956
  have htrace : WordTrace (prefixWord ++ tailWord_3765956) baseStart_3765956 baseEnd_3765956 := by
    simpa [prefixWord, tailWord_3765956, baseEnd_3765956] using wordTrace_append hprefix tailTrace_3765956
  have hstable : (prefixWord ++ tailWord_3765956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765956).length < 2 ^ (prefixWord ++ tailWord_3765956).sum := by decide
  have hdescent : baseEnd_3765956 < baseStart_3765956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3765999 : List Nat := [1, 1, 2, 1, 5, 1, 2, 9]
def baseStart_3765999 : Nat := 118140960795 + 3765999 * 2 ^ 59
def prefixEnd_3765999 : Nat := 4983230072969 + 3 ^ 40 * 3765999 * 2
def baseEnd_3765999 : Nat := 143242046766793795947629

theorem tailTrace_3765999 : CollatzResearch.WordTrace tailWord_3765999 prefixEnd_3765999 143242046766793795947629 := by
  unfold tailWord_3765999
  simp only [CollatzResearch.WordTrace]
  refine ⟨137357267883436279268021051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91571511922290852845347367 137357267883436279268021051)
  ·
    refine ⟨206035901825154418902031577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137357267883436279268021051 206035901825154418902031577)
    ·
      refine ⟨154526926368865814176523683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206035901825154418902031577 154526926368865814176523683)
      ·
        refine ⟨231790389553298721264785525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154526926368865814176523683 231790389553298721264785525)
        ·
          refine ⟨21730349020621755118573643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 231790389553298721264785525 21730349020621755118573643)
          ·
            refine ⟨32595523530932632677860465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21730349020621755118573643 32595523530932632677860465)
            ·
              refine ⟨24446642648199474508395349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32595523530932632677860465 24446642648199474508395349)
              ·
                refine ⟨143242046766793795947629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24446642648199474508395349 143242046766793795947629)
                ·
                  rfl

theorem cell22_3765999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 9].length) (baseStart_3765999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3765999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3765999 prefixEnd_3765999 := by exact prefixLift 3765999
  have htrace : WordTrace (prefixWord ++ tailWord_3765999) baseStart_3765999 baseEnd_3765999 := by
    simpa [prefixWord, tailWord_3765999, baseEnd_3765999] using wordTrace_append hprefix tailTrace_3765999
  have hstable : (prefixWord ++ tailWord_3765999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3765999).length < 2 ^ (prefixWord ++ tailWord_3765999).sum := by decide
  have hdescent : baseEnd_3765999 < baseStart_3765999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3765999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766018 : List Nat := [3, 4, 1, 1, 1, 1, 2, 3, 2, 4]
def baseStart_3766018 : Nat := 118140960795 + 3766018 * 2 ^ 59
def prefixEnd_3766018 : Nat := 4983230072969 + 3 ^ 40 * 3766018 * 2
def baseEnd_3766018 : Nat := 1289184924989434447303603

theorem tailTrace_3766018 : CollatzResearch.WordTrace tailWord_3766018 prefixEnd_3766018 1289184924989434447303603 := by
  unfold tailWord_3766018
  simp only [CollatzResearch.WordTrace]
  refine ⟨34339490217591861378240677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91571973913578297008641805 34339490217591861378240677)
  ·
    refine ⟨6438654415798474008420127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34339490217591861378240677 6438654415798474008420127)
    ·
      refine ⟨9657981623697711012630191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6438654415798474008420127 9657981623697711012630191)
      ·
        refine ⟨14486972435546566518945287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9657981623697711012630191 14486972435546566518945287)
        ·
          refine ⟨21730458653319849778417931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14486972435546566518945287 21730458653319849778417931)
          ·
            refine ⟨32595687979979774667626897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21730458653319849778417931 32595687979979774667626897)
            ·
              refine ⟨24446765984984831000720173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32595687979979774667626897 24446765984984831000720173)
              ·
                refine ⟨9167537244369311625270065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24446765984984831000720173 9167537244369311625270065)
                ·
                  refine ⟨6875652933276983718952549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9167537244369311625270065 6875652933276983718952549)
                  ·
                    refine ⟨1289184924989434447303603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6875652933276983718952549 1289184924989434447303603)
                    ·
                      rfl

theorem cell22_3766018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_3766018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766018 prefixEnd_3766018 := by exact prefixLift 3766018
  have htrace : WordTrace (prefixWord ++ tailWord_3766018) baseStart_3766018 baseEnd_3766018 := by
    simpa [prefixWord, tailWord_3766018, baseEnd_3766018] using wordTrace_append hprefix tailTrace_3766018
  have hstable : (prefixWord ++ tailWord_3766018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766018).length < 2 ^ (prefixWord ++ tailWord_3766018).sum := by decide
  have hdescent : baseEnd_3766018 < baseStart_3766018 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766106 : List Nat := [3, 1, 1, 2, 1, 3, 2, 3, 6]
def baseStart_3766106 : Nat := 118140960795 + 3766106 * 2 ^ 59
def prefixEnd_3766106 : Nat := 4983230072969 + 3 ^ 40 * 3766106 * 2
def baseEnd_3766106 : Nat := 429738349729277183701111

theorem tailTrace_3766106 : CollatzResearch.WordTrace tailWord_3766106 prefixEnd_3766106 429738349729277183701111 := by
  unfold tailWord_3766106
  simp only [CollatzResearch.WordTrace]
  refine ⟨34340292623512159135541543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91574113662699091028110781 34340292623512159135541543)
  ·
    refine ⟨51510438935268238703312315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34340292623512159135541543 51510438935268238703312315)
    ·
      refine ⟨77265658402902358054968473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51510438935268238703312315 77265658402902358054968473)
      ·
        refine ⟨57949243802176768541226355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77265658402902358054968473 57949243802176768541226355)
        ·
          refine ⟨86923865703265152811839533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57949243802176768541226355 86923865703265152811839533)
          ·
            refine ⟨32596449638724432304439825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86923865703265152811839533 32596449638724432304439825)
            ·
              refine ⟨24447337229043324228329869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32596449638724432304439825 24447337229043324228329869)
              ·
                refine ⟨9167751460891246585623701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24447337229043324228329869 9167751460891246585623701)
                ·
                  refine ⟨429738349729277183701111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9167751460891246585623701 429738349729277183701111)
                  ·
                    rfl

theorem cell22_3766106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 6].length) (baseStart_3766106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766106 prefixEnd_3766106 := by exact prefixLift 3766106
  have htrace : WordTrace (prefixWord ++ tailWord_3766106) baseStart_3766106 baseEnd_3766106 := by
    simpa [prefixWord, tailWord_3766106, baseEnd_3766106] using wordTrace_append hprefix tailTrace_3766106
  have hstable : (prefixWord ++ tailWord_3766106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766106).length < 2 ^ (prefixWord ++ tailWord_3766106).sum := by decide
  have hdescent : baseEnd_3766106 < baseStart_3766106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766142 : List Nat := [4, 2, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_3766142 : Nat := 118140960795 + 3766142 * 2 ^ 59
def prefixEnd_3766142 : Nat := 4983230072969 + 3 ^ 40 * 3766142 * 2
def baseEnd_3766142 : Nat := 1289227372723539457203223

theorem tailTrace_3766142 : CollatzResearch.WordTrace tailWord_3766142 prefixEnd_3766142 1289227372723539457203223 := by
  unfold tailWord_3766142
  simp only [CollatzResearch.WordTrace]
  refine ⟨17170310440239776836309585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91574989014612143126984453 17170310440239776836309585)
  ·
    refine ⟨12877732830179832627232189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17170310440239776836309585 12877732830179832627232189)
    ·
      refine ⟨4829149811317437235212071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12877732830179832627232189 4829149811317437235212071)
      ·
        refine ⟨7243724716976155852818107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4829149811317437235212071 7243724716976155852818107)
        ·
          refine ⟨10865587075464233779227161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7243724716976155852818107 10865587075464233779227161)
          ·
            refine ⟨8149190306598175334420371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10865587075464233779227161 8149190306598175334420371)
            ·
              refine ⟨12223785459897263001630557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8149190306598175334420371 12223785459897263001630557)
              ·
                refine ⟨4583919547461473625611459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12223785459897263001630557 4583919547461473625611459)
                ·
                  refine ⟨6875879321192210438417189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4583919547461473625611459 6875879321192210438417189)
                  ·
                    refine ⟨1289227372723539457203223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6875879321192210438417189 1289227372723539457203223)
                    ·
                      rfl

theorem cell22_3766142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_3766142 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766142 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766142 prefixEnd_3766142 := by exact prefixLift 3766142
  have htrace : WordTrace (prefixWord ++ tailWord_3766142) baseStart_3766142 baseEnd_3766142 := by
    simpa [prefixWord, tailWord_3766142, baseEnd_3766142] using wordTrace_append hprefix tailTrace_3766142
  have hstable : (prefixWord ++ tailWord_3766142).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766142).length < 2 ^ (prefixWord ++ tailWord_3766142).sum := by decide
  have hdescent : baseEnd_3766142 < baseStart_3766142 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766181 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 2, 6]
def baseStart_3766181 : Nat := 118140960795 + 3766181 * 2 ^ 59
def prefixEnd_3766181 : Nat := 4983230072969 + 3 ^ 40 * 3766181 * 2
def baseEnd_3766181 : Nat := 1289240723220556355478103

theorem tailTrace_3766181 : CollatzResearch.WordTrace tailWord_3766181 prefixEnd_3766181 1289240723220556355478103 := by
  unfold tailWord_3766181
  simp only [CollatzResearch.WordTrace]
  refine ⟨137363905968776924351146397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91575937312517949567430931 137363905968776924351146397)
  ·
    refine ⟨51511464738291346631679899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137363905968776924351146397 51511464738291346631679899)
    ·
      refine ⟨77267197107437019947519849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51511464738291346631679899 77267197107437019947519849)
      ·
        refine ⟨57950397830577764960639887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77267197107437019947519849 57950397830577764960639887)
        ·
          refine ⟨86925596745866647440959831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57950397830577764960639887 86925596745866647440959831)
          ·
            refine ⟨130388395118799971161439747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86925596745866647440959831 130388395118799971161439747)
            ·
              refine ⟨195582592678199956742159621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130388395118799971161439747 195582592678199956742159621)
              ·
                refine ⟨36671736127162491889154929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195582592678199956742159621 36671736127162491889154929)
                ·
                  refine ⟨27503802095371868916866197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36671736127162491889154929 27503802095371868916866197)
                  ·
                    refine ⟨1289240723220556355478103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27503802095371868916866197 1289240723220556355478103)
                    ·
                      rfl

theorem cell22_3766181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 6].length) (baseStart_3766181 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766181 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766181 prefixEnd_3766181 := by exact prefixLift 3766181
  have htrace : WordTrace (prefixWord ++ tailWord_3766181) baseStart_3766181 baseEnd_3766181 := by
    simpa [prefixWord, tailWord_3766181, baseEnd_3766181] using wordTrace_append hprefix tailTrace_3766181
  have hstable : (prefixWord ++ tailWord_3766181).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766181).length < 2 ^ (prefixWord ++ tailWord_3766181).sum := by decide
  have hdescent : baseEnd_3766181 < baseStart_3766181 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766228 : List Nat := [2, 4, 1, 2, 1, 1, 2, 1, 1, 7]
def baseStart_3766228 : Nat := 118140960795 + 3766228 * 2 ^ 59
def prefixEnd_3766228 : Nat := 4983230072969 + 3 ^ 40 * 3766228 * 2
def baseEnd_3766228 : Nat := 1289256812281063899552959

theorem tailTrace_3766228 : CollatzResearch.WordTrace tailWord_3766228 prefixEnd_3766228 1289256812281063899552959 := by
  unfold tailWord_3766228
  simp only [CollatzResearch.WordTrace]
  refine ⟨68682810099803325689053669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91577080133071100918738225 68682810099803325689053669)
  ·
    refine ⟨12878026893713123566697563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68682810099803325689053669 12878026893713123566697563)
    ·
      refine ⟨19317040340569685350046345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12878026893713123566697563 19317040340569685350046345)
      ·
        refine ⟨14487780255427264012534759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19317040340569685350046345 14487780255427264012534759)
        ·
          refine ⟨21731670383140896018802139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14487780255427264012534759 21731670383140896018802139)
          ·
            refine ⟨32597505574711344028203209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21731670383140896018802139 32597505574711344028203209)
            ·
              refine ⟨24448129181033508021152407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32597505574711344028203209 24448129181033508021152407)
              ·
                refine ⟨36672193771550262031728611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24448129181033508021152407 36672193771550262031728611)
                ·
                  refine ⟨55008290657325393047592917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 36672193771550262031728611 55008290657325393047592917)
                  ·
                    refine ⟨1289256812281063899552959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55008290657325393047592917 1289256812281063899552959)
                    ·
                      rfl

theorem cell22_3766228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 1, 7].length) (baseStart_3766228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766228 prefixEnd_3766228 := by exact prefixLift 3766228
  have htrace : WordTrace (prefixWord ++ tailWord_3766228) baseStart_3766228 baseEnd_3766228 := by
    simpa [prefixWord, tailWord_3766228, baseEnd_3766228] using wordTrace_append hprefix tailTrace_3766228
  have hstable : (prefixWord ++ tailWord_3766228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766228).length < 2 ^ (prefixWord ++ tailWord_3766228).sum := by decide
  have hdescent : baseEnd_3766228 < baseStart_3766228 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766273 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 3, 5]
def baseStart_3766273 : Nat := 118140960795 + 3766273 * 2 ^ 59
def prefixEnd_3766273 : Nat := 4983230072969 + 3 ^ 40 * 3766273 * 2
def baseEnd_3766273 : Nat := 1289272216700698782177821

theorem tailTrace_3766273 : CollatzResearch.WordTrace tailWord_3766273 prefixEnd_3766273 1289272216700698782177821 := by
  unfold tailWord_3766273
  simp only [CollatzResearch.WordTrace]
  refine ⟨137367261484443624063495473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91578174322962416042330315 137367261484443624063495473)
  ·
    refine ⟨103025446113332718047621605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137367261484443624063495473 103025446113332718047621605)
    ·
      refine ⟨19317271146249884633929051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103025446113332718047621605 19317271146249884633929051)
      ·
        refine ⟨28975906719374826950893577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19317271146249884633929051 28975906719374826950893577)
        ·
          refine ⟨21731930039531120213170183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28975906719374826950893577 21731930039531120213170183)
          ·
            refine ⟨32597895059296680319755275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21731930039531120213170183 32597895059296680319755275)
            ·
              refine ⟨48896842588945020479632913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32597895059296680319755275 48896842588945020479632913)
              ·
                refine ⟨36672631941708765359724685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48896842588945020479632913 36672631941708765359724685)
                ·
                  refine ⟨13752236978140787009896757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36672631941708765359724685 13752236978140787009896757)
                  ·
                    refine ⟨1289272216700698782177821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13752236978140787009896757 1289272216700698782177821)
                    ·
                      rfl

theorem cell22_3766273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 5].length) (baseStart_3766273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766273 prefixEnd_3766273 := by exact prefixLift 3766273
  have htrace : WordTrace (prefixWord ++ tailWord_3766273) baseStart_3766273 baseEnd_3766273 := by
    simpa [prefixWord, tailWord_3766273, baseEnd_3766273] using wordTrace_append hprefix tailTrace_3766273
  have hstable : (prefixWord ++ tailWord_3766273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766273).length < 2 ^ (prefixWord ++ tailWord_3766273).sum := by decide
  have hdescent : baseEnd_3766273 < baseStart_3766273 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766305 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 1, 6]
def baseStart_3766305 : Nat := 118140960795 + 3766305 * 2 ^ 59
def prefixEnd_3766305 : Nat := 4983230072969 + 3 ^ 40 * 3766305 * 2
def baseEnd_3766305 : Nat := 1289283170954661365377723

theorem tailTrace_3766305 : CollatzResearch.WordTrace tailWord_3766305 prefixEnd_3766305 1289283170954661365377723 := by
  unfold tailWord_3766305
  simp only [CollatzResearch.WordTrace]
  refine ⟨137368428620327693528660369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91578952413551795685773579 137368428620327693528660369)
  ·
    refine ⟨103026321465245770146495277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137368428620327693528660369 103026321465245770146495277)
    ·
      refine ⟨38634870549467163804935729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103026321465245770146495277 38634870549467163804935729)
      ·
        refine ⟨28976152912100372853701797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38634870549467163804935729 28976152912100372853701797)
        ·
          refine ⟨5433028671018819910069087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28976152912100372853701797 5433028671018819910069087)
          ·
            refine ⟨8149543006528229865103631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5433028671018819910069087 8149543006528229865103631)
            ·
              refine ⟨12224314509792344797655447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8149543006528229865103631 12224314509792344797655447)
              ·
                refine ⟨18336471764688517196483171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12224314509792344797655447 18336471764688517196483171)
                ·
                  refine ⟨27504707647032775794724757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18336471764688517196483171 27504707647032775794724757)
                  ·
                    refine ⟨1289283170954661365377723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27504707647032775794724757 1289283170954661365377723)
                    ·
                      rfl

theorem cell22_3766305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_3766305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766305 prefixEnd_3766305 := by exact prefixLift 3766305
  have htrace : WordTrace (prefixWord ++ tailWord_3766305) baseStart_3766305 baseEnd_3766305 := by
    simpa [prefixWord, tailWord_3766305, baseEnd_3766305] using wordTrace_append hprefix tailTrace_3766305
  have hstable : (prefixWord ++ tailWord_3766305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766305).length < 2 ^ (prefixWord ++ tailWord_3766305).sum := by decide
  have hdescent : baseEnd_3766305 < baseStart_3766305 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766311 : List Nat := [1, 1, 7, 1, 2, 2, 2, 1, 1, 4]
def baseStart_3766311 : Nat := 118140960795 + 3766311 * 2 ^ 59
def prefixEnd_3766311 : Nat := 4983230072969 + 3 ^ 40 * 3766311 * 2
def baseEnd_3766311 : Nat := 1289285224877279349727705

theorem tailTrace_3766311 : CollatzResearch.WordTrace tailWord_3766311 prefixEnd_3766311 1289285224877279349727705 := by
  unfold tailWord_3766311
  simp only [CollatzResearch.WordTrace]
  refine ⟨137368647458305956553378787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91579098305537304368919191 137368647458305956553378787)
  ·
    refine ⟨206052971187458934830068181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137368647458305956553378787 206052971187458934830068181)
    ·
      refine ⟨4829366512206068785079723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 206052971187458934830068181 4829366512206068785079723)
      ·
        refine ⟨7244049768309103177619585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4829366512206068785079723 7244049768309103177619585)
        ·
          refine ⟨5433037326231827383214689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7244049768309103177619585 5433037326231827383214689)
          ·
            refine ⟨4074777994673870537411017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5433037326231827383214689 4074777994673870537411017)
            ·
              refine ⟨3056083496005402903058263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4074777994673870537411017 3056083496005402903058263)
              ·
                refine ⟨4584125244008104354587395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3056083496005402903058263 4584125244008104354587395)
                ·
                  refine ⟨6876187866012156531881093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4584125244008104354587395 6876187866012156531881093)
                  ·
                    refine ⟨1289285224877279349727705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6876187866012156531881093 1289285224877279349727705)
                    ·
                      rfl

theorem cell22_3766311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_3766311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766311 prefixEnd_3766311 := by exact prefixLift 3766311
  have htrace : WordTrace (prefixWord ++ tailWord_3766311) baseStart_3766311 baseEnd_3766311 := by
    simpa [prefixWord, tailWord_3766311, baseEnd_3766311] using wordTrace_append hprefix tailTrace_3766311
  have hstable : (prefixWord ++ tailWord_3766311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766311).length < 2 ^ (prefixWord ++ tailWord_3766311).sum := by decide
  have hdescent : baseEnd_3766311 < baseStart_3766311 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766324 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 4, 3]
def baseStart_3766324 : Nat := 118140960795 + 3766324 * 2 ^ 59
def prefixEnd_3766324 : Nat := 4983230072969 + 3 ^ 40 * 3766324 * 2
def baseEnd_3766324 : Nat := 1289289675042951649152665

theorem tailTrace_3766324 : CollatzResearch.WordTrace tailWord_3766324 prefixEnd_3766324 1289289675042951649152665 := by
  unfold tailWord_3766324
  simp only [CollatzResearch.WordTrace]
  refine ⟨68684560803629429886801013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91579414404839239849068017 68684560803629429886801013)
  ·
    refine ⟨6439177575340259051887595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68684560803629429886801013 6439177575340259051887595)
    ·
      refine ⟨9658766363010388577831393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6439177575340259051887595 9658766363010388577831393)
      ·
        refine ⟨7244074772257791433373545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9658766363010388577831393 7244074772257791433373545)
        ·
          refine ⟨5433056079193343575030159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7244074772257791433373545 5433056079193343575030159)
          ·
            refine ⟨8149584118790015362545239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5433056079193343575030159 8149584118790015362545239)
            ·
              refine ⟨12224376178185023043817859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8149584118790015362545239 12224376178185023043817859)
              ·
                refine ⟨18336564267277534565726789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12224376178185023043817859 18336564267277534565726789)
                ·
                  refine ⟨3438105800114537731073773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18336564267277534565726789 3438105800114537731073773)
                  ·
                    refine ⟨1289289675042951649152665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3438105800114537731073773 1289289675042951649152665)
                    ·
                      rfl

theorem cell22_3766324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_3766324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766324 prefixEnd_3766324 := by exact prefixLift 3766324
  have htrace : WordTrace (prefixWord ++ tailWord_3766324) baseStart_3766324 baseEnd_3766324 := by
    simpa [prefixWord, tailWord_3766324, baseEnd_3766324] using wordTrace_append hprefix tailTrace_3766324
  have hstable : (prefixWord ++ tailWord_3766324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766324).length < 2 ^ (prefixWord ++ tailWord_3766324).sum := by decide
  have hdescent : baseEnd_3766324 < baseStart_3766324 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766335 : List Nat := [1, 1, 2, 2, 3, 1, 3, 3, 3, 3]
def baseStart_3766335 : Nat := 118140960795 + 3766335 * 2 ^ 59
def prefixEnd_3766335 : Nat := 4983230072969 + 3 ^ 40 * 3766335 * 2
def baseEnd_3766335 : Nat := 1289293440567751287127631

theorem tailTrace_3766335 : CollatzResearch.WordTrace tailWord_3766335 prefixEnd_3766335 1289293440567751287127631 := by
  unfold tailWord_3766335
  simp only [CollatzResearch.WordTrace]
  refine ⟨137369522810219008652252459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91579681873479339101501639 137369522810219008652252459)
  ·
    refine ⟨206054284215328512978378689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137369522810219008652252459 206054284215328512978378689)
    ·
      refine ⟨154540713161496384733784017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206054284215328512978378689 154540713161496384733784017)
      ·
        refine ⟨115905534871122288550338013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154540713161496384733784017 115905534871122288550338013)
        ·
          refine ⟨43464575576670858206376755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115905534871122288550338013 43464575576670858206376755)
          ·
            refine ⟨65196863365006287309565133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43464575576670858206376755 65196863365006287309565133)
            ·
              refine ⟨24448823761877357741086925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65196863365006287309565133 24448823761877357741086925)
              ·
                refine ⟨9168308910704009152907597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24448823761877357741086925 9168308910704009152907597)
                ·
                  refine ⟨3438115841514003432340349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9168308910704009152907597 3438115841514003432340349)
                  ·
                    refine ⟨1289293440567751287127631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3438115841514003432340349 1289293440567751287127631)
                    ·
                      rfl

theorem cell22_3766335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 3, 3, 3].length) (baseStart_3766335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766335 prefixEnd_3766335 := by exact prefixLift 3766335
  have htrace : WordTrace (prefixWord ++ tailWord_3766335) baseStart_3766335 baseEnd_3766335 := by
    simpa [prefixWord, tailWord_3766335, baseEnd_3766335] using wordTrace_append hprefix tailTrace_3766335
  have hstable : (prefixWord ++ tailWord_3766335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766335).length < 2 ^ (prefixWord ++ tailWord_3766335).sum := by decide
  have hdescent : baseEnd_3766335 < baseStart_3766335 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766354 : List Nat := [3, 2, 2, 1, 5, 1, 2, 6]
def baseStart_3766354 : Nat := 118140960795 + 3766354 * 2 ^ 59
def prefixEnd_3766354 : Nat := 4983230072969 + 3 ^ 40 * 3766354 * 2
def baseEnd_3766354 : Nat := 143255549406226841211397

theorem tailTrace_3766354 : CollatzResearch.WordTrace tailWord_3766354 prefixEnd_3766354 143255549406226841211397 := by
  unfold tailWord_3766354
  simp only [CollatzResearch.WordTrace]
  refine ⟨34342553949287543724298529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91580143864766783264796077 34342553949287543724298529)
  ·
    refine ⟨25756915461965657793223897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34342553949287543724298529 25756915461965657793223897)
    ·
      refine ⟨19317686596474243344917923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25756915461965657793223897 19317686596474243344917923)
      ·
        refine ⟨28976529894711365017376885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19317686596474243344917923 28976529894711365017376885)
        ·
          refine ⟨2716549677629190470379083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28976529894711365017376885 2716549677629190470379083)
          ·
            refine ⟨4074824516443785705568625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2716549677629190470379083 4074824516443785705568625)
            ·
              refine ⟨3056118387332839279176469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4074824516443785705568625 3056118387332839279176469)
              ·
                refine ⟨143255549406226841211397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3056118387332839279176469 143255549406226841211397)
                ·
                  rfl

theorem cell22_3766354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 6].length) (baseStart_3766354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766354 prefixEnd_3766354 := by exact prefixLift 3766354
  have htrace : WordTrace (prefixWord ++ tailWord_3766354) baseStart_3766354 baseEnd_3766354 := by
    simpa [prefixWord, tailWord_3766354, baseEnd_3766354] using wordTrace_append hprefix tailTrace_3766354
  have hstable : (prefixWord ++ tailWord_3766354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766354).length < 2 ^ (prefixWord ++ tailWord_3766354).sum := by decide
  have hdescent : baseEnd_3766354 < baseStart_3766354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766386 : List Nat := [3, 2, 1, 2, 2, 3, 3, 2, 1, 3]
def baseStart_3766386 : Nat := 118140960795 + 3766386 * 2 ^ 59
def prefixEnd_3766386 : Nat := 4983230072969 + 3 ^ 40 * 3766386 * 2
def baseEnd_3766386 : Nat := 1289310898910004154102475

theorem tailTrace_3766386 : CollatzResearch.WordTrace tailWord_3766386 prefixEnd_3766386 1289310898910004154102475 := by
  unfold tailWord_3766386
  simp only [CollatzResearch.WordTrace]
  refine ⟨34342845733258561090589753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91580921955356162908239341 34342845733258561090589753)
  ·
    refine ⟨25757134299943920817942315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34342845733258561090589753 25757134299943920817942315)
    ·
      refine ⟨38635701449915881226913473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25757134299943920817942315 38635701449915881226913473)
      ·
        refine ⟨28976776087436910920185105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38635701449915881226913473 28976776087436910920185105)
        ·
          refine ⟨21732582065577683190138829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28976776087436910920185105 21732582065577683190138829)
          ·
            refine ⟨8149718274591631196302061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21732582065577683190138829 8149718274591631196302061)
            ·
              refine ⟨3056144352971861698613273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8149718274591631196302061 3056144352971861698613273)
              ·
                refine ⟨2292108264728896273959955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3056144352971861698613273 2292108264728896273959955)
                ·
                  refine ⟨3438162397093344410939933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2292108264728896273959955 3438162397093344410939933)
                  ·
                    refine ⟨1289310898910004154102475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3438162397093344410939933 1289310898910004154102475)
                    ·
                      rfl

theorem cell22_3766386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_3766386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766386 prefixEnd_3766386 := by exact prefixLift 3766386
  have htrace : WordTrace (prefixWord ++ tailWord_3766386) baseStart_3766386 baseEnd_3766386 := by
    simpa [prefixWord, tailWord_3766386, baseEnd_3766386] using wordTrace_append hprefix tailTrace_3766386
  have hstable : (prefixWord ++ tailWord_3766386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766386).length < 2 ^ (prefixWord ++ tailWord_3766386).sum := by decide
  have hdescent : baseEnd_3766386 < baseStart_3766386 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766425 : List Nat := [1, 2, 1, 2, 1, 2, 1, 3, 6, 3]
def baseStart_3766425 : Nat := 118140960795 + 3766425 * 2 ^ 59
def prefixEnd_3766425 : Nat := 4983230072969 + 3 ^ 40 * 3766425 * 2
def baseEnd_3766425 : Nat := 1289324249407021052377355

theorem tailTrace_3766425 : CollatzResearch.WordTrace tailWord_3766425 prefixEnd_3766425 1289324249407021052377355 := by
  unfold tailWord_3766425
  simp only [CollatzResearch.WordTrace]
  refine ⟨137372805379892954023028729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91581870253261969348685819 137372805379892954023028729)
  ·
    refine ⟨103029604034919715517271547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137372805379892954023028729 103029604034919715517271547)
    ·
      refine ⟨154544406052379573275907321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103029604034919715517271547 154544406052379573275907321)
      ·
        refine ⟨115908304539284679956930491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154544406052379573275907321 115908304539284679956930491)
        ·
          refine ⟨173862456808927019935395737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115908304539284679956930491 173862456808927019935395737)
          ·
            refine ⟨130396842606695264951546803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173862456808927019935395737 130396842606695264951546803)
            ·
              refine ⟨195595263910042897427320205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130396842606695264951546803 195595263910042897427320205)
              ·
                refine ⟨73348223966266086535245077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 195595263910042897427320205 73348223966266086535245077)
                ·
                  refine ⟨3438197998418722806339613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 73348223966266086535245077 3438197998418722806339613)
                  ·
                    refine ⟨1289324249407021052377355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3438197998418722806339613 1289324249407021052377355)
                    ·
                      rfl

theorem cell22_3766425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 3, 6, 3].length) (baseStart_3766425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766425 prefixEnd_3766425 := by exact prefixLift 3766425
  have htrace : WordTrace (prefixWord ++ tailWord_3766425) baseStart_3766425 baseEnd_3766425 := by
    simpa [prefixWord, tailWord_3766425, baseEnd_3766425] using wordTrace_append hprefix tailTrace_3766425
  have hstable : (prefixWord ++ tailWord_3766425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766425).length < 2 ^ (prefixWord ++ tailWord_3766425).sum := by decide
  have hdescent : baseEnd_3766425 < baseStart_3766425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766429 : List Nat := [1, 4, 2, 1, 1, 4, 3, 1, 1, 4]
def baseStart_3766429 : Nat := 118140960795 + 3766429 * 2 ^ 59
def prefixEnd_3766429 : Nat := 4983230072969 + 3 ^ 40 * 3766429 * 2
def baseEnd_3766429 : Nat := 1289325618688766375277343

theorem tailTrace_3766429 : CollatzResearch.WordTrace tailWord_3766429 prefixEnd_3766429 1289325618688766375277343 := by
  unfold tailWord_3766429
  simp only [CollatzResearch.WordTrace]
  refine ⟨137372951271878462706174341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91581967514585641804116227 137372951271878462706174341)
  ·
    refine ⟨25757428363477211757407689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137372951271878462706174341 25757428363477211757407689)
    ·
      refine ⟨19318071272607908818055767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25757428363477211757407689 19318071272607908818055767)
      ·
        refine ⟨28977106908911863227083651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19318071272607908818055767 28977106908911863227083651)
        ·
          refine ⟨43465660363367794840625477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28977106908911863227083651 43465660363367794840625477)
          ·
            refine ⟨8149811318131461532617277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43465660363367794840625477 8149811318131461532617277)
            ·
              refine ⟨3056179244299298074731479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8149811318131461532617277 3056179244299298074731479)
              ·
                refine ⟨4584268866448947112097219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3056179244299298074731479 4584268866448947112097219)
                ·
                  refine ⟨6876403299673420668145829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4584268866448947112097219 6876403299673420668145829)
                  ·
                    refine ⟨1289325618688766375277343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6876403299673420668145829 1289325618688766375277343)
                    ·
                      rfl

theorem cell22_3766429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 3, 1, 1, 4].length) (baseStart_3766429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766429 prefixEnd_3766429 := by exact prefixLift 3766429
  have htrace : WordTrace (prefixWord ++ tailWord_3766429) baseStart_3766429 baseEnd_3766429 := by
    simpa [prefixWord, tailWord_3766429, baseEnd_3766429] using wordTrace_append hprefix tailTrace_3766429
  have hstable : (prefixWord ++ tailWord_3766429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766429).length < 2 ^ (prefixWord ++ tailWord_3766429).sum := by decide
  have hdescent : baseEnd_3766429 < baseStart_3766429 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766455 : List Nat := [1, 1, 3, 1, 4, 2, 3, 7]
def baseStart_3766455 : Nat := 118140960795 + 3766455 * 2 ^ 59
def prefixEnd_3766455 : Nat := 4983230072969 + 3 ^ 40 * 3766455 * 2
def baseEnd_3766455 : Nat := 143259391002234552680807

theorem tailTrace_3766455 : CollatzResearch.WordTrace tailWord_3766455 prefixEnd_3766455 143259391002234552680807 := by
  unfold tailWord_3766455
  simp only [CollatzResearch.WordTrace]
  refine ⟨137373899569784269146620819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91582599713189512764413879 137373899569784269146620819)
  ·
    refine ⟨206060849354676403719931229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137373899569784269146620819 206060849354676403719931229)
    ·
      refine ⟨77272818508003651394974211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206060849354676403719931229 77272818508003651394974211)
      ·
        refine ⟨115909227762005477092461317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77272818508003651394974211 115909227762005477092461317)
        ·
          refine ⟨21732980205376026954836497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115909227762005477092461317 21732980205376026954836497)
          ·
            refine ⟨16299735154032020216127373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21732980205376026954836497 16299735154032020216127373)
            ·
              refine ⟨6112400682762007581047765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16299735154032020216127373 6112400682762007581047765)
              ·
                refine ⟨143259391002234552680807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6112400682762007581047765 143259391002234552680807)
                ·
                  rfl

theorem cell22_3766455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 3, 7].length) (baseStart_3766455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766455 prefixEnd_3766455 := by exact prefixLift 3766455
  have htrace : WordTrace (prefixWord ++ tailWord_3766455) baseStart_3766455 baseEnd_3766455 := by
    simpa [prefixWord, tailWord_3766455, baseEnd_3766455] using wordTrace_append hprefix tailTrace_3766455
  have hstable : (prefixWord ++ tailWord_3766455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766455).length < 2 ^ (prefixWord ++ tailWord_3766455).sum := by decide
  have hdescent : baseEnd_3766455 < baseStart_3766455 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766504 : List Nat := [2, 1, 4, 1, 2, 3, 2, 1, 3, 3]
def baseStart_3766504 : Nat := 118140960795 + 3766504 * 2 ^ 59
def prefixEnd_3766504 : Nat := 4983230072969 + 3 ^ 40 * 3766504 * 2
def baseEnd_3766504 : Nat := 1289351292721491179652113

theorem tailTrace_3766504 : CollatzResearch.WordTrace tailWord_3766504 prefixEnd_3766504 1289351292721491179652113 := by
  unfold tailWord_3766504
  simp only [CollatzResearch.WordTrace]
  refine ⟨68687843373303375257577283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91583791164404500343436377 68687843373303375257577283)
  ·
    refine ⟨103031765059955062886365925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68687843373303375257577283 103031765059955062886365925)
    ·
      refine ⟨19318455948741574291193611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103031765059955062886365925 19318455948741574291193611)
      ·
        refine ⟨28977683923112361436790417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19318455948741574291193611 28977683923112361436790417)
        ·
          refine ⟨21733262942334271077592813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28977683923112361436790417 21733262942334271077592813)
          ·
            refine ⟨8149973603375351654097305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21733262942334271077592813 8149973603375351654097305)
            ·
              refine ⟨6112480202531513740572979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8149973603375351654097305 6112480202531513740572979)
              ·
                refine ⟨9168720303797270610859469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6112480202531513740572979 9168720303797270610859469)
                ·
                  refine ⟨3438270113923976479072301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9168720303797270610859469 3438270113923976479072301)
                  ·
                    refine ⟨1289351292721491179652113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3438270113923976479072301 1289351292721491179652113)
                    ·
                      rfl

theorem cell22_3766504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 3, 3].length) (baseStart_3766504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766504 prefixEnd_3766504 := by exact prefixLift 3766504
  have htrace : WordTrace (prefixWord ++ tailWord_3766504) baseStart_3766504 baseEnd_3766504 := by
    simpa [prefixWord, tailWord_3766504, baseEnd_3766504] using wordTrace_append hprefix tailTrace_3766504
  have hstable : (prefixWord ++ tailWord_3766504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766504).length < 2 ^ (prefixWord ++ tailWord_3766504).sum := by decide
  have hdescent : baseEnd_3766504 < baseStart_3766504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766515 : List Nat := [1, 1, 1, 2, 2, 4, 1, 3, 2, 5]
def baseStart_3766515 : Nat := 118140960795 + 3766515 * 2 ^ 59
def prefixEnd_3766515 : Nat := 4983230072969 + 3 ^ 40 * 3766515 * 2
def baseEnd_3766515 : Nat := 1289355058246290817627079

theorem tailTrace_3766515 : CollatzResearch.WordTrace tailWord_3766515 prefixEnd_3766515 1289355058246290817627079 := by
  unfold tailWord_3766515
  simp only [CollatzResearch.WordTrace]
  refine ⟨137376087949566899393804999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91584058633044599595869999 137376087949566899393804999)
  ·
    refine ⟨206064131924350349090707499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137376087949566899393804999 206064131924350349090707499)
    ·
      refine ⟨309096197886525523636061249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206064131924350349090707499 309096197886525523636061249)
      ·
        refine ⟨231822148414894142727045937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309096197886525523636061249 231822148414894142727045937)
        ·
          refine ⟨173866611311170607045284453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231822148414894142727045937 173866611311170607045284453)
          ·
            refine ⟨32599989620844488820990835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173866611311170607045284453 32599989620844488820990835)
            ·
              refine ⟨48899984431266733231486253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32599989620844488820990835 48899984431266733231486253)
              ·
                refine ⟨18337494161725024961807345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48899984431266733231486253 18337494161725024961807345)
                ·
                  refine ⟨13753120621293768721355509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18337494161725024961807345 13753120621293768721355509)
                  ·
                    refine ⟨1289355058246290817627079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13753120621293768721355509 1289355058246290817627079)
                    ·
                      rfl

theorem cell22_3766515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 5].length) (baseStart_3766515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766515 prefixEnd_3766515 := by exact prefixLift 3766515
  have htrace : WordTrace (prefixWord ++ tailWord_3766515) baseStart_3766515 baseEnd_3766515 := by
    simpa [prefixWord, tailWord_3766515, baseEnd_3766515] using wordTrace_append hprefix tailTrace_3766515
  have hstable : (prefixWord ++ tailWord_3766515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766515).length < 2 ^ (prefixWord ++ tailWord_3766515).sum := by decide
  have hdescent : baseEnd_3766515 < baseStart_3766515 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766568 : List Nat := [2, 1, 5, 1, 4, 1, 2, 1, 5]
def baseStart_3766568 : Nat := 118140960795 + 3766568 * 2 ^ 59
def prefixEnd_3766568 : Nat := 4983230072969 + 3 ^ 40 * 3766568 * 2
def baseEnd_3766568 : Nat := 429791067076472115350639

theorem tailTrace_3766568 : CollatzResearch.WordTrace tailWord_3766568 prefixEnd_3766568 429791067076472115350639 := by
  unfold tailWord_3766568
  simp only [CollatzResearch.WordTrace]
  refine ⟨68689010509187444722742179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91585347345583259630322905 68689010509187444722742179)
  ·
    refine ⟨103033515763781167084113269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68689010509187444722742179 103033515763781167084113269)
    ·
      refine ⟨9659392102854484414135619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 103033515763781167084113269 9659392102854484414135619)
      ·
        refine ⟨14489088154281726621203429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9659392102854484414135619 14489088154281726621203429)
        ·
          refine ⟨2716704028927823741475643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14489088154281726621203429 2716704028927823741475643)
          ·
            refine ⟨4075056043391735612213465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2716704028927823741475643 4075056043391735612213465)
            ·
              refine ⟨3056292032543801709160099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4075056043391735612213465 3056292032543801709160099)
              ·
                refine ⟨4584438048815702563740149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3056292032543801709160099 4584438048815702563740149)
                ·
                  refine ⟨429791067076472115350639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4584438048815702563740149 429791067076472115350639)
                  ·
                    rfl

theorem cell22_3766568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 5].length) (baseStart_3766568 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766568 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766568 prefixEnd_3766568 := by exact prefixLift 3766568
  have htrace : WordTrace (prefixWord ++ tailWord_3766568) baseStart_3766568 baseEnd_3766568 := by
    simpa [prefixWord, tailWord_3766568, baseEnd_3766568] using wordTrace_append hprefix tailTrace_3766568
  have hstable : (prefixWord ++ tailWord_3766568).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766568).length < 2 ^ (prefixWord ++ tailWord_3766568).sum := by decide
  have hdescent : baseEnd_3766568 < baseStart_3766568 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766575 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 3, 6]
def baseStart_3766575 : Nat := 118140960795 + 3766575 * 2 ^ 59
def prefixEnd_3766575 : Nat := 4983230072969 + 3 ^ 40 * 3766575 * 2
def baseEnd_3766575 : Nat := 1289375597472470661126895

theorem tailTrace_3766575 : CollatzResearch.WordTrace tailWord_3766575 prefixEnd_3766575 1289375597472470661126895 := by
  unfold tailWord_3766575
  simp only [CollatzResearch.WordTrace]
  refine ⟨137378276329349529640989179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91585517552899686427326119 137378276329349529640989179)
  ·
    refine ⟨206067414494024294461483769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137378276329349529640989179 206067414494024294461483769)
    ·
      refine ⟨154550560870518220846112827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206067414494024294461483769 154550560870518220846112827)
      ·
        refine ⟨231825841305777331269169241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154550560870518220846112827 231825841305777331269169241)
        ·
          refine ⟨173869380979332998451876931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231825841305777331269169241 173869380979332998451876931)
          ·
            refine ⟨260804071468999497677815397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173869380979332998451876931 260804071468999497677815397)
            ·
              refine ⟨48900763400437405814590387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260804071468999497677815397 48900763400437405814590387)
              ·
                refine ⟨73351145100656108721885581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48900763400437405814590387 73351145100656108721885581)
                ·
                  refine ⟨27506679412746040770707093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 73351145100656108721885581 27506679412746040770707093)
                  ·
                    refine ⟨1289375597472470661126895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27506679412746040770707093 1289375597472470661126895)
                    ·
                      rfl

theorem cell22_3766575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 6].length) (baseStart_3766575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766575 prefixEnd_3766575 := by exact prefixLift 3766575
  have htrace : WordTrace (prefixWord ++ tailWord_3766575) baseStart_3766575 baseEnd_3766575 := by
    simpa [prefixWord, tailWord_3766575, baseEnd_3766575] using wordTrace_append hprefix tailTrace_3766575
  have hstable : (prefixWord ++ tailWord_3766575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766575).length < 2 ^ (prefixWord ++ tailWord_3766575).sum := by decide
  have hdescent : baseEnd_3766575 < baseStart_3766575 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766613 : List Nat := [1, 3, 2, 2, 4, 2, 2, 2, 4]
def baseStart_3766613 : Nat := 118140960795 + 3766613 * 2 ^ 59
def prefixEnd_3766613 : Nat := 4983230072969 + 3 ^ 40 * 3766613 * 2
def baseEnd_3766613 : Nat := 429796201883017076225593

theorem tailTrace_3766613 : CollatzResearch.WordTrace tailWord_3766613 prefixEnd_3766613 429796201883017076225593 := by
  unfold tailWord_3766613
  simp only [CollatzResearch.WordTrace]
  refine ⟨137379662303211862130872493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91586441535474574753914995 137379662303211862130872493)
  ·
    refine ⟨51517373363704448299077185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137379662303211862130872493 51517373363704448299077185)
    ·
      refine ⟨38638030022778336224307889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51517373363704448299077185 38638030022778336224307889)
      ·
        refine ⟨28978522517083752168230917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38638030022778336224307889 28978522517083752168230917)
        ·
          refine ⟨5433472971953203531543297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28978522517083752168230917 5433472971953203531543297)
          ·
            refine ⟨4075104728964902648657473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5433472971953203531543297 4075104728964902648657473)
            ·
              refine ⟨3056328546723676986493105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4075104728964902648657473 3056328546723676986493105)
              ·
                refine ⟨2292246410042757739869829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3056328546723676986493105 2292246410042757739869829)
                ·
                  refine ⟨429796201883017076225593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2292246410042757739869829 429796201883017076225593)
                  ·
                    rfl

theorem cell22_3766613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 2, 2, 2, 4].length) (baseStart_3766613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766613 prefixEnd_3766613 := by exact prefixLift 3766613
  have htrace : WordTrace (prefixWord ++ tailWord_3766613) baseStart_3766613 baseEnd_3766613 := by
    simpa [prefixWord, tailWord_3766613, baseEnd_3766613] using wordTrace_append hprefix tailTrace_3766613
  have hstable : (prefixWord ++ tailWord_3766613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766613).length < 2 ^ (prefixWord ++ tailWord_3766613).sum := by decide
  have hdescent : baseEnd_3766613 < baseStart_3766613 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766624 : List Nat := [2, 1, 1, 3, 5, 2, 1, 7]
def baseStart_3766624 : Nat := 118140960795 + 3766624 * 2 ^ 59
def prefixEnd_3766624 : Nat := 4983230072969 + 3 ^ 40 * 3766624 * 2
def baseEnd_3766624 : Nat := 143265819019316762961305

theorem tailTrace_3766624 : CollatzResearch.WordTrace tailWord_3766624 prefixEnd_3766624 143265819019316762961305 := by
  unfold tailWord_3766624
  simp only [CollatzResearch.WordTrace]
  refine ⟨68690031753086005504761463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91586709004114674006348617 68690031753086005504761463)
  ·
    refine ⟨103035047629629008257142195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68690031753086005504761463 103035047629629008257142195)
    ·
      refine ⟨154552571444443512385713293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103035047629629008257142195 154552571444443512385713293)
      ·
        refine ⟨57957214291666317144642485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154552571444443512385713293 57957214291666317144642485)
        ·
          refine ⟨5433488839843717232310233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57957214291666317144642485 5433488839843717232310233)
          ·
            refine ⟨4075116629882787924232675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5433488839843717232310233 4075116629882787924232675)
            ·
              refine ⟨6112674944824181886349013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4075116629882787924232675 6112674944824181886349013)
              ·
                refine ⟨143265819019316762961305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6112674944824181886349013 143265819019316762961305)
                ·
                  rfl

theorem cell22_3766624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 7].length) (baseStart_3766624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766624 prefixEnd_3766624 := by exact prefixLift 3766624
  have htrace : WordTrace (prefixWord ++ tailWord_3766624) baseStart_3766624 baseEnd_3766624 := by
    simpa [prefixWord, tailWord_3766624, baseEnd_3766624] using wordTrace_append hprefix tailTrace_3766624
  have hstable : (prefixWord ++ tailWord_3766624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766624).length < 2 ^ (prefixWord ++ tailWord_3766624).sum := by decide
  have hdescent : baseEnd_3766624 < baseStart_3766624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766637 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 2, 6]
def baseStart_3766637 : Nat := 118140960795 + 3766637 * 2 ^ 59
def prefixEnd_3766637 : Nat := 4983230072969 + 3 ^ 40 * 3766637 * 2
def baseEnd_3766637 : Nat := 1289396821339523166076705

theorem tailTrace_3766637 : CollatzResearch.WordTrace tailWord_3766637 prefixEnd_3766637 1289396821339523166076705 := by
  unfold tailWord_3766637
  simp only [CollatzResearch.WordTrace]
  refine ⟨137380537655124914229746165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91587025103416609486497443 137380537655124914229746165)
  ·
    refine ⟨12879425405167960709038703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137380537655124914229746165 12879425405167960709038703)
    ·
      refine ⟨19319138107751941063558055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12879425405167960709038703 19319138107751941063558055)
      ·
        refine ⟨28978707161627911595337083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19319138107751941063558055 28978707161627911595337083)
        ·
          refine ⟨43468060742441867393005625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28978707161627911595337083 43468060742441867393005625)
          ·
            refine ⟨32601045556831400544754219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43468060742441867393005625 32601045556831400544754219)
            ·
              refine ⟨48901568335247100817131329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32601045556831400544754219 48901568335247100817131329)
              ·
                refine ⟨36676176251435325612848497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48901568335247100817131329 36676176251435325612848497)
                ·
                  refine ⟨27507132188576494209636373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36676176251435325612848497 27507132188576494209636373)
                  ·
                    refine ⟨1289396821339523166076705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27507132188576494209636373 1289396821339523166076705)
                    ·
                      rfl

theorem cell22_3766637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_3766637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766637 prefixEnd_3766637 := by exact prefixLift 3766637
  have htrace : WordTrace (prefixWord ++ tailWord_3766637) baseStart_3766637 baseEnd_3766637 := by
    simpa [prefixWord, tailWord_3766637, baseEnd_3766637] using wordTrace_append hprefix tailTrace_3766637
  have hstable : (prefixWord ++ tailWord_3766637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766637).length < 2 ^ (prefixWord ++ tailWord_3766637).sum := by decide
  have hdescent : baseEnd_3766637 < baseStart_3766637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766667 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 2, 5]
def baseStart_3766667 : Nat := 118140960795 + 3766667 * 2 ^ 59
def prefixEnd_3766667 : Nat := 4983230072969 + 3 ^ 40 * 3766667 * 2
def baseEnd_3766667 : Nat := 1289407090952613087826613

theorem tailTrace_3766667 : CollatzResearch.WordTrace tailWord_3766667 prefixEnd_3766667 1289407090952613087826613 := by
  unfold tailWord_3766667
  simp only [CollatzResearch.WordTrace]
  refine ⟨137381631845016229353338255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91587754563344152902225503 137381631845016229353338255)
  ·
    refine ⟨206072447767524344030007383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137381631845016229353338255 206072447767524344030007383)
    ·
      refine ⟨309108671651286516045011075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206072447767524344030007383 309108671651286516045011075)
      ·
        refine ⟨463663007476929774067516613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309108671651286516045011075 463663007476929774067516613)
        ·
          refine ⟨86936813901924332637659365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 463663007476929774067516613 86936813901924332637659365)
          ·
            refine ⟨16300652606610812369561131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86936813901924332637659365 16300652606610812369561131)
            ·
              refine ⟨24450978909916218554341697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16300652606610812369561131 24450978909916218554341697)
              ·
                refine ⟨18338234182437163915756273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24450978909916218554341697 18338234182437163915756273)
                ·
                  refine ⟨13753675636827872936817205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18338234182437163915756273 13753675636827872936817205)
                  ·
                    refine ⟨1289407090952613087826613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13753675636827872936817205 1289407090952613087826613)
                    ·
                      rfl

theorem cell22_3766667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 5].length) (baseStart_3766667 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766667 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766667 prefixEnd_3766667 := by exact prefixLift 3766667
  have htrace : WordTrace (prefixWord ++ tailWord_3766667) baseStart_3766667 baseEnd_3766667 := by
    simpa [prefixWord, tailWord_3766667, baseEnd_3766667] using wordTrace_append hprefix tailTrace_3766667
  have hstable : (prefixWord ++ tailWord_3766667).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766667).length < 2 ^ (prefixWord ++ tailWord_3766667).sum := by decide
  have hdescent : baseEnd_3766667 < baseStart_3766667 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766712 : List Nat := [2, 1, 2, 1, 2, 2, 1, 3, 3, 5]
def baseStart_3766712 : Nat := 118140960795 + 3766712 * 2 ^ 59
def prefixEnd_3766712 : Nat := 4983230072969 + 3 ^ 40 * 3766712 * 2
def baseEnd_3766712 : Nat := 1289422495372247970451475

theorem tailTrace_3766712 : CollatzResearch.WordTrace tailWord_3766712 prefixEnd_3766712 1289422495372247970451475 := by
  unfold tailWord_3766712
  simp only [CollatzResearch.WordTrace]
  refine ⟨68691636564926601019363195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91588848753235468025817593 68691636564926601019363195)
  ·
    refine ⟨103037454847389901529044793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68691636564926601019363195 103037454847389901529044793)
    ·
      refine ⟨77278091135542426146783595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103037454847389901529044793 77278091135542426146783595)
      ·
        refine ⟨115917136703313639220175393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77278091135542426146783595 115917136703313639220175393)
        ·
          refine ⟨86937852527485229415131545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115917136703313639220175393 86937852527485229415131545)
          ·
            refine ⟨65203389395613922061348659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86937852527485229415131545 65203389395613922061348659)
            ·
              refine ⟨97805084093420883092022989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65203389395613922061348659 97805084093420883092022989)
              ·
                refine ⟨36676906535032831159508621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 97805084093420883092022989 36676906535032831159508621)
                ·
                  refine ⟨13753839950637311684815733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 36676906535032831159508621 13753839950637311684815733)
                  ·
                    refine ⟨1289422495372247970451475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13753839950637311684815733 1289422495372247970451475)
                    ·
                      rfl

theorem cell22_3766712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 3, 3, 5].length) (baseStart_3766712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766712 prefixEnd_3766712 := by exact prefixLift 3766712
  have htrace : WordTrace (prefixWord ++ tailWord_3766712) baseStart_3766712 baseEnd_3766712 := by
    simpa [prefixWord, tailWord_3766712, baseEnd_3766712] using wordTrace_append hprefix tailTrace_3766712
  have hstable : (prefixWord ++ tailWord_3766712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766712).length < 2 ^ (prefixWord ++ tailWord_3766712).sum := by decide
  have hdescent : baseEnd_3766712 < baseStart_3766712 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766716 : List Nat := [2, 2, 2, 4, 1, 1, 2, 3, 1, 4]
def baseStart_3766716 : Nat := 118140960795 + 3766716 * 2 ^ 59
def prefixEnd_3766716 : Nat := 4983230072969 + 3 ^ 40 * 3766716 * 2
def baseEnd_3766716 : Nat := 1289423864653993293351463

theorem tailTrace_3766716 : CollatzResearch.WordTrace tailWord_3766716 prefixEnd_3766716 1289423864653993293351463 := by
  unfold tailWord_3766716
  simp only [CollatzResearch.WordTrace]
  refine ⟨68691709510919355360936001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91588946014559140481248001 68691709510919355360936001)
  ·
    refine ⟨51518782133189516520702001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68691709510919355360936001 51518782133189516520702001)
    ·
      refine ⟨38639086599892137390526501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51518782133189516520702001 38639086599892137390526501)
      ·
        refine ⟨7244828737479775760723719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38639086599892137390526501 7244828737479775760723719)
        ·
          refine ⟨10867243106219663641085579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7244828737479775760723719 10867243106219663641085579)
          ·
            refine ⟨16300864659329495461628369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10867243106219663641085579 16300864659329495461628369)
            ·
              refine ⟨12225648494497121596221277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16300864659329495461628369 12225648494497121596221277)
              ·
                refine ⟨4584618185436420598582979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12225648494497121596221277 4584618185436420598582979)
                ·
                  refine ⟨6876927278154630897874469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4584618185436420598582979 6876927278154630897874469)
                  ·
                    refine ⟨1289423864653993293351463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6876927278154630897874469 1289423864653993293351463)
                    ·
                      rfl

theorem cell22_3766716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_3766716 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766716 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766716 prefixEnd_3766716 := by exact prefixLift 3766716
  have htrace : WordTrace (prefixWord ++ tailWord_3766716) baseStart_3766716 baseEnd_3766716 := by
    simpa [prefixWord, tailWord_3766716, baseEnd_3766716] using wordTrace_append hprefix tailTrace_3766716
  have hstable : (prefixWord ++ tailWord_3766716).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766716).length < 2 ^ (prefixWord ++ tailWord_3766716).sum := by decide
  have hdescent : baseEnd_3766716 < baseStart_3766716 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766729 : List Nat := [1, 2, 1, 1, 2, 1, 6, 1, 4, 3]
def baseStart_3766729 : Nat := 118140960795 + 3766729 * 2 ^ 59
def prefixEnd_3766729 : Nat := 4983230072969 + 3 ^ 40 * 3766729 * 2
def baseEnd_3766729 : Nat := 1289428314819665592776423

theorem tailTrace_3766729 : CollatzResearch.WordTrace tailWord_3766729 prefixEnd_3766729 1289428314819665592776423 := by
  unfold tailWord_3766729
  simp only [CollatzResearch.WordTrace]
  refine ⟨137383893170791613942095241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91589262113861075961396827 137383893170791613942095241)
  ·
    refine ⟨103037919878093710456571431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137383893170791613942095241 103037919878093710456571431)
    ·
      refine ⟨154556879817140565684857147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103037919878093710456571431 154556879817140565684857147)
      ·
        refine ⟨231835319725710848527285721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154556879817140565684857147 231835319725710848527285721)
        ·
          refine ⟨173876489794283136395464291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231835319725710848527285721 173876489794283136395464291)
          ·
            refine ⟨260814734691424704593196437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173876489794283136395464291 260814734691424704593196437)
            ·
              refine ⟨12225690688660533027806083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 260814734691424704593196437 12225690688660533027806083)
              ·
                refine ⟨18338536032990799541709125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12225690688660533027806083 18338536032990799541709125)
                ·
                  refine ⟨3438475506185774914070461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18338536032990799541709125 3438475506185774914070461)
                  ·
                    refine ⟨1289428314819665592776423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3438475506185774914070461 1289428314819665592776423)
                    ·
                      rfl

theorem cell22_3766729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 6, 1, 4, 3].length) (baseStart_3766729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766729 prefixEnd_3766729 := by exact prefixLift 3766729
  have htrace : WordTrace (prefixWord ++ tailWord_3766729) baseStart_3766729 baseEnd_3766729 := by
    simpa [prefixWord, tailWord_3766729, baseEnd_3766729] using wordTrace_append hprefix tailTrace_3766729
  have hstable : (prefixWord ++ tailWord_3766729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766729).length < 2 ^ (prefixWord ++ tailWord_3766729).sum := by decide
  have hdescent : baseEnd_3766729 < baseStart_3766729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766746 : List Nat := [3, 1, 1, 2, 3, 1, 3, 3, 2, 3]
def baseStart_3766746 : Nat := 118140960795 + 3766746 * 2 ^ 59
def prefixEnd_3766746 : Nat := 4983230072969 + 3 ^ 40 * 3766746 * 2
def baseEnd_3766746 : Nat := 1289434134267083215101371

theorem tailTrace_3766746 : CollatzResearch.WordTrace tailWord_3766746 prefixEnd_3766746 1289434134267083215101371 := by
  unfold tailWord_3766746
  simp only [CollatzResearch.WordTrace]
  refine ⟨34346128302932506461366023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91589675474486683896976061 34346128302932506461366023)
  ·
    refine ⟨51519192454398759692049035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34346128302932506461366023 51519192454398759692049035)
    ·
      refine ⟨77278788681598139538073553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51519192454398759692049035 77278788681598139538073553)
      ·
        refine ⟨57959091511198604653555165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77278788681598139538073553 57959091511198604653555165)
        ·
          refine ⟨21734659316699476745083187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57959091511198604653555165 21734659316699476745083187)
          ·
            refine ⟨32601988975049215117624781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21734659316699476745083187 32601988975049215117624781)
            ·
              refine ⟨12225745865643455669109293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32601988975049215117624781 12225745865643455669109293)
              ·
                refine ⟨4584654699616295875915985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12225745865643455669109293 4584654699616295875915985)
                ·
                  refine ⟨3438491024712221906936989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4584654699616295875915985 3438491024712221906936989)
                  ·
                    refine ⟨1289434134267083215101371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3438491024712221906936989 1289434134267083215101371)
                    ·
                      rfl

theorem cell22_3766746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 3, 3, 2, 3].length) (baseStart_3766746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766746 prefixEnd_3766746 := by exact prefixLift 3766746
  have htrace : WordTrace (prefixWord ++ tailWord_3766746) baseStart_3766746 baseEnd_3766746 := by
    simpa [prefixWord, tailWord_3766746, baseEnd_3766746] using wordTrace_append hprefix tailTrace_3766746
  have hstable : (prefixWord ++ tailWord_3766746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766746).length < 2 ^ (prefixWord ++ tailWord_3766746).sum := by decide
  have hdescent : baseEnd_3766746 < baseStart_3766746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766838 : List Nat := [5, 1, 2, 1, 2, 1, 3, 2, 5]
def baseStart_3766838 : Nat := 118140960795 + 3766838 * 2 ^ 59
def prefixEnd_3766838 : Nat := 4983230072969 + 3 ^ 40 * 3766838 * 2
def baseEnd_3766838 : Nat := 429821875915741880600363

theorem tailTrace_3766838 : CollatzResearch.WordTrace tailWord_3766838 prefixEnd_3766838 429821875915741880600363 := by
  unfold tailWord_3766838
  simp only [CollatzResearch.WordTrace]
  refine ⟨8586741795462295347363323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91591912484931150371875445 8586741795462295347363323)
  ·
    refine ⟨12880112693193443021044985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8586741795462295347363323 12880112693193443021044985)
    ·
      refine ⟨9660084519895082265783739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12880112693193443021044985 9660084519895082265783739)
      ·
        refine ⟨14490126779842623398675609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9660084519895082265783739 14490126779842623398675609)
        ·
          refine ⟨10867595084881967549006707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14490126779842623398675609 10867595084881967549006707)
          ·
            refine ⟨16301392627322951323510061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10867595084881967549006707 16301392627322951323510061)
            ·
              refine ⟨6113022235246106746316273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16301392627322951323510061 6113022235246106746316273)
              ·
                refine ⟨4584766676434580059737205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6113022235246106746316273 4584766676434580059737205)
                ·
                  refine ⟨429821875915741880600363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4584766676434580059737205 429821875915741880600363)
                  ·
                    rfl

theorem cell22_3766838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 5].length) (baseStart_3766838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766838 prefixEnd_3766838 := by exact prefixLift 3766838
  have htrace : WordTrace (prefixWord ++ tailWord_3766838) baseStart_3766838 baseEnd_3766838 := by
    simpa [prefixWord, tailWord_3766838, baseEnd_3766838] using wordTrace_append hprefix tailTrace_3766838
  have hstable : (prefixWord ++ tailWord_3766838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766838).length < 2 ^ (prefixWord ++ tailWord_3766838).sum := by decide
  have hdescent : baseEnd_3766838 < baseStart_3766838 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766864 : List Nat := [2, 1, 1, 1, 1, 3, 2, 5, 1, 5]
def baseStart_3766864 : Nat := 118140960795 + 3766864 * 2 ^ 59
def prefixEnd_3766864 : Nat := 4983230072969 + 3 ^ 40 * 3766864 * 2
def baseEnd_3766864 : Nat := 1289474528078570240651009

theorem tailTrace_3766864 : CollatzResearch.WordTrace tailWord_3766864 prefixEnd_3766864 1289474528078570240651009 := by
  unfold tailWord_3766864
  simp only [CollatzResearch.WordTrace]
  refine ⟨68694408512651265999129823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91592544683535021332173097 68694408512651265999129823)
  ·
    refine ⟨103041612768976898998694735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68694408512651265999129823 103041612768976898998694735)
    ·
      refine ⟨154562419153465348498042103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103041612768976898998694735 154562419153465348498042103)
      ·
        refine ⟨231843628730198022747063155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154562419153465348498042103 231843628730198022747063155)
        ·
          refine ⟨347765443095297034120594733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231843628730198022747063155 347765443095297034120594733)
          ·
            refine ⟨130412041160736387795223025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 347765443095297034120594733 130412041160736387795223025)
            ·
              refine ⟨97809030870552290846417269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130412041160736387795223025 97809030870552290846417269)
              ·
                refine ⟨9169596644114277266851619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 97809030870552290846417269 9169596644114277266851619)
                ·
                  refine ⟨13754394966171415900277429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9169596644114277266851619 13754394966171415900277429)
                  ·
                    refine ⟨1289474528078570240651009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13754394966171415900277429 1289474528078570240651009)
                    ·
                      rfl

theorem cell22_3766864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 1, 5].length) (baseStart_3766864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766864 prefixEnd_3766864 := by exact prefixLift 3766864
  have htrace : WordTrace (prefixWord ++ tailWord_3766864) baseStart_3766864 baseEnd_3766864 := by
    simpa [prefixWord, tailWord_3766864, baseEnd_3766864] using wordTrace_append hprefix tailTrace_3766864
  have hstable : (prefixWord ++ tailWord_3766864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766864).length < 2 ^ (prefixWord ++ tailWord_3766864).sum := by decide
  have hdescent : baseEnd_3766864 < baseStart_3766864 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766868 : List Nat := [2, 4, 1, 1, 1, 4, 2, 2, 1, 4]
def baseStart_3766868 : Nat := 118140960795 + 3766868 * 2 ^ 59
def prefixEnd_3766868 : Nat := 4983230072969 + 3 ^ 40 * 3766868 * 2
def baseEnd_3766868 : Nat := 1289475897360315563550997

theorem tailTrace_3766868 : CollatzResearch.WordTrace tailWord_3766868 prefixEnd_3766868 1289475897360315563550997 := by
  unfold tailWord_3766868
  simp only [CollatzResearch.WordTrace]
  refine ⟨68694481458644020340702629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91592641944858693787603505 68694481458644020340702629)
  ·
    refine ⟨12880215273495753813881743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68694481458644020340702629 12880215273495753813881743)
    ·
      refine ⟨19320322910243630720822615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12880215273495753813881743 19320322910243630720822615)
      ·
        refine ⟨28980484365365446081233923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19320322910243630720822615 28980484365365446081233923)
        ·
          refine ⟨43470726548048169121850885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28980484365365446081233923 43470726548048169121850885)
          ·
            refine ⟨8150761227759031710347041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43470726548048169121850885 8150761227759031710347041)
            ·
              refine ⟨6113070920819273782760281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8150761227759031710347041 6113070920819273782760281)
              ·
                refine ⟨4584803190614455337070211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6113070920819273782760281 4584803190614455337070211)
                ·
                  refine ⟨6877204785921683005605317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4584803190614455337070211 6877204785921683005605317)
                  ·
                    refine ⟨1289475897360315563550997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6877204785921683005605317 1289475897360315563550997)
                    ·
                      rfl

theorem cell22_3766868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_3766868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766868 prefixEnd_3766868 := by exact prefixLift 3766868
  have htrace : WordTrace (prefixWord ++ tailWord_3766868) baseStart_3766868 baseEnd_3766868 := by
    simpa [prefixWord, tailWord_3766868, baseEnd_3766868] using wordTrace_append hprefix tailTrace_3766868
  have hstable : (prefixWord ++ tailWord_3766868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766868).length < 2 ^ (prefixWord ++ tailWord_3766868).sum := by decide
  have hdescent : baseEnd_3766868 < baseStart_3766868 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766879 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 6, 4]
def baseStart_3766879 : Nat := 118140960795 + 3766879 * 2 ^ 59
def prefixEnd_3766879 : Nat := 4983230072969 + 3 ^ 40 * 3766879 * 2
def baseEnd_3766879 : Nat := 1289479662885115201525963

theorem tailTrace_3766879 : CollatzResearch.WordTrace tailWord_3766879 prefixEnd_3766879 1289479662885115201525963 := by
  unfold tailWord_3766879
  simp only [CollatzResearch.WordTrace]
  refine ⟨137389364120248189560055691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91592909413498793040037127 137389364120248189560055691)
  ·
    refine ⟨206084046180372284340083537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137389364120248189560055691 206084046180372284340083537)
    ·
      refine ⟨154563034635279213255062653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206084046180372284340083537 154563034635279213255062653)
      ·
        refine ⟨57961137988229704970648495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154563034635279213255062653 57961137988229704970648495)
        ·
          refine ⟨86941706982344557455972743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57961137988229704970648495 86941706982344557455972743)
          ·
            refine ⟨130412560473516836183959115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86941706982344557455972743 130412560473516836183959115)
            ·
              refine ⟨195618840710275254275938673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130412560473516836183959115 195618840710275254275938673)
              ·
                refine ⟨146714130532706440706954005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195618840710275254275938673 146714130532706440706954005)
                ·
                  refine ⟨6877224868720614408138469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146714130532706440706954005 6877224868720614408138469)
                  ·
                    refine ⟨1289479662885115201525963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6877224868720614408138469 1289479662885115201525963)
                    ·
                      rfl

theorem cell22_3766879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 6, 4].length) (baseStart_3766879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766879 prefixEnd_3766879 := by exact prefixLift 3766879
  have htrace : WordTrace (prefixWord ++ tailWord_3766879) baseStart_3766879 baseEnd_3766879 := by
    simpa [prefixWord, tailWord_3766879, baseEnd_3766879] using wordTrace_append hprefix tailTrace_3766879
  have hstable : (prefixWord ++ tailWord_3766879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766879).length < 2 ^ (prefixWord ++ tailWord_3766879).sum := by decide
  have hdescent : baseEnd_3766879 < baseStart_3766879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766881 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 4, 3]
def baseStart_3766881 : Nat := 118140960795 + 3766881 * 2 ^ 59
def prefixEnd_3766881 : Nat := 4983230072969 + 3 ^ 40 * 3766881 * 2
def baseEnd_3766881 : Nat := 1289480347525987862975957

theorem tailTrace_3766881 : CollatzResearch.WordTrace tailWord_3766881 prefixEnd_3766881 1289480347525987862975957 := by
  unfold tailWord_3766881
  simp only [CollatzResearch.WordTrace]
  refine ⟨137389437066240943901628497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91592958044160629267752331 137389437066240943901628497)
  ·
    refine ⟨103042077799680707926221373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137389437066240943901628497 103042077799680707926221373)
    ·
      refine ⟨38640779174880265472333015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 103042077799680707926221373 38640779174880265472333015)
      ·
        refine ⟨57961168762320398208499523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38640779174880265472333015 57961168762320398208499523)
        ·
          refine ⟨86941753143480597312749285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57961168762320398208499523 86941753143480597312749285)
          ·
            refine ⟨16301578714402611996140491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86941753143480597312749285 16301578714402611996140491)
            ·
              refine ⟨24452368071603917994210737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16301578714402611996140491 24452368071603917994210737)
              ·
                refine ⟨18339276053702938495658053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24452368071603917994210737 18339276053702938495658053)
                ·
                  refine ⟨3438614260069300967935885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 18339276053702938495658053 3438614260069300967935885)
                  ·
                    refine ⟨1289480347525987862975957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3438614260069300967935885 1289480347525987862975957)
                    ·
                      rfl

theorem cell22_3766881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_3766881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766881 prefixEnd_3766881 := by exact prefixLift 3766881
  have htrace : WordTrace (prefixWord ++ tailWord_3766881) baseStart_3766881 baseEnd_3766881 := by
    simpa [prefixWord, tailWord_3766881, baseEnd_3766881] using wordTrace_append hprefix tailTrace_3766881
  have hstable : (prefixWord ++ tailWord_3766881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766881).length < 2 ^ (prefixWord ++ tailWord_3766881).sum := by decide
  have hdescent : baseEnd_3766881 < baseStart_3766881 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766924 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 4, 6]
def baseStart_3766924 : Nat := 118140960795 + 3766924 * 2 ^ 59
def prefixEnd_3766924 : Nat := 4983230072969 + 3 ^ 40 * 3766924 * 2
def baseEnd_3766924 : Nat := 1289495067304750084150825

theorem tailTrace_3766924 : CollatzResearch.WordTrace tailWord_3766924 prefixEnd_3766924 1289495067304750084150825 := by
  unfold tailWord_3766924
  simp only [CollatzResearch.WordTrace]
  refine ⟨68695502702542581122721913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91594003603390108163629217 68695502702542581122721913)
  ·
    refine ⟨51521627026906935842041435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68695502702542581122721913 51521627026906935842041435)
    ·
      refine ⟨77282440540360403763062153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51521627026906935842041435 77282440540360403763062153)
      ·
        refine ⟨57961830405270302822296615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77282440540360403763062153 57961830405270302822296615)
        ·
          refine ⟨86942745607905454233444923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57961830405270302822296615 86942745607905454233444923)
          ·
            refine ⟨130414118411858181350167385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86942745607905454233444923 130414118411858181350167385)
            ·
              refine ⟨97810588808893636012625539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 130414118411858181350167385 97810588808893636012625539)
              ·
                refine ⟨146715883213340454018938309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97810588808893636012625539 146715883213340454018938309)
                ·
                  refine ⟨27509228102501335128550933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146715883213340454018938309 27509228102501335128550933)
                  ·
                    refine ⟨1289495067304750084150825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27509228102501335128550933 1289495067304750084150825)
                    ·
                      rfl

theorem cell22_3766924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 6].length) (baseStart_3766924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766924 prefixEnd_3766924 := by exact prefixLift 3766924
  have htrace : WordTrace (prefixWord ++ tailWord_3766924) baseStart_3766924 baseEnd_3766924 := by
    simpa [prefixWord, tailWord_3766924, baseEnd_3766924] using wordTrace_append hprefix tailTrace_3766924
  have hstable : (prefixWord ++ tailWord_3766924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766924).length < 2 ^ (prefixWord ++ tailWord_3766924).sum := by decide
  have hdescent : baseEnd_3766924 < baseStart_3766924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766958 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 2, 6]
def baseStart_3766958 : Nat := 118140960795 + 3766958 * 2 ^ 59
def prefixEnd_3766958 : Nat := 4983230072969 + 3 ^ 40 * 3766958 * 2
def baseEnd_3766958 : Nat := 1289506706199585328800721

theorem tailTrace_3766958 : CollatzResearch.WordTrace tailWord_3766958 prefixEnd_3766958 1289506706199585328800721 := by
  unfold tailWord_3766958
  simp only [CollatzResearch.WordTrace]
  refine ⟨17174030685870248256522691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91594830324641324034787685 17174030685870248256522691)
  ·
    refine ⟨25761046028805372384784037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17174030685870248256522691 25761046028805372384784037)
    ·
      refine ⟨4830196130401007322147007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25761046028805372384784037 4830196130401007322147007)
      ·
        refine ⟨7245294195601510983220511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4830196130401007322147007 7245294195601510983220511)
        ·
          refine ⟨10867941293402266474830767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7245294195601510983220511 10867941293402266474830767)
          ·
            refine ⟨16301911940103399712246151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10867941293402266474830767 16301911940103399712246151)
            ·
              refine ⟨24452867910155099568369227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16301911940103399712246151 24452867910155099568369227)
              ·
                refine ⟨36679301865232649352553841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24452867910155099568369227 36679301865232649352553841)
                ·
                  refine ⟨27509476398924487014415381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36679301865232649352553841 27509476398924487014415381)
                  ·
                    refine ⟨1289506706199585328800721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27509476398924487014415381 1289506706199585328800721)
                    ·
                      rfl

theorem cell22_3766958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_3766958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766958 prefixEnd_3766958 := by exact prefixLift 3766958
  have htrace : WordTrace (prefixWord ++ tailWord_3766958) baseStart_3766958 baseEnd_3766958 := by
    simpa [prefixWord, tailWord_3766958, baseEnd_3766958] using wordTrace_append hprefix tailTrace_3766958
  have hstable : (prefixWord ++ tailWord_3766958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766958).length < 2 ^ (prefixWord ++ tailWord_3766958).sum := by decide
  have hdescent : baseEnd_3766958 < baseStart_3766958 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3766977 : List Nat := [1, 2, 6, 2, 1, 1, 1, 2, 3, 3]
def baseStart_3766977 : Nat := 118140960795 + 3766977 * 2 ^ 59
def prefixEnd_3766977 : Nat := 4983230072969 + 3 ^ 40 * 3766977 * 2
def baseEnd_3766977 : Nat := 1289513210287875612575663

theorem tailTrace_3766977 : CollatzResearch.WordTrace tailWord_3766977 prefixEnd_3766977 1289513210287875612575663 := by
  unfold tailWord_3766977
  simp only [CollatzResearch.WordTrace]
  refine ⟨137392938473893152297123185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91595292315928768198082123 137392938473893152297123185)
  ·
    refine ⟨103044703855419864222842389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137392938473893152297123185 103044703855419864222842389)
    ·
      refine ⟨4830220493222806135445737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103044703855419864222842389 4830220493222806135445737)
      ·
        refine ⟨3622665369917104601584303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4830220493222806135445737 3622665369917104601584303)
        ·
          refine ⟨5433998054875656902376455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3622665369917104601584303 5433998054875656902376455)
          ·
            refine ⟨8150997082313485353564683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5433998054875656902376455 8150997082313485353564683)
            ·
              refine ⟨12226495623470228030347025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8150997082313485353564683 12226495623470228030347025)
              ·
                refine ⟨9169871717602671022760269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12226495623470228030347025 9169871717602671022760269)
                ·
                  refine ⟨3438701894101001633535101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9169871717602671022760269 3438701894101001633535101)
                  ·
                    refine ⟨1289513210287875612575663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3438701894101001633535101 1289513210287875612575663)
                    ·
                      rfl

theorem cell22_3766977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_3766977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3766977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3766977 prefixEnd_3766977 := by exact prefixLift 3766977
  have htrace : WordTrace (prefixWord ++ tailWord_3766977) baseStart_3766977 baseEnd_3766977 := by
    simpa [prefixWord, tailWord_3766977, baseEnd_3766977] using wordTrace_append hprefix tailTrace_3766977
  have hstable : (prefixWord ++ tailWord_3766977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3766977).length < 2 ^ (prefixWord ++ tailWord_3766977).sum := by decide
  have hdescent : baseEnd_3766977 < baseStart_3766977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3766977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767033 : List Nat := [1, 2, 1, 3, 1, 1, 1, 7, 2, 3]
def baseStart_3767033 : Nat := 118140960795 + 3767033 * 2 ^ 59
def prefixEnd_3767033 : Nat := 4983230072969 + 3 ^ 40 * 3767033 * 2
def baseEnd_3767033 : Nat := 1289532380232310133175491

theorem tailTrace_3767033 : CollatzResearch.WordTrace tailWord_3767033 prefixEnd_3767033 1289532380232310133175491 := by
  unfold tailWord_3767033
  simp only [CollatzResearch.WordTrace]
  refine ⟨137394980961690273861161753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91596653974460182574107835 137394980961690273861161753)
  ·
    refine ⟨103046235721267705395871315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137394980961690273861161753 103046235721267705395871315)
    ·
      refine ⟨154569353581901558093806973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103046235721267705395871315 154569353581901558093806973)
      ·
        refine ⟨57963507593213084285177615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154569353581901558093806973 57963507593213084285177615)
        ·
          refine ⟨86945261389819626427766423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57963507593213084285177615 86945261389819626427766423)
          ·
            refine ⟨130417892084729439641649635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86945261389819626427766423 130417892084729439641649635)
            ·
              refine ⟨195626838127094159462474453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130417892084729439641649635 195626838127094159462474453)
              ·
                refine ⟨4585004018603769362401745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 195626838127094159462474453 4585004018603769362401745)
                ·
                  refine ⟨3438753013952827021801309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4585004018603769362401745 3438753013952827021801309)
                  ·
                    refine ⟨1289532380232310133175491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3438753013952827021801309 1289532380232310133175491)
                    ·
                      rfl

theorem cell22_3767033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 7, 2, 3].length) (baseStart_3767033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767033 prefixEnd_3767033 := by exact prefixLift 3767033
  have htrace : WordTrace (prefixWord ++ tailWord_3767033) baseStart_3767033 baseEnd_3767033 := by
    simpa [prefixWord, tailWord_3767033, baseEnd_3767033] using wordTrace_append hprefix tailTrace_3767033
  have hstable : (prefixWord ++ tailWord_3767033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767033).length < 2 ^ (prefixWord ++ tailWord_3767033).sum := by decide
  have hdescent : baseEnd_3767033 < baseStart_3767033 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767063 : List Nat := [1, 1, 3, 4, 3, 2, 8]
def baseStart_3767063 : Nat := 118140960795 + 3767063 * 2 ^ 59
def prefixEnd_3767063 : Nat := 4983230072969 + 3 ^ 40 * 3767063 * 2
def baseEnd_3767063 : Nat := 47760838883162964997237

theorem tailTrace_3767063 : CollatzResearch.WordTrace tailWord_3767063 prefixEnd_3767063 47760838883162964997237 := by
  unfold tailWord_3767063
  simp only [CollatzResearch.WordTrace]
  refine ⟨137396075151581588984753843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91597383434387725989835895 137396075151581588984753843)
  ·
    refine ⟨206094112727372383477130765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137396075151581588984753843 206094112727372383477130765)
    ·
      refine ⟨77285292272764643803924037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206094112727372383477130765 77285292272764643803924037)
      ·
        refine ⟨14490992301143370713235757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 77285292272764643803924037 14490992301143370713235757)
        ·
          refine ⟨5434122112928764017463409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14490992301143370713235757 5434122112928764017463409)
          ·
            refine ⟨4075591584696573013097557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5434122112928764017463409 4075591584696573013097557)
            ·
              refine ⟨47760838883162964997237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4075591584696573013097557 47760838883162964997237)
              ·
                rfl

theorem cell22_3767063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 8].length) (baseStart_3767063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767063 prefixEnd_3767063 := by exact prefixLift 3767063
  have htrace : WordTrace (prefixWord ++ tailWord_3767063) baseStart_3767063 baseEnd_3767063 := by
    simpa [prefixWord, tailWord_3767063, baseEnd_3767063] using wordTrace_append hprefix tailTrace_3767063
  have hstable : (prefixWord ++ tailWord_3767063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767063).length < 2 ^ (prefixWord ++ tailWord_3767063).sum := by decide
  have hdescent : baseEnd_3767063 < baseStart_3767063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767069 : List Nat := [1, 4, 2, 4, 1, 1, 3, 2, 4]
def baseStart_3767069 : Nat := 118140960795 + 3767069 * 2 ^ 59
def prefixEnd_3767069 : Nat := 4983230072969 + 3 ^ 40 * 3767069 * 2
def baseEnd_3767069 : Nat := 429848234589339346425127

theorem tailTrace_3767069 : CollatzResearch.WordTrace tailWord_3767069 prefixEnd_3767069 429848234589339346425127 := by
  unfold tailWord_3767069
  simp only [CollatzResearch.WordTrace]
  refine ⟨137396293989559852009472261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91597529326373234672981507 137396293989559852009472261)
  ·
    refine ⟨25761805123042472251776049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137396293989559852009472261 25761805123042472251776049)
    ·
      refine ⟨19321353842281854188832037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25761805123042472251776049 19321353842281854188832037)
      ·
        refine ⟨3622753845427847660406007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19321353842281854188832037 3622753845427847660406007)
        ·
          refine ⟨5434130768141771490609011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3622753845427847660406007 5434130768141771490609011)
          ·
            refine ⟨8151196152212657235913517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5434130768141771490609011 8151196152212657235913517)
            ·
              refine ⟨3056698557079746463467569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8151196152212657235913517 3056698557079746463467569)
              ·
                refine ⟨2292523917809809847600677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3056698557079746463467569 2292523917809809847600677)
                ·
                  refine ⟨429848234589339346425127, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2292523917809809847600677 429848234589339346425127)
                  ·
                    rfl

theorem cell22_3767069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_3767069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767069 prefixEnd_3767069 := by exact prefixLift 3767069
  have htrace : WordTrace (prefixWord ++ tailWord_3767069) baseStart_3767069 baseEnd_3767069 := by
    simpa [prefixWord, tailWord_3767069, baseEnd_3767069] using wordTrace_append hprefix tailTrace_3767069
  have hstable : (prefixWord ++ tailWord_3767069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767069).length < 2 ^ (prefixWord ++ tailWord_3767069).sum := by decide
  have hdescent : baseEnd_3767069 < baseStart_3767069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767129 : List Nat := [1, 2, 1, 2, 2, 6, 2, 2, 1, 3]
def baseStart_3767129 : Nat := 118140960795 + 3767129 * 2 ^ 59
def prefixEnd_3767129 : Nat := 4983230072969 + 3 ^ 40 * 3767129 * 2
def baseEnd_3767129 : Nat := 1289565242994197882775197

theorem tailTrace_3767129 : CollatzResearch.WordTrace tailWord_3767129 prefixEnd_3767129 1289565242994197882775197 := by
  unfold tailWord_3767129
  simp only [CollatzResearch.WordTrace]
  refine ⟨137398482369342482256656441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91598988246228321504437627 137398482369342482256656441)
  ·
    refine ⟨103048861777006861692492331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137398482369342482256656441 103048861777006861692492331)
    ·
      refine ⟨154573292665510292538738497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103048861777006861692492331 154573292665510292538738497)
      ·
        refine ⟨115929969499132719404053873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154573292665510292538738497 115929969499132719404053873)
        ·
          refine ⟨86947477124349539553040405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115929969499132719404053873 86947477124349539553040405)
          ·
            refine ⟨4075662990203884666548769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 86947477124349539553040405 4075662990203884666548769)
            ·
              refine ⟨3056747242652913499911577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4075662990203884666548769 3056747242652913499911577)
              ·
                refine ⟨2292560431989685124933683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3056747242652913499911577 2292560431989685124933683)
                ·
                  refine ⟨3438840647984527687400525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2292560431989685124933683 3438840647984527687400525)
                  ·
                    refine ⟨1289565242994197882775197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3438840647984527687400525 1289565242994197882775197)
                    ·
                      rfl

theorem cell22_3767129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 1, 3].length) (baseStart_3767129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767129 prefixEnd_3767129 := by exact prefixLift 3767129
  have htrace : WordTrace (prefixWord ++ tailWord_3767129) baseStart_3767129 baseEnd_3767129 := by
    simpa [prefixWord, tailWord_3767129, baseEnd_3767129] using wordTrace_append hprefix tailTrace_3767129
  have hstable : (prefixWord ++ tailWord_3767129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767129).length < 2 ^ (prefixWord ++ tailWord_3767129).sum := by decide
  have hdescent : baseEnd_3767129 < baseStart_3767129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767153 : List Nat := [1, 2, 2, 2, 1, 5, 1, 2, 6]
def baseStart_3767153 : Nat := 118140960795 + 3767153 * 2 ^ 59
def prefixEnd_3767153 : Nat := 4983230072969 + 3 ^ 40 * 3767153 * 2
def baseEnd_3767153 : Nat := 429857819561556606725041

theorem tailTrace_3767153 : CollatzResearch.WordTrace tailWord_3767153 prefixEnd_3767153 429857819561556606725041 := by
  unfold tailWord_3767153
  simp only [CollatzResearch.WordTrace]
  refine ⟨137399357721255534355530113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91599571814170356237020075 137399357721255534355530113)
  ·
    refine ⟨103049518290941650766647585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137399357721255534355530113 103049518290941650766647585)
    ·
      refine ⟨77287138718206238074985689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103049518290941650766647585 77287138718206238074985689)
      ·
        refine ⟨57965354038654678556239267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77287138718206238074985689 57965354038654678556239267)
        ·
          refine ⟨86948031057982017834358901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57965354038654678556239267 86948031057982017834358901)
          ·
            refine ⟨8151377911685814171971147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86948031057982017834358901 8151377911685814171971147)
            ·
              refine ⟨12227066867528721257956721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8151377911685814171971147 12227066867528721257956721)
              ·
                refine ⟨9170300150646540943467541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12227066867528721257956721 9170300150646540943467541)
                ·
                  refine ⟨429857819561556606725041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9170300150646540943467541 429857819561556606725041)
                  ·
                    rfl

theorem cell22_3767153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 5, 1, 2, 6].length) (baseStart_3767153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767153 prefixEnd_3767153 := by exact prefixLift 3767153
  have htrace : WordTrace (prefixWord ++ tailWord_3767153) baseStart_3767153 baseEnd_3767153 := by
    simpa [prefixWord, tailWord_3767153, baseEnd_3767153] using wordTrace_append hprefix tailTrace_3767153
  have hstable : (prefixWord ++ tailWord_3767153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767153).length < 2 ^ (prefixWord ++ tailWord_3767153).sum := by decide
  have hdescent : baseEnd_3767153 < baseStart_3767153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767202 : List Nat := [3, 3, 1, 2, 2, 3, 1, 1, 1, 5]
def baseStart_3767202 : Nat := 118140960795 + 3767202 * 2 ^ 59
def prefixEnd_3767202 : Nat := 4983230072969 + 3 ^ 40 * 3767202 * 2
def baseEnd_3767202 : Nat := 1289590232386050025699973

theorem tailTrace_3767202 : CollatzResearch.WordTrace tailWord_3767202 prefixEnd_3767202 1289590232386050025699973 := by
  unfold tailWord_3767202
  simp only [CollatzResearch.WordTrace]
  refine ⟨34350286224519503931015965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91600763265385343816042573 34350286224519503931015965)
  ·
    refine ⟨12881357334194813974130987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34350286224519503931015965 12881357334194813974130987)
    ·
      refine ⟨19322036001292220961196481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12881357334194813974130987 19322036001292220961196481)
      ·
        refine ⟨14491527000969165720897361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19322036001292220961196481 14491527000969165720897361)
        ·
          refine ⟨10868645250726874290673021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14491527000969165720897361 10868645250726874290673021)
          ·
            refine ⟨4075741969022577859002383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10868645250726874290673021 4075741969022577859002383)
            ·
              refine ⟨6113612953533866788503575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4075741969022577859002383 6113612953533866788503575)
              ·
                refine ⟨9170419430300800182755363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6113612953533866788503575 9170419430300800182755363)
                ·
                  refine ⟨13755629145451200274133045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9170419430300800182755363 13755629145451200274133045)
                  ·
                    refine ⟨1289590232386050025699973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13755629145451200274133045 1289590232386050025699973)
                    ·
                      rfl

theorem cell22_3767202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 1, 5].length) (baseStart_3767202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767202 prefixEnd_3767202 := by exact prefixLift 3767202
  have htrace : WordTrace (prefixWord ++ tailWord_3767202) baseStart_3767202 baseEnd_3767202 := by
    simpa [prefixWord, tailWord_3767202, baseEnd_3767202] using wordTrace_append hprefix tailTrace_3767202
  have hstable : (prefixWord ++ tailWord_3767202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767202).length < 2 ^ (prefixWord ++ tailWord_3767202).sum := by decide
  have hdescent : baseEnd_3767202 < baseStart_3767202 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767238 : List Nat := [6, 1, 3, 1, 1, 2, 1, 1, 6]
def baseStart_3767238 : Nat := 118140960795 + 3767238 * 2 ^ 59
def prefixEnd_3767238 : Nat := 4983230072969 + 3 ^ 40 * 3767238 * 2
def baseEnd_3767238 : Nat := 429867518640585977266621

theorem tailTrace_3767238 : CollatzResearch.WordTrace tailWord_3767238 prefixEnd_3767238 429867518640585977266621 := by
  unfold tailWord_3767238
  simp only [CollatzResearch.WordTrace]
  refine ⟨4293826810185862308511699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 91601638617298395914916245 4293826810185862308511699)
  ·
    refine ⟨6440740215278793462767549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4293826810185862308511699 6440740215278793462767549)
    ·
      refine ⟨2415277580729547548537831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6440740215278793462767549 2415277580729547548537831)
      ·
        refine ⟨3622916371094321322806747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2415277580729547548537831 3622916371094321322806747)
        ·
          refine ⟨5434374556641481984210121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3622916371094321322806747 5434374556641481984210121)
          ·
            refine ⟨4075780917481111488157591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5434374556641481984210121 4075780917481111488157591)
            ·
              refine ⟨6113671376221667232236387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4075780917481111488157591 6113671376221667232236387)
              ·
                refine ⟨9170507064332500848354581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6113671376221667232236387 9170507064332500848354581)
                ·
                  refine ⟨429867518640585977266621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9170507064332500848354581 429867518640585977266621)
                  ·
                    rfl

theorem cell22_3767238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_3767238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767238 prefixEnd_3767238 := by exact prefixLift 3767238
  have htrace : WordTrace (prefixWord ++ tailWord_3767238) baseStart_3767238 baseEnd_3767238 := by
    simpa [prefixWord, tailWord_3767238, baseEnd_3767238] using wordTrace_append hprefix tailTrace_3767238
  have hstable : (prefixWord ++ tailWord_3767238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767238).length < 2 ^ (prefixWord ++ tailWord_3767238).sum := by decide
  have hdescent : baseEnd_3767238 < baseStart_3767238 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767243 : List Nat := [1, 1, 1, 1, 3, 5, 2, 1, 7]
def baseStart_3767243 : Nat := 118140960795 + 3767243 * 2 ^ 59
def prefixEnd_3767243 : Nat := 4983230072969 + 3 ^ 40 * 3767243 * 2
def baseEnd_3767243 : Nat := 429868089174646528474949

theorem tailTrace_3767243 : CollatzResearch.WordTrace tailWord_3767243 prefixEnd_3767243 429868089174646528474949 := by
  unfold tailWord_3767243
  simp only [CollatzResearch.WordTrace]
  refine ⟨137402640290929479726306383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91601760193952986484204255 137402640290929479726306383)
  ·
    refine ⟨206103960436394219589459575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137402640290929479726306383 206103960436394219589459575)
    ·
      refine ⟨309155940654591329384189363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206103960436394219589459575 309155940654591329384189363)
      ·
        refine ⟨463733910981886994076284045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309155940654591329384189363 463733910981886994076284045)
        ·
          refine ⟨173900216618207622778606517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 463733910981886994076284045 173900216618207622778606517)
          ·
            refine ⟨16303145307956964635494361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 173900216618207622778606517 16303145307956964635494361)
            ·
              refine ⟨12227358980967723476620771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16303145307956964635494361 12227358980967723476620771)
              ·
                refine ⟨18341038471451585214931157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12227358980967723476620771 18341038471451585214931157)
                ·
                  refine ⟨429868089174646528474949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18341038471451585214931157 429868089174646528474949)
                  ·
                    rfl

theorem cell22_3767243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 1, 7].length) (baseStart_3767243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767243 prefixEnd_3767243 := by exact prefixLift 3767243
  have htrace : WordTrace (prefixWord ++ tailWord_3767243) baseStart_3767243 baseEnd_3767243 := by
    simpa [prefixWord, tailWord_3767243, baseEnd_3767243] using wordTrace_append hprefix tailTrace_3767243
  have hstable : (prefixWord ++ tailWord_3767243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767243).length < 2 ^ (prefixWord ++ tailWord_3767243).sum := by decide
  have hdescent : baseEnd_3767243 < baseStart_3767243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767247 : List Nat := [1, 1, 2, 1, 1, 8, 1, 1, 3, 3]
def baseStart_3767247 : Nat := 118140960795 + 3767247 * 2 ^ 59
def prefixEnd_3767247 : Nat := 4983230072969 + 3 ^ 40 * 3767247 * 2
def baseEnd_3767247 : Nat := 1289605636805684908324835

theorem tailTrace_3767247 : CollatzResearch.WordTrace tailWord_3767247 prefixEnd_3767247 1289605636805684908324835 := by
  unfold tailWord_3767247
  simp only [CollatzResearch.WordTrace]
  refine ⟨137402786182914988409451995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91601857455276658939634663 137402786182914988409451995)
  ·
    refine ⟨206104179274372482614177993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137402786182914988409451995 206104179274372482614177993)
    ·
      refine ⟨154578134455779361960633495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206104179274372482614177993 154578134455779361960633495)
      ·
        refine ⟨231867201683669042940950243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154578134455779361960633495 231867201683669042940950243)
        ·
          refine ⟨347800802525503564411425365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231867201683669042940950243 347800802525503564411425365)
          ·
            refine ⟨4075790654595744895446391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 347800802525503564411425365 4075790654595744895446391)
            ·
              refine ⟨6113685981893617343169587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4075790654595744895446391 6113685981893617343169587)
              ·
                refine ⟨9170528972840426014754381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6113685981893617343169587 9170528972840426014754381)
                ·
                  refine ⟨3438948364815159755532893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9170528972840426014754381 3438948364815159755532893)
                  ·
                    refine ⟨1289605636805684908324835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3438948364815159755532893 1289605636805684908324835)
                    ·
                      rfl

theorem cell22_3767247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 8, 1, 1, 3, 3].length) (baseStart_3767247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767247 prefixEnd_3767247 := by exact prefixLift 3767247
  have htrace : WordTrace (prefixWord ++ tailWord_3767247) baseStart_3767247 baseEnd_3767247 := by
    simpa [prefixWord, tailWord_3767247, baseEnd_3767247] using wordTrace_append hprefix tailTrace_3767247
  have hstable : (prefixWord ++ tailWord_3767247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767247).length < 2 ^ (prefixWord ++ tailWord_3767247).sum := by decide
  have hdescent : baseEnd_3767247 < baseStart_3767247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767290 : List Nat := [3, 1, 1, 1, 1, 2, 1, 7, 1, 4]
def baseStart_3767290 : Nat := 118140960795 + 3767290 * 2 ^ 59
def prefixEnd_3767290 : Nat := 4983230072969 + 3 ^ 40 * 3767290 * 2
def baseEnd_3767290 : Nat := 1289620356584447129499703

theorem tailTrace_3767290 : CollatzResearch.WordTrace tailWord_3767290 prefixEnd_3767290 1289620356584447129499703 := by
  unfold tailWord_3767290
  simp only [CollatzResearch.WordTrace]
  refine ⟨34351088630439801688316831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91602903014506137835511549 34351088630439801688316831)
  ·
    refine ⟨51526632945659702532475247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34351088630439801688316831 51526632945659702532475247)
    ·
      refine ⟨77289949418489553798712871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51526632945659702532475247 77289949418489553798712871)
      ·
        refine ⟨115934924127734330698069307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77289949418489553798712871 115934924127734330698069307)
        ·
          refine ⟨173902386191601496047103961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115934924127734330698069307 173902386191601496047103961)
          ·
            refine ⟨130426789643701122035327971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173902386191601496047103961 130426789643701122035327971)
            ·
              refine ⟨195640184465551683052991957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130426789643701122035327971 195640184465551683052991957)
              ·
                refine ⟨4585316823411367571554499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 195640184465551683052991957 4585316823411367571554499)
                ·
                  refine ⟨6877975235117051357331749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4585316823411367571554499 6877975235117051357331749)
                  ·
                    refine ⟨1289620356584447129499703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6877975235117051357331749 1289620356584447129499703)
                    ·
                      rfl

theorem cell22_3767290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 7, 1, 4].length) (baseStart_3767290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767290 prefixEnd_3767290 := by exact prefixLift 3767290
  have htrace : WordTrace (prefixWord ++ tailWord_3767290) baseStart_3767290 baseEnd_3767290 := by
    simpa [prefixWord, tailWord_3767290, baseEnd_3767290] using wordTrace_append hprefix tailTrace_3767290
  have hstable : (prefixWord ++ tailWord_3767290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767290).length < 2 ^ (prefixWord ++ tailWord_3767290).sum := by decide
  have hdescent : baseEnd_3767290 < baseStart_3767290 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767294 : List Nat := [4, 2, 2, 2, 2, 1, 2, 2, 5]
def baseStart_3767294 : Nat := 118140960795 + 3767294 * 2 ^ 59
def prefixEnd_3767294 : Nat := 4983230072969 + 3 ^ 40 * 3767294 * 2
def baseEnd_3767294 : Nat := 429873908622064150799897

theorem tailTrace_3767294 : CollatzResearch.WordTrace tailWord_3767294 prefixEnd_3767294 429873908622064150799897 := by
  unfold tailWord_3767294
  simp only [CollatzResearch.WordTrace]
  refine ⟨17175562551718089429551617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91603000275829810290941957 17175562551718089429551617)
  ·
    refine ⟨12881671913788567072163713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17175562551718089429551617 12881671913788567072163713)
    ·
      refine ⟨9661253935341425304122785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12881671913788567072163713 9661253935341425304122785)
      ·
        refine ⟨7245940451506068978092089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9661253935341425304122785 7245940451506068978092089)
        ·
          refine ⟨5434455338629551733569067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7245940451506068978092089 5434455338629551733569067)
          ·
            refine ⟨8151683007944327600353601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5434455338629551733569067 8151683007944327600353601)
            ·
              refine ⟨6113762255958245700265201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8151683007944327600353601 6113762255958245700265201)
              ·
                refine ⟨4585321691968684275198901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6113762255958245700265201 4585321691968684275198901)
                ·
                  refine ⟨429873908622064150799897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4585321691968684275198901 429873908622064150799897)
                  ·
                    rfl

theorem cell22_3767294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_3767294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767294 prefixEnd_3767294 := by exact prefixLift 3767294
  have htrace : WordTrace (prefixWord ++ tailWord_3767294) baseStart_3767294 baseEnd_3767294 := by
    simpa [prefixWord, tailWord_3767294, baseEnd_3767294] using wordTrace_append hprefix tailTrace_3767294
  have hstable : (prefixWord ++ tailWord_3767294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767294).length < 2 ^ (prefixWord ++ tailWord_3767294).sum := by decide
  have hdescent : baseEnd_3767294 < baseStart_3767294 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767298 : List Nat := [3, 4, 1, 3, 1, 1, 1, 4, 1, 3]
def baseStart_3767298 : Nat := 118140960795 + 3767298 * 2 ^ 59
def prefixEnd_3767298 : Nat := 4983230072969 + 3 ^ 40 * 3767298 * 2
def baseEnd_3767298 : Nat := 1289623095147937775299679

theorem tailTrace_3767298 : CollatzResearch.WordTrace tailWord_3767298 prefixEnd_3767298 1289623095147937775299679 := by
  unfold tailWord_3767298
  simp only [CollatzResearch.WordTrace]
  refine ⟨34351161576432556029889637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91603097537153482746372365 34351161576432556029889637)
  ·
    refine ⟨6440842795581104255604307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34351161576432556029889637 6440842795581104255604307)
    ·
      refine ⟨9661264193371656383406461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6440842795581104255604307 9661264193371656383406461)
      ·
        refine ⟨3622974072514371143777423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9661264193371656383406461 3622974072514371143777423)
        ·
          refine ⟨5434461108771556715666135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3622974072514371143777423 5434461108771556715666135)
          ·
            refine ⟨8151691663157335073499203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5434461108771556715666135 8151691663157335073499203)
            ·
              refine ⟨12227537494736002610248805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8151691663157335073499203 12227537494736002610248805)
              ·
                refine ⟨2292663280263000489421651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12227537494736002610248805 2292663280263000489421651)
                ·
                  refine ⟨3438994920394500734132477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2292663280263000489421651 3438994920394500734132477)
                  ·
                    refine ⟨1289623095147937775299679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3438994920394500734132477 1289623095147937775299679)
                    ·
                      rfl

theorem cell22_3767298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_3767298 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767298 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767298 prefixEnd_3767298 := by exact prefixLift 3767298
  have htrace : WordTrace (prefixWord ++ tailWord_3767298) baseStart_3767298 baseEnd_3767298 := by
    simpa [prefixWord, tailWord_3767298, baseEnd_3767298] using wordTrace_append hprefix tailTrace_3767298
  have hstable : (prefixWord ++ tailWord_3767298).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767298).length < 2 ^ (prefixWord ++ tailWord_3767298).sum := by decide
  have hdescent : baseEnd_3767298 < baseStart_3767298 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767320 : List Nat := [2, 1, 2, 3, 2, 2, 1, 3, 1, 5]
def baseStart_3767320 : Nat := 118140960795 + 3767320 * 2 ^ 59
def prefixEnd_3767320 : Nat := 4983230072969 + 3 ^ 40 * 3767320 * 2
def baseEnd_3767320 : Nat := 1289630626197537051249611

theorem tailTrace_3767320 : CollatzResearch.WordTrace tailWord_3767320 prefixEnd_3767320 1289630626197537051249611 := by
  unfold tailWord_3767320
  simp only [CollatzResearch.WordTrace]
  refine ⟨68702724355825260938429707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91603632474433681251239609 68702724355825260938429707)
  ·
    refine ⟨103054086533737891407644561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68702724355825260938429707 103054086533737891407644561)
    ·
      refine ⟨77290564900303418555733421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103054086533737891407644561 77290564900303418555733421)
      ·
        refine ⟨28983961837613781958400033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77290564900303418555733421 28983961837613781958400033)
        ·
          refine ⟨21737971378210336468800025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28983961837613781958400033 21737971378210336468800025)
          ·
            refine ⟨16303478533657752351600019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21737971378210336468800025 16303478533657752351600019)
            ·
              refine ⟨24455217800486628527400029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16303478533657752351600019 24455217800486628527400029)
              ·
                refine ⟨9170706675182485697775011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24455217800486628527400029 9170706675182485697775011)
                ·
                  refine ⟨13756060012773728546662517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9170706675182485697775011 13756060012773728546662517)
                  ·
                    refine ⟨1289630626197537051249611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13756060012773728546662517 1289630626197537051249611)
                    ·
                      rfl

theorem cell22_3767320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 3, 1, 5].length) (baseStart_3767320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767320 prefixEnd_3767320 := by exact prefixLift 3767320
  have htrace : WordTrace (prefixWord ++ tailWord_3767320) baseStart_3767320 baseEnd_3767320 := by
    simpa [prefixWord, tailWord_3767320, baseEnd_3767320] using wordTrace_append hprefix tailTrace_3767320
  have hstable : (prefixWord ++ tailWord_3767320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767320).length < 2 ^ (prefixWord ++ tailWord_3767320).sum := by decide
  have hdescent : baseEnd_3767320 < baseStart_3767320 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767380 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 2, 6]
def baseStart_3767380 : Nat := 118140960795 + 3767380 * 2 ^ 59
def prefixEnd_3767380 : Nat := 4983230072969 + 3 ^ 40 * 3767380 * 2
def baseEnd_3767380 : Nat := 1289651165423716894749427

theorem tailTrace_3767380 : CollatzResearch.WordTrace tailWord_3767380 prefixEnd_3767380 1289651165423716894749427 := by
  unfold tailWord_3767380
  simp only [CollatzResearch.WordTrace]
  refine ⟨68703818545716576062021797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91605091394288768082695729 68703818545716576062021797)
  ·
    refine ⟨12881965977321858011629087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68703818545716576062021797 12881965977321858011629087)
    ·
      refine ⟨19322948965982787017443631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12881965977321858011629087 19322948965982787017443631)
      ·
        refine ⟨28984423448974180526165447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19322948965982787017443631 28984423448974180526165447)
        ·
          refine ⟨43476635173461270789248171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28984423448974180526165447 43476635173461270789248171)
          ·
            refine ⟨65214952760191906183872257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43476635173461270789248171 65214952760191906183872257)
            ·
              refine ⟨48911214570143929637904193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65214952760191906183872257 48911214570143929637904193)
              ·
                refine ⟨36683410927607947228428145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48911214570143929637904193 36683410927607947228428145)
                ·
                  refine ⟨27512558195705960421321109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 36683410927607947228428145 27512558195705960421321109)
                  ·
                    refine ⟨1289651165423716894749427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27512558195705960421321109 1289651165423716894749427)
                    ·
                      rfl

theorem cell22_3767380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 2, 6].length) (baseStart_3767380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767380 prefixEnd_3767380 := by exact prefixLift 3767380
  have htrace : WordTrace (prefixWord ++ tailWord_3767380) baseStart_3767380 baseEnd_3767380 := by
    simpa [prefixWord, tailWord_3767380, baseEnd_3767380] using wordTrace_append hprefix tailTrace_3767380
  have hstable : (prefixWord ++ tailWord_3767380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767380).length < 2 ^ (prefixWord ++ tailWord_3767380).sum := by decide
  have hdescent : baseEnd_3767380 < baseStart_3767380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767422 : List Nat := [4, 2, 4, 1, 1, 2, 2, 1, 2, 3]
def baseStart_3767422 : Nat := 118140960795 + 3767422 * 2 ^ 59
def prefixEnd_3767422 : Nat := 4983230072969 + 3 ^ 40 * 3767422 * 2
def baseEnd_3767422 : Nat := 1289665542882042785199299

theorem tailTrace_3767422 : CollatzResearch.WordTrace tailWord_3767422 prefixEnd_3767422 1289665542882042785199299 := by
  unfold tailWord_3767422
  simp only [CollatzResearch.WordTrace]
  refine ⟨17176146119660124162134065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91606112638187328864715013 17176146119660124162134065)
  ·
    refine ⟨12882109589745093121600549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17176146119660124162134065 12882109589745093121600549)
    ·
      refine ⟨2415395548077204960300103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12882109589745093121600549 2415395548077204960300103)
      ·
        refine ⟨3623093322115807440450155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2415395548077204960300103 3623093322115807440450155)
        ·
          refine ⟨5434639983173711160675233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3623093322115807440450155 5434639983173711160675233)
          ·
            refine ⟨4075979987380283370506425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5434639983173711160675233 4075979987380283370506425)
            ·
              refine ⟨3056984990535212527879819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4075979987380283370506425 3056984990535212527879819)
              ·
                refine ⟨4585477485802818791819729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3056984990535212527879819 4585477485802818791819729)
                ·
                  refine ⟨3439108114352114093864797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4585477485802818791819729 3439108114352114093864797)
                  ·
                    refine ⟨1289665542882042785199299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3439108114352114093864797 1289665542882042785199299)
                    ·
                      rfl

theorem cell22_3767422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 2, 2, 1, 2, 3].length) (baseStart_3767422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767422 prefixEnd_3767422 := by exact prefixLift 3767422
  have htrace : WordTrace (prefixWord ++ tailWord_3767422) baseStart_3767422 baseEnd_3767422 := by
    simpa [prefixWord, tailWord_3767422, baseEnd_3767422] using wordTrace_append hprefix tailTrace_3767422
  have hstable : (prefixWord ++ tailWord_3767422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767422).length < 2 ^ (prefixWord ++ tailWord_3767422).sum := by decide
  have hdescent : baseEnd_3767422 < baseStart_3767422 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767474 : List Nat := [3, 2, 1, 1, 1, 5, 1, 4, 4]
def baseStart_3767474 : Nat := 118140960795 + 3767474 * 2 ^ 59
def prefixEnd_3767474 : Nat := 4983230072969 + 3 ^ 40 * 3767474 * 2
def baseEnd_3767474 : Nat := 429894447848243994299713

theorem tailTrace_3767474 : CollatzResearch.WordTrace tailWord_3767474 prefixEnd_3767474 429894447848243994299713 := by
  unfold tailWord_3767474
  simp only [CollatzResearch.WordTrace]
  refine ⟨34352766388273151544491369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91607377035395070785310317 34352766388273151544491369)
  ·
    refine ⟨25764574791204863658368527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34352766388273151544491369 25764574791204863658368527)
    ·
      refine ⟨38646862186807295487552791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25764574791204863658368527 38646862186807295487552791)
      ·
        refine ⟨57970293280210943231329187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38646862186807295487552791 57970293280210943231329187)
        ·
          refine ⟨86955439920316414846993781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57970293280210943231329187 86955439920316414846993781)
          ·
            refine ⟨8152072492529663891905667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86955439920316414846993781 8152072492529663891905667)
            ·
              refine ⟨12228108738794495837858501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8152072492529663891905667 12228108738794495837858501)
              ·
                refine ⟨2292770388523967969598469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12228108738794495837858501 2292770388523967969598469)
                ·
                  refine ⟨429894447848243994299713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2292770388523967969598469 429894447848243994299713)
                  ·
                    rfl

theorem cell22_3767474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_3767474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767474 prefixEnd_3767474 := by exact prefixLift 3767474
  have htrace : WordTrace (prefixWord ++ tailWord_3767474) baseStart_3767474 baseEnd_3767474 := by
    simpa [prefixWord, tailWord_3767474, baseEnd_3767474] using wordTrace_append hprefix tailTrace_3767474
  have hstable : (prefixWord ++ tailWord_3767474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767474).length < 2 ^ (prefixWord ++ tailWord_3767474).sum := by decide
  have hdescent : baseEnd_3767474 < baseStart_3767474 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767489 : List Nat := [1, 2, 6, 1, 1, 1, 1, 3, 1, 5]
def baseStart_3767489 : Nat := 118140960795 + 3767489 * 2 ^ 59
def prefixEnd_3767489 : Nat := 4983230072969 + 3 ^ 40 * 3767489 * 2
def baseEnd_3767489 : Nat := 1289688478351276943774093

theorem tailTrace_3767489 : CollatzResearch.WordTrace tailWord_3767489 prefixEnd_3767489 1289688478351276943774093 := by
  unfold tailWord_3767489
  simp only [CollatzResearch.WordTrace]
  refine ⟨137411612648038263739761521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91607741765358842493174347 137411612648038263739761521)
  ·
    refine ⟨103058709486028697804821141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137411612648038263739761521 103058709486028697804821141)
    ·
      refine ⟨4830877007157595209600991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 103058709486028697804821141 4830877007157595209600991)
      ·
        refine ⟨7246315510736392814401487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4830877007157595209600991 7246315510736392814401487)
        ·
          refine ⟨10869473266104589221602231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7246315510736392814401487 10869473266104589221602231)
          ·
            refine ⟨16304209899156883832403347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10869473266104589221602231 16304209899156883832403347)
            ·
              refine ⟨24456314848735325748605021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16304209899156883832403347 24456314848735325748605021)
              ·
                refine ⟨9171118068275747155726883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24456314848735325748605021 9171118068275747155726883)
                ·
                  refine ⟨13756677102413620733590325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9171118068275747155726883 13756677102413620733590325)
                  ·
                    refine ⟨1289688478351276943774093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13756677102413620733590325 1289688478351276943774093)
                    ·
                      rfl

theorem cell22_3767489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_3767489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767489 prefixEnd_3767489 := by exact prefixLift 3767489
  have htrace : WordTrace (prefixWord ++ tailWord_3767489) baseStart_3767489 baseEnd_3767489 := by
    simpa [prefixWord, tailWord_3767489, baseEnd_3767489] using wordTrace_append hprefix tailTrace_3767489
  have hstable : (prefixWord ++ tailWord_3767489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767489).length < 2 ^ (prefixWord ++ tailWord_3767489).sum := by decide
  have hdescent : baseEnd_3767489 < baseStart_3767489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767508 : List Nat := [2, 4, 1, 4, 1, 1, 2, 3, 4]
def baseStart_3767508 : Nat := 118140960795 + 3767508 * 2 ^ 59
def prefixEnd_3767508 : Nat := 4983230072969 + 3 ^ 40 * 3767508 * 2
def baseEnd_3767508 : Nat := 429898327479855742516345

theorem tailTrace_3767508 : CollatzResearch.WordTrace tailWord_3767508 prefixEnd_3767508 429898327479855742516345 := by
  unfold tailWord_3767508
  simp only [CollatzResearch.WordTrace]
  refine ⟨68706152817484714992351589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91608203756646286656468785 68706152817484714992351589)
  ·
    refine ⟨12882403653278384061065923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68706152817484714992351589 12882403653278384061065923)
    ·
      refine ⟨19323605479917576091598885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12882403653278384061065923 19323605479917576091598885)
      ·
        refine ⟨3623176027484545517174791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19323605479917576091598885 3623176027484545517174791)
        ·
          refine ⟨5434764041226818275762187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3623176027484545517174791 5434764041226818275762187)
          ·
            refine ⟨8152146061840227413643281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5434764041226818275762187 8152146061840227413643281)
            ·
              refine ⟨6114109546380170560232461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8152146061840227413643281 6114109546380170560232461)
              ·
                refine ⟨2292791079892563960087173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6114109546380170560232461 2292791079892563960087173)
                ·
                  refine ⟨429898327479855742516345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2292791079892563960087173 429898327479855742516345)
                  ·
                    rfl

theorem cell22_3767508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_3767508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767508 prefixEnd_3767508 := by exact prefixLift 3767508
  have htrace : WordTrace (prefixWord ++ tailWord_3767508) baseStart_3767508 baseEnd_3767508 := by
    simpa [prefixWord, tailWord_3767508, baseEnd_3767508] using wordTrace_append hprefix tailTrace_3767508
  have hstable : (prefixWord ++ tailWord_3767508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767508).length < 2 ^ (prefixWord ++ tailWord_3767508).sum := by decide
  have hdescent : baseEnd_3767508 < baseStart_3767508 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767510 : List Nat := [5, 2, 1, 2, 2, 2, 2, 1, 1, 4]
def baseStart_3767510 : Nat := 118140960795 + 3767510 * 2 ^ 59
def prefixEnd_3767510 : Nat := 4983230072969 + 3 ^ 40 * 3767510 * 2
def baseEnd_3767510 : Nat := 1289695667080439888999029

theorem tailTrace_3767510 : CollatzResearch.WordTrace tailWord_3767510 prefixEnd_3767510 1289695667080439888999029 := by
  unfold tailWord_3767510
  simp only [CollatzResearch.WordTrace]
  refine ⟨8588273661310136520392249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 91608252387308122884183989 8588273661310136520392249)
  ·
    refine ⟨6441205245982602390294187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8588273661310136520392249 6441205245982602390294187)
    ·
      refine ⟨9661807868973903585441281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6441205245982602390294187 9661807868973903585441281)
      ·
        refine ⟨7246355901730427689080961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9661807868973903585441281 7246355901730427689080961)
        ·
          refine ⟨5434766926297820766810721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7246355901730427689080961 5434766926297820766810721)
          ·
            refine ⟨4076075194723365575108041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5434766926297820766810721 4076075194723365575108041)
            ·
              refine ⟨3057056396042524181331031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4076075194723365575108041 3057056396042524181331031)
              ·
                refine ⟨4585584594063786271996547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3057056396042524181331031 4585584594063786271996547)
                ·
                  refine ⟨6878376891095679407994821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4585584594063786271996547 6878376891095679407994821)
                  ·
                    refine ⟨1289695667080439888999029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6878376891095679407994821 1289695667080439888999029)
                    ·
                      rfl

theorem cell22_3767510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_3767510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767510 prefixEnd_3767510 := by exact prefixLift 3767510
  have htrace : WordTrace (prefixWord ++ tailWord_3767510) baseStart_3767510 baseEnd_3767510 := by
    simpa [prefixWord, tailWord_3767510, baseEnd_3767510] using wordTrace_append hprefix tailTrace_3767510
  have hstable : (prefixWord ++ tailWord_3767510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767510).length < 2 ^ (prefixWord ++ tailWord_3767510).sum := by decide
  have hdescent : baseEnd_3767510 < baseStart_3767510 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767534 : List Nat := [4, 1, 2, 1, 1, 1, 3, 3, 3, 3]
def baseStart_3767534 : Nat := 118140960795 + 3767534 * 2 ^ 59
def prefixEnd_3767534 : Nat := 4983230072969 + 3 ^ 40 * 3767534 * 2
def baseEnd_3767534 : Nat := 1289703882770911826398955

theorem tailTrace_3767534 : CollatzResearch.WordTrace tailWord_3767534 prefixEnd_3767534 1289703882770911826398955 := by
  unfold tailWord_3767534
  simp only [CollatzResearch.WordTrace]
  refine ⟨17176656741609404553143707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91608835955250157616766437 17176656741609404553143707)
  ·
    refine ⟨25764985112414106829715561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17176656741609404553143707 25764985112414106829715561)
    ·
      refine ⟨19323738834310580122286671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25764985112414106829715561 19323738834310580122286671)
      ·
        refine ⟨28985608251465870183430007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19323738834310580122286671 28985608251465870183430007)
        ·
          refine ⟨43478412377198805275145011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28985608251465870183430007 43478412377198805275145011)
          ·
            refine ⟨65217618565798207912717517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43478412377198805275145011 65217618565798207912717517)
            ·
              refine ⟨24456606962174327967269069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65217618565798207912717517 24456606962174327967269069)
              ·
                refine ⟨9171227610815372987725901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24456606962174327967269069 9171227610815372987725901)
                ·
                  refine ⟨3439210354055764870397213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9171227610815372987725901 3439210354055764870397213)
                  ·
                    refine ⟨1289703882770911826398955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3439210354055764870397213 1289703882770911826398955)
                    ·
                      rfl

theorem cell22_3767534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_3767534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767534 prefixEnd_3767534 := by exact prefixLift 3767534
  have htrace : WordTrace (prefixWord ++ tailWord_3767534) baseStart_3767534 baseEnd_3767534 := by
    simpa [prefixWord, tailWord_3767534, baseEnd_3767534] using wordTrace_append hprefix tailTrace_3767534
  have hstable : (prefixWord ++ tailWord_3767534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767534).length < 2 ^ (prefixWord ++ tailWord_3767534).sum := by decide
  have hdescent : baseEnd_3767534 < baseStart_3767534 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767540 : List Nat := [2, 6, 1, 2, 1, 2, 1, 1, 1, 5]
def baseStart_3767540 : Nat := 118140960795 + 3767540 * 2 ^ 59
def prefixEnd_3767540 : Nat := 4983230072969 + 3 ^ 40 * 3767540 * 2
def baseEnd_3767540 : Nat := 1289705936693529810748937

theorem tailTrace_3767540 : CollatzResearch.WordTrace tailWord_3767540 prefixEnd_3767540 1289705936693529810748937 := by
  unfold tailWord_3767540
  simp only [CollatzResearch.WordTrace]
  refine ⟨68706736385426749724934037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91608981847235666299912049 68706736385426749724934037)
  ·
    refine ⟨3220628268066878893356283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68706736385426749724934037 3220628268066878893356283)
    ·
      refine ⟨4830942402100318340034425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3220628268066878893356283 4830942402100318340034425)
      ·
        refine ⟨3623206801575238755025819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4830942402100318340034425 3623206801575238755025819)
        ·
          refine ⟨5434810202362858132538729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3623206801575238755025819 5434810202362858132538729)
          ·
            refine ⟨4076107651772143599404047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5434810202362858132538729 4076107651772143599404047)
            ·
              refine ⟨6114161477658215399106071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4076107651772143599404047 6114161477658215399106071)
              ·
                refine ⟨9171242216487323098659107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6114161477658215399106071 9171242216487323098659107)
                ·
                  refine ⟨13756863324730984647988661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9171242216487323098659107 13756863324730984647988661)
                  ·
                    refine ⟨1289705936693529810748937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13756863324730984647988661 1289705936693529810748937)
                    ·
                      rfl

theorem cell22_3767540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_3767540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767540 prefixEnd_3767540 := by exact prefixLift 3767540
  have htrace : WordTrace (prefixWord ++ tailWord_3767540) baseStart_3767540 baseEnd_3767540 := by
    simpa [prefixWord, tailWord_3767540, baseEnd_3767540] using wordTrace_append hprefix tailTrace_3767540
  have hstable : (prefixWord ++ tailWord_3767540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767540).length < 2 ^ (prefixWord ++ tailWord_3767540).sum := by decide
  have hdescent : baseEnd_3767540 < baseStart_3767540 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767637 : List Nat := [1, 3, 2, 2, 3, 11]
def baseStart_3767637 : Nat := 118140960795 + 3767637 * 2 ^ 59
def prefixEnd_3767637 : Nat := 4983230072969 + 3 ^ 40 * 3767637 * 2
def baseEnd_3767637 : Nat := 15922705454022887544119

theorem tailTrace_3767637 : CollatzResearch.WordTrace tailWord_3767637 prefixEnd_3767637 15922705454022887544119 := by
  unfold tailWord_3767637
  simp only [CollatzResearch.WordTrace]
  refine ⟨137417010651502085016149165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91611340434334723344099443 137417010651502085016149165)
  ·
    refine ⟨51531378994313281881055937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137417010651502085016149165 51531378994313281881055937)
    ·
      refine ⟨38648534245734961410791953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51531378994313281881055937 38648534245734961410791953)
      ·
        refine ⟨28986400684301221058093965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38648534245734961410791953 28986400684301221058093965)
        ·
          refine ⟨10869900256612957896785237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28986400684301221058093965 10869900256612957896785237)
          ·
            refine ⟨15922705454022887544119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10869900256612957896785237 15922705454022887544119)
            ·
              rfl

theorem cell22_3767637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 11].length) (baseStart_3767637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767637 prefixEnd_3767637 := by exact prefixLift 3767637
  have htrace : WordTrace (prefixWord ++ tailWord_3767637) baseStart_3767637 baseEnd_3767637 := by
    simpa [prefixWord, tailWord_3767637, baseEnd_3767637] using wordTrace_append hprefix tailTrace_3767637
  have hstable : (prefixWord ++ tailWord_3767637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767637).length < 2 ^ (prefixWord ++ tailWord_3767637).sum := by decide
  have hdescent : baseEnd_3767637 < baseStart_3767637 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767639 : List Nat := [1, 1, 3, 2, 3, 2, 2, 2, 2, 4]
def baseStart_3767639 : Nat := 118140960795 + 3767639 * 2 ^ 59
def prefixEnd_3767639 : Nat := 4983230072969 + 3 ^ 40 * 3767639 * 2
def baseEnd_3767639 : Nat := 1289739826416726552523633

theorem tailTrace_3767639 : CollatzResearch.WordTrace tailWord_3767639 prefixEnd_3767639 1289739826416726552523633 := by
  unfold tailWord_3767639
  simp only [CollatzResearch.WordTrace]
  refine ⟨137417083597494839357721971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91611389064996559571814647 137417083597494839357721971)
  ·
    refine ⟨206125625396242259036582957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137417083597494839357721971 206125625396242259036582957)
    ·
      refine ⟨77297109523590847138718609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 206125625396242259036582957 77297109523590847138718609)
      ·
        refine ⟨57972832142693135354038957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77297109523590847138718609 57972832142693135354038957)
        ·
          refine ⟨21739812053509925757764609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57972832142693135354038957 21739812053509925757764609)
          ·
            refine ⟨16304859040132444318323457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21739812053509925757764609 16304859040132444318323457)
            ·
              refine ⟨12228644280099333238742593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16304859040132444318323457 12228644280099333238742593)
              ·
                refine ⟨9171483210074499929056945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12228644280099333238742593 9171483210074499929056945)
                ·
                  refine ⟨6878612407555874946792709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9171483210074499929056945 6878612407555874946792709)
                  ·
                    refine ⟨1289739826416726552523633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6878612407555874946792709 1289739826416726552523633)
                    ·
                      rfl

theorem cell22_3767639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_3767639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767639 prefixEnd_3767639 := by exact prefixLift 3767639
  have htrace : WordTrace (prefixWord ++ tailWord_3767639) baseStart_3767639 baseEnd_3767639 := by
    simpa [prefixWord, tailWord_3767639, baseEnd_3767639] using wordTrace_append hprefix tailTrace_3767639
  have hstable : (prefixWord ++ tailWord_3767639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767639).length < 2 ^ (prefixWord ++ tailWord_3767639).sum := by decide
  have hdescent : baseEnd_3767639 < baseStart_3767639 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767697 : List Nat := [1, 2, 2, 1, 1, 1, 2, 2, 3, 7]
def baseStart_3767697 : Nat := 118140960795 + 3767697 * 2 ^ 59
def prefixEnd_3767697 : Nat := 4983230072969 + 3 ^ 40 * 3767697 * 2
def baseEnd_3767697 : Nat := 1289759681002033734573455

theorem tailTrace_3767697 : CollatzResearch.WordTrace tailWord_3767697 prefixEnd_3767697 1289759681002033734573455 := by
  unfold tailWord_3767697
  simp only [CollatzResearch.WordTrace]
  refine ⟨137419199031284715263333345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91612799354189810175555563 137419199031284715263333345)
  ·
    refine ⟨103064399273463536447500009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137419199031284715263333345 103064399273463536447500009)
    ·
      refine ⟨77298299455097652335625007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103064399273463536447500009 77298299455097652335625007)
      ·
        refine ⟨115947449182646478503437511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77298299455097652335625007 115947449182646478503437511)
        ·
          refine ⟨173921173773969717755156267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115947449182646478503437511 173921173773969717755156267)
          ·
            refine ⟨260881760660954576632734401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173921173773969717755156267 260881760660954576632734401)
            ·
              refine ⟨195661320495715932474550801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260881760660954576632734401 195661320495715932474550801)
              ·
                refine ⟨146745990371786949355913101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195661320495715932474550801 146745990371786949355913101)
                ·
                  refine ⟨55029746389420106008467413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 146745990371786949355913101 55029746389420106008467413)
                  ·
                    refine ⟨1289759681002033734573455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55029746389420106008467413 1289759681002033734573455)
                    ·
                      rfl

theorem cell22_3767697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_3767697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767697 prefixEnd_3767697 := by exact prefixLift 3767697
  have htrace : WordTrace (prefixWord ++ tailWord_3767697) baseStart_3767697 baseEnd_3767697 := by
    simpa [prefixWord, tailWord_3767697, baseEnd_3767697] using wordTrace_append hprefix tailTrace_3767697
  have hstable : (prefixWord ++ tailWord_3767697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767697).length < 2 ^ (prefixWord ++ tailWord_3767697).sum := by decide
  have hdescent : baseEnd_3767697 < baseStart_3767697 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767737 : List Nat := [1, 2, 1, 4, 5, 1, 1, 3, 1, 3]
def baseStart_3767737 : Nat := 118140960795 + 3767737 * 2 ^ 59
def prefixEnd_3767737 : Nat := 4983230072969 + 3 ^ 40 * 3767737 * 2
def baseEnd_3767737 : Nat := 1289773373819486963573333

theorem tailTrace_3767737 : CollatzResearch.WordTrace tailWord_3767737 prefixEnd_3767737 1289773373819486963573333 := by
  unfold tailWord_3767737
  simp only [CollatzResearch.WordTrace]
  refine ⟨137420657951139802094789465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91613771967426534729859643 137420657951139802094789465)
  ·
    refine ⟨103065493463354851571092099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137420657951139802094789465 103065493463354851571092099)
    ·
      refine ⟨154598240195032277356638149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103065493463354851571092099 154598240195032277356638149)
      ·
        refine ⟨28987170036568552004369653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 154598240195032277356638149 28987170036568552004369653)
        ·
          refine ⟨2717547190928301750409655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 28987170036568552004369653 2717547190928301750409655)
          ·
            refine ⟨4076320786392452625614483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2717547190928301750409655 4076320786392452625614483)
            ·
              refine ⟨6114481179588678938421725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4076320786392452625614483 6114481179588678938421725)
              ·
                refine ⟨2292930442345754601908147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6114481179588678938421725 2292930442345754601908147)
                ·
                  refine ⟨3439395663518631902862221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2292930442345754601908147 3439395663518631902862221)
                  ·
                    refine ⟨1289773373819486963573333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3439395663518631902862221 1289773373819486963573333)
                    ·
                      rfl

theorem cell22_3767737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 1, 3].length) (baseStart_3767737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767737 prefixEnd_3767737 := by exact prefixLift 3767737
  have htrace : WordTrace (prefixWord ++ tailWord_3767737) baseStart_3767737 baseEnd_3767737 := by
    simpa [prefixWord, tailWord_3767737, baseEnd_3767737] using wordTrace_append hprefix tailTrace_3767737
  have hstable : (prefixWord ++ tailWord_3767737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767737).length < 2 ^ (prefixWord ++ tailWord_3767737).sum := by decide
  have hdescent : baseEnd_3767737 < baseStart_3767737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767806 : List Nat := [4, 2, 2, 3, 11]
def baseStart_3767806 : Nat := 118140960795 + 3767806 * 2 ^ 59
def prefixEnd_3767806 : Nat := 4983230072969 + 3 ^ 40 * 3767806 * 2
def baseEnd_3767806 : Nat := 5307806559381044376947

theorem tailTrace_3767806 : CollatzResearch.WordTrace tailWord_3767806 prefixEnd_3767806 5307806559381044376947 := by
  unfold tailWord_3767806
  simp only [CollatzResearch.WordTrace]
  refine ⟨17177896823486228359881409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91615449725259884586034181 17177896823486228359881409)
  ·
    refine ⟨12883422617614671269911057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17177896823486228359881409 12883422617614671269911057)
    ·
      refine ⟨9662566963211003452433293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12883422617614671269911057 9662566963211003452433293)
      ·
        refine ⟨3623462611204126294662485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9662566963211003452433293 3623462611204126294662485)
        ·
          refine ⟨5307806559381044376947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3623462611204126294662485 5307806559381044376947)
          ·
            rfl

theorem cell22_3767806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 11].length) (baseStart_3767806 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767806 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767806 prefixEnd_3767806 := by exact prefixLift 3767806
  have htrace : WordTrace (prefixWord ++ tailWord_3767806) baseStart_3767806 baseEnd_3767806 := by
    simpa [prefixWord, tailWord_3767806, baseEnd_3767806] using wordTrace_append hprefix tailTrace_3767806
  have hstable : (prefixWord ++ tailWord_3767806).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767806).length < 2 ^ (prefixWord ++ tailWord_3767806).sum := by decide
  have hdescent : baseEnd_3767806 < baseStart_3767806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767810 : List Nat := [3, 4, 1, 2, 1, 1, 1, 4, 2, 3]
def baseStart_3767810 : Nat := 118140960795 + 3767810 * 2 ^ 59
def prefixEnd_3767810 : Nat := 4983230072969 + 3 ^ 40 * 3767810 * 2
def baseEnd_3767810 : Nat := 1289798363211339106498109

theorem tailTrace_3767810 : CollatzResearch.WordTrace tailWord_3767810 prefixEnd_3767810 1289798363211339106498109 := by
  unfold tailWord_3767810
  simp only [CollatzResearch.WordTrace]
  refine ⟨34355830119968833890549221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91615546986583557041464589 34355830119968833890549221)
  ·
    refine ⟨6441718147494156354477979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34355830119968833890549221 6441718147494156354477979)
    ·
      refine ⟨9662577221241234531716969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6441718147494156354477979 9662577221241234531716969)
      ·
        refine ⟨7246932915930925898787727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9662577221241234531716969 7246932915930925898787727)
        ·
          refine ⟨10870399373896388848181591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7246932915930925898787727 10870399373896388848181591)
          ·
            refine ⟨16305599060844583272272387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10870399373896388848181591 16305599060844583272272387)
            ·
              refine ⟨24458398591266874908408581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16305599060844583272272387 24458398591266874908408581)
              ·
                refine ⟨4585949735862539045326609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24458398591266874908408581 4585949735862539045326609)
                ·
                  refine ⟨3439462301896904283994957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4585949735862539045326609 3439462301896904283994957)
                  ·
                    refine ⟨1289798363211339106498109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3439462301896904283994957 1289798363211339106498109)
                    ·
                      rfl

theorem cell22_3767810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_3767810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767810 prefixEnd_3767810 := by exact prefixLift 3767810
  have htrace : WordTrace (prefixWord ++ tailWord_3767810) baseStart_3767810 baseEnd_3767810 := by
    simpa [prefixWord, tailWord_3767810, baseEnd_3767810] using wordTrace_append hprefix tailTrace_3767810
  have hstable : (prefixWord ++ tailWord_3767810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767810).length < 2 ^ (prefixWord ++ tailWord_3767810).sum := by decide
  have hdescent : baseEnd_3767810 < baseStart_3767810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767812 : List Nat := [2, 3, 2, 3, 2, 2, 2, 2, 4]
def baseStart_3767812 : Nat := 118140960795 + 3767812 * 2 ^ 59
def prefixEnd_3767812 : Nat := 4983230072969 + 3 ^ 40 * 3767812 * 2
def baseEnd_3767812 : Nat := 429933015950737255982701

theorem tailTrace_3767812 : CollatzResearch.WordTrace tailWord_3767812 prefixEnd_3767812 429933015950737255982701 := by
  unfold tailWord_3767812
  simp only [CollatzResearch.WordTrace]
  refine ⟨68711696712934044951884845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91615595617245393269179793 68711696712934044951884845)
  ·
    refine ⟨25766886267350266856956817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68711696712934044951884845 25766886267350266856956817)
    ·
      refine ⟨19325164700512700142717613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25766886267350266856956817 19325164700512700142717613)
      ·
        refine ⟨7246936762692262553519105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19325164700512700142717613 7246936762692262553519105)
        ·
          refine ⟨5435202572019196915139329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7246936762692262553519105 5435202572019196915139329)
          ·
            refine ⟨4076401929014397686354497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5435202572019196915139329 4076401929014397686354497)
            ·
              refine ⟨3057301446760798264765873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4076401929014397686354497 3057301446760798264765873)
              ·
                refine ⟨2292976085070598698574405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3057301446760798264765873 2292976085070598698574405)
                ·
                  refine ⟨429933015950737255982701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2292976085070598698574405 429933015950737255982701)
                  ·
                    rfl

theorem cell22_3767812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_3767812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767812 prefixEnd_3767812 := by exact prefixLift 3767812
  have htrace : WordTrace (prefixWord ++ tailWord_3767812) baseStart_3767812 baseEnd_3767812 := by
    simpa [prefixWord, tailWord_3767812, baseEnd_3767812] using wordTrace_append hprefix tailTrace_3767812
  have hstable : (prefixWord ++ tailWord_3767812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767812).length < 2 ^ (prefixWord ++ tailWord_3767812).sum := by decide
  have hdescent : baseEnd_3767812 < baseStart_3767812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767834 : List Nat := [3, 1, 1, 3, 1, 1, 1, 2, 9]
def baseStart_3767834 : Nat := 118140960795 + 3767834 * 2 ^ 59
def prefixEnd_3767834 : Nat := 4983230072969 + 3 ^ 40 * 3767834 * 2
def baseEnd_3767834 : Nat := 429935526300603681299345

theorem tailTrace_3767834 : CollatzResearch.WordTrace tailWord_3767834 prefixEnd_3767834 429935526300603681299345 := by
  unfold tailWord_3767834
  simp only [CollatzResearch.WordTrace]
  refine ⟨34356048957947096915267639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91616130554525591774047037 34356048957947096915267639)
  ·
    refine ⟨51534073436920645372901459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34356048957947096915267639 51534073436920645372901459)
    ·
      refine ⟨77301110155380968059352189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51534073436920645372901459 77301110155380968059352189)
      ·
        refine ⟨28987916308267863022257071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77301110155380968059352189 28987916308267863022257071)
        ·
          refine ⟨43481874462401794533385607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28987916308267863022257071 43481874462401794533385607)
          ·
            refine ⟨65222811693602691800078411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43481874462401794533385607 65222811693602691800078411)
            ·
              refine ⟨97834217540404037700117617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65222811693602691800078411 97834217540404037700117617)
              ·
                refine ⟨73375663155303028275088213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 97834217540404037700117617 73375663155303028275088213)
                ·
                  refine ⟨429935526300603681299345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73375663155303028275088213 429935526300603681299345)
                  ·
                    rfl

theorem cell22_3767834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 2, 9].length) (baseStart_3767834 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767834 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767834 prefixEnd_3767834 := by exact prefixLift 3767834
  have htrace : WordTrace (prefixWord ++ tailWord_3767834) baseStart_3767834 baseEnd_3767834 := by
    simpa [prefixWord, tailWord_3767834, baseEnd_3767834] using wordTrace_append hprefix tailTrace_3767834
  have hstable : (prefixWord ++ tailWord_3767834).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767834).length < 2 ^ (prefixWord ++ tailWord_3767834).sum := by decide
  have hdescent : baseEnd_3767834 < baseStart_3767834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767911 : List Nat := [1, 1, 5, 1, 1, 1, 2, 4, 1, 5]
def baseStart_3767911 : Nat := 118140960795 + 3767911 * 2 ^ 59
def prefixEnd_3767911 : Nat := 4983230072969 + 3 ^ 40 * 3767911 * 2
def baseEnd_3767911 : Nat := 1289832937575408509722799

theorem tailTrace_3767911 : CollatzResearch.WordTrace tailWord_3767911 prefixEnd_3767911 1289832937575408509722799 := by
  unfold tailWord_3767911
  simp only [CollatzResearch.WordTrace]
  refine ⟨137427004252509429811623587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91618002835006286541082391 137427004252509429811623587)
  ·
    refine ⟨206140506378764144717435381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137427004252509429811623587 206140506378764144717435381)
    ·
      refine ⟨19325672473009138567259567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 206140506378764144717435381 19325672473009138567259567)
      ·
        refine ⟨28988508709513707850889351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19325672473009138567259567 28988508709513707850889351)
        ·
          refine ⟨43482763064270561776334027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28988508709513707850889351 43482763064270561776334027)
          ·
            refine ⟨65224144596405842664501041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43482763064270561776334027 65224144596405842664501041)
            ·
              refine ⟨48918108447304381998375781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65224144596405842664501041 48918108447304381998375781)
              ·
                refine ⟨9172145333869571624695459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48918108447304381998375781 9172145333869571624695459)
                ·
                  refine ⟨13758218000804357437043189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9172145333869571624695459 13758218000804357437043189)
                  ·
                    refine ⟨1289832937575408509722799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13758218000804357437043189 1289832937575408509722799)
                    ·
                      rfl

theorem cell22_3767911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_3767911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767911 prefixEnd_3767911 := by exact prefixLift 3767911
  have htrace : WordTrace (prefixWord ++ tailWord_3767911) baseStart_3767911 baseEnd_3767911 := by
    simpa [prefixWord, tailWord_3767911, baseEnd_3767911] using wordTrace_append hprefix tailTrace_3767911
  have hstable : (prefixWord ++ tailWord_3767911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767911).length < 2 ^ (prefixWord ++ tailWord_3767911).sum := by decide
  have hdescent : baseEnd_3767911 < baseStart_3767911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767913 : List Nat := [1, 2, 1, 1, 1, 4, 5, 3, 4]
def baseStart_3767913 : Nat := 118140960795 + 3767913 * 2 ^ 59
def prefixEnd_3767913 : Nat := 4983230072969 + 3 ^ 40 * 3767913 * 2
def baseEnd_3767913 : Nat := 429944540738760390390931

theorem tailTrace_3767913 : CollatzResearch.WordTrace tailWord_3767913 prefixEnd_3767913 429944540738760390390931 := by
  unfold tailWord_3767913
  simp only [CollatzResearch.WordTrace]
  refine ⟨137427077198502184153196393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91618051465668122768797595 137427077198502184153196393)
  ·
    refine ⟨103070307898876638114897295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137427077198502184153196393 103070307898876638114897295)
    ·
      refine ⟨154605461848314957172345943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103070307898876638114897295 154605461848314957172345943)
      ·
        refine ⟨231908192772472435758518915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154605461848314957172345943 231908192772472435758518915)
        ·
          refine ⟨347862289158708653637778373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231908192772472435758518915 347862289158708653637778373)
          ·
            refine ⟨65224179217257872557083445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 347862289158708653637778373 65224179217257872557083445)
            ·
              refine ⟨6114766801617925552226573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65224179217257872557083445 6114766801617925552226573)
              ·
                refine ⟨2293037550606722082084965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6114766801617925552226573 2293037550606722082084965)
                ·
                  refine ⟨429944540738760390390931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2293037550606722082084965 429944540738760390390931)
                  ·
                    rfl

theorem cell22_3767913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 4].length) (baseStart_3767913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767913 prefixEnd_3767913 := by exact prefixLift 3767913
  have htrace : WordTrace (prefixWord ++ tailWord_3767913) baseStart_3767913 baseEnd_3767913 := by
    simpa [prefixWord, tailWord_3767913, baseEnd_3767913] using wordTrace_append hprefix tailTrace_3767913
  have hstable : (prefixWord ++ tailWord_3767913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767913).length < 2 ^ (prefixWord ++ tailWord_3767913).sum := by decide
  have hdescent : baseEnd_3767913 < baseStart_3767913 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767941 : List Nat := [1, 3, 1, 1, 4, 1, 4, 7]
def baseStart_3767941 : Nat := 118140960795 + 3767941 * 2 ^ 59
def prefixEnd_3767941 : Nat := 4983230072969 + 3 ^ 40 * 3767941 * 2
def baseEnd_3767941 : Nat := 143315911909833159052523

theorem tailTrace_3767941 : CollatzResearch.WordTrace tailWord_3767941 prefixEnd_3767941 143315911909833159052523 := by
  unfold tailWord_3767941
  simp only [CollatzResearch.WordTrace]
  refine ⟨137428098442400744935215677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91618732294933829956810451 137428098442400744935215677)
  ·
    refine ⟨51535536915900279350705879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137428098442400744935215677 51535536915900279350705879)
    ·
      refine ⟨77303305373850419026058819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51535536915900279350705879 77303305373850419026058819)
      ·
        refine ⟨115954958060775628539088229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77303305373850419026058819 115954958060775628539088229)
        ·
          refine ⟨21741554636395430351079043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115954958060775628539088229 21741554636395430351079043)
          ·
            refine ⟨32612331954593145526618565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21741554636395430351079043 32612331954593145526618565)
            ·
              refine ⟨6114812241486214786240981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32612331954593145526618565 6114812241486214786240981)
              ·
                refine ⟨143315911909833159052523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6114812241486214786240981 143315911909833159052523)
                ·
                  rfl

theorem cell22_3767941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 4, 7].length) (baseStart_3767941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767941 prefixEnd_3767941 := by exact prefixLift 3767941
  have htrace : WordTrace (prefixWord ++ tailWord_3767941) baseStart_3767941 baseEnd_3767941 := by
    simpa [prefixWord, tailWord_3767941, baseEnd_3767941] using wordTrace_append hprefix tailTrace_3767941
  have hstable : (prefixWord ++ tailWord_3767941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767941).length < 2 ^ (prefixWord ++ tailWord_3767941).sum := by decide
  have hdescent : baseEnd_3767941 < baseStart_3767941 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767945 : List Nat := [1, 2, 1, 1, 4, 1, 6, 1, 2, 3]
def baseStart_3767945 : Nat := 118140960795 + 3767945 * 2 ^ 59
def prefixEnd_3767945 : Nat := 4983230072969 + 3 ^ 40 * 3767945 * 2
def baseEnd_3767945 : Nat := 1289844576470243754372695

theorem tailTrace_3767945 : CollatzResearch.WordTrace tailWord_3767945 prefixEnd_3767945 1289844576470243754372695 := by
  unfold tailWord_3767945
  simp only [CollatzResearch.WordTrace]
  refine ⟨137428244334386253618361289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91618829556257502412240859 137428244334386253618361289)
  ·
    refine ⟨103071183250789690213770967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137428244334386253618361289 103071183250789690213770967)
    ·
      refine ⟨154606774876184535320656451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103071183250789690213770967 154606774876184535320656451)
      ·
        refine ⟨231910162314276802980984677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154606774876184535320656451 231910162314276802980984677)
        ·
          refine ⟨43483155433926900558934627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 231910162314276802980984677 43483155433926900558934627)
          ·
            refine ⟨65224733150890350838401941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43483155433926900558934627 65224733150890350838401941)
            ·
              refine ⟨3057409366447985195550091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 65224733150890350838401941 3057409366447985195550091)
              ·
                refine ⟨4586114049671977793325137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3057409366447985195550091 4586114049671977793325137)
                ·
                  refine ⟨3439585537253983344993853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4586114049671977793325137 3439585537253983344993853)
                  ·
                    refine ⟨1289844576470243754372695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3439585537253983344993853 1289844576470243754372695)
                    ·
                      rfl

theorem cell22_3767945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 6, 1, 2, 3].length) (baseStart_3767945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767945 prefixEnd_3767945 := by exact prefixLift 3767945
  have htrace : WordTrace (prefixWord ++ tailWord_3767945) baseStart_3767945 baseEnd_3767945 := by
    simpa [prefixWord, tailWord_3767945, baseEnd_3767945] using wordTrace_append hprefix tailTrace_3767945
  have hstable : (prefixWord ++ tailWord_3767945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767945).length < 2 ^ (prefixWord ++ tailWord_3767945).sum := by decide
  have hdescent : baseEnd_3767945 < baseStart_3767945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3767986 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 7]
def baseStart_3767986 : Nat := 118140960795 + 3767986 * 2 ^ 59
def prefixEnd_3767986 : Nat := 4983230072969 + 3 ^ 40 * 3767986 * 2
def baseEnd_3767986 : Nat := 429952870536044438032523

theorem tailTrace_3767986 : CollatzResearch.WordTrace tailWord_3767986 prefixEnd_3767986 429952870536044438032523 := by
  unfold tailWord_3767986
  simp only [CollatzResearch.WordTrace]
  refine ⟨34357434931809429405150953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91619826484825145080402541 34357434931809429405150953)
  ·
    refine ⟨25768076198857072053863215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34357434931809429405150953 25768076198857072053863215)
    ·
      refine ⟨38652114298285608080794823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25768076198857072053863215 38652114298285608080794823)
      ·
        refine ⟨57978171447428412121192235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38652114298285608080794823 57978171447428412121192235)
        ·
          refine ⟨86967257171142618181788353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57978171447428412121192235 86967257171142618181788353)
          ·
            refine ⟨65225442878356963636341265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86967257171142618181788353 65225442878356963636341265)
            ·
              refine ⟨48919082158767722727255949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65225442878356963636341265 48919082158767722727255949)
              ·
                refine ⟨18344655809537896022720981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 48919082158767722727255949 18344655809537896022720981)
                ·
                  refine ⟨429952870536044438032523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18344655809537896022720981 429952870536044438032523)
                  ·
                    rfl

theorem cell22_3767986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 7].length) (baseStart_3767986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3767986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3767986 prefixEnd_3767986 := by exact prefixLift 3767986
  have htrace : WordTrace (prefixWord ++ tailWord_3767986) baseStart_3767986 baseEnd_3767986 := by
    simpa [prefixWord, tailWord_3767986, baseEnd_3767986] using wordTrace_append hprefix tailTrace_3767986
  have hstable : (prefixWord ++ tailWord_3767986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3767986).length < 2 ^ (prefixWord ++ tailWord_3767986).sum := by decide
  have hdescent : baseEnd_3767986 < baseStart_3767986 := by decide
  rcases family_descends (prefixWord ++ tailWord_3767986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768031 : List Nat := [1, 1, 2, 3, 2, 2, 1, 2, 8]
def baseStart_3768031 : Nat := 118140960795 + 3768031 * 2 ^ 59
def prefixEnd_3768031 : Nat := 4983230072969 + 3 ^ 40 * 3768031 * 2
def baseEnd_3768031 : Nat := 429958005342589398907477

theorem tailTrace_3768031 : CollatzResearch.WordTrace tailWord_3768031 prefixEnd_3768031 429958005342589398907477 := by
  unfold tailWord_3768031
  simp only [CollatzResearch.WordTrace]
  refine ⟨137431381012074690305991947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91620920674716460203994631 137431381012074690305991947)
  ·
    refine ⟨206147071518112035458987921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137431381012074690305991947 206147071518112035458987921)
    ·
      refine ⟨154610303638584026594240941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206147071518112035458987921 154610303638584026594240941)
      ·
        refine ⟨57978863864469009972840353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154610303638584026594240941 57978863864469009972840353)
        ·
          refine ⟨43484147898351757479630265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57978863864469009972840353 43484147898351757479630265)
          ·
            refine ⟨32613110923763818109722699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43484147898351757479630265 32613110923763818109722699)
            ·
              refine ⟨48919666385645727164584049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32613110923763818109722699 48919666385645727164584049)
              ·
                refine ⟨36689749789234295373438037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48919666385645727164584049 36689749789234295373438037)
                ·
                  refine ⟨429958005342589398907477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36689749789234295373438037 429958005342589398907477)
                  ·
                    rfl

theorem cell22_3768031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 2, 8].length) (baseStart_3768031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768031 prefixEnd_3768031 := by exact prefixLift 3768031
  have htrace : WordTrace (prefixWord ++ tailWord_3768031) baseStart_3768031 baseEnd_3768031 := by
    simpa [prefixWord, tailWord_3768031, baseEnd_3768031] using wordTrace_append hprefix tailTrace_3768031
  have hstable : (prefixWord ++ tailWord_3768031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768031).length < 2 ^ (prefixWord ++ tailWord_3768031).sum := by decide
  have hdescent : baseEnd_3768031 < baseStart_3768031 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768052 : List Nat := [2, 6, 1, 1, 1, 1, 2, 1, 2, 5]
def baseStart_3768052 : Nat := 118140960795 + 3768052 * 2 ^ 59
def prefixEnd_3768052 : Nat := 4983230072969 + 3 ^ 40 * 3768052 * 2
def baseEnd_3768052 : Nat := 1289881204756931141947367

theorem tailTrace_3768052 : CollatzResearch.WordTrace tailWord_3768052 prefixEnd_3768052 1289881204756931141947367 := by
  unfold tailWord_3768052
  simp only [CollatzResearch.WordTrace]
  refine ⟨68716073472499305446253205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91621431296665740595004273 68716073472499305446253205)
  ·
    refine ⟨3221065944023404942793119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68716073472499305446253205 3221065944023404942793119)
    ·
      refine ⟨4831598916035107414189679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3221065944023404942793119 4831598916035107414189679)
      ·
        refine ⟨7247398374052661121284519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4831598916035107414189679 7247398374052661121284519)
        ·
          refine ⟨10871097561078991681926779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7247398374052661121284519 10871097561078991681926779)
          ·
            refine ⟨16306646341618487522890169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10871097561078991681926779 16306646341618487522890169)
            ·
              refine ⟨12229984756213865642167627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16306646341618487522890169 12229984756213865642167627)
              ·
                refine ⟨18344977134320798463251441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12229984756213865642167627 18344977134320798463251441)
                ·
                  refine ⟨13758732850740598847438581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18344977134320798463251441 13758732850740598847438581)
                  ·
                    refine ⟨1289881204756931141947367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13758732850740598847438581 1289881204756931141947367)
                    ·
                      rfl

theorem cell22_3768052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_3768052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768052 prefixEnd_3768052 := by exact prefixLift 3768052
  have htrace : WordTrace (prefixWord ++ tailWord_3768052) baseStart_3768052 baseEnd_3768052 := by
    simpa [prefixWord, tailWord_3768052, baseEnd_3768052] using wordTrace_append hprefix tailTrace_3768052
  have hstable : (prefixWord ++ tailWord_3768052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768052).length < 2 ^ (prefixWord ++ tailWord_3768052).sum := by decide
  have hdescent : baseEnd_3768052 < baseStart_3768052 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768063 : List Nat := [1, 1, 2, 2, 1, 3, 5, 1, 1, 5]
def baseStart_3768063 : Nat := 118140960795 + 3768063 * 2 ^ 59
def prefixEnd_3768063 : Nat := 4983230072969 + 3 ^ 40 * 3768063 * 2
def baseEnd_3768063 : Nat := 1289884970281730779922333

theorem tailTrace_3768063 : CollatzResearch.WordTrace tailWord_3768063 prefixEnd_3768063 1289884970281730779922333 := by
  unfold tailWord_3768063
  simp only [CollatzResearch.WordTrace]
  refine ⟨137432548147958759771156843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91621698765305839847437895 137432548147958759771156843)
  ·
    refine ⟨206148822221938139656735265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137432548147958759771156843 206148822221938139656735265)
    ·
      refine ⟨154611616666453604742551449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206148822221938139656735265 154611616666453604742551449)
      ·
        refine ⟨115958712499840203556913587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154611616666453604742551449 115958712499840203556913587)
        ·
          refine ⟨173938068749760305335370381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115958712499840203556913587 173938068749760305335370381)
          ·
            refine ⟨65226775781160114500763893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173938068749760305335370381 65226775781160114500763893)
            ·
              refine ⟨6115010229483760734446615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 65226775781160114500763893 6115010229483760734446615)
              ·
                refine ⟨9172515344225641101669923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6115010229483760734446615 9172515344225641101669923)
                ·
                  refine ⟨13758773016338461652504885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9172515344225641101669923 13758773016338461652504885)
                  ·
                    refine ⟨1289884970281730779922333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13758773016338461652504885 1289884970281730779922333)
                    ·
                      rfl

theorem cell22_3768063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 5].length) (baseStart_3768063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768063 prefixEnd_3768063 := by exact prefixLift 3768063
  have htrace : WordTrace (prefixWord ++ tailWord_3768063) baseStart_3768063 baseEnd_3768063 := by
    simpa [prefixWord, tailWord_3768063, baseEnd_3768063] using wordTrace_append hprefix tailTrace_3768063
  have hstable : (prefixWord ++ tailWord_3768063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768063).length < 2 ^ (prefixWord ++ tailWord_3768063).sum := by decide
  have hdescent : baseEnd_3768063 < baseStart_3768063 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768078 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 1, 6]
def baseStart_3768078 : Nat := 118140960795 + 3768078 * 2 ^ 59
def prefixEnd_3768078 : Nat := 4983230072969 + 3 ^ 40 * 3768078 * 2
def baseEnd_3768078 : Nat := 1289890105088275740797287

theorem tailTrace_3768078 : CollatzResearch.WordTrace tailWord_3768078 prefixEnd_3768078 1289890105088275740797287 := by
  unfold tailWord_3768078
  simp only [CollatzResearch.WordTrace]
  refine ⟨17179136905363052166619111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91622063495269611555301925 17179136905363052166619111)
  ·
    refine ⟨25768705358044578249928667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17179136905363052166619111 25768705358044578249928667)
    ·
      refine ⟨38653058037066867374893001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25768705358044578249928667 38653058037066867374893001)
      ·
        refine ⟨28989793527800150531169751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38653058037066867374893001 28989793527800150531169751)
        ·
          refine ⟨43484690291700225796754627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28989793527800150531169751 43484690291700225796754627)
          ·
            refine ⟨65227035437550338695131941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43484690291700225796754627 65227035437550338695131941)
            ·
              refine ⟨12230069144540688505337239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65227035437550338695131941 12230069144540688505337239)
              ·
                refine ⟨18345103716811032758005859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12230069144540688505337239 18345103716811032758005859)
                ·
                  refine ⟨27517655575216549137008789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 18345103716811032758005859 27517655575216549137008789)
                  ·
                    refine ⟨1289890105088275740797287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27517655575216549137008789 1289890105088275740797287)
                    ·
                      rfl

theorem cell22_3768078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 1, 6].length) (baseStart_3768078 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768078 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768078 prefixEnd_3768078 := by exact prefixLift 3768078
  have htrace : WordTrace (prefixWord ++ tailWord_3768078) baseStart_3768078 baseEnd_3768078 := by
    simpa [prefixWord, tailWord_3768078, baseEnd_3768078] using wordTrace_append hprefix tailTrace_3768078
  have hstable : (prefixWord ++ tailWord_3768078).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768078).length < 2 ^ (prefixWord ++ tailWord_3768078).sum := by decide
  have hdescent : baseEnd_3768078 < baseStart_3768078 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768091 : List Nat := [1, 1, 1, 1, 1, 1, 4, 2, 1, 9]
def baseStart_3768091 : Nat := 118140960795 + 3768091 * 2 ^ 59
def prefixEnd_3768091 : Nat := 4983230072969 + 3 ^ 40 * 3768091 * 2
def baseEnd_3768091 : Nat := 1289894555253948040222247

theorem tailTrace_3768091 : CollatzResearch.WordTrace tailWord_3768091 prefixEnd_3768091 1289894555253948040222247 := by
  unfold tailWord_3768091
  simp only [CollatzResearch.WordTrace]
  refine ⟨137433569391857320553176127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91622379594571547035450751 137433569391857320553176127)
  ·
    refine ⟨206150354087785980829764191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137433569391857320553176127 206150354087785980829764191)
    ·
      refine ⟨309225531131678971244646287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206150354087785980829764191 309225531131678971244646287)
      ·
        refine ⟨463838296697518456866969431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309225531131678971244646287 463838296697518456866969431)
        ·
          refine ⟨695757445046277685300454147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 463838296697518456866969431 695757445046277685300454147)
          ·
            refine ⟨1043636167569416527950681221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 695757445046277685300454147 1043636167569416527950681221)
            ·
              refine ⟨195681781419265598990752729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1043636167569416527950681221 195681781419265598990752729)
              ·
                refine ⟨146761336064449199243064547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195681781419265598990752729 146761336064449199243064547)
                ·
                  refine ⟨220142004096673798864596821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 146761336064449199243064547 220142004096673798864596821)
                  ·
                    refine ⟨1289894555253948040222247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 220142004096673798864596821 1289894555253948040222247)
                    ·
                      rfl

theorem cell22_3768091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 9].length) (baseStart_3768091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768091 prefixEnd_3768091 := by exact prefixLift 3768091
  have htrace : WordTrace (prefixWord ++ tailWord_3768091) baseStart_3768091 baseEnd_3768091 := by
    simpa [prefixWord, tailWord_3768091, baseEnd_3768091] using wordTrace_append hprefix tailTrace_3768091
  have hstable : (prefixWord ++ tailWord_3768091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768091).length < 2 ^ (prefixWord ++ tailWord_3768091).sum := by decide
  have hdescent : baseEnd_3768091 < baseStart_3768091 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768114 : List Nat := [3, 2, 1, 1, 3, 4, 2, 1, 2, 3]
def baseStart_3768114 : Nat := 118140960795 + 3768114 * 2 ^ 59
def prefixEnd_3768114 : Nat := 4983230072969 + 3 ^ 40 * 3768114 * 2
def baseEnd_3768114 : Nat := 1289902428623983646897177

theorem tailTrace_3768114 : CollatzResearch.WordTrace tailWord_3768114 prefixEnd_3768114 1289902428623983646897177 := by
  unfold tailWord_3768114
  simp only [CollatzResearch.WordTrace]
  refine ⟨34358602067693498870315849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91622938847182663654175597 34358602067693498870315849)
  ·
    refine ⟨25768951550770124152736887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34358602067693498870315849 25768951550770124152736887)
    ·
      refine ⟨38653427326155186229105331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25768951550770124152736887 38653427326155186229105331)
      ·
        refine ⟨57980140989232779343657997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38653427326155186229105331 57980140989232779343657997)
        ·
          refine ⟨21742552870962292253871749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57980140989232779343657997 21742552870962292253871749)
          ·
            refine ⟨4076728663305429797600953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21742552870962292253871749 4076728663305429797600953)
            ·
              refine ⟨3057546497479072348200715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4076728663305429797600953 3057546497479072348200715)
              ·
                refine ⟨4586319746218608522301073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3057546497479072348200715 4586319746218608522301073)
                ·
                  refine ⟨3439739809663956391725805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4586319746218608522301073 3439739809663956391725805)
                  ·
                    refine ⟨1289902428623983646897177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3439739809663956391725805 1289902428623983646897177)
                    ·
                      rfl

theorem cell22_3768114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 2, 3].length) (baseStart_3768114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768114 prefixEnd_3768114 := by exact prefixLift 3768114
  have htrace : WordTrace (prefixWord ++ tailWord_3768114) baseStart_3768114 baseEnd_3768114 := by
    simpa [prefixWord, tailWord_3768114, baseEnd_3768114] using wordTrace_append hprefix tailTrace_3768114
  have hstable : (prefixWord ++ tailWord_3768114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768114).length < 2 ^ (prefixWord ++ tailWord_3768114).sum := by decide
  have hdescent : baseEnd_3768114 < baseStart_3768114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768153 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 2, 5]
def baseStart_3768153 : Nat := 118140960795 + 3768153 * 2 ^ 59
def prefixEnd_3768153 : Nat := 4983230072969 + 3 ^ 40 * 3768153 * 2
def baseEnd_3768153 : Nat := 1289915779121000545172057

theorem tailTrace_3768153 : CollatzResearch.WordTrace tailWord_3768153 prefixEnd_3768153 1289915779121000545172057 := by
  unfold tailWord_3768153
  simp only [CollatzResearch.WordTrace]
  refine ⟨137435830717632705141933113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91623887145088470094622075 137435830717632705141933113)
  ·
    refine ⟨103076873038224528856449835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137435830717632705141933113 103076873038224528856449835)
    ·
      refine ⟨154615309557336793284674753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103076873038224528856449835 154615309557336793284674753)
      ·
        refine ⟨115961482168002594963506065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154615309557336793284674753 115961482168002594963506065)
        ·
          refine ⟨86971111626001946222629549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115961482168002594963506065 86971111626001946222629549)
          ·
            refine ⟨32614166859750729833486081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86971111626001946222629549 32614166859750729833486081)
            ·
              refine ⟨24460625144813047375114561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32614166859750729833486081 24460625144813047375114561)
              ·
                refine ⟨18345468858609785531335921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24460625144813047375114561 18345468858609785531335921)
                ·
                  refine ⟨13759101643957339148501941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18345468858609785531335921 13759101643957339148501941)
                  ·
                    refine ⟨1289915779121000545172057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13759101643957339148501941 1289915779121000545172057)
                    ·
                      rfl

theorem cell22_3768153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_3768153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768153 prefixEnd_3768153 := by exact prefixLift 3768153
  have htrace : WordTrace (prefixWord ++ tailWord_3768153) baseStart_3768153 baseEnd_3768153 := by
    simpa [prefixWord, tailWord_3768153, baseEnd_3768153] using wordTrace_append hprefix tailTrace_3768153
  have hstable : (prefixWord ++ tailWord_3768153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768153).length < 2 ^ (prefixWord ++ tailWord_3768153).sum := by decide
  have hdescent : baseEnd_3768153 < baseStart_3768153 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768159 : List Nat := [1, 1, 2, 3, 1, 4, 4, 2, 1, 3]
def baseStart_3768159 : Nat := 118140960795 + 3768159 * 2 ^ 59
def prefixEnd_3768159 : Nat := 4983230072969 + 3 ^ 40 * 3768159 * 2
def baseEnd_3768159 : Nat := 1289917833043618529522039

theorem tailTrace_3768159 : CollatzResearch.WordTrace tailWord_3768159 prefixEnd_3768159 1289917833043618529522039 := by
  unfold tailWord_3768159
  simp only [CollatzResearch.WordTrace]
  refine ⟨137436049555610968166651531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91624033037073978777767687 137436049555610968166651531)
  ·
    refine ⟨206154074333416452249977297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137436049555610968166651531 206154074333416452249977297)
    ·
      refine ⟨154615555750062339187482973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206154074333416452249977297 154615555750062339187482973)
      ·
        refine ⟨57980833406273377195306115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154615555750062339187482973 57980833406273377195306115)
        ·
          refine ⟨86971250109410065792959173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57980833406273377195306115 86971250109410065792959173)
          ·
            refine ⟨16307109395514387336179845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86971250109410065792959173 16307109395514387336179845)
            ·
              refine ⟨3057583011658947625533721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16307109395514387336179845 3057583011658947625533721)
              ·
                refine ⟨2293187258744210719150291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3057583011658947625533721 2293187258744210719150291)
                ·
                  refine ⟨3439780888116316078725437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2293187258744210719150291 3439780888116316078725437)
                  ·
                    refine ⟨1289917833043618529522039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3439780888116316078725437 1289917833043618529522039)
                    ·
                      rfl

theorem cell22_3768159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 4, 2, 1, 3].length) (baseStart_3768159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768159 prefixEnd_3768159 := by exact prefixLift 3768159
  have htrace : WordTrace (prefixWord ++ tailWord_3768159) baseStart_3768159 baseEnd_3768159 := by
    simpa [prefixWord, tailWord_3768159, baseEnd_3768159] using wordTrace_append hprefix tailTrace_3768159
  have hstable : (prefixWord ++ tailWord_3768159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768159).length < 2 ^ (prefixWord ++ tailWord_3768159).sum := by decide
  have hdescent : baseEnd_3768159 < baseStart_3768159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768185 : List Nat := [1, 2, 1, 3, 2, 2, 2, 4, 1, 4]
def baseStart_3768185 : Nat := 118140960795 + 3768185 * 2 ^ 59
def prefixEnd_3768185 : Nat := 4983230072969 + 3 ^ 40 * 3768185 * 2
def baseEnd_3768185 : Nat := 1289926733374963128371959

theorem tailTrace_3768185 : CollatzResearch.WordTrace tailWord_3768185 prefixEnd_3768185 1289926733374963128371959 := by
  unfold tailWord_3768185
  simp only [CollatzResearch.WordTrace]
  refine ⟨137436997853516774607098009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91624665235677849738065339 137436997853516774607098009)
  ·
    refine ⟨103077748390137580955323507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137436997853516774607098009 103077748390137580955323507)
    ·
      refine ⟨154616622585206371432985261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103077748390137580955323507 154616622585206371432985261)
      ·
        refine ⟨57981233469452389287369473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154616622585206371432985261 57981233469452389287369473)
        ·
          refine ⟨43485925102089291965527105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57981233469452389287369473 43485925102089291965527105)
          ·
            refine ⟨32614443826566968974145329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43485925102089291965527105 32614443826566968974145329)
            ·
              refine ⟨24460832869925226730608997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32614443826566968974145329 24460832869925226730608997)
              ·
                refine ⟨4586406163110980011989187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24460832869925226730608997 4586406163110980011989187)
                ·
                  refine ⟨6879609244666470017983781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4586406163110980011989187 6879609244666470017983781)
                  ·
                    refine ⟨1289926733374963128371959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6879609244666470017983781 1289926733374963128371959)
                    ·
                      rfl

theorem cell22_3768185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 4].length) (baseStart_3768185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768185 prefixEnd_3768185 := by exact prefixLift 3768185
  have htrace : WordTrace (prefixWord ++ tailWord_3768185) baseStart_3768185 baseEnd_3768185 := by
    simpa [prefixWord, tailWord_3768185, baseEnd_3768185] using wordTrace_append hprefix tailTrace_3768185
  have hstable : (prefixWord ++ tailWord_3768185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768185).length < 2 ^ (prefixWord ++ tailWord_3768185).sum := by decide
  have hdescent : baseEnd_3768185 < baseStart_3768185 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768206 : List Nat := [4, 1, 1, 5, 2, 1, 1, 2, 5]
def baseStart_3768206 : Nat := 118140960795 + 3768206 * 2 ^ 59
def prefixEnd_3768206 : Nat := 4983230072969 + 3 ^ 40 * 3768206 * 2
def baseEnd_3768206 : Nat := 429977974034708691198965

theorem tailTrace_3768206 : CollatzResearch.WordTrace tailWord_3768206 prefixEnd_3768206 429977974034708691198965 := by
  unfold tailWord_3768206
  simp only [CollatzResearch.WordTrace]
  refine ⟨17179720473305086899201559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91625175857627130129074981 17179720473305086899201559)
  ·
    refine ⟨25769580709957630348802339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17179720473305086899201559 25769580709957630348802339)
    ·
      refine ⟨38654371064936445523203509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25769580709957630348802339 38654371064936445523203509)
      ·
        refine ⟨3623847287337791767800329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38654371064936445523203509 3623847287337791767800329)
        ·
          refine ⟨2717885465503343825850247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3623847287337791767800329 2717885465503343825850247)
          ·
            refine ⟨4076828198255015738775371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2717885465503343825850247 4076828198255015738775371)
            ·
              refine ⟨6115242297382523608163057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4076828198255015738775371 6115242297382523608163057)
              ·
                refine ⟨4586431723036892706122293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6115242297382523608163057 4586431723036892706122293)
                ·
                  refine ⟨429977974034708691198965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4586431723036892706122293 429977974034708691198965)
                  ·
                    rfl

theorem cell22_3768206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 1, 2, 5].length) (baseStart_3768206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768206 prefixEnd_3768206 := by exact prefixLift 3768206
  have htrace : WordTrace (prefixWord ++ tailWord_3768206) baseStart_3768206 baseEnd_3768206 := by
    simpa [prefixWord, tailWord_3768206, baseEnd_3768206] using wordTrace_append hprefix tailTrace_3768206
  have hstable : (prefixWord ++ tailWord_3768206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768206).length < 2 ^ (prefixWord ++ tailWord_3768206).sum := by decide
  have hdescent : baseEnd_3768206 < baseStart_3768206 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768243 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 2, 7]
def baseStart_3768243 : Nat := 118140960795 + 3768243 * 2 ^ 59
def prefixEnd_3768243 : Nat := 4983230072969 + 3 ^ 40 * 3768243 * 2
def baseEnd_3768243 : Nat := 1289946587960270310421781

theorem tailTrace_3768243 : CollatzResearch.WordTrace tailWord_3768243 prefixEnd_3768243 1289946587960270310421781 := by
  unfold tailWord_3768243
  simp only [CollatzResearch.WordTrace]
  refine ⟨137439113287306650512709383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91626075524871100341806255 137439113287306650512709383)
  ·
    refine ⟨206158669930959975769064075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137439113287306650512709383 206158669930959975769064075)
    ·
      refine ⟨309238004896439963653596113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206158669930959975769064075 309238004896439963653596113)
      ·
        refine ⟨231928503672329972740197085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309238004896439963653596113 231928503672329972740197085)
        ·
          refine ⟨86973188877123739777573907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 231928503672329972740197085 86973188877123739777573907)
          ·
            refine ⟨130459783315685609666360861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86973188877123739777573907 130459783315685609666360861)
            ·
              refine ⟨48922418743382103624885323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130459783315685609666360861 48922418743382103624885323)
              ·
                refine ⟨73383628115073155437327985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48922418743382103624885323 73383628115073155437327985)
                ·
                  refine ⟨55037721086304866577995989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 73383628115073155437327985 55037721086304866577995989)
                  ·
                    refine ⟨1289946587960270310421781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 55037721086304866577995989 1289946587960270310421781)
                    ·
                      rfl

theorem cell22_3768243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 7].length) (baseStart_3768243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768243 prefixEnd_3768243 := by exact prefixLift 3768243
  have htrace : WordTrace (prefixWord ++ tailWord_3768243) baseStart_3768243 baseEnd_3768243 := by
    simpa [prefixWord, tailWord_3768243, baseEnd_3768243] using wordTrace_append hprefix tailTrace_3768243
  have hstable : (prefixWord ++ tailWord_3768243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768243).length < 2 ^ (prefixWord ++ tailWord_3768243).sum := by decide
  have hdescent : baseEnd_3768243 < baseStart_3768243 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768245 : List Nat := [1, 3, 3, 2, 1, 3, 1, 8]
def baseStart_3768245 : Nat := 118140960795 + 3768245 * 2 ^ 59
def prefixEnd_3768245 : Nat := 4983230072969 + 3 ^ 40 * 3768245 * 2
def baseEnd_3768245 : Nat := 143327474733460330207975

theorem tailTrace_3768245 : CollatzResearch.WordTrace tailWord_3768245 prefixEnd_3768245 143327474733460330207975 := by
  unfold tailWord_3768245
  simp only [CollatzResearch.WordTrace]
  refine ⟨137439186233299404854282189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91626124155532936569521459 137439186233299404854282189)
  ·
    refine ⟨51539694837487276820355821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137439186233299404854282189 51539694837487276820355821)
    ·
      refine ⟨19327385564057728807633433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51539694837487276820355821 19327385564057728807633433)
      ·
        refine ⟨14495539173043296605725075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19327385564057728807633433 14495539173043296605725075)
        ·
          refine ⟨21743308759564944908587613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14495539173043296605725075 21743308759564944908587613)
          ·
            refine ⟨8153740784836854340720355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21743308759564944908587613 8153740784836854340720355)
            ·
              refine ⟨12230611177255281511080533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8153740784836854340720355 12230611177255281511080533)
              ·
                refine ⟨143327474733460330207975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12230611177255281511080533 143327474733460330207975)
                ·
                  rfl

theorem cell22_3768245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 1, 8].length) (baseStart_3768245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768245 prefixEnd_3768245 := by exact prefixLift 3768245
  have htrace : WordTrace (prefixWord ++ tailWord_3768245) baseStart_3768245 baseEnd_3768245 := by
    simpa [prefixWord, tailWord_3768245, baseEnd_3768245] using wordTrace_append hprefix tailTrace_3768245
  have hstable : (prefixWord ++ tailWord_3768245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768245).length < 2 ^ (prefixWord ++ tailWord_3768245).sum := by decide
  have hdescent : baseEnd_3768245 < baseStart_3768245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768369 : List Nat := [1, 2, 2, 3, 1, 4, 2, 3, 4]
def baseStart_3768369 : Nat := 118140960795 + 3768369 * 2 ^ 59
def prefixEnd_3768369 : Nat := 4983230072969 + 3 ^ 40 * 3768369 * 2
def baseEnd_3768369 : Nat := 429996573445082660590465

theorem tailTrace_3768369 : CollatzResearch.WordTrace tailWord_3768369 prefixEnd_3768369 429996573445082660590465 := by
  unfold tailWord_3768369
  simp only [CollatzResearch.WordTrace]
  refine ⟨137443708884850174031796161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91629139256566782687864107 137443708884850174031796161)
  ·
    refine ⟨103082781663637630523847121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137443708884850174031796161 103082781663637630523847121)
    ·
      refine ⟨77312086247728222892885341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103082781663637630523847121 77312086247728222892885341)
      ·
        refine ⟨28992032342898083584832003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77312086247728222892885341 28992032342898083584832003)
        ·
          refine ⟨43488048514347125377248005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28992032342898083584832003 43488048514347125377248005)
          ·
            refine ⟨8154009096440086008234001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43488048514347125377248005 8154009096440086008234001)
            ·
              refine ⟨6115506822330064506175501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8154009096440086008234001 6115506822330064506175501)
              ·
                refine ⟨2293315058373774189815813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6115506822330064506175501 2293315058373774189815813)
                ·
                  refine ⟨429996573445082660590465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2293315058373774189815813 429996573445082660590465)
                  ·
                    rfl

theorem cell22_3768369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 2, 3, 4].length) (baseStart_3768369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768369 prefixEnd_3768369 := by exact prefixLift 3768369
  have htrace : WordTrace (prefixWord ++ tailWord_3768369) baseStart_3768369 baseEnd_3768369 := by
    simpa [prefixWord, tailWord_3768369, baseEnd_3768369] using wordTrace_append hprefix tailTrace_3768369
  have hstable : (prefixWord ++ tailWord_3768369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768369).length < 2 ^ (prefixWord ++ tailWord_3768369).sum := by decide
  have hdescent : baseEnd_3768369 < baseStart_3768369 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768380 : List Nat := [2, 2, 2, 2, 2, 1, 11]
def baseStart_3768380 : Nat := 118140960795 + 3768380 * 2 ^ 59
def prefixEnd_3768380 : Nat := 4983230072969 + 3 ^ 40 * 3768380 * 2
def baseEnd_3768380 : Nat := 47777536513335097027643

theorem tailTrace_3768380 : CollatzResearch.WordTrace tailWord_3768380 prefixEnd_3768380 47777536513335097027643 := by
  unfold tailWord_3768380
  simp only [CollatzResearch.WordTrace]
  refine ⟨68722055043905161455223297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91629406725206881940297729 68722055043905161455223297)
  ·
    refine ⟨51541541282928871091417473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68722055043905161455223297 51541541282928871091417473)
    ·
      refine ⟨38656155962196653318563105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51541541282928871091417473 38656155962196653318563105)
      ·
        refine ⟨28992116971647489988922329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38656155962196653318563105 28992116971647489988922329)
        ·
          refine ⟨21744087728735617491691747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28992116971647489988922329 21744087728735617491691747)
          ·
            refine ⟨32616131593103426237537621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21744087728735617491691747 32616131593103426237537621)
            ·
              refine ⟨47777536513335097027643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32616131593103426237537621 47777536513335097027643)
              ·
                rfl

theorem cell22_3768380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 11].length) (baseStart_3768380 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768380 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768380 prefixEnd_3768380 := by exact prefixLift 3768380
  have htrace : WordTrace (prefixWord ++ tailWord_3768380) baseStart_3768380 baseEnd_3768380 := by
    simpa [prefixWord, tailWord_3768380, baseEnd_3768380] using wordTrace_append hprefix tailTrace_3768380
  have hstable : (prefixWord ++ tailWord_3768380).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768380).length < 2 ^ (prefixWord ++ tailWord_3768380).sum := by decide
  have hdescent : baseEnd_3768380 < baseStart_3768380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768384 : List Nat := [2, 1, 1, 2, 2, 4, 3, 2, 2, 3]
def baseStart_3768384 : Nat := 118140960795 + 3768384 * 2 ^ 59
def prefixEnd_3768384 : Nat := 4983230072969 + 3 ^ 40 * 3768384 * 2
def baseEnd_3768384 : Nat := 1289994855141792942646349

theorem tailTrace_3768384 : CollatzResearch.WordTrace tailWord_3768384 prefixEnd_3768384 1289994855141792942646349 := by
  unfold tailWord_3768384
  simp only [CollatzResearch.WordTrace]
  refine ⟨68722127989897915796796103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91629503986530554395728137 68722127989897915796796103)
  ·
    refine ⟨103083191984846873695194155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68722127989897915796796103 103083191984846873695194155)
    ·
      refine ⟨154624787977270310542791233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103083191984846873695194155 154624787977270310542791233)
      ·
        refine ⟨115968590982952732907093425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154624787977270310542791233 115968590982952732907093425)
        ·
          refine ⟨86976443237214549680320069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115968590982952732907093425 86976443237214549680320069)
          ·
            refine ⟨16308083106977728065060013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86976443237214549680320069 16308083106977728065060013)
            ·
              refine ⟨6115531165116648024397505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16308083106977728065060013 6115531165116648024397505)
              ·
                refine ⟨4586648373837486018298129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6115531165116648024397505 4586648373837486018298129)
                ·
                  refine ⟨3439986280378114513723597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4586648373837486018298129 3439986280378114513723597)
                  ·
                    refine ⟨1289994855141792942646349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3439986280378114513723597 1289994855141792942646349)
                    ·
                      rfl

theorem cell22_3768384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 2, 3].length) (baseStart_3768384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768384 prefixEnd_3768384 := by exact prefixLift 3768384
  have htrace : WordTrace (prefixWord ++ tailWord_3768384) baseStart_3768384 baseEnd_3768384 := by
    simpa [prefixWord, tailWord_3768384, baseEnd_3768384] using wordTrace_append hprefix tailTrace_3768384
  have hstable : (prefixWord ++ tailWord_3768384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768384).length < 2 ^ (prefixWord ++ tailWord_3768384).sum := by decide
  have hdescent : baseEnd_3768384 < baseStart_3768384 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768397 : List Nat := [1, 6, 1, 1, 1, 1, 2, 9]
def baseStart_3768397 : Nat := 118140960795 + 3768397 * 2 ^ 59
def prefixEnd_3768397 : Nat := 4983230072969 + 3 ^ 40 * 3768397 * 2
def baseEnd_3768397 : Nat := 143333256145273915785701

theorem tailTrace_3768397 : CollatzResearch.WordTrace tailWord_3768397 prefixEnd_3768397 143333256145273915785701 := by
  unfold tailWord_3768397
  simp only [CollatzResearch.WordTrace]
  refine ⟨137444730128748734813815445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91629820085832489875876963 137444730128748734813815445)
  ·
    refine ⟨6442721724785096944397599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 137444730128748734813815445 6442721724785096944397599)
    ·
      refine ⟨9664082587177645416596399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6442721724785096944397599 9664082587177645416596399)
      ·
        refine ⟨14496123880766468124894599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9664082587177645416596399 14496123880766468124894599)
        ·
          refine ⟨21744185821149702187341899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14496123880766468124894599 21744185821149702187341899)
          ·
            refine ⟨32616278731724553281012849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21744185821149702187341899 32616278731724553281012849)
            ·
              refine ⟨24462209048793414960759637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32616278731724553281012849 24462209048793414960759637)
              ·
                refine ⟨143333256145273915785701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24462209048793414960759637 143333256145273915785701)
                ·
                  rfl

theorem cell22_3768397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 9].length) (baseStart_3768397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768397 prefixEnd_3768397 := by exact prefixLift 3768397
  have htrace : WordTrace (prefixWord ++ tailWord_3768397) baseStart_3768397 baseEnd_3768397 := by
    simpa [prefixWord, tailWord_3768397, baseEnd_3768397] using wordTrace_append hprefix tailTrace_3768397
  have hstable : (prefixWord ++ tailWord_3768397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768397).length < 2 ^ (prefixWord ++ tailWord_3768397).sum := by decide
  have hdescent : baseEnd_3768397 < baseStart_3768397 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768425 : List Nat := [1, 2, 1, 1, 1, 5, 1, 1, 9]
def baseStart_3768425 : Nat := 118140960795 + 3768425 * 2 ^ 59
def prefixEnd_3768425 : Nat := 4983230072969 + 3 ^ 40 * 3768425 * 2
def baseEnd_3768425 : Nat := 430002963426560834123741

theorem tailTrace_3768425 : CollatzResearch.WordTrace tailWord_3768425 prefixEnd_3768425 430002963426560834123741 := by
  unfold tailWord_3768425
  simp only [CollatzResearch.WordTrace]
  refine ⟨137445751372647295595834729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91630500915098197063889819 137445751372647295595834729)
  ·
    refine ⟨103084313529485471696876047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137445751372647295595834729 103084313529485471696876047)
    ·
      refine ⟨154626470294228207545314071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103084313529485471696876047 154626470294228207545314071)
      ·
        refine ⟨231939705441342311317971107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154626470294228207545314071 231939705441342311317971107)
        ·
          refine ⟨347909558162013466976956661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231939705441342311317971107 347909558162013466976956661)
          ·
            refine ⟨32616521077688762529089687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 347909558162013466976956661 32616521077688762529089687)
            ·
              refine ⟨48924781616533143793634531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32616521077688762529089687 48924781616533143793634531)
              ·
                refine ⟨73387172424799715690451797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48924781616533143793634531 73387172424799715690451797)
                ·
                  refine ⟨430002963426560834123741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73387172424799715690451797 430002963426560834123741)
                  ·
                    rfl

theorem cell22_3768425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 1, 9].length) (baseStart_3768425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768425 prefixEnd_3768425 := by exact prefixLift 3768425
  have htrace : WordTrace (prefixWord ++ tailWord_3768425) baseStart_3768425 baseEnd_3768425 := by
    simpa [prefixWord, tailWord_3768425, baseEnd_3768425] using wordTrace_append hprefix tailTrace_3768425
  have hstable : (prefixWord ++ tailWord_3768425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768425).length < 2 ^ (prefixWord ++ tailWord_3768425).sum := by decide
  have hdescent : baseEnd_3768425 < baseStart_3768425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768497 : List Nat := [1, 2, 2, 5, 3, 1, 2, 2, 1, 3]
def baseStart_3768497 : Nat := 118140960795 + 3768497 * 2 ^ 59
def prefixEnd_3768497 : Nat := 4983230072969 + 3 ^ 40 * 3768497 * 2
def baseEnd_3768497 : Nat := 1290033537351098314571003

theorem tailTrace_3768497 : CollatzResearch.WordTrace tailWord_3768497 prefixEnd_3768497 1290033537351098314571003 := by
  unfold tailWord_3768497
  simp only [CollatzResearch.WordTrace]
  refine ⟨137448377428386451892455745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91632251618924301261637163 137448377428386451892455745)
  ·
    refine ⟨103086283071289838919341809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137448377428386451892455745 103086283071289838919341809)
    ·
      refine ⟨77314712303467379189506357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103086283071289838919341809 77314712303467379189506357)
      ·
        refine ⟨7248254278450066799016221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77314712303467379189506357 7248254278450066799016221)
        ·
          refine ⟨2718095354418775049631083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7248254278450066799016221 2718095354418775049631083)
          ·
            refine ⟨4077143031628162574446625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2718095354418775049631083 4077143031628162574446625)
            ·
              refine ⟨3057857273721121930834969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4077143031628162574446625 3057857273721121930834969)
              ·
                refine ⟨2293392955290841448126227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3057857273721121930834969 2293392955290841448126227)
                ·
                  refine ⟨3440089432936262172189341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2293392955290841448126227 3440089432936262172189341)
                  ·
                    refine ⟨1290033537351098314571003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3440089432936262172189341 1290033537351098314571003)
                    ·
                      rfl

theorem cell22_3768497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 3, 1, 2, 2, 1, 3].length) (baseStart_3768497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768497 prefixEnd_3768497 := by exact prefixLift 3768497
  have htrace : WordTrace (prefixWord ++ tailWord_3768497) baseStart_3768497 baseEnd_3768497 := by
    simpa [prefixWord, tailWord_3768497, baseEnd_3768497] using wordTrace_append hprefix tailTrace_3768497
  have hstable : (prefixWord ++ tailWord_3768497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768497).length < 2 ^ (prefixWord ++ tailWord_3768497).sum := by decide
  have hdescent : baseEnd_3768497 < baseStart_3768497 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768504 : List Nat := [2, 1, 2, 1, 2, 1, 5, 4, 4]
def baseStart_3768504 : Nat := 118140960795 + 3768504 * 2 ^ 59
def prefixEnd_3768504 : Nat := 4983230072969 + 3 ^ 40 * 3768504 * 2
def baseEnd_3768504 : Nat := 430011977864717543215327

theorem tailTrace_3768504 : CollatzResearch.WordTrace tailWord_3768504 prefixEnd_3768504 430011977864717543215327 := by
  unfold tailWord_3768504
  simp only [CollatzResearch.WordTrace]
  refine ⟨68724316369680546043980283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91632421826240728058640377 68724316369680546043980283)
  ·
    refine ⟨103086474554520819065970425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68724316369680546043980283 103086474554520819065970425)
    ·
      refine ⟨77314855915890614299477819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103086474554520819065970425 77314855915890614299477819)
      ·
        refine ⟨115972283873835921449216729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77314855915890614299477819 115972283873835921449216729)
        ·
          refine ⟨86979212905376941086912547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115972283873835921449216729 86979212905376941086912547)
          ·
            refine ⟨130468819358065411630368821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86979212905376941086912547 130468819358065411630368821)
            ·
              refine ⟨12231451814818632340347077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 130468819358065411630368821 12231451814818632340347077)
              ·
                refine ⟨2293397215278493563815077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12231451814818632340347077 2293397215278493563815077)
                ·
                  refine ⟨430011977864717543215327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2293397215278493563815077 430011977864717543215327)
                  ·
                    rfl

theorem cell22_3768504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 4].length) (baseStart_3768504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768504 prefixEnd_3768504 := by exact prefixLift 3768504
  have htrace : WordTrace (prefixWord ++ tailWord_3768504) baseStart_3768504 baseEnd_3768504 := by
    simpa [prefixWord, tailWord_3768504, baseEnd_3768504] using wordTrace_append hprefix tailTrace_3768504
  have hstable : (prefixWord ++ tailWord_3768504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768504).length < 2 ^ (prefixWord ++ tailWord_3768504).sum := by decide
  have hdescent : baseEnd_3768504 < baseStart_3768504 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768517 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 4, 4]
def baseStart_3768517 : Nat := 118140960795 + 3768517 * 2 ^ 59
def prefixEnd_3768517 : Nat := 4983230072969 + 3 ^ 40 * 3768517 * 2
def baseEnd_3768517 : Nat := 1290040383759824929070941

theorem tailTrace_3768517 : CollatzResearch.WordTrace tailWord_3768517 prefixEnd_3768517 1290040383759824929070941 := by
  unfold tailWord_3768517
  simp only [CollatzResearch.WordTrace]
  refine ⟨137449106888313995308183805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91632737925542663538789203 137449106888313995308183805)
  ·
    refine ⟨51543415083117748240568927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137449106888313995308183805 51543415083117748240568927)
    ·
      refine ⟨77315122624676622360853391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51543415083117748240568927 77315122624676622360853391)
      ·
        refine ⟨115972683937014933541280087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77315122624676622360853391 115972683937014933541280087)
        ·
          refine ⟨173959025905522400311920131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115972683937014933541280087 173959025905522400311920131)
          ·
            refine ⟨260938538858283600467880197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173959025905522400311920131 260938538858283600467880197)
            ·
              refine ⟨48925976035928175087727537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260938538858283600467880197 48925976035928175087727537)
              ·
                refine ⟨36694482026946131315795653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48925976035928175087727537 36694482026946131315795653)
                ·
                  refine ⟨6880215380052399621711685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36694482026946131315795653 6880215380052399621711685)
                  ·
                    refine ⟨1290040383759824929070941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6880215380052399621711685 1290040383759824929070941)
                    ·
                      rfl

theorem cell22_3768517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 4].length) (baseStart_3768517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768517 prefixEnd_3768517 := by exact prefixLift 3768517
  have htrace : WordTrace (prefixWord ++ tailWord_3768517) baseStart_3768517 baseEnd_3768517 := by
    simpa [prefixWord, tailWord_3768517, baseEnd_3768517] using wordTrace_append hprefix tailTrace_3768517
  have hstable : (prefixWord ++ tailWord_3768517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768517).length < 2 ^ (prefixWord ++ tailWord_3768517).sum := by decide
  have hdescent : baseEnd_3768517 < baseStart_3768517 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768583 : List Nat := [1, 1, 4, 5, 1, 2, 2, 6]
def baseStart_3768583 : Nat := 118140960795 + 3768583 * 2 ^ 59
def prefixEnd_3768583 : Nat := 4983230072969 + 3 ^ 40 * 3768583 * 2
def baseEnd_3768583 : Nat := 143340330767624750768971

theorem tailTrace_3768583 : CollatzResearch.WordTrace tailWord_3768583 prefixEnd_3768583 143340330767624750768971 := by
  unfold tailWord_3768583
  simp only [CollatzResearch.WordTrace]
  refine ⟨137451514106074888580086403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91634342737383259053390935 137451514106074888580086403)
  ·
    refine ⟨206177271159112332870129605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137451514106074888580086403 206177271159112332870129605)
    ·
      refine ⟨38658238342333562413149301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206177271159112332870129605 38658238342333562413149301)
      ·
        refine ⟨3624209844593771476232747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38658238342333562413149301 3624209844593771476232747)
        ·
          refine ⟨5436314766890657214349121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3624209844593771476232747 5436314766890657214349121)
          ·
            refine ⟨4077236075167992910761841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5436314766890657214349121 4077236075167992910761841)
            ·
              refine ⟨3057927056375994683071381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4077236075167992910761841 3057927056375994683071381)
              ·
                refine ⟨143340330767624750768971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3057927056375994683071381 143340330767624750768971)
                ·
                  rfl

theorem cell22_3768583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 2, 2, 6].length) (baseStart_3768583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768583 prefixEnd_3768583 := by exact prefixLift 3768583
  have htrace : WordTrace (prefixWord ++ tailWord_3768583) baseStart_3768583 baseEnd_3768583 := by
    simpa [prefixWord, tailWord_3768583, baseEnd_3768583] using wordTrace_append hprefix tailTrace_3768583
  have hstable : (prefixWord ++ tailWord_3768583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768583).length < 2 ^ (prefixWord ++ tailWord_3768583).sum := by decide
  have hdescent : baseEnd_3768583 < baseStart_3768583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768628 : List Nat := [2, 5, 1, 1, 1, 2, 4, 1, 5]
def baseStart_3768628 : Nat := 118140960795 + 3768628 * 2 ^ 59
def prefixEnd_3768628 : Nat := 4983230072969 + 3 ^ 40 * 3768628 * 2
def baseEnd_3768628 : Nat := 430026127109419213181867

theorem tailTrace_3768628 : CollatzResearch.WordTrace tailWord_3768628 prefixEnd_3768628 430026127109419213181867 := by
  unfold tailWord_3768628
  simp only [CollatzResearch.WordTrace]
  refine ⟨68726577695455930632737269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91635436927274574176983025 68726577695455930632737269)
  ·
    refine ⟨6443116658948993496819119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68726577695455930632737269 6443116658948993496819119)
    ·
      refine ⟨9664674988423490245228679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6443116658948993496819119 9664674988423490245228679)
      ·
        refine ⟨14497012482635235367843019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9664674988423490245228679 14497012482635235367843019)
        ·
          refine ⟨21745518723952853051764529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14497012482635235367843019 21745518723952853051764529)
          ·
            refine ⟨16309139042964639788823397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21745518723952853051764529 16309139042964639788823397)
            ·
              refine ⟨3057963570555869960404387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16309139042964639788823397 3057963570555869960404387)
              ·
                refine ⟨4586945355833804940606581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3057963570555869960404387 4586945355833804940606581)
                ·
                  refine ⟨430026127109419213181867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4586945355833804940606581 430026127109419213181867)
                  ·
                    rfl

theorem cell22_3768628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 5].length) (baseStart_3768628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768628 prefixEnd_3768628 := by exact prefixLift 3768628
  have htrace : WordTrace (prefixWord ++ tailWord_3768628) baseStart_3768628 baseEnd_3768628 := by
    simpa [prefixWord, tailWord_3768628, baseEnd_3768628] using wordTrace_append hprefix tailTrace_3768628
  have hstable : (prefixWord ++ tailWord_3768628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768628).length < 2 ^ (prefixWord ++ tailWord_3768628).sum := by decide
  have hdescent : baseEnd_3768628 < baseStart_3768628 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768671 : List Nat := [1, 1, 2, 3, 1, 2, 3, 4, 2, 3]
def baseStart_3768671 : Nat := 118140960795 + 3768671 * 2 ^ 59
def prefixEnd_3768671 : Nat := 4983230072969 + 3 ^ 40 * 3768671 * 2
def baseEnd_3768671 : Nat := 1290093101107019860720469

theorem tailTrace_3768671 : CollatzResearch.WordTrace tailWord_3768671 prefixEnd_3768671 1290093101107019860720469 := by
  unfold tailWord_3768671
  simp only [CollatzResearch.WordTrace]
  refine ⟨137454723729756079609289867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91636482486504053072859911 137454723729756079609289867)
  ·
    refine ⟨206182085594634119413934801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137454723729756079609289867 206182085594634119413934801)
    ·
      refine ⟨154636564195975589560451101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206182085594634119413934801 154636564195975589560451101)
      ·
        refine ⟨57988711573490846085169163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154636564195975589560451101 57988711573490846085169163)
        ·
          refine ⟨86983067360236269127753745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57988711573490846085169163 86983067360236269127753745)
          ·
            refine ⟨65237300520177201845815309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86983067360236269127753745 65237300520177201845815309)
            ·
              refine ⟨24463987695066450692180741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65237300520177201845815309 24463987695066450692180741)
              ·
                refine ⟨4586997692824959504783889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24463987695066450692180741 4586997692824959504783889)
                ·
                  refine ⟨3440248269618719628587917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4586997692824959504783889 3440248269618719628587917)
                  ·
                    refine ⟨1290093101107019860720469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3440248269618719628587917 1290093101107019860720469)
                    ·
                      rfl

theorem cell22_3768671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 3].length) (baseStart_3768671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768671 prefixEnd_3768671 := by exact prefixLift 3768671
  have htrace : WordTrace (prefixWord ++ tailWord_3768671) baseStart_3768671 baseEnd_3768671 := by
    simpa [prefixWord, tailWord_3768671, baseEnd_3768671] using wordTrace_append hprefix tailTrace_3768671
  have hstable : (prefixWord ++ tailWord_3768671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768671).length < 2 ^ (prefixWord ++ tailWord_3768671).sum := by decide
  have hdescent : baseEnd_3768671 < baseStart_3768671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768701 : List Nat := [1, 4, 1, 1, 2, 4, 3, 6]
def baseStart_3768701 : Nat := 118140960795 + 3768701 * 2 ^ 59
def prefixEnd_3768701 : Nat := 4983230072969 + 3 ^ 40 * 3768701 * 2
def baseEnd_3768701 : Nat := 143344818968901086941153

theorem tailTrace_3768701 : CollatzResearch.WordTrace tailWord_3768701 prefixEnd_3768701 143344818968901086941153 := by
  unfold tailWord_3768701
  simp only [CollatzResearch.WordTrace]
  refine ⟨137455817919647394732881957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91637211946431596488587971 137455817919647394732881957)
  ·
    refine ⟨25772965859933886512415367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 137455817919647394732881957 25772965859933886512415367)
    ·
      refine ⟨38659448789900829768623051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25772965859933886512415367 38659448789900829768623051)
      ·
        refine ⟨57989173184851244652934577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38659448789900829768623051 57989173184851244652934577)
        ·
          refine ⟨43491879888638433489700933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57989173184851244652934577 43491879888638433489700933)
          ·
            refine ⟨8154727479119706279318925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43491879888638433489700933 8154727479119706279318925)
            ·
              refine ⟨3058022804669889854744597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8154727479119706279318925 3058022804669889854744597)
              ·
                refine ⟨143344818968901086941153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3058022804669889854744597 143344818968901086941153)
                ·
                  rfl

theorem cell22_3768701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 6].length) (baseStart_3768701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768701 prefixEnd_3768701 := by exact prefixLift 3768701
  have htrace : WordTrace (prefixWord ++ tailWord_3768701) baseStart_3768701 baseEnd_3768701 := by
    simpa [prefixWord, tailWord_3768701, baseEnd_3768701] using wordTrace_append hprefix tailTrace_3768701
  have hstable : (prefixWord ++ tailWord_3768701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768701).length < 2 ^ (prefixWord ++ tailWord_3768701).sum := by decide
  have hdescent : baseEnd_3768701 < baseStart_3768701 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768729 : List Nat := [1, 2, 1, 2, 1, 4, 3, 1, 7]
def baseStart_3768729 : Nat := 118140960795 + 3768729 * 2 ^ 59
def prefixEnd_3768729 : Nat := 4983230072969 + 3 ^ 40 * 3768729 * 2
def baseEnd_3768729 : Nat := 430037651897442347590097

theorem tailTrace_3768729 : CollatzResearch.WordTrace tailWord_3768729 prefixEnd_3768729 430037651897442347590097 := by
  unfold tailWord_3768729
  simp only [CollatzResearch.WordTrace]
  refine ⟨137456839163545955514901241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91637892775697303676600827 137456839163545955514901241)
  ·
    refine ⟨103092629372659466636175931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137456839163545955514901241 103092629372659466636175931)
    ·
      refine ⟨154638944058989199954263897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103092629372659466636175931 154638944058989199954263897)
      ·
        refine ⟨115979208044241899965697923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154638944058989199954263897 115979208044241899965697923)
        ·
          refine ⟨173968812066362849948546885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115979208044241899965697923 173968812066362849948546885)
          ·
            refine ⟨32619152262443034365352541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173968812066362849948546885 32619152262443034365352541)
            ·
              refine ⟨12232182098416137887007203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32619152262443034365352541 12232182098416137887007203)
              ·
                refine ⟨18348273147624206830510805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12232182098416137887007203 18348273147624206830510805)
                ·
                  refine ⟨430037651897442347590097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18348273147624206830510805 430037651897442347590097)
                  ·
                    rfl

theorem cell22_3768729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 1, 7].length) (baseStart_3768729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768729 prefixEnd_3768729 := by exact prefixLift 3768729
  have htrace : WordTrace (prefixWord ++ tailWord_3768729) baseStart_3768729 baseEnd_3768729 := by
    simpa [prefixWord, tailWord_3768729, baseEnd_3768729] using wordTrace_append hprefix tailTrace_3768729
  have hstable : (prefixWord ++ tailWord_3768729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768729).length < 2 ^ (prefixWord ++ tailWord_3768729).sum := by decide
  have hdescent : baseEnd_3768729 < baseStart_3768729 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768810 : List Nat := [3, 1, 3, 1, 3, 3, 1, 2, 1, 4]
def baseStart_3768810 : Nat := 118140960795 + 3768810 * 2 ^ 59
def prefixEnd_3768810 : Nat := 4983230072969 + 3 ^ 40 * 3768810 * 2
def baseEnd_3768810 : Nat := 1290140683647669831495043

theorem tailTrace_3768810 : CollatzResearch.WordTrace tailWord_3768810 prefixEnd_3768810 1290140683647669831495043 := by
  unfold tailWord_3768810
  simp only [CollatzResearch.WordTrace]
  refine ⟨34364948369063126587149971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91639862317501670899066589 34364948369063126587149971)
  ·
    refine ⟨51547422553594689880724957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34364948369063126587149971 51547422553594689880724957)
    ·
      refine ⟨19330283457598008705271859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51547422553594689880724957 19330283457598008705271859)
      ·
        refine ⟨28995425186397013057907789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19330283457598008705271859 28995425186397013057907789)
        ·
          refine ⟨10873284444898879896715421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28995425186397013057907789 10873284444898879896715421)
          ·
            refine ⟨4077481666837079961268283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10873284444898879896715421 4077481666837079961268283)
            ·
              refine ⟨6116222500255619941902425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4077481666837079961268283 6116222500255619941902425)
              ·
                refine ⟨4587166875191714956426819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6116222500255619941902425 4587166875191714956426819)
                ·
                  refine ⟨6880750312787572434640229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4587166875191714956426819 6880750312787572434640229)
                  ·
                    refine ⟨1290140683647669831495043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6880750312787572434640229 1290140683647669831495043)
                    ·
                      rfl

theorem cell22_3768810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 3, 1, 2, 1, 4].length) (baseStart_3768810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768810 prefixEnd_3768810 := by exact prefixLift 3768810
  have htrace : WordTrace (prefixWord ++ tailWord_3768810) baseStart_3768810 baseEnd_3768810 := by
    simpa [prefixWord, tailWord_3768810, baseEnd_3768810] using wordTrace_append hprefix tailTrace_3768810
  have hstable : (prefixWord ++ tailWord_3768810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768810).length < 2 ^ (prefixWord ++ tailWord_3768810).sum := by decide
  have hdescent : baseEnd_3768810 < baseStart_3768810 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768819 : List Nat := [1, 1, 1, 2, 2, 2, 3, 10]
def baseStart_3768819 : Nat := 118140960795 + 3768819 * 2 ^ 59
def prefixEnd_3768819 : Nat := 4983230072969 + 3 ^ 40 * 3768819 * 2
def baseEnd_3768819 : Nat := 143349307170177423113335

theorem tailTrace_3768819 : CollatzResearch.WordTrace tailWord_3768819 prefixEnd_3768819 143349307170177423113335 := by
  unfold tailWord_3768819
  simp only [CollatzResearch.WordTrace]
  refine ⟨137460121733219900885677511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91640081155479933923785007 137460121733219900885677511)
  ·
    refine ⟨206190182599829851328516267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137460121733219900885677511 206190182599829851328516267)
    ·
      refine ⟨309285273899744776992774401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206190182599829851328516267 309285273899744776992774401)
      ·
        refine ⟨231963955424808582744580801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 309285273899744776992774401 231963955424808582744580801)
        ·
          refine ⟨173972966568606437058435601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 231963955424808582744580801 173972966568606437058435601)
          ·
            refine ⟨130479724926454827793826701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173972966568606437058435601 130479724926454827793826701)
            ·
              refine ⟨48929896847420560422685013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 130479724926454827793826701 48929896847420560422685013)
              ·
                refine ⟨143349307170177423113335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 48929896847420560422685013 143349307170177423113335)
                ·
                  rfl

theorem cell22_3768819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 10].length) (baseStart_3768819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768819 prefixEnd_3768819 := by exact prefixLift 3768819
  have htrace : WordTrace (prefixWord ++ tailWord_3768819) baseStart_3768819 baseEnd_3768819 := by
    simpa [prefixWord, tailWord_3768819, baseEnd_3768819] using wordTrace_append hprefix tailTrace_3768819
  have hstable : (prefixWord ++ tailWord_3768819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768819).length < 2 ^ (prefixWord ++ tailWord_3768819).sum := by decide
  have hdescent : baseEnd_3768819 < baseStart_3768819 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768836 : List Nat := [2, 3, 2, 3, 1, 11]
def baseStart_3768836 : Nat := 118140960795 + 3768836 * 2 ^ 59
def prefixEnd_3768836 : Nat := 4983230072969 + 3 ^ 40 * 3768836 * 2
def baseEnd_3768836 : Nat := 15927772641716227535123

theorem tailTrace_3768836 : CollatzResearch.WordTrace tailWord_3768836 prefixEnd_3768836 15927772641716227535123 := by
  unfold tailWord_3768836
  simp only [CollatzResearch.WordTrace]
  refine ⟨68730370887079156394523181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91640494516105541859364241 68730370887079156394523181)
  ·
    refine ⟨25773889082654683647946193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68730370887079156394523181 25773889082654683647946193)
    ·
      refine ⟨19330416811991012735959645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25773889082654683647946193 19330416811991012735959645)
      ·
        refine ⟨7248906304496629775984867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19330416811991012735959645 7248906304496629775984867)
        ·
          refine ⟨10873359456744944663977301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7248906304496629775984867 10873359456744944663977301)
          ·
            refine ⟨15927772641716227535123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 10873359456744944663977301 15927772641716227535123)
            ·
              rfl

theorem cell22_3768836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 11].length) (baseStart_3768836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768836 prefixEnd_3768836 := by exact prefixLift 3768836
  have htrace : WordTrace (prefixWord ++ tailWord_3768836) baseStart_3768836 baseEnd_3768836 := by
    simpa [prefixWord, tailWord_3768836, baseEnd_3768836] using wordTrace_append hprefix tailTrace_3768836
  have hstable : (prefixWord ++ tailWord_3768836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768836).length < 2 ^ (prefixWord ++ tailWord_3768836).sum := by decide
  have hdescent : baseEnd_3768836 < baseStart_3768836 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768866 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 4, 6]
def baseStart_3768866 : Nat := 118140960795 + 3768866 * 2 ^ 59
def prefixEnd_3768866 : Nat := 4983230072969 + 3 ^ 40 * 3768866 * 2
def baseEnd_3768866 : Nat := 1290159853592104352094871

theorem tailTrace_3768866 : CollatzResearch.WordTrace tailWord_3768866 prefixEnd_3768866 1290159853592104352094871 := by
  unfold tailWord_3768866
  simp only [CollatzResearch.WordTrace]
  refine ⟨34365458991012406978159613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91641223976033085275092301 34365458991012406978159613)
  ·
    refine ⟨12887047121629652616809855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34365458991012406978159613 12887047121629652616809855)
    ·
      refine ⟨19330570682444478925214783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12887047121629652616809855 19330570682444478925214783)
      ·
        refine ⟨28995856023666718387822175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19330570682444478925214783 28995856023666718387822175)
        ·
          refine ⟨43493784035500077581733263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28995856023666718387822175 43493784035500077581733263)
          ·
            refine ⟨65240676053250116372599895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43493784035500077581733263 65240676053250116372599895)
            ·
              refine ⟨97861014079875174558899843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 65240676053250116372599895 97861014079875174558899843)
              ·
                refine ⟨146791521119812761838349765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 97861014079875174558899843 146791521119812761838349765)
                ·
                  refine ⟨27523410209964892844690581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 146791521119812761838349765 27523410209964892844690581)
                  ·
                    refine ⟨1290159853592104352094871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 27523410209964892844690581 1290159853592104352094871)
                    ·
                      rfl

theorem cell22_3768866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 4, 6].length) (baseStart_3768866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768866 prefixEnd_3768866 := by exact prefixLift 3768866
  have htrace : WordTrace (prefixWord ++ tailWord_3768866) baseStart_3768866 baseEnd_3768866 := by
    simpa [prefixWord, tailWord_3768866, baseEnd_3768866] using wordTrace_append hprefix tailTrace_3768866
  have hstable : (prefixWord ++ tailWord_3768866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768866).length < 2 ^ (prefixWord ++ tailWord_3768866).sum := by decide
  have hdescent : baseEnd_3768866 < baseStart_3768866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768896 : List Nat := [2, 1, 1, 2, 2, 2, 3, 2, 2, 5]
def baseStart_3768896 : Nat := 118140960795 + 3768896 * 2 ^ 59
def prefixEnd_3768896 : Nat := 4983230072969 + 3 ^ 40 * 3768896 * 2
def baseEnd_3768896 : Nat := 1290170123205194273844779

theorem tailTrace_3768896 : CollatzResearch.WordTrace tailWord_3768896 prefixEnd_3768896 1290170123205194273844779 := by
  unfold tailWord_3768896
  simp only [CollatzResearch.WordTrace]
  refine ⟨68731465076970471518115271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91641953435960628690820361 68731465076970471518115271)
  ·
    refine ⟨103097197615455707277172907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68731465076970471518115271 103097197615455707277172907)
    ·
      refine ⟨154645796423183560915759361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103097197615455707277172907 154645796423183560915759361)
      ·
        refine ⟨115984347317387670686819521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154645796423183560915759361 115984347317387670686819521)
        ·
          refine ⟨86988260488040753015114641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115984347317387670686819521 86988260488040753015114641)
          ·
            refine ⟨65241195366030564761335981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86988260488040753015114641 65241195366030564761335981)
            ·
              refine ⟨24465448262261461785500993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65241195366030564761335981 24465448262261461785500993)
              ·
                refine ⟨18349086196696096339125745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24465448262261461785500993 18349086196696096339125745)
                ·
                  refine ⟨13761814647522072254344309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 18349086196696096339125745 13761814647522072254344309)
                  ·
                    refine ⟨1290170123205194273844779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13761814647522072254344309 1290170123205194273844779)
                    ·
                      rfl

theorem cell22_3768896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 2, 5].length) (baseStart_3768896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768896 prefixEnd_3768896 := by exact prefixLift 3768896
  have htrace : WordTrace (prefixWord ++ tailWord_3768896) baseStart_3768896 baseEnd_3768896 := by
    simpa [prefixWord, tailWord_3768896, baseEnd_3768896] using wordTrace_append hprefix tailTrace_3768896
  have hstable : (prefixWord ++ tailWord_3768896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768896).length < 2 ^ (prefixWord ++ tailWord_3768896).sum := by decide
  have hdescent : baseEnd_3768896 < baseStart_3768896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768902 : List Nat := [6, 1, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_3768902 : Nat := 118140960795 + 3768902 * 2 ^ 59
def prefixEnd_3768902 : Nat := 4983230072969 + 3 ^ 40 * 3768902 * 2
def baseEnd_3768902 : Nat := 1290172177127812258194761

theorem tailTrace_3768902 : CollatzResearch.WordTrace tailWord_3768902 prefixEnd_3768902 1290172177127812258194761 := by
  unfold tailWord_3768902
  simp only [CollatzResearch.WordTrace]
  refine ⟨4295723405997475189404655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 91642099327946137373965973 4295723405997475189404655)
  ·
    refine ⟨6443585108996212784106983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4295723405997475189404655 6443585108996212784106983)
    ·
      refine ⟨9665377663494319176160475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6443585108996212784106983 9665377663494319176160475)
      ·
        refine ⟨14498066495241478764240713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9665377663494319176160475 14498066495241478764240713)
        ·
          refine ⟨10873549871431109073180535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14498066495241478764240713 10873549871431109073180535)
          ·
            refine ⟨16310324807146663609770803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10873549871431109073180535 16310324807146663609770803)
            ·
              refine ⟨24465487210719995414656205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16310324807146663609770803 24465487210719995414656205)
              ·
                refine ⟨9174557704019998280496077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24465487210719995414656205 9174557704019998280496077)
                ·
                  refine ⟨3440459139007499355186029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9174557704019998280496077 3440459139007499355186029)
                  ·
                    refine ⟨1290172177127812258194761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3440459139007499355186029 1290172177127812258194761)
                    ·
                      rfl

theorem cell22_3768902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_3768902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768902 prefixEnd_3768902 := by exact prefixLift 3768902
  have htrace : WordTrace (prefixWord ++ tailWord_3768902) baseStart_3768902 baseEnd_3768902 := by
    simpa [prefixWord, tailWord_3768902, baseEnd_3768902] using wordTrace_append hprefix tailTrace_3768902
  have hstable : (prefixWord ++ tailWord_3768902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768902).length < 2 ^ (prefixWord ++ tailWord_3768902).sum := by decide
  have hdescent : baseEnd_3768902 < baseStart_3768902 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768911 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 5, 4]
def baseStart_3768911 : Nat := 118140960795 + 3768911 * 2 ^ 59
def prefixEnd_3768911 : Nat := 4983230072969 + 3 ^ 40 * 3768911 * 2
def baseEnd_3768911 : Nat := 1290175258011739234719733

theorem tailTrace_3768911 : CollatzResearch.WordTrace tailWord_3768911 prefixEnd_3768911 1290175258011739234719733 := by
  unfold tailWord_3768911
  simp only [CollatzResearch.WordTrace]
  refine ⟨137463477248886600598026587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91642318165924400398684391 137463477248886600598026587)
  ·
    refine ⟨206195215873329900897039881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137463477248886600598026587 206195215873329900897039881)
    ·
      refine ⟨154646411904997425672779911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206195215873329900897039881 154646411904997425672779911)
      ·
        refine ⟨231969617857496138509169867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154646411904997425672779911 231969617857496138509169867)
        ·
          refine ⟨347954426786244207763754801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231969617857496138509169867 347954426786244207763754801)
          ·
            refine ⟨260965820089683155822816101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 347954426786244207763754801 260965820089683155822816101)
            ·
              refine ⟨48931091266815591716778019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 260965820089683155822816101 48931091266815591716778019)
              ·
                refine ⟨73396636900223387575167029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48931091266815591716778019 73396636900223387575167029)
                ·
                  refine ⟨6880934709395942585171909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 73396636900223387575167029 6880934709395942585171909)
                  ·
                    refine ⟨1290175258011739234719733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6880934709395942585171909 1290175258011739234719733)
                    ·
                      rfl

theorem cell22_3768911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 4].length) (baseStart_3768911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768911 prefixEnd_3768911 := by exact prefixLift 3768911
  have htrace : WordTrace (prefixWord ++ tailWord_3768911) baseStart_3768911 baseEnd_3768911 := by
    simpa [prefixWord, tailWord_3768911, baseEnd_3768911] using wordTrace_append hprefix tailTrace_3768911
  have hstable : (prefixWord ++ tailWord_3768911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768911).length < 2 ^ (prefixWord ++ tailWord_3768911).sum := by decide
  have hdescent : baseEnd_3768911 < baseStart_3768911 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768928 : List Nat := [2, 1, 1, 3, 2, 1, 3, 4, 1, 4]
def baseStart_3768928 : Nat := 118140960795 + 3768928 * 2 ^ 59
def prefixEnd_3768928 : Nat := 4983230072969 + 3 ^ 40 * 3768928 * 2
def baseEnd_3768928 : Nat := 1290181077459156857044681

theorem tailTrace_3768928 : CollatzResearch.WordTrace tailWord_3768928 prefixEnd_3768928 1290181077459156857044681 := by
  unfold tailWord_3768928
  simp only [CollatzResearch.WordTrace]
  refine ⟨68732048644912506250697719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91642731526550008334263625 68732048644912506250697719)
  ·
    refine ⟨103098072967368759376046579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68732048644912506250697719 103098072967368759376046579)
    ·
      refine ⟨154647109451053139064069869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103098072967368759376046579 154647109451053139064069869)
      ·
        refine ⟨57992666044144927149026201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 154647109451053139064069869 57992666044144927149026201)
        ·
          refine ⟨43494499533108695361769651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57992666044144927149026201 43494499533108695361769651)
          ·
            refine ⟨65241749299663043042654477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43494499533108695361769651 65241749299663043042654477)
            ·
              refine ⟨24465655987373641140995429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 65241749299663043042654477 24465655987373641140995429)
              ·
                refine ⟨4587310497632557713936643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 24465655987373641140995429 4587310497632557713936643)
                ·
                  refine ⟨6880965746448836570904965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4587310497632557713936643 6880965746448836570904965)
                  ·
                    refine ⟨1290181077459156857044681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6880965746448836570904965 1290181077459156857044681)
                    ·
                      rfl

theorem cell22_3768928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 1, 4].length) (baseStart_3768928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768928 prefixEnd_3768928 := by exact prefixLift 3768928
  have htrace : WordTrace (prefixWord ++ tailWord_3768928) baseStart_3768928 baseEnd_3768928 := by
    simpa [prefixWord, tailWord_3768928, baseEnd_3768928] using wordTrace_append hprefix tailTrace_3768928
  have hstable : (prefixWord ++ tailWord_3768928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768928).length < 2 ^ (prefixWord ++ tailWord_3768928).sum := by decide
  have hdescent : baseEnd_3768928 < baseStart_3768928 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768936 : List Nat := [2, 1, 4, 3, 3, 1, 1, 3, 1, 3]
def baseStart_3768936 : Nat := 118140960795 + 3768936 * 2 ^ 59
def prefixEnd_3768936 : Nat := 4983230072969 + 3 ^ 40 * 3768936 * 2
def baseEnd_3768936 : Nat := 1290183816022647502844657

theorem tailTrace_3768936 : CollatzResearch.WordTrace tailWord_3768936 prefixEnd_3768936 1290183816022647502844657 := by
  unfold tailWord_3768936
  simp only [CollatzResearch.WordTrace]
  refine ⟨68732194536898014933843331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91642926049197353245124441 68732194536898014933843331)
  ·
    refine ⟨103098291805347022400764997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68732194536898014933843331 103098291805347022400764997)
    ·
      refine ⟨19330929713502566700143437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 103098291805347022400764997 19330929713502566700143437)
      ·
        refine ⟨7249098642563462512553789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19330929713502566700143437 7249098642563462512553789)
        ·
          refine ⟨2718411990961298442207671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7249098642563462512553789 2718411990961298442207671)
          ·
            refine ⟨4077617986441947663311507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2718411990961298442207671 4077617986441947663311507)
            ·
              refine ⟨6116426979662921494967261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4077617986441947663311507 6116426979662921494967261)
              ·
                refine ⟨2293660117373595560612723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6116426979662921494967261 2293660117373595560612723)
                ·
                  refine ⟨3440490176060393340919085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2293660117373595560612723 3440490176060393340919085)
                  ·
                    refine ⟨1290183816022647502844657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3440490176060393340919085 1290183816022647502844657)
                    ·
                      rfl

theorem cell22_3768936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 1, 3].length) (baseStart_3768936 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768936 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768936 prefixEnd_3768936 := by exact prefixLift 3768936
  have htrace : WordTrace (prefixWord ++ tailWord_3768936) baseStart_3768936 baseEnd_3768936 := by
    simpa [prefixWord, tailWord_3768936, baseEnd_3768936] using wordTrace_append hprefix tailTrace_3768936
  have hstable : (prefixWord ++ tailWord_3768936).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768936).length < 2 ^ (prefixWord ++ tailWord_3768936).sum := by decide
  have hdescent : baseEnd_3768936 < baseStart_3768936 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3768988 : List Nat := [2, 2, 3, 2, 2, 1, 2, 8]
def baseStart_3768988 : Nat := 118140960795 + 3768988 * 2 ^ 59
def prefixEnd_3768988 : Nat := 4983230072969 + 3 ^ 40 * 3768988 * 2
def baseEnd_3768988 : Nat := 143355735187259633393833

theorem tailTrace_3768988 : CollatzResearch.WordTrace tailWord_3768988 prefixEnd_3768988 143355735187259633393833 := by
  unfold tailWord_3768988
  simp only [CollatzResearch.WordTrace]
  refine ⟨68733142834803821374289809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91644190446405095165719745 68733142834803821374289809)
  ·
    refine ⟨51549857126102866030717357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68733142834803821374289809 51549857126102866030717357)
    ·
      refine ⟨19331196422288574761519009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51549857126102866030717357 19331196422288574761519009)
      ·
        refine ⟨14498397316716431071139257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19331196422288574761519009 14498397316716431071139257)
        ·
          refine ⟨10873797987537323303354443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14498397316716431071139257 10873797987537323303354443)
          ·
            refine ⟨16310696981305984955031665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10873797987537323303354443 16310696981305984955031665)
            ·
              refine ⟨12233022735979488716273749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16310696981305984955031665 12233022735979488716273749)
              ·
                refine ⟨143355735187259633393833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12233022735979488716273749 143355735187259633393833)
                ·
                  rfl

theorem cell22_3768988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 8].length) (baseStart_3768988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3768988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3768988 prefixEnd_3768988 := by exact prefixLift 3768988
  have htrace : WordTrace (prefixWord ++ tailWord_3768988) baseStart_3768988 baseEnd_3768988 := by
    simpa [prefixWord, tailWord_3768988, baseEnd_3768988] using wordTrace_append hprefix tailTrace_3768988
  have hstable : (prefixWord ++ tailWord_3768988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3768988).length < 2 ^ (prefixWord ++ tailWord_3768988).sum := by decide
  have hdescent : baseEnd_3768988 < baseStart_3768988 := by decide
  rcases family_descends (prefixWord ++ tailWord_3768988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769001 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 1, 8]
def baseStart_3769001 : Nat := 118140960795 + 3769001 * 2 ^ 59
def prefixEnd_3769001 : Nat := 4983230072969 + 3 ^ 40 * 3769001 * 2
def baseEnd_3769001 : Nat := 1290206066851008999969457

theorem tailTrace_3769001 : CollatzResearch.WordTrace tailWord_3769001 prefixEnd_3769001 1290206066851008999969457 := by
  unfold tailWord_3769001
  simp only [CollatzResearch.WordTrace]
  refine ⟨137466759818560545968802857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91644506545707030645868571 137466759818560545968802857)
  ·
    refine ⟨103100069863920409476602143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137466759818560545968802857 103100069863920409476602143)
    ·
      refine ⟨154650104795880614214903215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103100069863920409476602143 154650104795880614214903215)
      ·
        refine ⟨231975157193820921322354823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154650104795880614214903215 231975157193820921322354823)
        ·
          refine ⟨347962735790731381983532235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231975157193820921322354823 347962735790731381983532235)
          ·
            refine ⟨521944103686097072975298353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 347962735790731381983532235 521944103686097072975298353)
            ·
              refine ⟨391458077764572804731473765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 521944103686097072975298353 391458077764572804731473765)
              ·
                refine ⟨73398389580857400887151331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 391458077764572804731473765 73398389580857400887151331)
                ·
                  refine ⟨110097584371286101330726997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 73398389580857400887151331 110097584371286101330726997)
                  ·
                    refine ⟨1290206066851008999969457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 110097584371286101330726997 1290206066851008999969457)
                    ·
                      rfl

theorem cell22_3769001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 8].length) (baseStart_3769001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769001 prefixEnd_3769001 := by exact prefixLift 3769001
  have htrace : WordTrace (prefixWord ++ tailWord_3769001) baseStart_3769001 baseEnd_3769001 := by
    simpa [prefixWord, tailWord_3769001, baseEnd_3769001] using wordTrace_append hprefix tailTrace_3769001
  have hstable : (prefixWord ++ tailWord_3769001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769001).length < 2 ^ (prefixWord ++ tailWord_3769001).sum := by decide
  have hdescent : baseEnd_3769001 < baseStart_3769001 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769009 : List Nat := [1, 2, 2, 6, 1, 1, 2, 2, 2, 3]
def baseStart_3769009 : Nat := 118140960795 + 3769009 * 2 ^ 59
def prefixEnd_3769009 : Nat := 4983230072969 + 3 ^ 40 * 3769009 * 2
def baseEnd_3769009 : Nat := 1290208805414499645769433

theorem tailTrace_3769009 : CollatzResearch.WordTrace tailWord_3769009 prefixEnd_3769009 1290208805414499645769433 := by
  unfold tailWord_3769009
  simp only [CollatzResearch.WordTrace]
  refine ⟨137467051602531563335094081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91644701068354375556729387 137467051602531563335094081)
  ·
    refine ⟨103100288701898672501320561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137467051602531563335094081 103100288701898672501320561)
    ·
      refine ⟨77325216526424004375990421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103100288701898672501320561 77325216526424004375990421)
      ·
        refine ⟨3624619524676125205124551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 77325216526424004375990421 3624619524676125205124551)
        ·
          refine ⟨5436929287014187807686827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3624619524676125205124551 5436929287014187807686827)
          ·
            refine ⟨8155393930521281711530241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5436929287014187807686827 8155393930521281711530241)
            ·
              refine ⟨6116545447890961283647681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8155393930521281711530241 6116545447890961283647681)
              ·
                refine ⟨4587409085918220962735761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6116545447890961283647681 4587409085918220962735761)
                ·
                  refine ⟨3440556814438665722051821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4587409085918220962735761 3440556814438665722051821)
                  ·
                    refine ⟨1290208805414499645769433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3440556814438665722051821 1290208805414499645769433)
                    ·
                      rfl

theorem cell22_3769009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 3].length) (baseStart_3769009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769009 prefixEnd_3769009 := by exact prefixLift 3769009
  have htrace : WordTrace (prefixWord ++ tailWord_3769009) baseStart_3769009 baseEnd_3769009 := by
    simpa [prefixWord, tailWord_3769009, baseEnd_3769009] using wordTrace_append hprefix tailTrace_3769009
  have hstable : (prefixWord ++ tailWord_3769009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769009).length < 2 ^ (prefixWord ++ tailWord_3769009).sum := by decide
  have hdescent : baseEnd_3769009 < baseStart_3769009 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769020 : List Nat := [2, 2, 2, 3, 1, 1, 2, 3, 3, 3]
def baseStart_3769020 : Nat := 118140960795 + 3769020 * 2 ^ 59
def prefixEnd_3769020 : Nat := 4983230072969 + 3 ^ 40 * 3769020 * 2
def baseEnd_3769020 : Nat := 1290212570939299283744399

theorem tailTrace_3769020 : CollatzResearch.WordTrace tailWord_3769020 prefixEnd_3769020 1290212570939299283744399 := by
  unfold tailWord_3769020
  simp only [CollatzResearch.WordTrace]
  refine ⟨68733726402745856106872257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91644968536994474809163009 68733726402745856106872257)
  ·
    refine ⟨51550294802059392080154193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68733726402745856106872257 51550294802059392080154193)
    ·
      refine ⟨38662721101544544060115645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51550294802059392080154193 38662721101544544060115645)
      ·
        refine ⟨14498520413079204022543367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38662721101544544060115645 14498520413079204022543367)
        ·
          refine ⟨21747780619618806033815051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14498520413079204022543367 21747780619618806033815051)
          ·
            refine ⟨32621670929428209050722577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21747780619618806033815051 32621670929428209050722577)
            ·
              refine ⟨24466253197071156788041933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32621670929428209050722577 24466253197071156788041933)
              ·
                refine ⟨9174844948901683795515725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24466253197071156788041933 9174844948901683795515725)
                ·
                  refine ⟨3440566855838131423318397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9174844948901683795515725 3440566855838131423318397)
                  ·
                    refine ⟨1290212570939299283744399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3440566855838131423318397 1290212570939299283744399)
                    ·
                      rfl

theorem cell22_3769020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_3769020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769020 prefixEnd_3769020 := by exact prefixLift 3769020
  have htrace : WordTrace (prefixWord ++ tailWord_3769020) baseStart_3769020 baseEnd_3769020 := by
    simpa [prefixWord, tailWord_3769020, baseEnd_3769020] using wordTrace_append hprefix tailTrace_3769020
  have hstable : (prefixWord ++ tailWord_3769020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769020).length < 2 ^ (prefixWord ++ tailWord_3769020).sum := by decide
  have hdescent : baseEnd_3769020 < baseStart_3769020 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769095 : List Nat := [1, 1, 4, 4, 1, 1, 2, 2, 6]
def baseStart_3769095 : Nat := 118140960795 + 3769095 * 2 ^ 59
def prefixEnd_3769095 : Nat := 4983230072969 + 3 ^ 40 * 3769095 * 2
def baseEnd_3769095 : Nat := 430079414990674696039723

theorem tailTrace_3769095 : CollatzResearch.WordTrace tailWord_3769095 prefixEnd_3769095 430079414990674696039723 := by
  unfold tailWord_3769095
  simp only [CollatzResearch.WordTrace]
  refine ⟨137470188280220000022724739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91646792186813333348483159 137470188280220000022724739)
  ·
    refine ⟨206205282420330000034087109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137470188280220000022724739 206205282420330000034087109)
    ·
      refine ⟨38663490453811875006391333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206205282420330000034087109 38663490453811875006391333)
      ·
        refine ⟨7249404460089726563698375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38663490453811875006391333 7249404460089726563698375)
        ·
          refine ⟨10874106690134589845547563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7249404460089726563698375 10874106690134589845547563)
          ·
            refine ⟨16311160035201884768321345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10874106690134589845547563 16311160035201884768321345)
            ·
              refine ⟨12233370026401413576241009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16311160035201884768321345 12233370026401413576241009)
              ·
                refine ⟨9175027519801060182180757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12233370026401413576241009 9175027519801060182180757)
                ·
                  refine ⟨430079414990674696039723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9175027519801060182180757 430079414990674696039723)
                  ·
                    rfl

theorem cell22_3769095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 6].length) (baseStart_3769095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769095 prefixEnd_3769095 := by exact prefixLift 3769095
  have htrace : WordTrace (prefixWord ++ tailWord_3769095) baseStart_3769095 baseEnd_3769095 := by
    simpa [prefixWord, tailWord_3769095, baseEnd_3769095] using wordTrace_append hprefix tailTrace_3769095
  have hstable : (prefixWord ++ tailWord_3769095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769095).length < 2 ^ (prefixWord ++ tailWord_3769095).sum := by decide
  have hdescent : baseEnd_3769095 < baseStart_3769095 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769125 : List Nat := [1, 3, 1, 2, 3, 1, 3, 2, 2, 4]
def baseStart_3769125 : Nat := 118140960795 + 3769125 * 2 ^ 59
def prefixEnd_3769125 : Nat := 4983230072969 + 3 ^ 40 * 3769125 * 2
def baseEnd_3769125 : Nat := 1290248514585114009869077

theorem tailTrace_3769125 : CollatzResearch.WordTrace tailWord_3769125 prefixEnd_3769125 1290248514585114009869077 := by
  unfold tailWord_3769125
  simp only [CollatzResearch.WordTrace]
  refine ⟨137471282470111315146316829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91647521646740876764211219 137471282470111315146316829)
  ·
    refine ⟨51551730926291743179868811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137471282470111315146316829 51551730926291743179868811)
    ·
      refine ⟨77327596389437614769803217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51551730926291743179868811 77327596389437614769803217)
      ·
        refine ⟨57995697292078211077352413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77327596389437614769803217 57995697292078211077352413)
        ·
          refine ⟨21748386484529329154007155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57995697292078211077352413 21748386484529329154007155)
          ·
            refine ⟨32622579726793993731010733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21748386484529329154007155 32622579726793993731010733)
            ·
              refine ⟨12233467397547747649129025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32622579726793993731010733 12233467397547747649129025)
              ·
                refine ⟨9175100548160810736846769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12233467397547747649129025 9175100548160810736846769)
                ·
                  refine ⟨6881325411120608052635077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9175100548160810736846769 6881325411120608052635077)
                  ·
                    refine ⟨1290248514585114009869077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6881325411120608052635077 1290248514585114009869077)
                    ·
                      rfl

theorem cell22_3769125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 4].length) (baseStart_3769125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769125 prefixEnd_3769125 := by exact prefixLift 3769125
  have htrace : WordTrace (prefixWord ++ tailWord_3769125) baseStart_3769125 baseEnd_3769125 := by
    simpa [prefixWord, tailWord_3769125, baseEnd_3769125] using wordTrace_append hprefix tailTrace_3769125
  have hstable : (prefixWord ++ tailWord_3769125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769125).length < 2 ^ (prefixWord ++ tailWord_3769125).sum := by decide
  have hdescent : baseEnd_3769125 < baseStart_3769125 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769155 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 5, 3]
def baseStart_3769155 : Nat := 118140960795 + 3769155 * 2 ^ 59
def prefixEnd_3769155 : Nat := 4983230072969 + 3 ^ 40 * 3769155 * 2
def baseEnd_3769155 : Nat := 1290258784198203931618985

theorem tailTrace_3769155 : CollatzResearch.WordTrace tailWord_3769155 prefixEnd_3769155 1290258784198203931618985 := by
  unfold tailWord_3769155
  simp only [CollatzResearch.WordTrace]
  refine ⟨137472376660002630269908919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91648251106668420179939279 137472376660002630269908919)
  ·
    refine ⟨206208564990003945404863379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137472376660002630269908919 206208564990003945404863379)
    ·
      refine ⟨309312847485005918107295069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206208564990003945404863379 309312847485005918107295069)
      ·
        refine ⟨115992317806877219290235651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 309312847485005918107295069 115992317806877219290235651)
        ·
          refine ⟨173988476710315828935353477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115992317806877219290235651 173988476710315828935353477)
          ·
            refine ⟨32622839383184217925378777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173988476710315828935353477 32622839383184217925378777)
            ·
              refine ⟨24467129537388163444034083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32622839383184217925378777 24467129537388163444034083)
              ·
                refine ⟨36700694306082245166051125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24467129537388163444034083 36700694306082245166051125)
                ·
                  refine ⟨3440690091195210484317293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 36700694306082245166051125 3440690091195210484317293)
                  ·
                    refine ⟨1290258784198203931618985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3440690091195210484317293 1290258784198203931618985)
                    ·
                      rfl

theorem cell22_3769155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 3].length) (baseStart_3769155 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769155 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769155 prefixEnd_3769155 := by exact prefixLift 3769155
  have htrace : WordTrace (prefixWord ++ tailWord_3769155) baseStart_3769155 baseEnd_3769155 := by
    simpa [prefixWord, tailWord_3769155, baseEnd_3769155] using wordTrace_append hprefix tailTrace_3769155
  have hstable : (prefixWord ++ tailWord_3769155).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769155).length < 2 ^ (prefixWord ++ tailWord_3769155).sum := by decide
  have hdescent : baseEnd_3769155 < baseStart_3769155 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769168 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 9]
def baseStart_3769168 : Nat := 118140960795 + 3769168 * 2 ^ 59
def prefixEnd_3769168 : Nat := 4983230072969 + 3 ^ 40 * 3769168 * 2
def baseEnd_3769168 : Nat := 430087744787958743681315

theorem tailTrace_3769168 : CollatzResearch.WordTrace tailWord_3769168 prefixEnd_3769168 430087744787958743681315 := by
  unfold tailWord_3769168
  simp only [CollatzResearch.WordTrace]
  refine ⟨68736425404477766745066079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91648567205970355660088105 68736425404477766745066079)
  ·
    refine ⟨103104638106716650117599119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68736425404477766745066079 103104638106716650117599119)
    ·
      refine ⟨154656957160074975176398679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103104638106716650117599119 154656957160074975176398679)
      ·
        refine ⟨231985435740112462764598019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154656957160074975176398679 231985435740112462764598019)
        ·
          refine ⟨347978153610168694146897029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 231985435740112462764598019 347978153610168694146897029)
          ·
            refine ⟨65245903801906630152543193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 347978153610168694146897029 65245903801906630152543193)
            ·
              refine ⟨48934427851429972614407395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65245903801906630152543193 48934427851429972614407395)
              ·
                refine ⟨73401641777144958921611093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48934427851429972614407395 73401641777144958921611093)
                ·
                  refine ⟨430087744787958743681315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73401641777144958921611093 430087744787958743681315)
                  ·
                    rfl

theorem cell22_3769168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 9].length) (baseStart_3769168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769168 prefixEnd_3769168 := by exact prefixLift 3769168
  have htrace : WordTrace (prefixWord ++ tailWord_3769168) baseStart_3769168 baseEnd_3769168 := by
    simpa [prefixWord, tailWord_3769168, baseEnd_3769168] using wordTrace_append hprefix tailTrace_3769168
  have hstable : (prefixWord ++ tailWord_3769168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769168).length < 2 ^ (prefixWord ++ tailWord_3769168).sum := by decide
  have hdescent : baseEnd_3769168 < baseStart_3769168 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769215 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 3, 4]
def baseStart_3769215 : Nat := 118140960795 + 3769215 * 2 ^ 59
def prefixEnd_3769215 : Nat := 4983230072969 + 3 ^ 40 * 3769215 * 2
def baseEnd_3769215 : Nat := 1290279323424383775118801

theorem tailTrace_3769215 : CollatzResearch.WordTrace tailWord_3769215 prefixEnd_3769215 1290279323424383775118801 := by
  unfold tailWord_3769215
  simp only [CollatzResearch.WordTrace]
  refine ⟨137474565039785260517093099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91649710026523507011395399 137474565039785260517093099)
  ·
    refine ⟨206211847559677890775639649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137474565039785260517093099 206211847559677890775639649)
    ·
      refine ⟨154658885669758418081729737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206211847559677890775639649 154658885669758418081729737)
      ·
        refine ⟨115994164252318813561297303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154658885669758418081729737 115994164252318813561297303)
        ·
          refine ⟨173991246378478220341945955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115994164252318813561297303 173991246378478220341945955)
          ·
            refine ⟨260986869567717330512918933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173991246378478220341945955 260986869567717330512918933)
            ·
              refine ⟨12233759510986749867793075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 260986869567717330512918933 12233759510986749867793075)
              ·
                refine ⟨18350639266480124801689613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12233759510986749867793075 18350639266480124801689613)
                ·
                  refine ⟨6881489724930046800633605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18350639266480124801689613 6881489724930046800633605)
                  ·
                    refine ⟨1290279323424383775118801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6881489724930046800633605 1290279323424383775118801)
                    ·
                      rfl

theorem cell22_3769215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 4].length) (baseStart_3769215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769215 prefixEnd_3769215 := by exact prefixLift 3769215
  have htrace : WordTrace (prefixWord ++ tailWord_3769215) baseStart_3769215 baseEnd_3769215 := by
    simpa [prefixWord, tailWord_3769215, baseEnd_3769215] using wordTrace_append hprefix tailTrace_3769215
  have hstable : (prefixWord ++ tailWord_3769215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769215).length < 2 ^ (prefixWord ++ tailWord_3769215).sum := by decide
  have hdescent : baseEnd_3769215 < baseStart_3769215 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769247 : List Nat := [1, 1, 2, 5, 2, 2, 2, 1, 6]
def baseStart_3769247 : Nat := 118140960795 + 3769247 * 2 ^ 59
def prefixEnd_3769247 : Nat := 4983230072969 + 3 ^ 40 * 3769247 * 2
def baseEnd_3769247 : Nat := 430096759226115452772901

theorem tailTrace_3769247 : CollatzResearch.WordTrace tailWord_3769247 prefixEnd_3769247 430096759226115452772901 := by
  unfold tailWord_3769247
  simp only [CollatzResearch.WordTrace]
  refine ⟨137475732175669329982257995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91650488117112886654838663 137475732175669329982257995)
  ·
    refine ⟨206213598263503994973386993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137475732175669329982257995 206213598263503994973386993)
    ·
      refine ⟨154660198697627996230040245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206213598263503994973386993 154660198697627996230040245)
      ·
        refine ⟨14499393627902624646566273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154660198697627996230040245 14499393627902624646566273)
        ·
          refine ⟨10874545220926968484924705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14499393627902624646566273 10874545220926968484924705)
          ·
            refine ⟨8155908915695226363693529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10874545220926968484924705 8155908915695226363693529)
            ·
              refine ⟨6116931686771419772770147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8155908915695226363693529 6116931686771419772770147)
              ·
                refine ⟨9175397530157129659155221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6116931686771419772770147 9175397530157129659155221)
                ·
                  refine ⟨430096759226115452772901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9175397530157129659155221 430096759226115452772901)
                  ·
                    rfl

theorem cell22_3769247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 2, 1, 6].length) (baseStart_3769247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769247 prefixEnd_3769247 := by exact prefixLift 3769247
  have htrace : WordTrace (prefixWord ++ tailWord_3769247) baseStart_3769247 baseEnd_3769247 := by
    simpa [prefixWord, tailWord_3769247, baseEnd_3769247] using wordTrace_append hprefix tailTrace_3769247
  have hstable : (prefixWord ++ tailWord_3769247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769247).length < 2 ^ (prefixWord ++ tailWord_3769247).sum := by decide
  have hdescent : baseEnd_3769247 < baseStart_3769247 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769260 : List Nat := [2, 2, 1, 1, 1, 1, 2, 4, 4, 4]
def baseStart_3769260 : Nat := 118140960795 + 3769260 * 2 ^ 59
def prefixEnd_3769260 : Nat := 4983230072969 + 3 ^ 40 * 3769260 * 2
def baseEnd_3769260 : Nat := 1290294727844018657743663

theorem tailTrace_3769260 : CollatzResearch.WordTrace tailWord_3769260 prefixEnd_3769260 1290294727844018657743663 := by
  unfold tailWord_3769260
  simp only [CollatzResearch.WordTrace]
  refine ⟨68738103162311116601240617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91650804216414822134987489 68738103162311116601240617)
  ·
    refine ⟨51553577371733337450930463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68738103162311116601240617 51553577371733337450930463)
    ·
      refine ⟨77330366057600006176395695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51553577371733337450930463 77330366057600006176395695)
      ·
        refine ⟨115995549086400009264593543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77330366057600006176395695 115995549086400009264593543)
        ·
          refine ⟨173993323629600013896890315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115995549086400009264593543 173993323629600013896890315)
          ·
            refine ⟨260989985444400020845335473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173993323629600013896890315 260989985444400020845335473)
            ·
              refine ⟨195742489083300015634001605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 260989985444400020845335473 195742489083300015634001605)
              ·
                refine ⟨36701716703118752931375301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 195742489083300015634001605 36701716703118752931375301)
                ·
                  refine ⟨6881571881834766174632869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 36701716703118752931375301 6881571881834766174632869)
                  ·
                    refine ⟨1290294727844018657743663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6881571881834766174632869 1290294727844018657743663)
                    ·
                      rfl

theorem cell22_3769260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_3769260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769260 prefixEnd_3769260 := by exact prefixLift 3769260
  have htrace : WordTrace (prefixWord ++ tailWord_3769260) baseStart_3769260 baseEnd_3769260 := by
    simpa [prefixWord, tailWord_3769260, baseEnd_3769260] using wordTrace_append hprefix tailTrace_3769260
  have hstable : (prefixWord ++ tailWord_3769260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769260).length < 2 ^ (prefixWord ++ tailWord_3769260).sum := by decide
  have hdescent : baseEnd_3769260 < baseStart_3769260 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769354 : List Nat := [3, 1, 2, 2, 3, 2, 2, 2, 5]
def baseStart_3769354 : Nat := 118140960795 + 3769354 * 2 ^ 59
def prefixEnd_3769354 : Nat := 4983230072969 + 3 ^ 40 * 3769354 * 2
def baseEnd_3769354 : Nat := 430108968655011248631125

theorem tailTrace_3769354 : CollatzResearch.WordTrace tailWord_3769354 prefixEnd_3769354 430108968655011248631125 := by
  unfold tailWord_3769354
  simp only [CollatzResearch.WordTrace]
  refine ⟨34369908696570421814100779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 91653089857521124837602077 34369908696570421814100779)
  ·
    refine ⟨51554863044855632721151169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34369908696570421814100779 51554863044855632721151169)
    ·
      refine ⟨38666147283641724540863377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51554863044855632721151169 38666147283641724540863377)
      ·
        refine ⟨28999610462731293405647533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38666147283641724540863377 28999610462731293405647533)
        ·
          refine ⟨10874853923524235027117825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28999610462731293405647533 10874853923524235027117825)
          ·
            refine ⟨8156140442643176270338369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10874853923524235027117825 8156140442643176270338369)
            ·
              refine ⟨6117105331982382202753777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8156140442643176270338369 6117105331982382202753777)
              ·
                refine ⟨4587828998986786652065333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6117105331982382202753777 4587828998986786652065333)
                ·
                  refine ⟨430108968655011248631125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4587828998986786652065333 430108968655011248631125)
                  ·
                    rfl

theorem cell22_3769354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 2, 2, 5].length) (baseStart_3769354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769354 prefixEnd_3769354 := by exact prefixLift 3769354
  have htrace : WordTrace (prefixWord ++ tailWord_3769354) baseStart_3769354 baseEnd_3769354 := by
    simpa [prefixWord, tailWord_3769354, baseEnd_3769354] using wordTrace_append hprefix tailTrace_3769354
  have hstable : (prefixWord ++ tailWord_3769354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769354).length < 2 ^ (prefixWord ++ tailWord_3769354).sum := by decide
  have hdescent : baseEnd_3769354 < baseStart_3769354 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769358 : List Nat := [4, 1, 1, 2, 2, 2, 4, 2, 1, 3]
def baseStart_3769358 : Nat := 118140960795 + 3769358 * 2 ^ 59
def prefixEnd_3769358 : Nat := 4983230072969 + 3 ^ 40 * 3769358 * 2
def baseEnd_3769358 : Nat := 1290328275246779068793363

theorem tailTrace_3769358 : CollatzResearch.WordTrace tailWord_3769358 prefixEnd_3769358 1290328275246779068793363 := by
  unfold tailWord_3769358
  simp only [CollatzResearch.WordTrace]
  refine ⟨17184972584783399492443591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91653187118844797293032485 17184972584783399492443591)
  ·
    refine ⟨25777458877175099238665387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17184972584783399492443591 25777458877175099238665387)
    ·
      refine ⟨38666188315762648857998081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25777458877175099238665387 38666188315762648857998081)
      ·
        refine ⟨28999641236821986643498561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38666188315762648857998081 28999641236821986643498561)
        ·
          refine ⟨21749730927616489982623921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28999641236821986643498561 21749730927616489982623921)
          ·
            refine ⟨16312298195712367486967941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21749730927616489982623921 16312298195712367486967941)
            ·
              refine ⟨3058555911696068903806489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16312298195712367486967941 3058555911696068903806489)
              ·
                refine ⟨2293916933772051677854867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3058555911696068903806489 2293916933772051677854867)
                ·
                  refine ⟨3440875400658077516782301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2293916933772051677854867 3440875400658077516782301)
                  ·
                    refine ⟨1290328275246779068793363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3440875400658077516782301 1290328275246779068793363)
                    ·
                      rfl

theorem cell22_3769358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 4, 2, 1, 3].length) (baseStart_3769358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769358 prefixEnd_3769358 := by exact prefixLift 3769358
  have htrace : WordTrace (prefixWord ++ tailWord_3769358) baseStart_3769358 baseEnd_3769358 := by
    simpa [prefixWord, tailWord_3769358, baseEnd_3769358] using wordTrace_append hprefix tailTrace_3769358
  have hstable : (prefixWord ++ tailWord_3769358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769358).length < 2 ^ (prefixWord ++ tailWord_3769358).sum := by decide
  have hdescent : baseEnd_3769358 < baseStart_3769358 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769401 : List Nat := [1, 2, 1, 5, 2, 1, 4, 1, 1, 4]
def baseStart_3769401 : Nat := 118140960795 + 3769401 * 2 ^ 59
def prefixEnd_3769401 : Nat := 4983230072969 + 3 ^ 40 * 3769401 * 2
def baseEnd_3769401 : Nat := 1290342995025541289968231

theorem tailTrace_3769401 : CollatzResearch.WordTrace tailWord_3769401 prefixEnd_3769401 1290342995025541289968231 := by
  unfold tailWord_3769401
  simp only [CollatzResearch.WordTrace]
  refine ⟨137481349017111414283364057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91654232678074276188909371 137481349017111414283364057)
  ·
    refine ⟨103111011762833560712523043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 137481349017111414283364057 103111011762833560712523043)
    ·
      refine ⟨154666517644250341068784565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103111011762833560712523043 154666517644250341068784565)
      ·
        refine ⟨14499986029148469475198553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 154666517644250341068784565 14499986029148469475198553)
        ·
          refine ⟨10874989521861352106398915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14499986029148469475198553 10874989521861352106398915)
          ·
            refine ⟨16312484282792028159598373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10874989521861352106398915 16312484282792028159598373)
            ·
              refine ⟨3058590803023505279924695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16312484282792028159598373 3058590803023505279924695)
              ·
                refine ⟨4587886204535257919887043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3058590803023505279924695 4587886204535257919887043)
                ·
                  refine ⟨6881829306802886879830565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4587886204535257919887043 6881829306802886879830565)
                  ·
                    refine ⟨1290342995025541289968231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6881829306802886879830565 1290342995025541289968231)
                    ·
                      rfl

theorem cell22_3769401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 4, 1, 1, 4].length) (baseStart_3769401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769401 prefixEnd_3769401 := by exact prefixLift 3769401
  have htrace : WordTrace (prefixWord ++ tailWord_3769401) baseStart_3769401 baseEnd_3769401 := by
    simpa [prefixWord, tailWord_3769401, baseEnd_3769401] using wordTrace_append hprefix tailTrace_3769401
  have hstable : (prefixWord ++ tailWord_3769401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769401).length < 2 ^ (prefixWord ++ tailWord_3769401).sum := by decide
  have hdescent : baseEnd_3769401 < baseStart_3769401 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769461 : List Nat := [1, 3, 4, 3, 1, 2, 8]
def baseStart_3769461 : Nat := 118140960795 + 3769461 * 2 ^ 59
def prefixEnd_3769461 : Nat := 4983230072969 + 3 ^ 40 * 3769461 * 2
def baseEnd_3769461 : Nat := 47791242009323004943261

theorem tailTrace_3769461 : CollatzResearch.WordTrace tailWord_3769461 prefixEnd_3769461 47791242009323004943261 := by
  unfold tailWord_3769461
  simp only [CollatzResearch.WordTrace]
  refine ⟨137483537396894044530548237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91655691597929363020365491 137483537396894044530548237)
  ·
    refine ⟨51556326523835266698955589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137483537396894044530548237 51556326523835266698955589)
    ·
      refine ⟨9666811223219112506054173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51556326523835266698955589 9666811223219112506054173)
      ·
        refine ⟨3625054208707167189770315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9666811223219112506054173 3625054208707167189770315)
        ·
          refine ⟨5437581313060750784655473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3625054208707167189770315 5437581313060750784655473)
          ·
            refine ⟨4078185984795563088491605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5437581313060750784655473 4078185984795563088491605)
            ·
              refine ⟨47791242009323004943261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4078185984795563088491605 47791242009323004943261)
              ·
                rfl

theorem cell22_3769461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 8].length) (baseStart_3769461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769461 prefixEnd_3769461 := by exact prefixLift 3769461
  have htrace : WordTrace (prefixWord ++ tailWord_3769461) baseStart_3769461 baseEnd_3769461 := by
    simpa [prefixWord, tailWord_3769461, baseEnd_3769461] using wordTrace_append hprefix tailTrace_3769461
  have hstable : (prefixWord ++ tailWord_3769461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769461).length < 2 ^ (prefixWord ++ tailWord_3769461).sum := by decide
  have hdescent : baseEnd_3769461 < baseStart_3769461 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769472 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 7]
def baseStart_3769472 : Nat := 118140960795 + 3769472 * 2 ^ 59
def prefixEnd_3769472 : Nat := 4983230072969 + 3 ^ 40 * 3769472 * 2
def baseEnd_3769472 : Nat := 430122433258840257147671

theorem tailTrace_3769472 : CollatzResearch.WordTrace tailWord_3769472 prefixEnd_3769472 430122433258840257147671 := by
  unfold tailWord_3769472
  simp only [CollatzResearch.WordTrace]
  refine ⟨68741969299927096704599335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91655959066569462272799113 68741969299927096704599335)
  ·
    refine ⟨103112953949890645056899003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68741969299927096704599335 103112953949890645056899003)
    ·
      refine ⟨154669430924835967585348505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103112953949890645056899003 154669430924835967585348505)
      ·
        refine ⟨116002073193626975689011379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154669430924835967585348505 116002073193626975689011379)
        ·
          refine ⟨174003109790440463533517069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116002073193626975689011379 174003109790440463533517069)
          ·
            refine ⟨65251166171415173825068901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174003109790440463533517069 65251166171415173825068901)
            ·
              refine ⟨12234593657140345092200419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 65251166171415173825068901 12234593657140345092200419)
              ·
                refine ⟨18351890485710517638300629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12234593657140345092200419 18351890485710517638300629)
                ·
                  refine ⟨430122433258840257147671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18351890485710517638300629 430122433258840257147671)
                  ·
                    rfl

theorem cell22_3769472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 7].length) (baseStart_3769472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769472 prefixEnd_3769472 := by exact prefixLift 3769472
  have htrace : WordTrace (prefixWord ++ tailWord_3769472) baseStart_3769472 baseEnd_3769472 := by
    simpa [prefixWord, tailWord_3769472, baseEnd_3769472] using wordTrace_append hprefix tailTrace_3769472
  have hstable : (prefixWord ++ tailWord_3769472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769472).length < 2 ^ (prefixWord ++ tailWord_3769472).sum := by decide
  have hdescent : baseEnd_3769472 < baseStart_3769472 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769476 : List Nat := [2, 3, 2, 1, 2, 2, 3, 1, 3, 3]
def baseStart_3769476 : Nat := 118140960795 + 3769476 * 2 ^ 59
def prefixEnd_3769476 : Nat := 4983230072969 + 3 ^ 40 * 3769476 * 2
def baseEnd_3769476 : Nat := 1290368669058266094343001

theorem tailTrace_3769476 : CollatzResearch.WordTrace tailWord_3769476 prefixEnd_3769476 1290368669058266094343001 := by
  unfold tailWord_3769476
  simp only [CollatzResearch.WordTrace]
  refine ⟨68742042245919851046172141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91656056327893134728229521 68742042245919851046172141)
  ·
    refine ⟨25778265842219944142314553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68742042245919851046172141 25778265842219944142314553)
    ·
      refine ⟨19333699381664958106735915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25778265842219944142314553 19333699381664958106735915)
      ·
        refine ⟨29000549072497437160103873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19333699381664958106735915 29000549072497437160103873)
        ·
          refine ⟨21750411804373077870077905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 29000549072497437160103873 21750411804373077870077905)
          ·
            refine ⟨16312808853279808402558429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21750411804373077870077905 16312808853279808402558429)
            ·
              refine ⟨6117303319979928150959411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16312808853279808402558429 6117303319979928150959411)
              ·
                refine ⟨9175954979969892226439117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6117303319979928150959411 9175954979969892226439117)
                ·
                  refine ⟨3440983117488709584914669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9175954979969892226439117 3440983117488709584914669)
                  ·
                    refine ⟨1290368669058266094343001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3440983117488709584914669 1290368669058266094343001)
                    ·
                      rfl

theorem cell22_3769476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_3769476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769476 prefixEnd_3769476 := by exact prefixLift 3769476
  have htrace : WordTrace (prefixWord ++ tailWord_3769476) baseStart_3769476 baseEnd_3769476 := by
    simpa [prefixWord, tailWord_3769476, baseEnd_3769476] using wordTrace_append hprefix tailTrace_3769476
  have hstable : (prefixWord ++ tailWord_3769476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769476).length < 2 ^ (prefixWord ++ tailWord_3769476).sum := by decide
  have hdescent : baseEnd_3769476 < baseStart_3769476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769519 : List Nat := [1, 1, 2, 1, 2, 3, 2, 5, 1, 4]
def baseStart_3769519 : Nat := 118140960795 + 3769519 * 2 ^ 59
def prefixEnd_3769519 : Nat := 4983230072969 + 3 ^ 40 * 3769519 * 2
def baseEnd_3769519 : Nat := 1290383388837028315517869

theorem tailTrace_3769519 : CollatzResearch.WordTrace tailWord_3769519 prefixEnd_3769519 1290383388837028315517869 := by
  unfold tailWord_3769519
  simp only [CollatzResearch.WordTrace]
  refine ⟨137485652830683920436159611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91657101887122613624106407 137485652830683920436159611)
  ·
    refine ⟨206228479246025880654239417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137485652830683920436159611 206228479246025880654239417)
    ·
      refine ⟨154671359434519410490679563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 206228479246025880654239417 154671359434519410490679563)
      ·
        refine ⟨232007039151779115736019345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154671359434519410490679563 232007039151779115736019345)
        ·
          refine ⟨174005279363834336802014509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 232007039151779115736019345 174005279363834336802014509)
          ·
            refine ⟨65251979761437876300755441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 174005279363834336802014509 65251979761437876300755441)
            ·
              refine ⟨48938984821078407225566581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 65251979761437876300755441 48938984821078407225566581)
              ·
                refine ⟨4588029826976100677396867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48938984821078407225566581 4588029826976100677396867)
                ·
                  refine ⟨6882044740464151016095301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4588029826976100677396867 6882044740464151016095301)
                  ·
                    refine ⟨1290383388837028315517869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6882044740464151016095301 1290383388837028315517869)
                    ·
                      rfl

theorem cell22_3769519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 4].length) (baseStart_3769519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769519 prefixEnd_3769519 := by exact prefixLift 3769519
  have htrace : WordTrace (prefixWord ++ tailWord_3769519) baseStart_3769519 baseEnd_3769519 := by
    simpa [prefixWord, tailWord_3769519, baseEnd_3769519] using wordTrace_append hprefix tailTrace_3769519
  have hstable : (prefixWord ++ tailWord_3769519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769519).length < 2 ^ (prefixWord ++ tailWord_3769519).sum := by decide
  have hdescent : baseEnd_3769519 < baseStart_3769519 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769611 : List Nat := [1, 1, 1, 1, 5, 3, 2, 2, 3, 3]
def baseStart_3769611 : Nat := 118140960795 + 3769611 * 2 ^ 59
def prefixEnd_3769611 : Nat := 4983230072969 + 3 ^ 40 * 3769611 * 2
def baseEnd_3769611 : Nat := 1290414882317170742217587

theorem tailTrace_3769611 : CollatzResearch.WordTrace tailWord_3769611 prefixEnd_3769611 1290414882317170742217587 := by
  unfold tailWord_3769611
  simp only [CollatzResearch.WordTrace]
  refine ⟨137489008346350620148508687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91659338897567080099005791 137489008346350620148508687)
  ·
    refine ⟨206233512519525930222763031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137489008346350620148508687 206233512519525930222763031)
    ·
      refine ⟨309350268779288895334144547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206233512519525930222763031 309350268779288895334144547)
      ·
        refine ⟨464025403168933343001216821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309350268779288895334144547 464025403168933343001216821)
        ·
          refine ⟨43502381547087500906364077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 464025403168933343001216821 43502381547087500906364077)
          ·
            refine ⟨16313393080157812839886529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43502381547087500906364077 16313393080157812839886529)
            ·
              refine ⟨12235044810118359629914897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16313393080157812839886529 12235044810118359629914897)
              ·
                refine ⟨9176283607588769722436173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12235044810118359629914897 9176283607588769722436173)
                ·
                  refine ⟨3441106352845788645913565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9176283607588769722436173 3441106352845788645913565)
                  ·
                    refine ⟨1290414882317170742217587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3441106352845788645913565 1290414882317170742217587)
                    ·
                      rfl

theorem cell22_3769611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 2, 2, 3, 3].length) (baseStart_3769611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769611 prefixEnd_3769611 := by exact prefixLift 3769611
  have htrace : WordTrace (prefixWord ++ tailWord_3769611) baseStart_3769611 baseEnd_3769611 := by
    simpa [prefixWord, tailWord_3769611, baseEnd_3769611] using wordTrace_append hprefix tailTrace_3769611
  have hstable : (prefixWord ++ tailWord_3769611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769611).length < 2 ^ (prefixWord ++ tailWord_3769611).sum := by decide
  have hdescent : baseEnd_3769611 < baseStart_3769611 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769624 : List Nat := [2, 1, 2, 3, 1, 3, 1, 2, 7]
def baseStart_3769624 : Nat := 118140960795 + 3769624 * 2 ^ 59
def prefixEnd_3769624 : Nat := 4983230072969 + 3 ^ 40 * 3769624 * 2
def baseEnd_3769624 : Nat := 430139777494281013880849

theorem tailTrace_3769624 : CollatzResearch.WordTrace tailWord_3769624 prefixEnd_3769624 430139777494281013880849 := by
  unfold tailWord_3769624
  simp only [CollatzResearch.WordTrace]
  refine ⟨68744741247651761684365963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91659654996869015579154617 68744741247651761684365963)
  ·
    refine ⟨103117111871477642526548945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68744741247651761684365963 103117111871477642526548945)
    ·
      refine ⟨77337833903608231894911709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103117111871477642526548945 77337833903608231894911709)
      ·
        refine ⟨29001687713853086960591891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77337833903608231894911709 29001687713853086960591891)
        ·
          refine ⟨43502531570779630440887837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 29001687713853086960591891 43502531570779630440887837)
          ·
            refine ⟨16313449339042361415332939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43502531570779630440887837 16313449339042361415332939)
            ·
              refine ⟨24470174008563542122999409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16313449339042361415332939 24470174008563542122999409)
              ·
                refine ⟨18352630506422656592249557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24470174008563542122999409 18352630506422656592249557)
                ·
                  refine ⟨430139777494281013880849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18352630506422656592249557 430139777494281013880849)
                  ·
                    rfl

theorem cell22_3769624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 2, 7].length) (baseStart_3769624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769624 prefixEnd_3769624 := by exact prefixLift 3769624
  have htrace : WordTrace (prefixWord ++ tailWord_3769624) baseStart_3769624 baseEnd_3769624 := by
    simpa [prefixWord, tailWord_3769624, baseEnd_3769624] using wordTrace_append hprefix tailTrace_3769624
  have hstable : (prefixWord ++ tailWord_3769624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769624).length < 2 ^ (prefixWord ++ tailWord_3769624).sum := by decide
  have hdescent : baseEnd_3769624 < baseStart_3769624 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769630 : List Nat := [4, 3, 2, 1, 3, 1, 8]
def baseStart_3769630 : Nat := 118140960795 + 3769630 * 2 ^ 59
def prefixEnd_3769630 : Nat := 4983230072969 + 3 ^ 40 * 3769630 * 2
def baseEnd_3769630 : Nat := 47793384681683741703427

theorem tailTrace_3769630 : CollatzResearch.WordTrace tailWord_3769630 prefixEnd_3769630 47793384681683741703427 := by
  unfold tailWord_3769630
  simp only [CollatzResearch.WordTrace]
  refine ⟨17186212666660223299181293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 91659800888854524262300229 17186212666660223299181293)
  ·
    refine ⟨6444829749997583737192985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17186212666660223299181293 6444829749997583737192985)
    ·
      refine ⟨4833622312498187802894739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6444829749997583737192985 4833622312498187802894739)
      ·
        refine ⟨7250433468747281704342109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4833622312498187802894739 7250433468747281704342109)
        ·
          refine ⟨2718912550780230639128291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7250433468747281704342109 2718912550780230639128291)
          ·
            refine ⟨4078368826170345958692437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2718912550780230639128291 4078368826170345958692437)
            ·
              refine ⟨47793384681683741703427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4078368826170345958692437 47793384681683741703427)
              ·
                rfl

theorem cell22_3769630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 8].length) (baseStart_3769630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769630 prefixEnd_3769630 := by exact prefixLift 3769630
  have htrace : WordTrace (prefixWord ++ tailWord_3769630) baseStart_3769630 baseEnd_3769630 := by
    simpa [prefixWord, tailWord_3769630, baseEnd_3769630] using wordTrace_append hprefix tailTrace_3769630
  have hstable : (prefixWord ++ tailWord_3769630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769630).length < 2 ^ (prefixWord ++ tailWord_3769630).sum := by decide
  have hdescent : baseEnd_3769630 < baseStart_3769630 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769645 : List Nat := [1, 5, 3, 1, 1, 1, 3, 1, 3, 3]
def baseStart_3769645 : Nat := 118140960795 + 3769645 * 2 ^ 59
def prefixEnd_3769645 : Nat := 4983230072969 + 3 ^ 40 * 3769645 * 2
def baseEnd_3769645 : Nat := 1290426521212005986867483

theorem tailTrace_3769645 : CollatzResearch.WordTrace tailWord_3769645 prefixEnd_3769645 1290426521212005986867483 := by
  unfold tailWord_3769645
  simp only [CollatzResearch.WordTrace]
  refine ⟨137490248428227443955246389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91660165618818295970164259 137490248428227443955246389)
  ·
    refine ⟨12889710790146322870804349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 137490248428227443955246389 12889710790146322870804349)
    ·
      refine ⟨4833641546304871076551631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12889710790146322870804349 4833641546304871076551631)
      ·
        refine ⟨7250462319457306614827447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4833641546304871076551631 7250462319457306614827447)
        ·
          refine ⟨10875693479185959922241171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7250462319457306614827447 10875693479185959922241171)
          ·
            refine ⟨16313540218778939883361757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10875693479185959922241171 16313540218778939883361757)
            ·
              refine ⟨6117577582042102456260659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16313540218778939883361757 6117577582042102456260659)
              ·
                refine ⟨9176366373063153684390989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6117577582042102456260659 9176366373063153684390989)
                ·
                  refine ⟨3441137389898682631646621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9176366373063153684390989 3441137389898682631646621)
                  ·
                    refine ⟨1290426521212005986867483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3441137389898682631646621 1290426521212005986867483)
                    ·
                      rfl

theorem cell22_3769645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_3769645 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769645 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769645 prefixEnd_3769645 := by exact prefixLift 3769645
  have htrace : WordTrace (prefixWord ++ tailWord_3769645) baseStart_3769645 baseEnd_3769645 := by
    simpa [prefixWord, tailWord_3769645, baseEnd_3769645] using wordTrace_append hprefix tailTrace_3769645
  have hstable : (prefixWord ++ tailWord_3769645).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769645).length < 2 ^ (prefixWord ++ tailWord_3769645).sum := by decide
  have hdescent : baseEnd_3769645 < baseStart_3769645 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769669 : List Nat := [1, 3, 1, 1, 1, 2, 1, 6, 6]
def baseStart_3769669 : Nat := 118140960795 + 3769669 * 2 ^ 59
def prefixEnd_3769669 : Nat := 4983230072969 + 3 ^ 40 * 3769669 * 2
def baseEnd_3769669 : Nat := 430144912300825974755803

theorem tailTrace_3769669 : CollatzResearch.WordTrace tailWord_3769669 prefixEnd_3769669 430144912300825974755803 := by
  unfold tailWord_3769669
  simp only [CollatzResearch.WordTrace]
  refine ⟨137491123780140496054120061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91660749186760330702746707 137491123780140496054120061)
  ·
    refine ⟨51559171417552686020295023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 137491123780140496054120061 51559171417552686020295023)
    ·
      refine ⟨77338757126329029030442535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51559171417552686020295023 77338757126329029030442535)
      ·
        refine ⟨116008135689493543545663803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77338757126329029030442535 116008135689493543545663803)
        ·
          refine ⟨174012203534240315318495705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 116008135689493543545663803 174012203534240315318495705)
          ·
            refine ⟨130509152650680236488871779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 174012203534240315318495705 130509152650680236488871779)
            ·
              refine ⟨195763728976020354733307669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 130509152650680236488871779 195763728976020354733307669)
              ·
                refine ⟨9176424795750954128123797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 195763728976020354733307669 9176424795750954128123797)
                ·
                  refine ⟨430144912300825974755803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9176424795750954128123797 430144912300825974755803)
                  ·
                    rfl

theorem cell22_3769669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 6].length) (baseStart_3769669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769669 prefixEnd_3769669 := by exact prefixLift 3769669
  have htrace : WordTrace (prefixWord ++ tailWord_3769669) baseStart_3769669 baseEnd_3769669 := by
    simpa [prefixWord, tailWord_3769669, baseEnd_3769669] using wordTrace_append hprefix tailTrace_3769669
  have hstable : (prefixWord ++ tailWord_3769669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769669).length < 2 ^ (prefixWord ++ tailWord_3769669).sum := by decide
  have hdescent : baseEnd_3769669 < baseStart_3769669 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769671 : List Nat := [1, 1, 4, 1, 2, 4, 1, 1, 3, 4]
def baseStart_3769671 : Nat := 118140960795 + 3769671 * 2 ^ 59
def prefixEnd_3769671 : Nat := 4983230072969 + 3 ^ 40 * 3769671 * 2
def baseEnd_3769671 : Nat := 1290435421543350585717403

theorem tailTrace_3769671 : CollatzResearch.WordTrace tailWord_3769671 prefixEnd_3769671 1290435421543350585717403 := by
  unfold tailWord_3769671
  simp only [CollatzResearch.WordTrace]
  refine ⟨137491196726133250395692867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91660797817422166930461911 137491196726133250395692867)
  ·
    refine ⟨206236795089199875593539301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137491196726133250395692867 206236795089199875593539301)
    ·
      refine ⟨38669399079224976673788619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 206236795089199875593539301 38669399079224976673788619)
      ·
        refine ⟨58004098618837465010682929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38669399079224976673788619 58004098618837465010682929)
        ·
          refine ⟨43503073964128098758012197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 58004098618837465010682929 43503073964128098758012197)
          ·
            refine ⟨8156826368274018517127287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43503073964128098758012197 8156826368274018517127287)
            ·
              refine ⟨12235239552411027775690931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8156826368274018517127287 12235239552411027775690931)
              ·
                refine ⟨18352859328616541663536397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12235239552411027775690931 18352859328616541663536397)
                ·
                  refine ⟨6882322248231203123826149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 18352859328616541663536397 6882322248231203123826149)
                  ·
                    refine ⟨1290435421543350585717403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6882322248231203123826149 1290435421543350585717403)
                    ·
                      rfl

theorem cell22_3769671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_3769671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769671 prefixEnd_3769671 := by exact prefixLift 3769671
  have htrace : WordTrace (prefixWord ++ tailWord_3769671) baseStart_3769671 baseEnd_3769671 := by
    simpa [prefixWord, tailWord_3769671, baseEnd_3769671] using wordTrace_append hprefix tailTrace_3769671
  have hstable : (prefixWord ++ tailWord_3769671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769671).length < 2 ^ (prefixWord ++ tailWord_3769671).sum := by decide
  have hdescent : baseEnd_3769671 < baseStart_3769671 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769688 : List Nat := [2, 1, 2, 2, 1, 1, 7, 1, 1, 4]
def baseStart_3769688 : Nat := 118140960795 + 3769688 * 2 ^ 59
def prefixEnd_3769688 : Nat := 4983230072969 + 3 ^ 40 * 3769688 * 2
def baseEnd_3769688 : Nat := 1290441240990768208042351

theorem tailTrace_3769688 : CollatzResearch.WordTrace tailWord_3769688 prefixEnd_3769688 1290441240990768208042351 := by
  unfold tailWord_3769688
  simp only [CollatzResearch.WordTrace]
  refine ⟨68745908383535831149530859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91661211178047774866041145 68745908383535831149530859)
  ·
    refine ⟨103118862575303746724296289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68745908383535831149530859 103118862575303746724296289)
    ·
      refine ⟨77339146931477810043222217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103118862575303746724296289 77339146931477810043222217)
      ·
        refine ⟨58004360198608357532416663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77339146931477810043222217 58004360198608357532416663)
        ·
          refine ⟨87006540297912536298624995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58004360198608357532416663 87006540297912536298624995)
          ·
            refine ⟨130509810446868804447937493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 87006540297912536298624995 130509810446868804447937493)
            ·
              refine ⟨3058823682348487604248535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 130509810446868804447937493 3058823682348487604248535)
              ·
                refine ⟨4588235523522731406372803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3058823682348487604248535 4588235523522731406372803)
                ·
                  refine ⟨6882353285284097109559205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4588235523522731406372803 6882353285284097109559205)
                  ·
                    refine ⟨1290441240990768208042351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6882353285284097109559205 1290441240990768208042351)
                    ·
                      rfl

theorem cell22_3769688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 7, 1, 1, 4].length) (baseStart_3769688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769688 prefixEnd_3769688 := by exact prefixLift 3769688
  have htrace : WordTrace (prefixWord ++ tailWord_3769688) baseStart_3769688 baseEnd_3769688 := by
    simpa [prefixWord, tailWord_3769688, baseEnd_3769688] using wordTrace_append hprefix tailTrace_3769688
  have hstable : (prefixWord ++ tailWord_3769688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769688).length < 2 ^ (prefixWord ++ tailWord_3769688).sum := by decide
  have hdescent : baseEnd_3769688 < baseStart_3769688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769752 : List Nat := [2, 1, 2, 5, 2, 2, 1, 2, 2, 3]
def baseStart_3769752 : Nat := 118140960795 + 3769752 * 2 ^ 59
def prefixEnd_3769752 : Nat := 4983230072969 + 3 ^ 40 * 3769752 * 2
def baseEnd_3769752 : Nat := 1290463149498693374442155

theorem tailTrace_3769752 : CollatzResearch.WordTrace tailWord_3769752 prefixEnd_3769752 1290463149498693374442155 := by
  unfold tailWord_3769752
  simp only [CollatzResearch.WordTrace]
  refine ⟨68747075519419900614695755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91662767359226534152927673 68747075519419900614695755)
  ·
    refine ⟨103120613279129850922043633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68747075519419900614695755 103120613279129850922043633)
    ·
      refine ⟨77340459959347388191532725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 103120613279129850922043633 77340459959347388191532725)
      ·
        refine ⟨7250668121188817642956193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 77340459959347388191532725 7250668121188817642956193)
        ·
          refine ⟨5438001090891613232217145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7250668121188817642956193 5438001090891613232217145)
          ·
            refine ⟨4078500818168709924162859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5438001090891613232217145 4078500818168709924162859)
            ·
              refine ⟨6117751227253064886244289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4078500818168709924162859 6117751227253064886244289)
              ·
                refine ⟨4588313420439798664683217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6117751227253064886244289 4588313420439798664683217)
                ·
                  refine ⟨3441235065329848998512413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4588313420439798664683217 3441235065329848998512413)
                  ·
                    refine ⟨1290463149498693374442155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3441235065329848998512413 1290463149498693374442155)
                    ·
                      rfl

theorem cell22_3769752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 2, 1, 2, 2, 3].length) (baseStart_3769752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769752 prefixEnd_3769752 := by exact prefixLift 3769752
  have htrace : WordTrace (prefixWord ++ tailWord_3769752) baseStart_3769752 baseEnd_3769752 := by
    simpa [prefixWord, tailWord_3769752, baseEnd_3769752] using wordTrace_append hprefix tailTrace_3769752
  have hstable : (prefixWord ++ tailWord_3769752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769752).length < 2 ^ (prefixWord ++ tailWord_3769752).sum := by decide
  have hdescent : baseEnd_3769752 < baseStart_3769752 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769763 : List Nat := [1, 1, 1, 4, 1, 3, 4, 1, 3, 3]
def baseStart_3769763 : Nat := 118140960795 + 3769763 * 2 ^ 59
def prefixEnd_3769763 : Nat := 4983230072969 + 3 ^ 40 * 3769763 * 2
def baseEnd_3769763 : Nat := 1290466915023493012417121

theorem tailTrace_3769763 : CollatzResearch.WordTrace tailWord_3769763 prefixEnd_3769763 1290466915023493012417121 := by
  unfold tailWord_3769763
  simp only [CollatzResearch.WordTrace]
  refine ⟨137494552241799950108041943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91663034827866633405361295 137494552241799950108041943)
  ·
    refine ⟨206241828362699925162062915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137494552241799950108041943 206241828362699925162062915)
    ·
      refine ⟨309362742544049887743094373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206241828362699925162062915 309362742544049887743094373)
      ·
        refine ⟨58005514227009353951830195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 309362742544049887743094373 58005514227009353951830195)
        ·
          refine ⟨87008271340514030927745293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 58005514227009353951830195 87008271340514030927745293)
          ·
            refine ⟨32628101752692761597904485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 87008271340514030927745293 32628101752692761597904485)
            ·
              refine ⟨6117769078629892799607091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32628101752692761597904485 6117769078629892799607091)
              ·
                refine ⟨9176653617944839199410637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6117769078629892799607091 9176653617944839199410637)
                ·
                  refine ⟨3441245106729314699778989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9176653617944839199410637 3441245106729314699778989)
                  ·
                    refine ⟨1290466915023493012417121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3441245106729314699778989 1290466915023493012417121)
                    ·
                      rfl

theorem cell22_3769763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 3].length) (baseStart_3769763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769763 prefixEnd_3769763 := by exact prefixLift 3769763
  have htrace : WordTrace (prefixWord ++ tailWord_3769763) baseStart_3769763 baseEnd_3769763 := by
    simpa [prefixWord, tailWord_3769763, baseEnd_3769763] using wordTrace_append hprefix tailTrace_3769763
  have hstable : (prefixWord ++ tailWord_3769763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769763).length < 2 ^ (prefixWord ++ tailWord_3769763).sum := by decide
  have hdescent : baseEnd_3769763 < baseStart_3769763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769840 : List Nat := [2, 1, 1, 1, 3, 6, 1, 2, 1, 4]
def baseStart_3769840 : Nat := 118140960795 + 3769840 * 2 ^ 59
def prefixEnd_3769840 : Nat := 4983230072969 + 3 ^ 40 * 3769840 * 2
def baseEnd_3769840 : Nat := 1290493273697090478241885

theorem tailTrace_3769840 : CollatzResearch.WordTrace tailWord_3769840 prefixEnd_3769840 1290493273697090478241885 := by
  unfold tailWord_3769840
  simp only [CollatzResearch.WordTrace]
  refine ⟨68748680331260496129297487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 91664907108347328172396649 68748680331260496129297487)
  ·
    refine ⟨103123020496890744193946231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68748680331260496129297487 103123020496890744193946231)
    ·
      refine ⟨154684530745336116290919347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 103123020496890744193946231 154684530745336116290919347)
      ·
        refine ⟨232026796118004174436379021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 154684530745336116290919347 232026796118004174436379021)
        ·
          refine ⟨87010048544251565413642133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 232026796118004174436379021 87010048544251565413642133)
          ·
            refine ⟨4078596025511792128764475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 87010048544251565413642133 4078596025511792128764475)
            ·
              refine ⟨6117894038267688193146713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4078596025511792128764475 6117894038267688193146713)
              ·
                refine ⟨4588420528700766144860035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6117894038267688193146713 4588420528700766144860035)
                ·
                  refine ⟨6882630793051149217290053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4588420528700766144860035 6882630793051149217290053)
                  ·
                    refine ⟨1290493273697090478241885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6882630793051149217290053 1290493273697090478241885)
                    ·
                      rfl

theorem cell22_3769840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 1, 4].length) (baseStart_3769840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769840 prefixEnd_3769840 := by exact prefixLift 3769840
  have htrace : WordTrace (prefixWord ++ tailWord_3769840) baseStart_3769840 baseEnd_3769840 := by
    simpa [prefixWord, tailWord_3769840, baseEnd_3769840] using wordTrace_append hprefix tailTrace_3769840
  have hstable : (prefixWord ++ tailWord_3769840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769840).length < 2 ^ (prefixWord ++ tailWord_3769840).sum := by decide
  have hdescent : baseEnd_3769840 < baseStart_3769840 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3769851 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 6, 4]
def baseStart_3769851 : Nat := 118140960795 + 3769851 * 2 ^ 59
def prefixEnd_3769851 : Nat := 4983230072969 + 3 ^ 40 * 3769851 * 2
def baseEnd_3769851 : Nat := 1290497039221890116216851

theorem tailTrace_3769851 : CollatzResearch.WordTrace tailWord_3769851 prefixEnd_3769851 1290497039221890116216851 := by
  unfold tailWord_3769851
  simp only [CollatzResearch.WordTrace]
  refine ⟨137497761865481141137245407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 91665174576987427424830271 137497761865481141137245407)
  ·
    refine ⟨206246642798221711705868111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 137497761865481141137245407 206246642798221711705868111)
    ·
      refine ⟨309369964197332567558802167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 206246642798221711705868111 309369964197332567558802167)
      ·
        refine ⟨464054946295998851338203251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 309369964197332567558802167 464054946295998851338203251)
        ·
          refine ⟨696082419443998277007304877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 464054946295998851338203251 696082419443998277007304877)
          ·
            refine ⟨261030907291499353877739329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 696082419443998277007304877 261030907291499353877739329)
            ·
              refine ⟨195773180468624515408304497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 261030907291499353877739329 195773180468624515408304497)
              ·
                refine ⟨146829885351468386556228373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 195773180468624515408304497 146829885351468386556228373)
                ·
                  refine ⟨6882650875850080619823205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 146829885351468386556228373 6882650875850080619823205)
                  ·
                    refine ⟨1290497039221890116216851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6882650875850080619823205 1290497039221890116216851)
                    ·
                      rfl

theorem cell22_3769851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 6, 4].length) (baseStart_3769851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_3769851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_3769851 prefixEnd_3769851 := by exact prefixLift 3769851
  have htrace : WordTrace (prefixWord ++ tailWord_3769851) baseStart_3769851 baseEnd_3769851 := by
    simpa [prefixWord, tailWord_3769851, baseEnd_3769851] using wordTrace_append hprefix tailTrace_3769851
  have hstable : (prefixWord ++ tailWord_3769851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3769851).length < 2 ^ (prefixWord ++ tailWord_3769851).sum := by decide
  have hdescent : baseEnd_3769851 < baseStart_3769851 := by decide
  rcases family_descends (prefixWord ++ tailWord_3769851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
