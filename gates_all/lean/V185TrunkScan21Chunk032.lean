import V185TrunkScan21Chunk031

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_387635 : List Nat := [1, 1, 1, 2, 4, 2, 3, 7]
def baseStart_387635 : Nat := 118140960795 + 387635 * 2 ^ 59
def prefixEnd_387635 : Nat := 4983230072969 + 3 ^ 40 * 387635 * 2
def baseEnd_387635 : Nat := 29487862741584608885897

theorem tailTrace_387635 : CollatzResearch.WordTrace tailWord_387635 prefixEnd_387635 29487862741584608885897 := by
  unfold tailWord_387635
  simp only [CollatzResearch.WordTrace]
  refine ⟨14138209950672072632436359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9425473300448048421624239 14138209950672072632436359)
  ·
    refine ⟨21207314926008108948654539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14138209950672072632436359 21207314926008108948654539)
    ·
      refine ⟨31810972389012163422981809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21207314926008108948654539 31810972389012163422981809)
      ·
        refine ⟨23858229291759122567236357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 31810972389012163422981809 23858229291759122567236357)
        ·
          refine ⟨4473417992204835481356817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 23858229291759122567236357 4473417992204835481356817)
          ·
            refine ⟨3355063494153626611017613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4473417992204835481356817 3355063494153626611017613)
            ·
              refine ⟨1258148810307609979131605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3355063494153626611017613 1258148810307609979131605)
              ·
                refine ⟨29487862741584608885897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1258148810307609979131605 29487862741584608885897)
                ·
                  rfl

theorem cell21_387635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 7].length) (baseStart_387635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387635 prefixEnd_387635 := by exact prefixLift 387635
  have htrace : WordTrace (prefixWord ++ tailWord_387635) baseStart_387635 baseEnd_387635 := by
    simpa [prefixWord, tailWord_387635, baseEnd_387635] using wordTrace_append hprefix tailTrace_387635
  have hstable : (prefixWord ++ tailWord_387635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387635).length < 2 ^ (prefixWord ++ tailWord_387635).sum := by decide
  have hdescent : baseEnd_387635 < baseStart_387635 := by decide
  rcases family_descends (prefixWord ++ tailWord_387635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387638 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 6]
def baseStart_387638 : Nat := 118140960795 + 387638 * 2 ^ 59
def prefixEnd_387638 : Nat := 4983230072969 + 3 ^ 40 * 387638 * 2
def baseEnd_387638 : Nat := 88464272865626488107685

theorem tailTrace_387638 : CollatzResearch.WordTrace tailWord_387638 prefixEnd_387638 88464272865626488107685 := by
  unfold tailWord_387638
  simp only [CollatzResearch.WordTrace]
  refine ⟨883644960603825259049723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9425546246440802763197045 883644960603825259049723)
  ·
    refine ⟨1325467440905737888574585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 883644960603825259049723 1325467440905737888574585)
    ·
      refine ⟨994100580679303416430939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1325467440905737888574585 994100580679303416430939)
      ·
        refine ⟨1491150871018955124646409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 994100580679303416430939 1491150871018955124646409)
        ·
          refine ⟨1118363153264216343484807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1491150871018955124646409 1118363153264216343484807)
          ·
            refine ⟨1677544729896324515227211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1118363153264216343484807 1677544729896324515227211)
            ·
              refine ⟨2516317094844486772840817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1677544729896324515227211 2516317094844486772840817)
              ·
                refine ⟨1887237821133365079630613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2516317094844486772840817 1887237821133365079630613)
                ·
                  refine ⟨88464272865626488107685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1887237821133365079630613 88464272865626488107685)
                  ·
                    rfl

theorem cell21_387638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_387638 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387638 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387638 prefixEnd_387638 := by exact prefixLift 387638
  have htrace : WordTrace (prefixWord ++ tailWord_387638) baseStart_387638 baseEnd_387638 := by
    simpa [prefixWord, tailWord_387638, baseEnd_387638] using wordTrace_append hprefix tailTrace_387638
  have hstable : (prefixWord ++ tailWord_387638).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387638).length < 2 ^ (prefixWord ++ tailWord_387638).sum := by decide
  have hdescent : baseEnd_387638 < baseStart_387638 := by decide
  rcases family_descends (prefixWord ++ tailWord_387638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387717 : List Nat := [1, 3, 1, 1, 4, 4, 2, 2, 3]
def baseStart_387717 : Nat := 118140960795 + 387717 * 2 ^ 59
def prefixEnd_387717 : Nat := 4983230072969 + 3 ^ 40 * 387717 * 2
def baseEnd_387717 : Nat := 88482301741939906290857

theorem tailTrace_387717 : CollatzResearch.WordTrace tailWord_387717 prefixEnd_387717 88482301741939906290857 := by
  unfold tailWord_387717
  simp only [CollatzResearch.WordTrace]
  refine ⟨14141200736375000636921405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9427467157583333757947603 14141200736375000636921405)
  ·
    refine ⟨5302950276140625238845527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14141200736375000636921405 5302950276140625238845527)
    ·
      refine ⟨7954425414210937858268291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5302950276140625238845527 7954425414210937858268291)
      ·
        refine ⟨11931638121316406787402437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7954425414210937858268291 11931638121316406787402437)
        ·
          refine ⟨2237182147746826272637957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11931638121316406787402437 2237182147746826272637957)
          ·
            refine ⟨419471652702529926119617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2237182147746826272637957 419471652702529926119617)
            ·
              refine ⟨314603739526897444589713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 419471652702529926119617 314603739526897444589713)
              ·
                refine ⟨235952804645173083442285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314603739526897444589713 235952804645173083442285)
                ·
                  refine ⟨88482301741939906290857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 235952804645173083442285 88482301741939906290857)
                  ·
                    rfl

theorem cell21_387717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 4, 2, 2, 3].length) (baseStart_387717 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387717 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387717 prefixEnd_387717 := by exact prefixLift 387717
  have htrace : WordTrace (prefixWord ++ tailWord_387717) baseStart_387717 baseEnd_387717 := by
    simpa [prefixWord, tailWord_387717, baseEnd_387717] using wordTrace_append hprefix tailTrace_387717
  have hstable : (prefixWord ++ tailWord_387717).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387717).length < 2 ^ (prefixWord ++ tailWord_387717).sum := by decide
  have hdescent : baseEnd_387717 < baseStart_387717 := by decide
  rcases family_descends (prefixWord ++ tailWord_387717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387745 : List Nat := [1, 2, 3, 3, 3, 1, 3, 5]
def baseStart_387745 : Nat := 118140960795 + 387745 * 2 ^ 59
def prefixEnd_387745 : Nat := 4983230072969 + 3 ^ 40 * 387745 * 2
def baseEnd_387745 : Nat := 29496230574472693274711

theorem tailTrace_387745 : CollatzResearch.WordTrace tailWord_387745 prefixEnd_387745 29496230574472693274711 := by
  unfold tailWord_387745
  simp only [CollatzResearch.WordTrace]
  refine ⟨14142221980273561418940689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9428147986849040945960459 14142221980273561418940689)
  ·
    refine ⟨10606666485205171064205517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14142221980273561418940689 10606666485205171064205517)
    ·
      refine ⟨3977499931951939149077069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10606666485205171064205517 3977499931951939149077069)
      ·
        refine ⟨1491562474481977180903901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3977499931951939149077069 1491562474481977180903901)
        ·
          refine ⟨559335927930741442838963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1491562474481977180903901 559335927930741442838963)
          ·
            refine ⟨839003891896112164258445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 559335927930741442838963 839003891896112164258445)
            ·
              refine ⟨314626459461042061596917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 839003891896112164258445 314626459461042061596917)
              ·
                refine ⟨29496230574472693274711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 314626459461042061596917 29496230574472693274711)
                ·
                  rfl

theorem cell21_387745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 5].length) (baseStart_387745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387745 prefixEnd_387745 := by exact prefixLift 387745
  have htrace : WordTrace (prefixWord ++ tailWord_387745) baseStart_387745 baseEnd_387745 := by
    simpa [prefixWord, tailWord_387745, baseEnd_387745] using wordTrace_append hprefix tailTrace_387745
  have hstable : (prefixWord ++ tailWord_387745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387745).length < 2 ^ (prefixWord ++ tailWord_387745).sum := by decide
  have hdescent : baseEnd_387745 < baseStart_387745 := by decide
  rcases family_descends (prefixWord ++ tailWord_387745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387759 : List Nat := [1, 1, 2, 1, 2, 5, 1, 5, 3]
def baseStart_387759 : Nat := 118140960795 + 387759 * 2 ^ 59
def prefixEnd_387759 : Nat := 4983230072969 + 3 ^ 40 * 387759 * 2
def baseEnd_387759 : Nat := 88491886714157166590771

theorem tailTrace_387759 : CollatzResearch.WordTrace tailWord_387759 prefixEnd_387759 88491886714157166590771 := by
  unfold tailWord_387759
  simp only [CollatzResearch.WordTrace]
  refine ⟨14142732602222841809950331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9428488401481894539966887 14142732602222841809950331)
  ·
    refine ⟨21214098903334262714925497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14142732602222841809950331 21214098903334262714925497)
    ·
      refine ⟨15910574177500697036194123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21214098903334262714925497 15910574177500697036194123)
      ·
        refine ⟨23865861266251045554291185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15910574177500697036194123 23865861266251045554291185)
        ·
          refine ⟨17899395949688284165718389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 23865861266251045554291185 17899395949688284165718389)
          ·
            refine ⟨1678068370283276640536099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17899395949688284165718389 1678068370283276640536099)
            ·
              refine ⟨2517102555424914960804149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1678068370283276640536099 2517102555424914960804149)
              ·
                refine ⟨235978364571085777575389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2517102555424914960804149 235978364571085777575389)
                ·
                  refine ⟨88491886714157166590771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 235978364571085777575389 88491886714157166590771)
                  ·
                    rfl

theorem cell21_387759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 5, 3].length) (baseStart_387759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387759 prefixEnd_387759 := by exact prefixLift 387759
  have htrace : WordTrace (prefixWord ++ tailWord_387759) baseStart_387759 baseEnd_387759 := by
    simpa [prefixWord, tailWord_387759, baseEnd_387759] using wordTrace_append hprefix tailTrace_387759
  have hstable : (prefixWord ++ tailWord_387759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387759).length < 2 ^ (prefixWord ++ tailWord_387759).sum := by decide
  have hdescent : baseEnd_387759 < baseStart_387759 := by decide
  rcases family_descends (prefixWord ++ tailWord_387759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387773 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 6]
def baseStart_387773 : Nat := 118140960795 + 387773 * 2 ^ 59
def prefixEnd_387773 : Nat := 4983230072969 + 3 ^ 40 * 387773 * 2
def baseEnd_387773 : Nat := 88495081704896253357409

theorem tailTrace_387773 : CollatzResearch.WordTrace tailWord_387773 prefixEnd_387773 88495081704896253357409 := by
  unfold tailWord_387773
  simp only [CollatzResearch.WordTrace]
  refine ⟨14143243224172122200959973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9428828816114748133973315 14143243224172122200959973)
  ·
    refine ⟨2651858104532272912679995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14143243224172122200959973 2651858104532272912679995)
    ·
      refine ⟨3977787156798409369019993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2651858104532272912679995 3977787156798409369019993)
      ·
        refine ⟨2983340367598807026764995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3977787156798409369019993 2983340367598807026764995)
        ·
          refine ⟨4475010551398210540147493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2983340367598807026764995 4475010551398210540147493)
          ·
            refine ⟨839064478387164476277655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4475010551398210540147493 839064478387164476277655)
            ·
              refine ⟨1258596717580746714416483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 839064478387164476277655 1258596717580746714416483)
              ·
                refine ⟨1887895076371120071624725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1258596717580746714416483 1887895076371120071624725)
                ·
                  refine ⟨88495081704896253357409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1887895076371120071624725 88495081704896253357409)
                  ·
                    rfl

theorem cell21_387773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 6].length) (baseStart_387773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387773 prefixEnd_387773 := by exact prefixLift 387773
  have htrace : WordTrace (prefixWord ++ tailWord_387773) baseStart_387773 baseEnd_387773 := by
    simpa [prefixWord, tailWord_387773, baseEnd_387773] using wordTrace_append hprefix tailTrace_387773
  have hstable : (prefixWord ++ tailWord_387773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387773).length < 2 ^ (prefixWord ++ tailWord_387773).sum := by decide
  have hdescent : baseEnd_387773 < baseStart_387773 := by decide
  rcases family_descends (prefixWord ++ tailWord_387773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387832 : List Nat := [2, 1, 2, 1, 1, 2, 3, 3, 6]
def baseStart_387832 : Nat := 118140960795 + 387832 * 2 ^ 59
def prefixEnd_387832 : Nat := 4983230072969 + 3 ^ 40 * 387832 * 2
def baseEnd_387832 : Nat := 88508546308725261873955

theorem tailTrace_387832 : CollatzResearch.WordTrace tailWord_387832 prefixEnd_387832 88508546308725261873955 := by
  unfold tailWord_387832
  simp only [CollatzResearch.WordTrace]
  refine ⟨7072697565479187638678875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9430263420638916851571833 7072697565479187638678875)
  ·
    refine ⟨10609046348218781458018313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7072697565479187638678875 10609046348218781458018313)
    ·
      refine ⟨7956784761164086093513735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10609046348218781458018313 7956784761164086093513735)
      ·
        refine ⟨11935177141746129140270603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7956784761164086093513735 11935177141746129140270603)
        ·
          refine ⟨17902765712619193710405905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11935177141746129140270603 17902765712619193710405905)
          ·
            refine ⟨13427074284464395282804429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17902765712619193710405905 13427074284464395282804429)
            ·
              refine ⟨5035152856674148231051661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13427074284464395282804429 5035152856674148231051661)
              ·
                refine ⟨1888182321252805586644373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5035152856674148231051661 1888182321252805586644373)
                ·
                  refine ⟨88508546308725261873955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1888182321252805586644373 88508546308725261873955)
                  ·
                    rfl

theorem cell21_387832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3, 6].length) (baseStart_387832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387832 prefixEnd_387832 := by exact prefixLift 387832
  have htrace : WordTrace (prefixWord ++ tailWord_387832) baseStart_387832 baseEnd_387832 := by
    simpa [prefixWord, tailWord_387832, baseEnd_387832] using wordTrace_append hprefix tailTrace_387832
  have hstable : (prefixWord ++ tailWord_387832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387832).length < 2 ^ (prefixWord ++ tailWord_387832).sum := by decide
  have hdescent : baseEnd_387832 < baseStart_387832 := by decide
  rcases family_descends (prefixWord ++ tailWord_387832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387886 : List Nat := [4, 1, 3, 2, 1, 3, 2, 2, 3]
def baseStart_387886 : Nat := 118140960795 + 387886 * 2 ^ 59
def prefixEnd_387886 : Nat := 4983230072969 + 3 ^ 40 * 387886 * 2
def baseEnd_387886 : Nat := 88520869844433167973845

theorem tailTrace_387886 : CollatzResearch.WordTrace tailWord_387886 prefixEnd_387886 88520869844433167973845 := by
  unfold tailWord_387886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1768420584095342812477939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9431576448508494999882341 1768420584095342812477939)
  ·
    refine ⟨2652630876143014218716909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1768420584095342812477939 2652630876143014218716909)
    ·
      refine ⟨994736578553630332018841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2652630876143014218716909 994736578553630332018841)
      ·
        refine ⟨746052433915222749014131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 994736578553630332018841 746052433915222749014131)
        ·
          refine ⟨1119078650872834123521197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746052433915222749014131 1119078650872834123521197)
          ·
            refine ⟨419654494077312796320449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1119078650872834123521197 419654494077312796320449)
            ·
              refine ⟨314740870557984597240337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 419654494077312796320449 314740870557984597240337)
              ·
                refine ⟨236055652918488447930253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314740870557984597240337 236055652918488447930253)
                ·
                  refine ⟨88520869844433167973845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236055652918488447930253 88520869844433167973845)
                  ·
                    rfl

theorem cell21_387886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 3, 2, 2, 3].length) (baseStart_387886 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387886 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387886 prefixEnd_387886 := by exact prefixLift 387886
  have htrace : WordTrace (prefixWord ++ tailWord_387886) baseStart_387886 baseEnd_387886 := by
    simpa [prefixWord, tailWord_387886, baseEnd_387886] using wordTrace_append hprefix tailTrace_387886
  have hstable : (prefixWord ++ tailWord_387886).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387886).length < 2 ^ (prefixWord ++ tailWord_387886).sum := by decide
  have hdescent : baseEnd_387886 < baseStart_387886 := by decide
  rcases family_descends (prefixWord ++ tailWord_387886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387939 : List Nat := [1, 1, 1, 5, 3, 2, 8]
def baseStart_387939 : Nat := 118140960795 + 387939 * 2 ^ 59
def prefixEnd_387939 : Nat := 4983230072969 + 3 ^ 40 * 387939 * 2
def baseEnd_387939 : Nat := 9836996129612983732267

theorem tailTrace_387939 : CollatzResearch.WordTrace tailWord_387939 prefixEnd_387939 9836996129612983732267 := by
  unfold tailWord_387939
  simp only [CollatzResearch.WordTrace]
  refine ⟨14149297741570732551502871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9432865161047155034335247 14149297741570732551502871)
  ·
    refine ⟨21223946612356098827254307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14149297741570732551502871 21223946612356098827254307)
    ·
      refine ⟨31835919918534148240881461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21223946612356098827254307 31835919918534148240881461)
      ·
        refine ⟨2984617492362576397582637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 31835919918534148240881461 2984617492362576397582637)
        ·
          refine ⟨1119231559635966149093489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2984617492362576397582637 1119231559635966149093489)
          ·
            refine ⟨839423669726974611820117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1119231559635966149093489 839423669726974611820117)
            ·
              refine ⟨9836996129612983732267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 839423669726974611820117 9836996129612983732267)
              ·
                rfl

theorem cell21_387939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 8].length) (baseStart_387939 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387939 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387939 prefixEnd_387939 := by exact prefixLift 387939
  have htrace : WordTrace (prefixWord ++ tailWord_387939) baseStart_387939 baseEnd_387939 := by
    simpa [prefixWord, tailWord_387939, baseEnd_387939] using wordTrace_append hprefix tailTrace_387939
  have hstable : (prefixWord ++ tailWord_387939).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387939).length < 2 ^ (prefixWord ++ tailWord_387939).sum := by decide
  have hdescent : baseEnd_387939 < baseStart_387939 := by decide
  rcases family_descends (prefixWord ++ tailWord_387939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_387990 : List Nat := [5, 3, 1, 1, 1, 3, 7]
def baseStart_387990 : Nat := 118140960795 + 387990 * 2 ^ 59
def prefixEnd_387990 : Nat := 4983230072969 + 3 ^ 40 * 387990 * 2
def baseEnd_387990 : Nat := 9838289340150233137811

theorem tailTrace_387990 : CollatzResearch.WordTrace tailWord_387990 prefixEnd_387990 9838289340150233137811 := by
  unfold tailWord_387990
  simp only [CollatzResearch.WordTrace]
  refine ⟨884447366524123016350589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9434105242923978841072949 884447366524123016350589)
  ·
    refine ⟨331667762446546131131471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 884447366524123016350589 331667762446546131131471)
    ·
      refine ⟨497501643669819196697207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 331667762446546131131471 497501643669819196697207)
      ·
        refine ⟨746252465504728795045811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 497501643669819196697207 746252465504728795045811)
        ·
          refine ⟨1119378698257093192568717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746252465504728795045811 1119378698257093192568717)
          ·
            refine ⟨419767011846409947213269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1119378698257093192568717 419767011846409947213269)
            ·
              refine ⟨9838289340150233137811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 419767011846409947213269 9838289340150233137811)
              ·
                rfl

theorem cell21_387990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 7].length) (baseStart_387990 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_387990 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_387990 prefixEnd_387990 := by exact prefixLift 387990
  have htrace : WordTrace (prefixWord ++ tailWord_387990) baseStart_387990 baseEnd_387990 := by
    simpa [prefixWord, tailWord_387990, baseEnd_387990] using wordTrace_append hprefix tailTrace_387990
  have hstable : (prefixWord ++ tailWord_387990).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_387990).length < 2 ^ (prefixWord ++ tailWord_387990).sum := by decide
  have hdescent : baseEnd_387990 < baseStart_387990 := by decide
  rcases family_descends (prefixWord ++ tailWord_387990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388001 : List Nat := [1, 2, 3, 4, 1, 1, 2, 1, 6]
def baseStart_388001 : Nat := 118140960795 + 388001 * 2 ^ 59
def prefixEnd_388001 : Nat := 4983230072969 + 3 ^ 40 * 388001 * 2
def baseEnd_388001 : Nat := 88547114411218523556943

theorem tailTrace_388001 : CollatzResearch.WordTrace tailWord_388001 prefixEnd_388001 88547114411218523556943 := by
  unfold tailWord_388001
  simp only [CollatzResearch.WordTrace]
  refine ⟨14151559067346117140259857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9434372711564078093506571 14151559067346117140259857)
  ·
    refine ⟨10613669300509587855194893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14151559067346117140259857 10613669300509587855194893)
    ·
      refine ⟨3980125987691095445698085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10613669300509587855194893 3980125987691095445698085)
      ·
        refine ⟨746273622692080396068391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3980125987691095445698085 746273622692080396068391)
        ·
          refine ⟨1119410434038120594102587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 746273622692080396068391 1119410434038120594102587)
          ·
            refine ⟨1679115651057180891153881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1119410434038120594102587 1679115651057180891153881)
            ·
              refine ⟨1259336738292885668365411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1679115651057180891153881 1259336738292885668365411)
              ·
                refine ⟨1889005107439328502548117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1259336738292885668365411 1889005107439328502548117)
                ·
                  refine ⟨88547114411218523556943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1889005107439328502548117 88547114411218523556943)
                  ·
                    rfl

theorem cell21_388001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 2, 1, 6].length) (baseStart_388001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388001 prefixEnd_388001 := by exact prefixLift 388001
  have htrace : WordTrace (prefixWord ++ tailWord_388001) baseStart_388001 baseEnd_388001 := by
    simpa [prefixWord, tailWord_388001, baseEnd_388001] using wordTrace_append hprefix tailTrace_388001
  have hstable : (prefixWord ++ tailWord_388001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388001).length < 2 ^ (prefixWord ++ tailWord_388001).sum := by decide
  have hdescent : baseEnd_388001 < baseStart_388001 := by decide
  rcases family_descends (prefixWord ++ tailWord_388001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388004 : List Nat := [2, 3, 1, 2, 1, 2, 5, 2, 3]
def baseStart_388004 : Nat := 118140960795 + 388004 * 2 ^ 59
def prefixEnd_388004 : Nat := 4983230072969 + 3 ^ 40 * 388004 * 2
def baseEnd_388004 : Nat := 88547799052091185006937

theorem tailTrace_388004 : CollatzResearch.WordTrace tailWord_388004 prefixEnd_388004 88547799052091185006937 := by
  unfold tailWord_388004
  simp only [CollatzResearch.WordTrace]
  refine ⟨7075834243167624326309533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9434445657556832435079377 7075834243167624326309533)
  ·
    refine ⟨2653437841187859122366075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7075834243167624326309533 2653437841187859122366075)
    ·
      refine ⟨3980156761781788683549113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2653437841187859122366075 3980156761781788683549113)
      ·
        refine ⟨2985117571336341512661835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3980156761781788683549113 2985117571336341512661835)
        ·
          refine ⟨4477676357004512268992753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2985117571336341512661835 4477676357004512268992753)
          ·
            refine ⟨3358257267753384201744565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4477676357004512268992753 3358257267753384201744565)
            ·
              refine ⟨314836618851879768913553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3358257267753384201744565 314836618851879768913553)
              ·
                refine ⟨236127464138909826685165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314836618851879768913553 236127464138909826685165)
                ·
                  refine ⟨88547799052091185006937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236127464138909826685165 88547799052091185006937)
                  ·
                    rfl

theorem cell21_388004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 5, 2, 3].length) (baseStart_388004 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388004 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388004 prefixEnd_388004 := by exact prefixLift 388004
  have htrace : WordTrace (prefixWord ++ tailWord_388004) baseStart_388004 baseEnd_388004 := by
    simpa [prefixWord, tailWord_388004, baseEnd_388004] using wordTrace_append hprefix tailTrace_388004
  have hstable : (prefixWord ++ tailWord_388004).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388004).length < 2 ^ (prefixWord ++ tailWord_388004).sum := by decide
  have hdescent : baseEnd_388004 < baseStart_388004 := by decide
  rcases family_descends (prefixWord ++ tailWord_388004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388122 : List Nat := [3, 1, 1, 3, 1, 2, 4, 1, 5]
def baseStart_388122 : Nat := 118140960795 + 388122 * 2 ^ 59
def prefixEnd_388122 : Nat := 4983230072969 + 3 ^ 40 * 388122 * 2
def baseEnd_388122 : Nat := 88574728259749202040029

theorem tailTrace_388122 : CollatzResearch.WordTrace tailWord_388122 prefixEnd_388122 88574728259749202040029 := by
  unfold tailWord_388122
  simp only [CollatzResearch.WordTrace]
  refine ⟨3538993074976938701353655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9437314866605169870276413 3538993074976938701353655)
  ·
    refine ⟨5308489612465408052030483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3538993074976938701353655 5308489612465408052030483)
    ·
      refine ⟨7962734418698112078045725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5308489612465408052030483 7962734418698112078045725)
      ·
        refine ⟨2986025407011792029267147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7962734418698112078045725 2986025407011792029267147)
        ·
          refine ⟨4479038110517688043900721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2986025407011792029267147 4479038110517688043900721)
          ·
            refine ⟨3359278582888266032925541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4479038110517688043900721 3359278582888266032925541)
            ·
              refine ⟨629864734291549881173539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3359278582888266032925541 629864734291549881173539)
              ·
                refine ⟨944797101437324821760309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 629864734291549881173539 944797101437324821760309)
                ·
                  refine ⟨88574728259749202040029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 944797101437324821760309 88574728259749202040029)
                  ·
                    rfl

theorem cell21_388122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 5].length) (baseStart_388122 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388122 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388122 prefixEnd_388122 := by exact prefixLift 388122
  have htrace : WordTrace (prefixWord ++ tailWord_388122) baseStart_388122 baseEnd_388122 := by
    simpa [prefixWord, tailWord_388122, baseEnd_388122] using wordTrace_append hprefix tailTrace_388122
  have hstable : (prefixWord ++ tailWord_388122).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388122).length < 2 ^ (prefixWord ++ tailWord_388122).sum := by decide
  have hdescent : baseEnd_388122 < baseStart_388122 := by decide
  rcases family_descends (prefixWord ++ tailWord_388122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388156 : List Nat := [2, 2, 2, 2, 2, 4, 1, 3, 3]
def baseStart_388156 : Nat := 118140960795 + 388156 * 2 ^ 59
def prefixEnd_388156 : Nat := 4983230072969 + 3 ^ 40 * 388156 * 2
def baseEnd_388156 : Nat := 88582487522972698473293

theorem tailTrace_388156 : CollatzResearch.WordTrace tailWord_388156 prefixEnd_388156 88582487522972698473293 := by
  unfold tailWord_388156
  simp only [CollatzResearch.WordTrace]
  refine ⟨7078606190892289306076161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9438141587856385741434881 7078606190892289306076161)
  ·
    refine ⟨5308954643169216979557121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7078606190892289306076161 5308954643169216979557121)
    ·
      refine ⟨3981715982376912734667841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5308954643169216979557121 3981715982376912734667841)
      ·
        refine ⟨2986286986782684551000881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3981715982376912734667841 2986286986782684551000881)
        ·
          refine ⟨2239715240087013413250661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2986286986782684551000881 2239715240087013413250661)
          ·
            refine ⟨419946607516315014984499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2239715240087013413250661 419946607516315014984499)
            ·
              refine ⟨629919911274472522476749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 419946607516315014984499 629919911274472522476749)
              ·
                refine ⟨236219966727927195928781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 629919911274472522476749 236219966727927195928781)
                ·
                  refine ⟨88582487522972698473293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236219966727927195928781 88582487522972698473293)
                  ·
                    rfl

theorem cell21_388156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 4, 1, 3, 3].length) (baseStart_388156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388156 prefixEnd_388156 := by exact prefixLift 388156
  have htrace : WordTrace (prefixWord ++ tailWord_388156) baseStart_388156 baseEnd_388156 := by
    simpa [prefixWord, tailWord_388156, baseEnd_388156] using wordTrace_append hprefix tailTrace_388156
  have hstable : (prefixWord ++ tailWord_388156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388156).length < 2 ^ (prefixWord ++ tailWord_388156).sum := by decide
  have hdescent : baseEnd_388156 < baseStart_388156 := by decide
  rcases family_descends (prefixWord ++ tailWord_388156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388167 : List Nat := [1, 1, 4, 1, 3, 4, 7]
def baseStart_388167 : Nat := 118140960795 + 388167 * 2 ^ 59
def prefixEnd_388167 : Nat := 4983230072969 + 3 ^ 40 * 388167 * 2
def baseEnd_388167 : Nat := 9842777541426569309993

theorem tailTrace_388167 : CollatzResearch.WordTrace tailWord_388167 prefixEnd_388167 9842777541426569309993 := by
  unfold tailWord_388167
  simp only [CollatzResearch.WordTrace]
  refine ⟨14157613584744727490802755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9438409056496484993868503 14157613584744727490802755)
  ·
    refine ⟨21236420377117091236204133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14157613584744727490802755 21236420377117091236204133)
    ·
      refine ⟨3981828820709454606788275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21236420377117091236204133 3981828820709454606788275)
      ·
        refine ⟨5972743231064181910182413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3981828820709454606788275 5972743231064181910182413)
        ·
          refine ⟨2239778711649068216318405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5972743231064181910182413 2239778711649068216318405)
          ·
            refine ⟨419958508434200290559701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2239778711649068216318405 419958508434200290559701)
            ·
              refine ⟨9842777541426569309993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 419958508434200290559701 9842777541426569309993)
              ·
                rfl

theorem cell21_388167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 4, 7].length) (baseStart_388167 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388167 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388167 prefixEnd_388167 := by exact prefixLift 388167
  have htrace : WordTrace (prefixWord ++ tailWord_388167) baseStart_388167 baseEnd_388167 := by
    simpa [prefixWord, tailWord_388167, baseEnd_388167] using wordTrace_append hprefix tailTrace_388167
  have hstable : (prefixWord ++ tailWord_388167).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388167).length < 2 ^ (prefixWord ++ tailWord_388167).sum := by decide
  have hdescent : baseEnd_388167 < baseStart_388167 := by decide
  rcases family_descends (prefixWord ++ tailWord_388167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388173 : List Nat := [1, 6, 1, 1, 1, 3, 3, 2, 3]
def baseStart_388173 : Nat := 118140960795 + 388173 * 2 ^ 59
def prefixEnd_388173 : Nat := 4983230072969 + 3 ^ 40 * 388173 * 2
def baseEnd_388173 : Nat := 88586367154584446689925

theorem tailTrace_388173 : CollatzResearch.WordTrace tailWord_388173 prefixEnd_388173 88586367154584446689925 := by
  unfold tailWord_388173
  simp only [CollatzResearch.WordTrace]
  refine ⟨14157832422722990515521173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9438554948481993677014115 14157832422722990515521173)
  ·
    refine ⟨663648394815140180415055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14157832422722990515521173 663648394815140180415055)
    ·
      refine ⟨995472592222710270622583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 663648394815140180415055 995472592222710270622583)
      ·
        refine ⟨1493208888334065405933875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 995472592222710270622583 1493208888334065405933875)
        ·
          refine ⟨2239813332501098108900813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1493208888334065405933875 2239813332501098108900813)
          ·
            refine ⟨839929999687911790837805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2239813332501098108900813 839929999687911790837805)
            ·
              refine ⟨314973749882966921564177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 839929999687911790837805 314973749882966921564177)
              ·
                refine ⟨236230312412225191173133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 314973749882966921564177 236230312412225191173133)
                ·
                  refine ⟨88586367154584446689925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236230312412225191173133 88586367154584446689925)
                  ·
                    rfl

theorem cell21_388173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_388173 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388173 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388173 prefixEnd_388173 := by exact prefixLift 388173
  have htrace : WordTrace (prefixWord ++ tailWord_388173) baseStart_388173 baseEnd_388173 := by
    simpa [prefixWord, tailWord_388173, baseEnd_388173] using wordTrace_append hprefix tailTrace_388173
  have hstable : (prefixWord ++ tailWord_388173).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388173).length < 2 ^ (prefixWord ++ tailWord_388173).sum := by decide
  have hdescent : baseEnd_388173 < baseStart_388173 := by decide
  rcases family_descends (prefixWord ++ tailWord_388173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388232 : List Nat := [2, 1, 3, 4, 2, 1, 1, 4, 3]
def baseStart_388232 : Nat := 118140960795 + 388232 * 2 ^ 59
def prefixEnd_388232 : Nat := 4983230072969 + 3 ^ 40 * 388232 * 2
def baseEnd_388232 : Nat := 88599831758413455206471

theorem tailTrace_388232 : CollatzResearch.WordTrace tailWord_388232 prefixEnd_388232 88599831758413455206471 := by
  unfold tailWord_388232
  simp only [CollatzResearch.WordTrace]
  refine ⟨7079992164754621795959475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9439989553006162394612633 7079992164754621795959475)
  ·
    refine ⟨10619988247131932693939213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7079992164754621795959475 10619988247131932693939213)
    ·
      refine ⟨3982495592674474760227205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10619988247131932693939213 3982495592674474760227205)
      ·
        refine ⟨746717923626464017542601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3982495592674474760227205 746717923626464017542601)
        ·
          refine ⟨560038442719848013156951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 746717923626464017542601 560038442719848013156951)
          ·
            refine ⟨840057664079772019735427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560038442719848013156951 840057664079772019735427)
            ·
              refine ⟨1260086496119658029603141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 840057664079772019735427 1260086496119658029603141)
              ·
                refine ⟨236266218022435880550589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1260086496119658029603141 236266218022435880550589)
                ·
                  refine ⟨88599831758413455206471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236266218022435880550589 88599831758413455206471)
                  ·
                    rfl

theorem cell21_388232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 4, 3].length) (baseStart_388232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388232 prefixEnd_388232 := by exact prefixLift 388232
  have htrace : WordTrace (prefixWord ++ tailWord_388232) baseStart_388232 baseEnd_388232 := by
    simpa [prefixWord, tailWord_388232, baseEnd_388232] using wordTrace_append hprefix tailTrace_388232
  have hstable : (prefixWord ++ tailWord_388232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388232).length < 2 ^ (prefixWord ++ tailWord_388232).sum := by decide
  have hdescent : baseEnd_388232 < baseStart_388232 := by decide
  rcases family_descends (prefixWord ++ tailWord_388232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388260 : List Nat := [2, 3, 1, 2, 3, 2, 3, 5]
def baseStart_388260 : Nat := 118140960795 + 388260 * 2 ^ 59
def prefixEnd_388260 : Nat := 4983230072969 + 3 ^ 40 * 388260 * 2
def baseEnd_388260 : Nat := 29535407246630542913249

theorem tailTrace_388260 : CollatzResearch.WordTrace tailWord_388260 prefixEnd_388260 29535407246630542913249 := by
  unfold tailWord_388260
  simp only [CollatzResearch.WordTrace]
  refine ⟨7080502786703902186969117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9440670382271869582625489 7080502786703902186969117)
  ·
    refine ⟨2655188545013963320113419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7080502786703902186969117 2655188545013963320113419)
    ·
      refine ⟨3982782817520944980170129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2655188545013963320113419 3982782817520944980170129)
      ·
        refine ⟨2987087113140708735127597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3982782817520944980170129 2987087113140708735127597)
        ·
          refine ⟨1120157667427765775672849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2987087113140708735127597 1120157667427765775672849)
          ·
            refine ⟨840118250570824331754637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1120157667427765775672849 840118250570824331754637)
            ·
              refine ⟨315044343964059124407989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 840118250570824331754637 315044343964059124407989)
              ·
                refine ⟨29535407246630542913249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 315044343964059124407989 29535407246630542913249)
                ·
                  rfl

theorem cell21_388260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 5].length) (baseStart_388260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388260 prefixEnd_388260 := by exact prefixLift 388260
  have htrace : WordTrace (prefixWord ++ tailWord_388260) baseStart_388260 baseEnd_388260 := by
    simpa [prefixWord, tailWord_388260, baseEnd_388260] using wordTrace_append hprefix tailTrace_388260
  have hstable : (prefixWord ++ tailWord_388260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388260).length < 2 ^ (prefixWord ++ tailWord_388260).sum := by decide
  have hdescent : baseEnd_388260 < baseStart_388260 := by decide
  rcases family_descends (prefixWord ++ tailWord_388260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388319 : List Nat := [1, 1, 2, 3, 2, 1, 6, 5]
def baseStart_388319 : Nat := 118140960795 + 388319 * 2 ^ 59
def prefixEnd_388319 : Nat := 4983230072969 + 3 ^ 40 * 388319 * 2
def baseEnd_388319 : Nat := 29539895447906879085431

theorem tailTrace_388319 : CollatzResearch.WordTrace tailWord_388319 prefixEnd_388319 29539895447906879085431 := by
  unfold tailWord_388319
  simp only [CollatzResearch.WordTrace]
  refine ⟨14163157480194057450336011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9442104986796038300224007 14163157480194057450336011)
  ·
    refine ⟨21244736220291086175504017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14163157480194057450336011 21244736220291086175504017)
    ·
      refine ⟨15933552165218314631628013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21244736220291086175504017 15933552165218314631628013)
      ·
        refine ⟨5975082061956867986860505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15933552165218314631628013 5975082061956867986860505)
        ·
          refine ⟨4481311546467650990145379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5975082061956867986860505 4481311546467650990145379)
          ·
            refine ⟨6721967319701476485218069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4481311546467650990145379 6721967319701476485218069)
            ·
              refine ⟨315092218111006710244597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6721967319701476485218069 315092218111006710244597)
              ·
                refine ⟨29539895447906879085431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 315092218111006710244597 29539895447906879085431)
                ·
                  rfl

theorem cell21_388319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 6, 5].length) (baseStart_388319 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388319 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388319 prefixEnd_388319 := by exact prefixLift 388319
  have htrace : WordTrace (prefixWord ++ tailWord_388319) baseStart_388319 baseEnd_388319 := by
    simpa [prefixWord, tailWord_388319, baseEnd_388319] using wordTrace_append hprefix tailTrace_388319
  have hstable : (prefixWord ++ tailWord_388319).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388319).length < 2 ^ (prefixWord ++ tailWord_388319).sum := by decide
  have hdescent : baseEnd_388319 < baseStart_388319 := by decide
  rcases family_descends (prefixWord ++ tailWord_388319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388325 : List Nat := [1, 3, 1, 4, 4, 1, 1, 3, 3]
def baseStart_388325 : Nat := 118140960795 + 388325 * 2 ^ 59
def prefixEnd_388325 : Nat := 4983230072969 + 3 ^ 40 * 388325 * 2
def baseEnd_388325 : Nat := 88621055625465960156281

theorem tailTrace_388325 : CollatzResearch.WordTrace tailWord_388325 prefixEnd_388325 88621055625465960156281 := by
  unfold tailWord_388325
  simp only [CollatzResearch.WordTrace]
  refine ⟨14163376318172320475054429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9442250878781546983369619 14163376318172320475054429)
  ·
    refine ⟨5311266119314620178145411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14163376318172320475054429 5311266119314620178145411)
    ·
      refine ⟨7966899178971930267218117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5311266119314620178145411 7966899178971930267218117)
      ·
        refine ⟨1493793596057236925103397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7966899178971930267218117 1493793596057236925103397)
        ·
          refine ⟨280086299260731923456887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1493793596057236925103397 280086299260731923456887)
          ·
            refine ⟨420129448891097885185331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280086299260731923456887 420129448891097885185331)
            ·
              refine ⟨630194173336646827777997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420129448891097885185331 630194173336646827777997)
              ·
                refine ⟨236322815001242560416749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 630194173336646827777997 236322815001242560416749)
                ·
                  refine ⟨88621055625465960156281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236322815001242560416749 88621055625465960156281)
                  ·
                    rfl

theorem cell21_388325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 3, 3].length) (baseStart_388325 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388325 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388325 prefixEnd_388325 := by exact prefixLift 388325
  have htrace : WordTrace (prefixWord ++ tailWord_388325) baseStart_388325 baseEnd_388325 := by
    simpa [prefixWord, tailWord_388325, baseEnd_388325] using wordTrace_append hprefix tailTrace_388325
  have hstable : (prefixWord ++ tailWord_388325).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388325).length < 2 ^ (prefixWord ++ tailWord_388325).sum := by decide
  have hdescent : baseEnd_388325 < baseStart_388325 := by decide
  rcases family_descends (prefixWord ++ tailWord_388325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388485 : List Nat := [1, 3, 1, 1, 3, 1, 4, 2, 5]
def baseStart_388485 : Nat := 118140960795 + 388485 * 2 ^ 59
def prefixEnd_388485 : Nat := 4983230072969 + 3 ^ 40 * 388485 * 2
def baseEnd_388485 : Nat := 88657569805341237489287

theorem tailTrace_388485 : CollatzResearch.WordTrace tailWord_388485 prefixEnd_388485 88657569805341237489287 := by
  unfold tailWord_388485
  simp only [CollatzResearch.WordTrace]
  refine ⟨14169211997592667800878909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9446141331728445200585939 14169211997592667800878909)
  ·
    refine ⟨5313454499097250425329591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14169211997592667800878909 5313454499097250425329591)
    ·
      refine ⟨7970181748645875637994387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5313454499097250425329591 7970181748645875637994387)
      ·
        refine ⟨11955272622968813456991581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7970181748645875637994387 11955272622968813456991581)
        ·
          refine ⟨4483227233613305046371843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11955272622968813456991581 4483227233613305046371843)
          ·
            refine ⟨6724840850419957569557765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4483227233613305046371843 6724840850419957569557765)
            ·
              refine ⟨1260907659453742044292081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6724840850419957569557765 1260907659453742044292081)
              ·
                refine ⟨945680744590306533219061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1260907659453742044292081 945680744590306533219061)
                ·
                  refine ⟨88657569805341237489287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 945680744590306533219061 88657569805341237489287)
                  ·
                    rfl

theorem cell21_388485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 2, 5].length) (baseStart_388485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388485 prefixEnd_388485 := by exact prefixLift 388485
  have htrace : WordTrace (prefixWord ++ tailWord_388485) baseStart_388485 baseEnd_388485 := by
    simpa [prefixWord, tailWord_388485, baseEnd_388485] using wordTrace_append hprefix tailTrace_388485
  have hstable : (prefixWord ++ tailWord_388485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388485).length < 2 ^ (prefixWord ++ tailWord_388485).sum := by decide
  have hdescent : baseEnd_388485 < baseStart_388485 := by decide
  rcases family_descends (prefixWord ++ tailWord_388485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388488 : List Nat := [2, 1, 3, 3, 1, 4, 2, 5]
def baseStart_388488 : Nat := 118140960795 + 388488 * 2 ^ 59
def prefixEnd_388488 : Nat := 4983230072969 + 3 ^ 40 * 388488 * 2
def baseEnd_388488 : Nat := 29552751482071299646427

theorem tailTrace_388488 : CollatzResearch.WordTrace tailWord_388488 prefixEnd_388488 29552751482071299646427 := by
  unfold tailWord_388488
  simp only [CollatzResearch.WordTrace]
  refine ⟨7084660708290899656619059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9446214277721199542158745 7084660708290899656619059)
  ·
    refine ⟨10626991062436349484928589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7084660708290899656619059 10626991062436349484928589)
    ·
      refine ⟨3985121648413631056848221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10626991062436349484928589 3985121648413631056848221)
      ·
        refine ⟨1494420618155111646318083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3985121648413631056848221 1494420618155111646318083)
        ·
          refine ⟨2241630927232667469477125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1494420618155111646318083 2241630927232667469477125)
          ·
            refine ⟨420305798856125150526961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2241630927232667469477125 420305798856125150526961)
            ·
              refine ⟨315229349142093862895221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420305798856125150526961 315229349142093862895221)
              ·
                refine ⟨29552751482071299646427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 315229349142093862895221 29552751482071299646427)
                ·
                  rfl

theorem cell21_388488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 4, 2, 5].length) (baseStart_388488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388488 prefixEnd_388488 := by exact prefixLift 388488
  have htrace : WordTrace (prefixWord ++ tailWord_388488) baseStart_388488 baseEnd_388488 := by
    simpa [prefixWord, tailWord_388488, baseEnd_388488] using wordTrace_append hprefix tailTrace_388488
  have hstable : (prefixWord ++ tailWord_388488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388488).length < 2 ^ (prefixWord ++ tailWord_388488).sum := by decide
  have hdescent : baseEnd_388488 < baseStart_388488 := by decide
  rcases family_descends (prefixWord ++ tailWord_388488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388516 : List Nat := [2, 3, 1, 2, 1, 1, 1, 6, 4]
def baseStart_388516 : Nat := 118140960795 + 388516 * 2 ^ 59
def prefixEnd_388516 : Nat := 4983230072969 + 3 ^ 40 * 388516 * 2
def baseEnd_388516 : Nat := 88664644427692072472557

theorem tailTrace_388516 : CollatzResearch.WordTrace tailWord_388516 prefixEnd_388516 88664644427692072472557 := by
  unfold tailWord_388516
  simp only [CollatzResearch.WordTrace]
  refine ⟨7085171330240180047628701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9446895106986906730171601 7085171330240180047628701)
  ·
    refine ⟨2656939248840067517860763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7085171330240180047628701 2656939248840067517860763)
    ·
      refine ⟨3985408873260101276791145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2656939248840067517860763 3985408873260101276791145)
      ·
        refine ⟨2989056654945075957593359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3985408873260101276791145 2989056654945075957593359)
        ·
          refine ⟨4483584982417613936390039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2989056654945075957593359 4483584982417613936390039)
          ·
            refine ⟨6725377473626420904585059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4483584982417613936390039 6725377473626420904585059)
            ·
              refine ⟨10088066210439631356877589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6725377473626420904585059 10088066210439631356877589)
              ·
                refine ⟨472878103614357719853637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10088066210439631356877589 472878103614357719853637)
                ·
                  refine ⟨88664644427692072472557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 472878103614357719853637 88664644427692072472557)
                  ·
                    rfl

theorem cell21_388516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_388516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388516 prefixEnd_388516 := by exact prefixLift 388516
  have htrace : WordTrace (prefixWord ++ tailWord_388516) baseStart_388516 baseEnd_388516 := by
    simpa [prefixWord, tailWord_388516, baseEnd_388516] using wordTrace_append hprefix tailTrace_388516
  have hstable : (prefixWord ++ tailWord_388516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388516).length < 2 ^ (prefixWord ++ tailWord_388516).sum := by decide
  have hdescent : baseEnd_388516 < baseStart_388516 := by decide
  rcases family_descends (prefixWord ++ tailWord_388516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388533 : List Nat := [1, 3, 3, 2, 2, 2, 1, 3, 4]
def baseStart_388533 : Nat := 118140960795 + 388533 * 2 ^ 59
def prefixEnd_388533 : Nat := 4983230072969 + 3 ^ 40 * 388533 * 2
def baseEnd_388533 : Nat := 88668524059303820689189

theorem tailTrace_388533 : CollatzResearch.WordTrace tailWord_388533 prefixEnd_388533 88668524059303820689189 := by
  unfold tailWord_388533
  simp only [CollatzResearch.WordTrace]
  refine ⟨14170962701418771998626253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9447308467612514665750835 14170962701418771998626253)
  ·
    refine ⟨5314111013032039499484845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14170962701418771998626253 5314111013032039499484845)
    ·
      refine ⟨1992791629887014812306817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5314111013032039499484845 1992791629887014812306817)
      ·
        refine ⟨1494593722415261109230113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1992791629887014812306817 1494593722415261109230113)
        ·
          refine ⟨1120945291811445831922585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1494593722415261109230113 1120945291811445831922585)
          ·
            refine ⟨840708968858584373941939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1120945291811445831922585 840708968858584373941939)
            ·
              refine ⟨1261063453287876560912909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 840708968858584373941939 1261063453287876560912909)
              ·
                refine ⟨472898794982953710342341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1261063453287876560912909 472898794982953710342341)
                ·
                  refine ⟨88668524059303820689189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 472898794982953710342341 88668524059303820689189)
                  ·
                    rfl

theorem cell21_388533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 4].length) (baseStart_388533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388533 prefixEnd_388533 := by exact prefixLift 388533
  have htrace : WordTrace (prefixWord ++ tailWord_388533) baseStart_388533 baseEnd_388533 := by
    simpa [prefixWord, tailWord_388533, baseEnd_388533] using wordTrace_append hprefix tailTrace_388533
  have hstable : (prefixWord ++ tailWord_388533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388533).length < 2 ^ (prefixWord ++ tailWord_388533).sum := by decide
  have hdescent : baseEnd_388533 < baseStart_388533 := by decide
  rcases family_descends (prefixWord ++ tailWord_388533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388592 : List Nat := [2, 1, 1, 1, 3, 4, 2, 3, 4]
def baseStart_388592 : Nat := 118140960795 + 388592 * 2 ^ 59
def prefixEnd_388592 : Nat := 4983230072969 + 3 ^ 40 * 388592 * 2
def baseEnd_388592 : Nat := 88681988663132829205735

theorem tailTrace_388592 : CollatzResearch.WordTrace tailWord_388592 prefixEnd_388592 88681988663132829205735 := by
  unfold tailWord_388592
  simp only [CollatzResearch.WordTrace]
  refine ⟨7086557304102512537512015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9448743072136683383349353 7086557304102512537512015)
  ·
    refine ⟨10629835956153768806268023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7086557304102512537512015 10629835956153768806268023)
    ·
      refine ⟨15944753934230653209402035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10629835956153768806268023 15944753934230653209402035)
      ·
        refine ⟨23917130901345979814103053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15944753934230653209402035 23917130901345979814103053)
        ·
          refine ⟨8968924088004742430288645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23917130901345979814103053 8968924088004742430288645)
          ·
            refine ⟨1681673266500889205679121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8968924088004742430288645 1681673266500889205679121)
            ·
              refine ⟨1261254949875666904259341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1681673266500889205679121 1261254949875666904259341)
              ·
                refine ⟨472970606203375089097253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1261254949875666904259341 472970606203375089097253)
                ·
                  refine ⟨88681988663132829205735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 472970606203375089097253 88681988663132829205735)
                  ·
                    rfl

theorem cell21_388592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 2, 3, 4].length) (baseStart_388592 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388592 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388592 prefixEnd_388592 := by exact prefixLift 388592
  have htrace : WordTrace (prefixWord ++ tailWord_388592) baseStart_388592 baseEnd_388592 := by
    simpa [prefixWord, tailWord_388592, baseEnd_388592] using wordTrace_append hprefix tailTrace_388592
  have hstable : (prefixWord ++ tailWord_388592).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388592).length < 2 ^ (prefixWord ++ tailWord_388592).sum := by decide
  have hdescent : baseEnd_388592 < baseStart_388592 := by decide
  rcases family_descends (prefixWord ++ tailWord_388592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388612 : List Nat := [2, 3, 2, 3, 2, 1, 2, 3, 3]
def baseStart_388612 : Nat := 118140960795 + 388612 * 2 ^ 59
def prefixEnd_388612 : Nat := 4983230072969 + 3 ^ 40 * 388612 * 2
def baseEnd_388612 : Nat := 88686552935617238872361

theorem tailTrace_388612 : CollatzResearch.WordTrace tailWord_388612 prefixEnd_388612 88686552935617238872361 := by
  unfold tailWord_388612
  simp only [CollatzResearch.WordTrace]
  refine ⟨7086922034066284245376045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9449229378755045660501393 7086922034066284245376045)
  ·
    refine ⟨2657595762774856592016017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7086922034066284245376045 2657595762774856592016017)
    ·
      refine ⟨1993196822081142444012013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2657595762774856592016017 1993196822081142444012013)
      ·
        refine ⟨747448808280428416504505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1993196822081142444012013 747448808280428416504505)
        ·
          refine ⟨560586606210321312378379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 747448808280428416504505 560586606210321312378379)
          ·
            refine ⟨840879909315481968567569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 560586606210321312378379 840879909315481968567569)
            ·
              refine ⟨630659931986611476425677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 840879909315481968567569 630659931986611476425677)
              ·
                refine ⟨236497474494979303659629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 630659931986611476425677 236497474494979303659629)
                ·
                  refine ⟨88686552935617238872361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236497474494979303659629 88686552935617238872361)
                  ·
                    rfl

theorem cell21_388612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 2, 1, 2, 3, 3].length) (baseStart_388612 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388612 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388612 prefixEnd_388612 := by exact prefixLift 388612
  have htrace : WordTrace (prefixWord ++ tailWord_388612) baseStart_388612 baseEnd_388612 := by
    simpa [prefixWord, tailWord_388612, baseEnd_388612] using wordTrace_append hprefix tailTrace_388612
  have hstable : (prefixWord ++ tailWord_388612).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388612).length < 2 ^ (prefixWord ++ tailWord_388612).sum := by decide
  have hdescent : baseEnd_388612 < baseStart_388612 := by decide
  rcases family_descends (prefixWord ++ tailWord_388612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388654 : List Nat := [4, 1, 3, 1, 2, 1, 2, 2, 5]
def baseStart_388654 : Nat := 118140960795 + 388654 * 2 ^ 59
def prefixEnd_388654 : Nat := 4983230072969 + 3 ^ 40 * 388654 * 2
def baseEnd_388654 : Nat := 88696137907834499172275

theorem tailTrace_388654 : CollatzResearch.WordTrace tailWord_388654 prefixEnd_388654 88696137907834499172275 := by
  unfold tailWord_388654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1771921991747551207972627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9450250622653606442520677 1771921991747551207972627)
  ·
    refine ⟨2657882987621326811958941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1771921991747551207972627 2657882987621326811958941)
    ·
      refine ⟨996706120357997554484603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2657882987621326811958941 996706120357997554484603)
      ·
        refine ⟨1495059180536996331726905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 996706120357997554484603 1495059180536996331726905)
        ·
          refine ⟨1121294385402747248795179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1495059180536996331726905 1121294385402747248795179)
          ·
            refine ⟨1681941578104120873192769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1121294385402747248795179 1681941578104120873192769)
            ·
              refine ⟨1261456183578090654894577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1681941578104120873192769 1261456183578090654894577)
              ·
                refine ⟨946092137683567991170933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1261456183578090654894577 946092137683567991170933)
                ·
                  refine ⟨88696137907834499172275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 946092137683567991170933 88696137907834499172275)
                  ·
                    rfl

theorem cell21_388654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 2, 5].length) (baseStart_388654 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388654 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388654 prefixEnd_388654 := by exact prefixLift 388654
  have htrace : WordTrace (prefixWord ++ tailWord_388654) baseStart_388654 baseEnd_388654 := by
    simpa [prefixWord, tailWord_388654, baseEnd_388654] using wordTrace_append hprefix tailTrace_388654
  have hstable : (prefixWord ++ tailWord_388654).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388654).length < 2 ^ (prefixWord ++ tailWord_388654).sum := by decide
  have hdescent : baseEnd_388654 < baseStart_388654 := by decide
  rcases family_descends (prefixWord ++ tailWord_388654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388671 : List Nat := [1, 1, 2, 2, 3, 5, 1, 3, 3]
def baseStart_388671 : Nat := 118140960795 + 388671 * 2 ^ 59
def prefixEnd_388671 : Nat := 4983230072969 + 3 ^ 40 * 388671 * 2
def baseEnd_388671 : Nat := 88700017539446247388907

theorem tailTrace_388671 : CollatzResearch.WordTrace tailWord_388671 prefixEnd_388671 88700017539446247388907 := by
  unfold tailWord_388671
  simp only [CollatzResearch.WordTrace]
  refine ⟨14175995974918821567149867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9450663983279214378099911 14175995974918821567149867)
  ·
    refine ⟨21263993962378232350724801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14175995974918821567149867 21263993962378232350724801)
    ·
      refine ⟨15947995471783674263043601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21263993962378232350724801 15947995471783674263043601)
      ·
        refine ⟨11960996603837755697282701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15947995471783674263043601 11960996603837755697282701)
        ·
          refine ⟨4485373726439158386481013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11960996603837755697282701 4485373726439158386481013)
          ·
            refine ⟨420503786853671098732595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4485373726439158386481013 420503786853671098732595)
            ·
              refine ⟨630755680280506648098893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420503786853671098732595 630755680280506648098893)
              ·
                refine ⟨236533380105189993037085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 630755680280506648098893 236533380105189993037085)
                ·
                  refine ⟨88700017539446247388907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236533380105189993037085 88700017539446247388907)
                  ·
                    rfl

theorem cell21_388671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 1, 3, 3].length) (baseStart_388671 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388671 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388671 prefixEnd_388671 := by exact prefixLift 388671
  have htrace : WordTrace (prefixWord ++ tailWord_388671) baseStart_388671 baseEnd_388671 := by
    simpa [prefixWord, tailWord_388671, baseEnd_388671] using wordTrace_append hprefix tailTrace_388671
  have hstable : (prefixWord ++ tailWord_388671).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388671).length < 2 ^ (prefixWord ++ tailWord_388671).sum := by decide
  have hdescent : baseEnd_388671 < baseStart_388671 := by decide
  rcases family_descends (prefixWord ++ tailWord_388671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388865 : List Nat := [1, 2, 4, 1, 1, 1, 5, 1, 5]
def baseStart_388865 : Nat := 118140960795 + 388865 * 2 ^ 59
def prefixEnd_388865 : Nat := 4983230072969 + 3 ^ 40 * 388865 * 2
def baseEnd_388865 : Nat := 88744290982545021155177

theorem tailTrace_388865 : CollatzResearch.WordTrace tailWord_388865 prefixEnd_388865 88744290982545021155177 := by
  unfold tailWord_388865
  simp only [CollatzResearch.WordTrace]
  refine ⟨14183071736215992699712049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9455381157477328466474699 14183071736215992699712049)
  ·
    refine ⟨10637303802161994524784037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14183071736215992699712049 10637303802161994524784037)
    ·
      refine ⟨1994494462905373973397007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10637303802161994524784037 1994494462905373973397007)
      ·
        refine ⟨2991741694358060960095511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1994494462905373973397007 2991741694358060960095511)
        ·
          refine ⟨4487612541537091440143267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2991741694358060960095511 4487612541537091440143267)
          ·
            refine ⟨6731418812305637160214901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4487612541537091440143267 6731418812305637160214901)
            ·
              refine ⟨631070513653653483770147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6731418812305637160214901 631070513653653483770147)
              ·
                refine ⟨946605770480480225655221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 631070513653653483770147 946605770480480225655221)
                ·
                  refine ⟨88744290982545021155177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 946605770480480225655221 88744290982545021155177)
                  ·
                    rfl

theorem cell21_388865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 5].length) (baseStart_388865 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388865 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388865 prefixEnd_388865 := by exact prefixLift 388865
  have htrace : WordTrace (prefixWord ++ tailWord_388865) baseStart_388865 baseEnd_388865 := by
    simpa [prefixWord, tailWord_388865, baseEnd_388865] using wordTrace_append hprefix tailTrace_388865
  have hstable : (prefixWord ++ tailWord_388865).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388865).length < 2 ^ (prefixWord ++ tailWord_388865).sum := by decide
  have hdescent : baseEnd_388865 < baseStart_388865 := by decide
  rcases family_descends (prefixWord ++ tailWord_388865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388871 : List Nat := [1, 1, 4, 4, 3, 1, 2, 1, 4]
def baseStart_388871 : Nat := 118140960795 + 388871 * 2 ^ 59
def prefixEnd_388871 : Nat := 4983230072969 + 3 ^ 40 * 388871 * 2
def baseEnd_388871 : Nat := 88745660264290344055165

theorem tailTrace_388871 : CollatzResearch.WordTrace tailWord_388871 prefixEnd_388871 88745660264290344055165 := by
  unfold tailWord_388871
  simp only [CollatzResearch.WordTrace]
  refine ⟨14183290574194255724430467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9455527049462837149620311 14183290574194255724430467)
  ·
    refine ⟨21274935861291383586645701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14183290574194255724430467 21274935861291383586645701)
    ·
      refine ⟨3989050473992134422496069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21274935861291383586645701 3989050473992134422496069)
      ·
        refine ⟨747946963873525204218013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3989050473992134422496069 747946963873525204218013)
        ·
          refine ⟨280480111452571951581755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 747946963873525204218013 280480111452571951581755)
          ·
            refine ⟨420720167178857927372633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280480111452571951581755 420720167178857927372633)
            ·
              refine ⟨315540125384143445529475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420720167178857927372633 315540125384143445529475)
              ·
                refine ⟨473310188076215168294213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 315540125384143445529475 473310188076215168294213)
                ·
                  refine ⟨88745660264290344055165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 473310188076215168294213 88745660264290344055165)
                  ·
                    rfl

theorem cell21_388871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 4].length) (baseStart_388871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388871 prefixEnd_388871 := by exact prefixLift 388871
  have htrace : WordTrace (prefixWord ++ tailWord_388871) baseStart_388871 baseEnd_388871 := by
    simpa [prefixWord, tailWord_388871, baseEnd_388871] using wordTrace_append hprefix tailTrace_388871
  have hstable : (prefixWord ++ tailWord_388871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388871).length < 2 ^ (prefixWord ++ tailWord_388871).sum := by decide
  have hdescent : baseEnd_388871 < baseStart_388871 := by decide
  rcases family_descends (prefixWord ++ tailWord_388871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388910 : List Nat := [4, 1, 3, 2, 11]
def baseStart_388910 : Nat := 118140960795 + 388910 * 2 ^ 59
def prefixEnd_388910 : Nat := 4983230072969 + 3 ^ 40 * 388910 * 2
def baseEnd_388910 : Nat := 1095735315995493122285

theorem tailTrace_388910 : CollatzResearch.WordTrace tailWord_388910 prefixEnd_388910 1095735315995493122285 := by
  unfold tailWord_388910
  simp only [CollatzResearch.WordTrace]
  refine ⟨1773089127631620673137523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9456475347368643590066789 1773089127631620673137523)
  ·
    refine ⟨2659633691447431009706285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1773089127631620673137523 2659633691447431009706285)
    ·
      refine ⟨997362634292786628639857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2659633691447431009706285 997362634292786628639857)
      ·
        refine ⟨748021975719589971479893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 997362634292786628639857 748021975719589971479893)
        ·
          refine ⟨1095735315995493122285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 748021975719589971479893 1095735315995493122285)
          ·
            rfl

theorem cell21_388910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 11].length) (baseStart_388910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388910 prefixEnd_388910 := by exact prefixLift 388910
  have htrace : WordTrace (prefixWord ++ tailWord_388910) baseStart_388910 baseEnd_388910 := by
    simpa [prefixWord, tailWord_388910, baseEnd_388910] using wordTrace_append hprefix tailTrace_388910
  have hstable : (prefixWord ++ tailWord_388910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388910).length < 2 ^ (prefixWord ++ tailWord_388910).sum := by decide
  have hdescent : baseEnd_388910 < baseStart_388910 := by decide
  rcases family_descends (prefixWord ++ tailWord_388910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388916 : List Nat := [2, 5, 1, 1, 2, 1, 4, 2, 3]
def baseStart_388916 : Nat := 118140960795 + 388916 * 2 ^ 59
def prefixEnd_388916 : Nat := 4983230072969 + 3 ^ 40 * 388916 * 2
def baseEnd_388916 : Nat := 88755929877380265805073

theorem tailTrace_388916 : CollatzResearch.WordTrace tailWord_388916 prefixEnd_388916 88755929877380265805073 := by
  unfold tailWord_388916
  simp only [CollatzResearch.WordTrace]
  refine ⟨7092465929515614204909301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9456621239354152273212401 7092465929515614204909301)
  ·
    refine ⟨664918680892088831710247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7092465929515614204909301 664918680892088831710247)
    ·
      refine ⟨997378021338133247565371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 664918680892088831710247 997378021338133247565371)
      ·
        refine ⟨1496067032007199871348057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 997378021338133247565371 1496067032007199871348057)
        ·
          refine ⟨1122050274005399903511043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1496067032007199871348057 1122050274005399903511043)
          ·
            refine ⟨1683075411008099855266565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1122050274005399903511043 1683075411008099855266565)
            ·
              refine ⟨315576639564018722862481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1683075411008099855266565 315576639564018722862481)
              ·
                refine ⟨236682479673014042146861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 315576639564018722862481 236682479673014042146861)
                ·
                  refine ⟨88755929877380265805073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236682479673014042146861 88755929877380265805073)
                  ·
                    rfl

theorem cell21_388916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_388916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388916 prefixEnd_388916 := by exact prefixLift 388916
  have htrace : WordTrace (prefixWord ++ tailWord_388916) baseStart_388916 baseEnd_388916 := by
    simpa [prefixWord, tailWord_388916, baseEnd_388916] using wordTrace_append hprefix tailTrace_388916
  have hstable : (prefixWord ++ tailWord_388916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388916).length < 2 ^ (prefixWord ++ tailWord_388916).sum := by decide
  have hdescent : baseEnd_388916 < baseStart_388916 := by decide
  rcases family_descends (prefixWord ++ tailWord_388916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388927 : List Nat := [1, 1, 2, 2, 6, 2, 1, 6]
def baseStart_388927 : Nat := 118140960795 + 388927 * 2 ^ 59
def prefixEnd_388927 : Nat := 4983230072969 + 3 ^ 40 * 388927 * 2
def baseEnd_388927 : Nat := 29586146742415563707239

theorem tailTrace_388927 : CollatzResearch.WordTrace tailWord_388927 prefixEnd_388927 29586146742415563707239 := by
  unfold tailWord_388927
  simp only [CollatzResearch.WordTrace]
  refine ⟨14185333061991377288469035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9456888707994251525646023 14185333061991377288469035)
  ·
    refine ⟨21277999592987065932703553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14185333061991377288469035 21277999592987065932703553)
    ·
      refine ⟨15958499694740299449527665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21277999592987065932703553 15958499694740299449527665)
      ·
        refine ⟨11968874771055224587145749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15958499694740299449527665 11968874771055224587145749)
        ·
          refine ⟨561041004893213652522457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 11968874771055224587145749 561041004893213652522457)
          ·
            refine ⟨420780753669910239391843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 561041004893213652522457 420780753669910239391843)
            ·
              refine ⟨631171130504865359087765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 420780753669910239391843 631171130504865359087765)
              ·
                refine ⟨29586146742415563707239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 631171130504865359087765 29586146742415563707239)
                ·
                  rfl

theorem cell21_388927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 2, 1, 6].length) (baseStart_388927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388927 prefixEnd_388927 := by exact prefixLift 388927
  have htrace : WordTrace (prefixWord ++ tailWord_388927) baseStart_388927 baseEnd_388927 := by
    simpa [prefixWord, tailWord_388927, baseEnd_388927] using wordTrace_append hprefix tailTrace_388927
  have hstable : (prefixWord ++ tailWord_388927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388927).length < 2 ^ (prefixWord ++ tailWord_388927).sum := by decide
  have hdescent : baseEnd_388927 < baseStart_388927 := by decide
  rcases family_descends (prefixWord ++ tailWord_388927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_388972 : List Nat := [2, 2, 1, 1, 4, 2, 3, 2, 4]
def baseStart_388972 : Nat := 118140960795 + 388972 * 2 ^ 59
def prefixEnd_388972 : Nat := 4983230072969 + 3 ^ 40 * 388972 * 2
def baseEnd_388972 : Nat := 88768709840336612871625

theorem tailTrace_388972 : CollatzResearch.WordTrace tailWord_388972 prefixEnd_388972 88768709840336612871625 := by
  unfold tailWord_388972
  simp only [CollatzResearch.WordTrace]
  refine ⟨7093487173414174986928585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9457982897885566649238113 7093487173414174986928585)
  ·
    refine ⟨5320115380060631240196439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7093487173414174986928585 5320115380060631240196439)
    ·
      refine ⟨7980173070090946860294659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5320115380060631240196439 7980173070090946860294659)
      ·
        refine ⟨11970259605136420290441989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7980173070090946860294659 11970259605136420290441989)
        ·
          refine ⟨2244423675963078804457873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11970259605136420290441989 2244423675963078804457873)
          ·
            refine ⟨1683317756972309103343405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2244423675963078804457873 1683317756972309103343405)
            ·
              refine ⟨631244158864615913753777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1683317756972309103343405 631244158864615913753777)
              ·
                refine ⟨473433119148461935315333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631244158864615913753777 473433119148461935315333)
                ·
                  refine ⟨88768709840336612871625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 473433119148461935315333 88768709840336612871625)
                  ·
                    rfl

theorem cell21_388972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_388972 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_388972 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_388972 prefixEnd_388972 := by exact prefixLift 388972
  have htrace : WordTrace (prefixWord ++ tailWord_388972) baseStart_388972 baseEnd_388972 := by
    simpa [prefixWord, tailWord_388972, baseEnd_388972] using wordTrace_append hprefix tailTrace_388972
  have hstable : (prefixWord ++ tailWord_388972).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_388972).length < 2 ^ (prefixWord ++ tailWord_388972).sum := by decide
  have hdescent : baseEnd_388972 < baseStart_388972 := by decide
  rcases family_descends (prefixWord ++ tailWord_388972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389085 : List Nat := [1, 4, 3, 1, 4, 1, 2, 2, 3]
def baseStart_389085 : Nat := 118140960795 + 389085 * 2 ^ 59
def prefixEnd_389085 : Nat := 4983230072969 + 3 ^ 40 * 389085 * 2
def baseEnd_389085 : Nat := 88794497979873527488061

theorem tailTrace_389085 : CollatzResearch.WordTrace tailWord_389085 prefixEnd_389085 88794497979873527488061 := by
  unfold tailWord_389085
  simp only [CollatzResearch.WordTrace]
  refine ⟨14191095795418970272720709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9460730530279313515147139 14191095795418970272720709)
  ·
    refine ⟨2660830461641056926135133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14191095795418970272720709 2660830461641056926135133)
    ·
      refine ⟨997811423115396347300675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2660830461641056926135133 997811423115396347300675)
      ·
        refine ⟨1496717134673094520951013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 997811423115396347300675 1496717134673094520951013)
        ·
          refine ⟨280634462751205222678315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1496717134673094520951013 280634462751205222678315)
          ·
            refine ⟨420951694126807834017473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280634462751205222678315 420951694126807834017473)
            ·
              refine ⟨315713770595105875513105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 420951694126807834017473 315713770595105875513105)
              ·
                refine ⟨236785327946329406634829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 315713770595105875513105 236785327946329406634829)
                ·
                  refine ⟨88794497979873527488061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 236785327946329406634829 88794497979873527488061)
                  ·
                    rfl

theorem cell21_389085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_389085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_389085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_389085 prefixEnd_389085 := by exact prefixLift 389085
  have htrace : WordTrace (prefixWord ++ tailWord_389085) baseStart_389085 baseEnd_389085 := by
    simpa [prefixWord, tailWord_389085, baseEnd_389085] using wordTrace_append hprefix tailTrace_389085
  have hstable : (prefixWord ++ tailWord_389085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389085).length < 2 ^ (prefixWord ++ tailWord_389085).sum := by decide
  have hdescent : baseEnd_389085 < baseStart_389085 := by decide
  rcases family_descends (prefixWord ++ tailWord_389085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389110 : List Nat := [5, 1, 1, 1, 4, 1, 1, 2, 5]
def baseStart_389110 : Nat := 118140960795 + 389110 * 2 ^ 59
def prefixEnd_389110 : Nat := 4983230072969 + 3 ^ 40 * 389110 * 2
def baseEnd_389110 : Nat := 88800203320479039571343

theorem tailTrace_389110 : CollatzResearch.WordTrace tailWord_389110 prefixEnd_389110 88800203320479039571343 := by
  unfold tailWord_389110
  simp only [CollatzResearch.WordTrace]
  refine ⟨887000476270524971398799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9461338413552266361587189 887000476270524971398799)
  ·
    refine ⟨1330500714405787457098199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 887000476270524971398799 1330500714405787457098199)
    ·
      refine ⟨1995751071608681185647299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1330500714405787457098199 1995751071608681185647299)
      ·
        refine ⟨2993626607413021778470949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1995751071608681185647299 2993626607413021778470949)
        ·
          refine ⟨561304988889941583463303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2993626607413021778470949 561304988889941583463303)
          ·
            refine ⟨841957483334912375194955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561304988889941583463303 841957483334912375194955)
            ·
              refine ⟨1262936225002368562792433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 841957483334912375194955 1262936225002368562792433)
              ·
                refine ⟨947202168751776422094325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1262936225002368562792433 947202168751776422094325)
                ·
                  refine ⟨88800203320479039571343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 947202168751776422094325 88800203320479039571343)
                  ·
                    rfl

theorem cell21_389110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 2, 5].length) (baseStart_389110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_389110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_389110 prefixEnd_389110 := by exact prefixLift 389110
  have htrace : WordTrace (prefixWord ++ tailWord_389110) baseStart_389110 baseEnd_389110 := by
    simpa [prefixWord, tailWord_389110, baseEnd_389110] using wordTrace_append hprefix tailTrace_389110
  have hstable : (prefixWord ++ tailWord_389110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389110).length < 2 ^ (prefixWord ++ tailWord_389110).sum := by decide
  have hdescent : baseEnd_389110 < baseStart_389110 := by decide
  rcases family_descends (prefixWord ++ tailWord_389110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389141 : List Nat := [1, 3, 2, 1, 5, 2, 1, 2, 4]
def baseStart_389141 : Nat := 118140960795 + 389141 * 2 ^ 59
def prefixEnd_389141 : Nat := 4983230072969 + 3 ^ 40 * 389141 * 2
def baseEnd_389141 : Nat := 88807277942829874554613

theorem tailTrace_389141 : CollatzResearch.WordTrace tailWord_389141 prefixEnd_389141 88807277942829874554613 := by
  unfold tailWord_389141
  simp only [CollatzResearch.WordTrace]
  refine ⟨14193138283216091836759277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9462092188810727891172851 14193138283216091836759277)
  ·
    refine ⟨5322426856206034438784729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14193138283216091836759277 5322426856206034438784729)
    ·
      refine ⟨3991820142154525829088547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5322426856206034438784729 3991820142154525829088547)
      ·
        refine ⟨5987730213231788743632821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3991820142154525829088547 5987730213231788743632821)
        ·
          refine ⟨561349707490480194715577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5987730213231788743632821 561349707490480194715577)
          ·
            refine ⟨421012280617860146036683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 561349707490480194715577 421012280617860146036683)
            ·
              refine ⟨631518420926790219055025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421012280617860146036683 631518420926790219055025)
              ·
                refine ⟨473638815695092664291269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631518420926790219055025 473638815695092664291269)
                ·
                  refine ⟨88807277942829874554613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 473638815695092664291269 88807277942829874554613)
                  ·
                    rfl

theorem cell21_389141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 4].length) (baseStart_389141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_389141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_389141 prefixEnd_389141 := by exact prefixLift 389141
  have htrace : WordTrace (prefixWord ++ tailWord_389141) baseStart_389141 baseEnd_389141 := by
    simpa [prefixWord, tailWord_389141, baseEnd_389141] using wordTrace_append hprefix tailTrace_389141
  have hstable : (prefixWord ++ tailWord_389141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389141).length < 2 ^ (prefixWord ++ tailWord_389141).sum := by decide
  have hdescent : baseEnd_389141 < baseStart_389141 := by decide
  rcases family_descends (prefixWord ++ tailWord_389141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389310 : List Nat := [4, 2, 1, 1, 5, 1, 1, 2, 4]
def baseStart_389310 : Nat := 118140960795 + 389310 * 2 ^ 59
def prefixEnd_389310 : Nat := 4983230072969 + 3 ^ 40 * 389310 * 2
def baseEnd_389310 : Nat := 88845846045323136237601

theorem tailTrace_389310 : CollatzResearch.WordTrace tailWord_389310 prefixEnd_389310 88845846045323136237601 := by
  unfold tailWord_389310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1774912777450479212457673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9466201479735889133107589 1774912777450479212457673)
  ·
    refine ⟨1331184583087859409343255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1774912777450479212457673 1331184583087859409343255)
    ·
      refine ⟨1996776874631789114014883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1331184583087859409343255 1996776874631789114014883)
      ·
        refine ⟨2995165311947683671022325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1996776874631789114014883 2995165311947683671022325)
        ·
          refine ⟨280796747995095344158343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2995165311947683671022325 280796747995095344158343)
          ·
            refine ⟨421195121992643016237515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280796747995095344158343 421195121992643016237515)
            ·
              refine ⟨631792682988964524356273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421195121992643016237515 631792682988964524356273)
              ·
                refine ⟨473844512241723393267205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 631792682988964524356273 473844512241723393267205)
                ·
                  refine ⟨88845846045323136237601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 473844512241723393267205 88845846045323136237601)
                  ·
                    rfl

theorem cell21_389310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 4].length) (baseStart_389310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_389310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_389310 prefixEnd_389310 := by exact prefixLift 389310
  have htrace : WordTrace (prefixWord ++ tailWord_389310) baseStart_389310 baseEnd_389310 := by
    simpa [prefixWord, tailWord_389310, baseEnd_389310] using wordTrace_append hprefix tailTrace_389310
  have hstable : (prefixWord ++ tailWord_389310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389310).length < 2 ^ (prefixWord ++ tailWord_389310).sum := by decide
  have hdescent : baseEnd_389310 < baseStart_389310 := by decide
  rcases family_descends (prefixWord ++ tailWord_389310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389383 : List Nat := [1, 1, 4, 5, 1, 1, 2, 6]
def baseStart_389383 : Nat := 118140960795 + 389383 * 2 ^ 59
def prefixEnd_389383 : Nat := 4983230072969 + 3 ^ 40 * 389383 * 2
def baseEnd_389383 : Nat := 29620835213297077173595

theorem tailTrace_389383 : CollatzResearch.WordTrace tailWord_389383 prefixEnd_389383 29620835213297077173595 := by
  unfold tailWord_389383
  simp only [CollatzResearch.WordTrace]
  refine ⟨14201964748339367167068803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9467976498892911444712535 14201964748339367167068803)
  ·
    refine ⟨21302947122509050750603205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14201964748339367167068803 21302947122509050750603205)
    ·
      refine ⟨3994302585470447015738101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21302947122509050750603205 3994302585470447015738101)
      ·
        refine ⟨374465867387854407725447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3994302585470447015738101 374465867387854407725447)
        ·
          refine ⟨561698801081781611588171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 374465867387854407725447 561698801081781611588171)
          ·
            refine ⟨842548201622672417382257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 561698801081781611588171 842548201622672417382257)
            ·
              refine ⟨631911151217004313036693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 842548201622672417382257 631911151217004313036693)
              ·
                refine ⟨29620835213297077173595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 631911151217004313036693 29620835213297077173595)
                ·
                  rfl

theorem cell21_389383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 1, 1, 2, 6].length) (baseStart_389383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_389383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_389383 prefixEnd_389383 := by exact prefixLift 389383
  have htrace : WordTrace (prefixWord ++ tailWord_389383) baseStart_389383 baseEnd_389383 := by
    simpa [prefixWord, tailWord_389383, baseEnd_389383] using wordTrace_append hprefix tailTrace_389383
  have hstable : (prefixWord ++ tailWord_389383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389383).length < 2 ^ (prefixWord ++ tailWord_389383).sum := by decide
  have hdescent : baseEnd_389383 < baseStart_389383 := by decide
  rcases family_descends (prefixWord ++ tailWord_389383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389425 : List Nat := [1, 2, 2, 3, 4, 9]
def baseStart_389425 : Nat := 118140960795 + 389425 * 2 ^ 59
def prefixEnd_389425 : Nat := 4983230072969 + 3 ^ 40 * 389425 * 2
def baseEnd_389425 : Nat := 3291558911559573771137

theorem tailTrace_389425 : CollatzResearch.WordTrace tailWord_389425 prefixEnd_389425 3291558911559573771137 := by
  unfold tailWord_389425
  simp only [CollatzResearch.WordTrace]
  refine ⟨14203496614187208340097729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9468997742791472226731819 14203496614187208340097729)
  ·
    refine ⟨10652622460640406255073297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14203496614187208340097729 10652622460640406255073297)
    ·
      refine ⟨7989466845480304691304973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10652622460640406255073297 7989466845480304691304973)
      ·
        refine ⟨2996050067055114259239365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7989466845480304691304973 2996050067055114259239365)
        ·
          refine ⟨561759387572833923607381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2996050067055114259239365 561759387572833923607381)
          ·
            refine ⟨3291558911559573771137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 561759387572833923607381 3291558911559573771137)
            ·
              rfl

theorem cell21_389425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 9].length) (baseStart_389425 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_389425 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_389425 prefixEnd_389425 := by exact prefixLift 389425
  have htrace : WordTrace (prefixWord ++ tailWord_389425) baseStart_389425 baseEnd_389425 := by
    simpa [prefixWord, tailWord_389425, baseEnd_389425] using wordTrace_append hprefix tailTrace_389425
  have hstable : (prefixWord ++ tailWord_389425).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389425).length < 2 ^ (prefixWord ++ tailWord_389425).sum := by decide
  have hdescent : baseEnd_389425 < baseStart_389425 := by decide
  rcases family_descends (prefixWord ++ tailWord_389425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389428 : List Nat := [2, 5, 1, 1, 1, 2, 1, 4, 4]
def baseStart_389428 : Nat := 118140960795 + 389428 * 2 ^ 59
def prefixEnd_389428 : Nat := 4983230072969 + 3 ^ 40 * 389428 * 2
def baseEnd_389428 : Nat := 88872775252981153270693

theorem tailTrace_389428 : CollatzResearch.WordTrace tailWord_389428 prefixEnd_389428 88872775252981153270693 := by
  unfold tailWord_389428
  simp only [CollatzResearch.WordTrace]
  refine ⟨7101803016588169926228469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9469070688784226568304625 7101803016588169926228469)
  ·
    refine ⟨665794032805140930583919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7101803016588169926228469 665794032805140930583919)
    ·
      refine ⟨998691049207711395875879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 665794032805140930583919 998691049207711395875879)
      ·
        refine ⟨1498036573811567093813819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 998691049207711395875879 1498036573811567093813819)
        ·
          refine ⟨2247054860717350640720729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1498036573811567093813819 2247054860717350640720729)
          ·
            refine ⟨1685291145538012980540547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2247054860717350640720729 1685291145538012980540547)
            ·
              refine ⟨2527936718307019470810821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1685291145538012980540547 2527936718307019470810821)
              ·
                refine ⟨473988134682566150777029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2527936718307019470810821 473988134682566150777029)
                ·
                  refine ⟨88872775252981153270693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 473988134682566150777029 88872775252981153270693)
                  ·
                    rfl

theorem cell21_389428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_389428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_389428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_389428 prefixEnd_389428 := by exact prefixLift 389428
  have htrace : WordTrace (prefixWord ++ tailWord_389428) baseStart_389428 baseEnd_389428 := by
    simpa [prefixWord, tailWord_389428, baseEnd_389428] using wordTrace_append hprefix tailTrace_389428
  have hstable : (prefixWord ++ tailWord_389428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389428).length < 2 ^ (prefixWord ++ tailWord_389428).sum := by decide
  have hdescent : baseEnd_389428 < baseStart_389428 := by decide
  rcases family_descends (prefixWord ++ tailWord_389428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389456 : List Nat := [2, 1, 1, 1, 1, 7, 1, 2, 5]
def baseStart_389456 : Nat := 118140960795 + 389456 * 2 ^ 59
def prefixEnd_389456 : Nat := 4983230072969 + 3 ^ 40 * 389456 * 2
def baseEnd_389456 : Nat := 88879165234459326803969

theorem tailTrace_389456 : CollatzResearch.WordTrace tailWord_389456 prefixEnd_389456 88879165234459326803969 := by
  unfold tailWord_389456
  simp only [CollatzResearch.WordTrace]
  refine ⟨7102313638537450317238111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9469751518049933756317481 7102313638537450317238111)
  ·
    refine ⟨10653470457806175475857167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7102313638537450317238111 10653470457806175475857167)
    ·
      refine ⟨15980205686709263213785751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10653470457806175475857167 15980205686709263213785751)
      ·
        refine ⟨23970308530063894820678627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15980205686709263213785751 23970308530063894820678627)
        ·
          refine ⟨35955462795095842231017941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 23970308530063894820678627 35955462795095842231017941)
          ·
            refine ⟨842706159260058802289483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 35955462795095842231017941 842706159260058802289483)
            ·
              refine ⟨1264059238890088203434225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842706159260058802289483 1264059238890088203434225)
              ·
                refine ⟨948044429167566152575669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1264059238890088203434225 948044429167566152575669)
                ·
                  refine ⟨88879165234459326803969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 948044429167566152575669 88879165234459326803969)
                  ·
                    rfl

theorem cell21_389456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 5].length) (baseStart_389456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_389456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_389456 prefixEnd_389456 := by exact prefixLift 389456
  have htrace : WordTrace (prefixWord ++ tailWord_389456) baseStart_389456 baseEnd_389456 := by
    simpa [prefixWord, tailWord_389456, baseEnd_389456] using wordTrace_append hprefix tailTrace_389456
  have hstable : (prefixWord ++ tailWord_389456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389456).length < 2 ^ (prefixWord ++ tailWord_389456).sum := by decide
  have hdescent : baseEnd_389456 < baseStart_389456 := by decide
  rcases family_descends (prefixWord ++ tailWord_389456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389518 : List Nat := [4, 1, 1, 4, 1, 2, 1, 7]
def baseStart_389518 : Nat := 118140960795 + 389518 * 2 ^ 59
def prefixEnd_389518 : Nat := 4983230072969 + 3 ^ 40 * 389518 * 2
def baseEnd_389518 : Nat := 29631104826386998923503

theorem tailTrace_389518 : CollatzResearch.WordTrace tailWord_389518 prefixEnd_389518 29631104826386998923503 := by
  unfold tailWord_389518
  simp only [CollatzResearch.WordTrace]
  refine ⟨1775861075356285652904151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9471259068566856815488805 1775861075356285652904151)
  ·
    refine ⟨2663791613034428479356227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1775861075356285652904151 2663791613034428479356227)
    ·
      refine ⟨3995687419551642719034341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2663791613034428479356227 3995687419551642719034341)
      ·
        refine ⟨749191391165933009818939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3995687419551642719034341 749191391165933009818939)
        ·
          refine ⟨1123787086748899514728409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 749191391165933009818939 1123787086748899514728409)
          ·
            refine ⟨842840315061674636046307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1123787086748899514728409 842840315061674636046307)
            ·
              refine ⟨1264260472592511954069461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 842840315061674636046307 1264260472592511954069461)
              ·
                refine ⟨29631104826386998923503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1264260472592511954069461 29631104826386998923503)
                ·
                  rfl

theorem cell21_389518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 1, 7].length) (baseStart_389518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_389518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_389518 prefixEnd_389518 := by exact prefixLift 389518
  have htrace : WordTrace (prefixWord ++ tailWord_389518) baseStart_389518 baseEnd_389518 := by
    simpa [prefixWord, tailWord_389518, baseEnd_389518] using wordTrace_append hprefix tailTrace_389518
  have hstable : (prefixWord ++ tailWord_389518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389518).length < 2 ^ (prefixWord ++ tailWord_389518).sum := by decide
  have hdescent : baseEnd_389518 < baseStart_389518 := by decide
  rcases family_descends (prefixWord ++ tailWord_389518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389524 : List Nat := [2, 4, 2, 1, 4, 1, 1, 3, 3]
def baseStart_389524 : Nat := 118140960795 + 389524 * 2 ^ 59
def prefixEnd_389524 : Nat := 4983230072969 + 3 ^ 40 * 389524 * 2
def baseEnd_389524 : Nat := 88894683760906319670497

theorem tailTrace_389524 : CollatzResearch.WordTrace tailWord_389524 prefixEnd_389524 88894683760906319670497 := by
  unfold tailWord_389524
  simp only [CollatzResearch.WordTrace]
  refine ⟨7103553720414274123975813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9471404960552365498634417 7103553720414274123975813)
  ·
    refine ⟨1331916322577676398245465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7103553720414274123975813 1331916322577676398245465)
    ·
      refine ⟨998937241933257298684099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1331916322577676398245465 998937241933257298684099)
      ·
        refine ⟨1498405862899885948026149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 998937241933257298684099 1498405862899885948026149)
        ·
          refine ⟨280951099293728615254903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1498405862899885948026149 280951099293728615254903)
          ·
            refine ⟨421426648940592922882355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 280951099293728615254903 421426648940592922882355)
            ·
              refine ⟨632139973410889384323533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421426648940592922882355 632139973410889384323533)
              ·
                refine ⟨237052490029083519121325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 632139973410889384323533 237052490029083519121325)
                ·
                  refine ⟨88894683760906319670497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 237052490029083519121325 88894683760906319670497)
                  ·
                    rfl

theorem cell21_389524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 4, 1, 1, 3, 3].length) (baseStart_389524 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_389524 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_389524 prefixEnd_389524 := by exact prefixLift 389524
  have htrace : WordTrace (prefixWord ++ tailWord_389524) baseStart_389524 baseEnd_389524 := by
    simpa [prefixWord, tailWord_389524, baseEnd_389524] using wordTrace_append hprefix tailTrace_389524
  have hstable : (prefixWord ++ tailWord_389524).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389524).length < 2 ^ (prefixWord ++ tailWord_389524).sum := by decide
  have hdescent : baseEnd_389524 < baseStart_389524 := by decide
  rcases family_descends (prefixWord ++ tailWord_389524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389656 : List Nat := [2, 1, 2, 3, 3, 3, 1, 2, 4]
def baseStart_389656 : Nat := 118140960795 + 389656 * 2 ^ 59
def prefixEnd_389656 : Nat := 4983230072969 + 3 ^ 40 * 389656 * 2
def baseEnd_389656 : Nat := 88924807959303423470227

theorem tailTrace_389656 : CollatzResearch.WordTrace tailWord_389656 prefixEnd_389656 88924807959303423470227 := by
  unfold tailWord_389656
  simp only [CollatzResearch.WordTrace]
  refine ⟨7105960938175167395878411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9474614584233556527837881 7105960938175167395878411)
  ·
    refine ⟨10658941407262751093817617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7105960938175167395878411 10658941407262751093817617)
    ·
      refine ⟨7994206055447063320363213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10658941407262751093817617 7994206055447063320363213)
      ·
        refine ⟨2997827270792648745136205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7994206055447063320363213 2997827270792648745136205)
        ·
          refine ⟨1124185226547243279426077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2997827270792648745136205 1124185226547243279426077)
          ·
            refine ⟨421569459955216229784779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1124185226547243279426077 421569459955216229784779)
            ·
              refine ⟨632354189932824344677169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421569459955216229784779 632354189932824344677169)
              ·
                refine ⟨474265642449618258507877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 632354189932824344677169 474265642449618258507877)
                ·
                  refine ⟨88924807959303423470227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 474265642449618258507877 88924807959303423470227)
                  ·
                    rfl

theorem cell21_389656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 3, 1, 2, 4].length) (baseStart_389656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_389656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_389656 prefixEnd_389656 := by exact prefixLift 389656
  have htrace : WordTrace (prefixWord ++ tailWord_389656) baseStart_389656 baseEnd_389656 := by
    simpa [prefixWord, tailWord_389656, baseEnd_389656] using wordTrace_append hprefix tailTrace_389656
  have hstable : (prefixWord ++ tailWord_389656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389656).length < 2 ^ (prefixWord ++ tailWord_389656).sum := by decide
  have hdescent : baseEnd_389656 < baseStart_389656 := by decide
  rcases family_descends (prefixWord ++ tailWord_389656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389701 : List Nat := [1, 3, 1, 1, 1, 5, 3, 3, 3]
def baseStart_389701 : Nat := 118140960795 + 389701 * 2 ^ 59
def prefixEnd_389701 : Nat := 4983230072969 + 3 ^ 40 * 389701 * 2
def baseEnd_389701 : Nat := 88935077572393345220135

theorem tailTrace_389701 : CollatzResearch.WordTrace tailWord_389701 prefixEnd_389701 88935077572393345220135 := by
  unfold tailWord_389701
  simp only [CollatzResearch.WordTrace]
  refine ⟨14213563161187307477144957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9475708774124871651429971 14213563161187307477144957)
  ·
    refine ⟨5330086185445240303929359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14213563161187307477144957 5330086185445240303929359)
    ·
      refine ⟨7995129278167860455894039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5330086185445240303929359 7995129278167860455894039)
      ·
        refine ⟨11992693917251790683841059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7995129278167860455894039 11992693917251790683841059)
        ·
          refine ⟨17989040875877686025761589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11992693917251790683841059 17989040875877686025761589)
          ·
            refine ⟨1686472582113533064915149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 17989040875877686025761589 1686472582113533064915149)
            ·
              refine ⟨632427218292574899343181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1686472582113533064915149 632427218292574899343181)
              ·
                refine ⟨237160206859715587253693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 632427218292574899343181 237160206859715587253693)
                ·
                  refine ⟨88935077572393345220135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 237160206859715587253693 88935077572393345220135)
                  ·
                    rfl

theorem cell21_389701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 3, 3, 3].length) (baseStart_389701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_389701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_389701 prefixEnd_389701 := by exact prefixLift 389701
  have htrace : WordTrace (prefixWord ++ tailWord_389701) baseStart_389701 baseEnd_389701 := by
    simpa [prefixWord, tailWord_389701, baseEnd_389701] using wordTrace_append hprefix tailTrace_389701
  have hstable : (prefixWord ++ tailWord_389701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389701).length < 2 ^ (prefixWord ++ tailWord_389701).sum := by decide
  have hdescent : baseEnd_389701 < baseStart_389701 := by decide
  rcases family_descends (prefixWord ++ tailWord_389701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389729 : List Nat := [1, 2, 3, 1, 1, 5, 2, 6]
def baseStart_389729 : Nat := 118140960795 + 389729 * 2 ^ 59
def prefixEnd_389729 : Nat := 4983230072969 + 3 ^ 40 * 389729 * 2
def baseEnd_389729 : Nat := 29647155851290506251137

theorem tailTrace_389729 : CollatzResearch.WordTrace tailWord_389729 prefixEnd_389729 29647155851290506251137 := by
  unfold tailWord_389729
  simp only [CollatzResearch.WordTrace]
  refine ⟨14214584405085868259164241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9476389603390578839442827 14214584405085868259164241)
  ·
    refine ⟨10660938303814401194373181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14214584405085868259164241 10660938303814401194373181)
    ·
      refine ⟨3997851863930400447889943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10660938303814401194373181 3997851863930400447889943)
      ·
        refine ⟨5996777795895600671834915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3997851863930400447889943 5996777795895600671834915)
        ·
          refine ⟨8995166693843401007752373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5996777795895600671834915 8995166693843401007752373)
          ·
            refine ⟨843296877547818844476785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8995166693843401007752373 843296877547818844476785)
            ·
              refine ⟨632472658160864133357589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 843296877547818844476785 632472658160864133357589)
              ·
                refine ⟨29647155851290506251137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 632472658160864133357589 29647155851290506251137)
                ·
                  rfl

theorem cell21_389729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 2, 6].length) (baseStart_389729 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_389729 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_389729 prefixEnd_389729 := by exact prefixLift 389729
  have htrace : WordTrace (prefixWord ++ tailWord_389729) baseStart_389729 baseEnd_389729 := by
    simpa [prefixWord, tailWord_389729, baseEnd_389729] using wordTrace_append hprefix tailTrace_389729
  have hstable : (prefixWord ++ tailWord_389729).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389729).length < 2 ^ (prefixWord ++ tailWord_389729).sum := by decide
  have hdescent : baseEnd_389729 < baseStart_389729 := by decide
  rcases family_descends (prefixWord ++ tailWord_389729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389743 : List Nat := [1, 1, 2, 1, 3, 2, 2, 4, 5]
def baseStart_389743 : Nat := 118140960795 + 389743 * 2 ^ 59
def prefixEnd_389743 : Nat := 4983230072969 + 3 ^ 40 * 389743 * 2
def baseEnd_389743 : Nat := 88944662544610605520049

theorem tailTrace_389743 : CollatzResearch.WordTrace tailWord_389743 prefixEnd_389743 88944662544610605520049 := by
  unfold tailWord_389743
  simp only [CollatzResearch.WordTrace]
  refine ⟨14215095027035148650173883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9476730018023432433449255 14215095027035148650173883)
  ·
    refine ⟨21322642540552722975260825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14215095027035148650173883 21322642540552722975260825)
    ·
      refine ⟨15991981905414542231445619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21322642540552722975260825 15991981905414542231445619)
      ·
        refine ⟨23987972858121813347168429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15991981905414542231445619 23987972858121813347168429)
        ·
          refine ⟨8995489821795680005188161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 23987972858121813347168429 8995489821795680005188161)
          ·
            refine ⟨6746617366346760003891121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8995489821795680005188161 6746617366346760003891121)
            ·
              refine ⟨5059963024760070002918341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6746617366346760003891121 5059963024760070002918341)
              ·
                refine ⟨948743067142513125547189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5059963024760070002918341 948743067142513125547189)
                ·
                  refine ⟨88944662544610605520049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 948743067142513125547189 88944662544610605520049)
                  ·
                    rfl

theorem cell21_389743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 5].length) (baseStart_389743 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_389743 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_389743 prefixEnd_389743 := by exact prefixLift 389743
  have htrace : WordTrace (prefixWord ++ tailWord_389743) baseStart_389743 baseEnd_389743 := by
    simpa [prefixWord, tailWord_389743, baseEnd_389743] using wordTrace_append hprefix tailTrace_389743
  have hstable : (prefixWord ++ tailWord_389743).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389743).length < 2 ^ (prefixWord ++ tailWord_389743).sum := by decide
  have hdescent : baseEnd_389743 < baseStart_389743 := by decide
  rcases family_descends (prefixWord ++ tailWord_389743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389836 : List Nat := [2, 2, 1, 5, 1, 1, 1, 3, 5]
def baseStart_389836 : Nat := 118140960795 + 389836 * 2 ^ 59
def prefixEnd_389836 : Nat := 4983230072969 + 3 ^ 40 * 389836 * 2
def baseEnd_389836 : Nat := 88965886411663110469859

theorem tailTrace_389836 : CollatzResearch.WordTrace tailWord_389836 prefixEnd_389836 88965886411663110469859 := by
  unfold tailWord_389836
  simp only [CollatzResearch.WordTrace]
  refine ⟨7109243507849112766654681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9478991343798817022206241 7109243507849112766654681)
  ·
    refine ⟨5331932630886834574991011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7109243507849112766654681 5331932630886834574991011)
    ·
      refine ⟨7997898946330251862486517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5331932630886834574991011 7997898946330251862486517)
      ·
        refine ⟨749803026218461112108111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7997898946330251862486517 749803026218461112108111)
        ·
          refine ⟨1124704539327691668162167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 749803026218461112108111 1124704539327691668162167)
          ·
            refine ⟨1687056808991537502243251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1124704539327691668162167 1687056808991537502243251)
            ·
              refine ⟨2530585213487306253364877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1687056808991537502243251 2530585213487306253364877)
              ·
                refine ⟨948969455057739845011829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2530585213487306253364877 948969455057739845011829)
                ·
                  refine ⟨88965886411663110469859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 948969455057739845011829 88965886411663110469859)
                  ·
                    rfl

theorem cell21_389836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_389836 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_389836 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_389836 prefixEnd_389836 := by exact prefixLift 389836
  have htrace : WordTrace (prefixWord ++ tailWord_389836) baseStart_389836 baseEnd_389836 := by
    simpa [prefixWord, tailWord_389836, baseEnd_389836] using wordTrace_append hprefix tailTrace_389836
  have hstable : (prefixWord ++ tailWord_389836).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389836).length < 2 ^ (prefixWord ++ tailWord_389836).sum := by decide
  have hdescent : baseEnd_389836 < baseStart_389836 := by decide
  rcases family_descends (prefixWord ++ tailWord_389836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_389870 : List Nat := [4, 1, 2, 1, 1, 5, 1, 3, 3]
def baseStart_389870 : Nat := 118140960795 + 389870 * 2 ^ 59
def prefixEnd_389870 : Nat := 4983230072969 + 3 ^ 40 * 389870 * 2
def baseEnd_389870 : Nat := 88973645674886606903123

theorem tailTrace_389870 : CollatzResearch.WordTrace tailWord_389870 prefixEnd_389870 88973645674886606903123 := by
  unfold tailWord_389870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1777465887196881167505883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9479818065050032893364709 1777465887196881167505883)
  ·
    refine ⟨2666198830795321751258825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1777465887196881167505883 2666198830795321751258825)
    ·
      refine ⟨1999649123096491313444119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2666198830795321751258825 1999649123096491313444119)
      ·
        refine ⟨2999473684644736970166179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1999649123096491313444119 2999473684644736970166179)
        ·
          refine ⟨4499210526967105455249269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2999473684644736970166179 4499210526967105455249269)
          ·
            refine ⟨421800986903166136429619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4499210526967105455249269 421800986903166136429619)
            ·
              refine ⟨632701480354749204644429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 421800986903166136429619 632701480354749204644429)
              ·
                refine ⟨237263055133030951741661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 632701480354749204644429 237263055133030951741661)
                ·
                  refine ⟨88973645674886606903123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 237263055133030951741661 88973645674886606903123)
                  ·
                    rfl

theorem cell21_389870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_389870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_389870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_389870 prefixEnd_389870 := by exact prefixLift 389870
  have htrace : WordTrace (prefixWord ++ tailWord_389870) baseStart_389870 baseEnd_389870 := by
    simpa [prefixWord, tailWord_389870, baseEnd_389870] using wordTrace_append hprefix tailTrace_389870
  have hstable : (prefixWord ++ tailWord_389870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_389870).length < 2 ^ (prefixWord ++ tailWord_389870).sum := by decide
  have hdescent : baseEnd_389870 < baseStart_389870 := by decide
  rcases family_descends (prefixWord ++ tailWord_389870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390005 : List Nat := [1, 3, 4, 1, 1, 2, 2, 4, 3]
def baseStart_390005 : Nat := 118140960795 + 390005 * 2 ^ 59
def prefixEnd_390005 : Nat := 4983230072969 + 3 ^ 40 * 390005 * 2
def baseEnd_390005 : Nat := 89004454514156372152847

theorem tailTrace_390005 : CollatzResearch.WordTrace tailWord_390005 prefixEnd_390005 89004454514156372152847 := by
  unfold tailWord_390005
  simp only [CollatzResearch.WordTrace]
  refine ⟨14224650952085967396211469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9483100634723978264140979 14224650952085967396211469)
  ·
    refine ⟨5334244107032237773579301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14224650952085967396211469 5334244107032237773579301)
    ·
      refine ⟨1000170770068544582546119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5334244107032237773579301 1000170770068544582546119)
      ·
        refine ⟨1500256155102816873819179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1000170770068544582546119 1500256155102816873819179)
        ·
          refine ⟨2250384232654225310728769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1500256155102816873819179 2250384232654225310728769)
          ·
            refine ⟨1687788174490668983046577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2250384232654225310728769 1687788174490668983046577)
            ·
              refine ⟨1265841130868001737284933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1687788174490668983046577 1265841130868001737284933)
              ·
                refine ⟨237345212037750325740925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1265841130868001737284933 237345212037750325740925)
                ·
                  refine ⟨89004454514156372152847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 237345212037750325740925 89004454514156372152847)
                  ·
                    rfl

theorem cell21_390005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 4, 3].length) (baseStart_390005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_390005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_390005 prefixEnd_390005 := by exact prefixLift 390005
  have htrace : WordTrace (prefixWord ++ tailWord_390005) baseStart_390005 baseEnd_390005 := by
    simpa [prefixWord, tailWord_390005, baseEnd_390005] using wordTrace_append hprefix tailTrace_390005
  have hstable : (prefixWord ++ tailWord_390005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390005).length < 2 ^ (prefixWord ++ tailWord_390005).sum := by decide
  have hdescent : baseEnd_390005 < baseStart_390005 := by decide
  rcases family_descends (prefixWord ++ tailWord_390005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390019 : List Nat := [1, 1, 1, 3, 4, 1, 5, 1, 4]
def baseStart_390019 : Nat := 118140960795 + 390019 * 2 ^ 59
def prefixEnd_390019 : Nat := 4983230072969 + 3 ^ 40 * 390019 * 2
def baseEnd_390019 : Nat := 89007649504895458919485

theorem tailTrace_390019 : CollatzResearch.WordTrace tailWord_390019 prefixEnd_390019 89007649504895458919485 := by
  unfold tailWord_390019
  simp only [CollatzResearch.WordTrace]
  refine ⟨14225161574035247787221111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9483441049356831858147407 14225161574035247787221111)
  ·
    refine ⟨21337742361052871680831667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14225161574035247787221111 21337742361052871680831667)
    ·
      refine ⟨32006613541579307521247501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21337742361052871680831667 32006613541579307521247501)
      ·
        refine ⟨12002480078092240320467813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32006613541579307521247501 12002480078092240320467813)
        ·
          refine ⟨2250465014642295060087715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12002480078092240320467813 2250465014642295060087715)
          ·
            refine ⟨3375697521963442590131573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2250465014642295060087715 3375697521963442590131573)
            ·
              refine ⟨316471642684072742824835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3375697521963442590131573 316471642684072742824835)
              ·
                refine ⟨474707464026109114237253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316471642684072742824835 474707464026109114237253)
                ·
                  refine ⟨89007649504895458919485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 474707464026109114237253 89007649504895458919485)
                  ·
                    rfl

theorem cell21_390019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 4].length) (baseStart_390019 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_390019 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_390019 prefixEnd_390019 := by exact prefixLift 390019
  have htrace : WordTrace (prefixWord ++ tailWord_390019) baseStart_390019 baseEnd_390019 := by
    simpa [prefixWord, tailWord_390019, baseEnd_390019] using wordTrace_append hprefix tailTrace_390019
  have hstable : (prefixWord ++ tailWord_390019).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390019).length < 2 ^ (prefixWord ++ tailWord_390019).sum := by decide
  have hdescent : baseEnd_390019 < baseStart_390019 := by decide
  rcases family_descends (prefixWord ++ tailWord_390019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390070 : List Nat := [5, 1, 4, 1, 1, 1, 1, 3, 4]
def baseStart_390070 : Nat := 118140960795 + 390070 * 2 ^ 59
def prefixEnd_390070 : Nat := 4983230072969 + 3 ^ 40 * 390070 * 2
def baseEnd_390070 : Nat := 89019288399730703569381

theorem tailTrace_390070 : CollatzResearch.WordTrace tailWord_390070 prefixEnd_390070 89019288399730703569381 := by
  unfold tailWord_390070
  simp only [CollatzResearch.WordTrace]
  refine ⟨889188856053155218582979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9484681131233655664885109 889188856053155218582979)
  ·
    refine ⟨1333783284079732827874469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 889188856053155218582979 1333783284079732827874469)
    ·
      refine ⟨250084365764949905226463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1333783284079732827874469 250084365764949905226463)
      ·
        refine ⟨375126548647424857839695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250084365764949905226463 375126548647424857839695)
        ·
          refine ⟨562689822971137286759543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375126548647424857839695 562689822971137286759543)
          ·
            refine ⟨844034734456705930139315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 562689822971137286759543 844034734456705930139315)
            ·
              refine ⟨1266052101685058895208973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 844034734456705930139315 1266052101685058895208973)
              ·
                refine ⟨474769538131897085703365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1266052101685058895208973 474769538131897085703365)
                ·
                  refine ⟨89019288399730703569381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 474769538131897085703365 89019288399730703569381)
                  ·
                    rfl

theorem cell21_390070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_390070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_390070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_390070 prefixEnd_390070 := by exact prefixLift 390070
  have htrace : WordTrace (prefixWord ++ tailWord_390070) baseStart_390070 baseEnd_390070 := by
    simpa [prefixWord, tailWord_390070, baseEnd_390070] using wordTrace_append hprefix tailTrace_390070
  have hstable : (prefixWord ++ tailWord_390070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390070).length < 2 ^ (prefixWord ++ tailWord_390070).sum := by decide
  have hdescent : baseEnd_390070 < baseStart_390070 := by decide
  rcases family_descends (prefixWord ++ tailWord_390070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390092 : List Nat := [2, 2, 1, 4, 1, 1, 1, 9]
def baseStart_390092 : Nat := 118140960795 + 390092 * 2 ^ 59
def prefixEnd_390092 : Nat := 4983230072969 + 3 ^ 40 * 390092 * 2
def baseEnd_390092 : Nat := 29674769699821184734223

theorem tailTrace_390092 : CollatzResearch.WordTrace tailWord_390092 prefixEnd_390092 29674769699821184734223 := by
  unfold tailWord_390092
  simp only [CollatzResearch.WordTrace]
  refine ⟨7113912051385390627314265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9485216068513854169752353 7113912051385390627314265)
  ·
    refine ⟨5335434038539042970485699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7113912051385390627314265 5335434038539042970485699)
    ·
      refine ⟨8003151057808564455728549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5335434038539042970485699 8003151057808564455728549)
      ·
        refine ⟨1500590823339105835449103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8003151057808564455728549 1500590823339105835449103)
        ·
          refine ⟨2250886235008658753173655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1500590823339105835449103 2250886235008658753173655)
          ·
            refine ⟨3376329352512988129760483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2250886235008658753173655 3376329352512988129760483)
            ·
              refine ⟨5064494028769482194640725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3376329352512988129760483 5064494028769482194640725)
              ·
                refine ⟨29674769699821184734223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5064494028769482194640725 29674769699821184734223)
                ·
                  rfl

theorem cell21_390092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 9].length) (baseStart_390092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_390092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_390092 prefixEnd_390092 := by exact prefixLift 390092
  have htrace : WordTrace (prefixWord ++ tailWord_390092) baseStart_390092 baseEnd_390092 := by
    simpa [prefixWord, tailWord_390092, baseEnd_390092] using wordTrace_append hprefix tailTrace_390092
  have hstable : (prefixWord ++ tailWord_390092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390092).length < 2 ^ (prefixWord ++ tailWord_390092).sum := by decide
  have hdescent : baseEnd_390092 < baseStart_390092 := by decide
  rcases family_descends (prefixWord ++ tailWord_390092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390126 : List Nat := [4, 1, 2, 1, 4, 2, 1, 6]
def baseStart_390126 : Nat := 118140960795 + 390126 * 2 ^ 59
def prefixEnd_390126 : Nat := 4983230072969 + 3 ^ 40 * 390126 * 2
def baseEnd_390126 : Nat := 29677356120895683545311

theorem tailTrace_390126 : CollatzResearch.WordTrace tailWord_390126 prefixEnd_390126 29677356120895683545311 := by
  unfold tailWord_390126
  simp only [CollatzResearch.WordTrace]
  refine ⟨1778633023080950632670779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9486042789765070040910821 1778633023080950632670779)
  ·
    refine ⟨2667949534621425949006169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1778633023080950632670779 2667949534621425949006169)
    ·
      refine ⟨2000962150966069461754627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2667949534621425949006169 2000962150966069461754627)
      ·
        refine ⟨3001443226449104192631941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2000962150966069461754627 3001443226449104192631941)
        ·
          refine ⟨562770604959207036118489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3001443226449104192631941 562770604959207036118489)
          ·
            refine ⟨422077953719405277088867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 562770604959207036118489 422077953719405277088867)
            ·
              refine ⟨633116930579107915633301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422077953719405277088867 633116930579107915633301)
              ·
                refine ⟨29677356120895683545311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 633116930579107915633301 29677356120895683545311)
                ·
                  rfl

theorem cell21_390126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 2, 1, 6].length) (baseStart_390126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_390126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_390126 prefixEnd_390126 := by exact prefixLift 390126
  have htrace : WordTrace (prefixWord ++ tailWord_390126) baseStart_390126 baseEnd_390126 := by
    simpa [prefixWord, tailWord_390126, baseEnd_390126] using wordTrace_append hprefix tailTrace_390126
  have hstable : (prefixWord ++ tailWord_390126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390126).length < 2 ^ (prefixWord ++ tailWord_390126).sum := by decide
  have hdescent : baseEnd_390126 < baseStart_390126 := by decide
  rcases family_descends (prefixWord ++ tailWord_390126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390168 : List Nat := [2, 1, 2, 3, 2, 3, 8]
def baseStart_390168 : Nat := 118140960795 + 390168 * 2 ^ 59
def prefixEnd_390168 : Nat := 4983230072969 + 3 ^ 40 * 390168 * 2
def baseEnd_390168 : Nat := 9893517037211590103983

theorem tailTrace_390168 : CollatzResearch.WordTrace tailWord_390168 prefixEnd_390168 9893517037211590103983 := by
  unfold tailWord_390168
  simp only [CollatzResearch.WordTrace]
  refine ⟨7115298025247723117197579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9487064033663630822930105 7115298025247723117197579)
  ·
    refine ⟨10672947037871584675796369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7115298025247723117197579 10672947037871584675796369)
    ·
      refine ⟨8004710278403688506847277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10672947037871584675796369 8004710278403688506847277)
      ·
        refine ⟨3001766354401383190067729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8004710278403688506847277 3001766354401383190067729)
        ·
          refine ⟨2251324765801037392550797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3001766354401383190067729 2251324765801037392550797)
          ·
            refine ⟨844246787175389022206549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2251324765801037392550797 844246787175389022206549)
            ·
              refine ⟨9893517037211590103983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 844246787175389022206549 9893517037211590103983)
              ·
                rfl

theorem cell21_390168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 3, 8].length) (baseStart_390168 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_390168 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_390168 prefixEnd_390168 := by exact prefixLift 390168
  have htrace : WordTrace (prefixWord ++ tailWord_390168) baseStart_390168 baseEnd_390168 := by
    simpa [prefixWord, tailWord_390168, baseEnd_390168] using wordTrace_append hprefix tailTrace_390168
  have hstable : (prefixWord ++ tailWord_390168).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390168).length < 2 ^ (prefixWord ++ tailWord_390168).sum := by decide
  have hdescent : baseEnd_390168 < baseStart_390168 := by decide
  rcases family_descends (prefixWord ++ tailWord_390168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390213 : List Nat := [1, 3, 1, 1, 1, 3, 3, 2, 6]
def baseStart_390213 : Nat := 118140960795 + 390213 * 2 ^ 59
def prefixEnd_390213 : Nat := 4983230072969 + 3 ^ 40 * 390213 * 2
def baseEnd_390213 : Nat := 89051922947994232685755

theorem tailTrace_390213 : CollatzResearch.WordTrace tailWord_390213 prefixEnd_390213 89051922947994232685755 := by
  unfold tailWord_390213
  simp only [CollatzResearch.WordTrace]
  refine ⟨14232237335332418919783293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9488158223554945946522195 14232237335332418919783293)
  ·
    refine ⟨5337089000749657094918735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14232237335332418919783293 5337089000749657094918735)
    ·
      refine ⟨8005633501124485642378103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5337089000749657094918735 8005633501124485642378103)
      ·
        refine ⟨12008450251686728463567155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8005633501124485642378103 12008450251686728463567155)
        ·
          refine ⟨18012675377530092695350733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12008450251686728463567155 18012675377530092695350733)
          ·
            refine ⟨6754753266573784760756525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18012675377530092695350733 6754753266573784760756525)
            ·
              refine ⟨2533032474965169285283697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6754753266573784760756525 2533032474965169285283697)
              ·
                refine ⟨1899774356223876963962773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2533032474965169285283697 1899774356223876963962773)
                ·
                  refine ⟨89051922947994232685755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1899774356223876963962773 89051922947994232685755)
                  ·
                    rfl

theorem cell21_390213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 2, 6].length) (baseStart_390213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_390213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_390213 prefixEnd_390213 := by exact prefixLift 390213
  have htrace : WordTrace (prefixWord ++ tailWord_390213) baseStart_390213 baseEnd_390213 := by
    simpa [prefixWord, tailWord_390213, baseEnd_390213] using wordTrace_append hprefix tailTrace_390213
  have hstable : (prefixWord ++ tailWord_390213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390213).length < 2 ^ (prefixWord ++ tailWord_390213).sum := by decide
  have hdescent : baseEnd_390213 < baseStart_390213 := by decide
  rcases family_descends (prefixWord ++ tailWord_390213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390247 : List Nat := [1, 1, 5, 1, 1, 3, 4, 1, 4]
def baseStart_390247 : Nat := 118140960795 + 390247 * 2 ^ 59
def prefixEnd_390247 : Nat := 4983230072969 + 3 ^ 40 * 390247 * 2
def baseEnd_390247 : Nat := 89059682211217729119019

theorem tailTrace_390247 : CollatzResearch.WordTrace tailWord_390247 prefixEnd_390247 89059682211217729119019 := by
  unfold tailWord_390247
  simp only [CollatzResearch.WordTrace]
  refine ⟨14233477417209242726520995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9488984944806161817680663 14233477417209242726520995)
  ·
    refine ⟨21350216125813864089781493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14233477417209242726520995 21350216125813864089781493)
    ·
      refine ⟨2001582761795049758417015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21350216125813864089781493 2001582761795049758417015)
      ·
        refine ⟨3002374142692574637625523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2001582761795049758417015 3002374142692574637625523)
        ·
          refine ⟨4503561214038861956438285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3002374142692574637625523 4503561214038861956438285)
          ·
            refine ⟨1688835455264573233664357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4503561214038861956438285 1688835455264573233664357)
            ·
              refine ⟨316656647862107481312067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1688835455264573233664357 316656647862107481312067)
              ·
                refine ⟨474984971793161221968101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316656647862107481312067 474984971793161221968101)
                ·
                  refine ⟨89059682211217729119019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 474984971793161221968101 89059682211217729119019)
                  ·
                    rfl

theorem cell21_390247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 4, 1, 4].length) (baseStart_390247 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_390247 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_390247 prefixEnd_390247 := by exact prefixLift 390247
  have htrace : WordTrace (prefixWord ++ tailWord_390247) baseStart_390247 baseEnd_390247 := by
    simpa [prefixWord, tailWord_390247, baseEnd_390247] using wordTrace_append hprefix tailTrace_390247
  have hstable : (prefixWord ++ tailWord_390247).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390247).length < 2 ^ (prefixWord ++ tailWord_390247).sum := by decide
  have hdescent : baseEnd_390247 < baseStart_390247 := by decide
  rcases family_descends (prefixWord ++ tailWord_390247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390337 : List Nat := [1, 2, 6, 1, 1, 2, 8]
def baseStart_390337 : Nat := 118140960795 + 390337 * 2 ^ 59
def prefixEnd_390337 : Nat := 4983230072969 + 3 ^ 40 * 390337 * 2
def baseEnd_390337 : Nat := 9897802381933063624315

theorem tailTrace_390337 : CollatzResearch.WordTrace tailWord_390337 prefixEnd_390337 9897802381933063624315 := by
  unfold tailWord_390337
  simp only [CollatzResearch.WordTrace]
  refine ⟨14236759986883188097297265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9491173324588792064864843 14236759986883188097297265)
  ·
    refine ⟨10677569990162391072972949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14236759986883188097297265 10677569990162391072972949)
    ·
      refine ⟨500511093288862081545607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10677569990162391072972949 500511093288862081545607)
      ·
        refine ⟨750766639933293122318411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 500511093288862081545607 750766639933293122318411)
        ·
          refine ⟨1126149959899939683477617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750766639933293122318411 1126149959899939683477617)
          ·
            refine ⟨844612469924954762608213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1126149959899939683477617 844612469924954762608213)
            ·
              refine ⟨9897802381933063624315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 844612469924954762608213 9897802381933063624315)
              ·
                rfl

theorem cell21_390337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 8].length) (baseStart_390337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_390337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_390337 prefixEnd_390337 := by exact prefixLift 390337
  have htrace : WordTrace (prefixWord ++ tailWord_390337) baseStart_390337 baseEnd_390337 := by
    simpa [prefixWord, tailWord_390337, baseEnd_390337] using wordTrace_append hprefix tailTrace_390337
  have hstable : (prefixWord ++ tailWord_390337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390337).length < 2 ^ (prefixWord ++ tailWord_390337).sum := by decide
  have hdescent : baseEnd_390337 < baseStart_390337 := by decide
  rcases family_descends (prefixWord ++ tailWord_390337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390340 : List Nat := [2, 3, 3, 1, 3, 2, 1, 2, 4]
def baseStart_390340 : Nat := 118140960795 + 390340 * 2 ^ 59
def prefixEnd_390340 : Nat := 4983230072969 + 3 ^ 40 * 390340 * 2
def baseEnd_390340 : Nat := 89080906078270234068829

theorem tailTrace_390340 : CollatzResearch.WordTrace tailWord_390340 prefixEnd_390340 89080906078270234068829 := by
  unfold tailWord_390340
  simp only [CollatzResearch.WordTrace]
  refine ⟨7118434702936159804828237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9491246270581546406437649 7118434702936159804828237)
  ·
    refine ⟨2669413013601059926810589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7118434702936159804828237 2669413013601059926810589)
    ·
      refine ⟨1001029880100397472553971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2669413013601059926810589 1001029880100397472553971)
      ·
        refine ⟨1501544820150596208830957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1001029880100397472553971 1501544820150596208830957)
        ·
          refine ⟨563079307556473578311609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1501544820150596208830957 563079307556473578311609)
          ·
            refine ⟨422309480667355183733707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 563079307556473578311609 422309480667355183733707)
            ·
              refine ⟨633464221001032775600561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422309480667355183733707 633464221001032775600561)
              ·
                refine ⟨475098165750774581700421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 633464221001032775600561 475098165750774581700421)
                ·
                  refine ⟨89080906078270234068829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 475098165750774581700421 89080906078270234068829)
                  ·
                    rfl

theorem cell21_390340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 4].length) (baseStart_390340 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_390340 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_390340 prefixEnd_390340 := by exact prefixLift 390340
  have htrace : WordTrace (prefixWord ++ tailWord_390340) baseStart_390340 baseEnd_390340 := by
    simpa [prefixWord, tailWord_390340, baseEnd_390340] using wordTrace_append hprefix tailTrace_390340
  have hstable : (prefixWord ++ tailWord_390340).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390340).length < 2 ^ (prefixWord ++ tailWord_390340).sum := by decide
  have hdescent : baseEnd_390340 < baseStart_390340 := by decide
  rcases family_descends (prefixWord ++ tailWord_390340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390388 : List Nat := [2, 6, 1, 2, 2, 1, 7]
def baseStart_390388 : Nat := 118140960795 + 390388 * 2 ^ 59
def prefixEnd_390388 : Nat := 4983230072969 + 3 ^ 40 * 390388 * 2
def baseEnd_390388 : Nat := 9899095592470313029859

theorem tailTrace_390388 : CollatzResearch.WordTrace tailWord_390388 prefixEnd_390388 9899095592470313029859 := by
  unfold tailWord_390388
  simp only [CollatzResearch.WordTrace]
  refine ⟨7119310054849211903701909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9492413406465615871602545 7119310054849211903701909)
  ·
    refine ⟨333717658821056807986027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7119310054849211903701909 333717658821056807986027)
    ·
      refine ⟨500576488231585211979041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 333717658821056807986027 500576488231585211979041)
      ·
        refine ⟨375432366173688908984281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 500576488231585211979041 375432366173688908984281)
        ·
          refine ⟨281574274630266681738211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375432366173688908984281 281574274630266681738211)
          ·
            refine ⟨422361411945400022607317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281574274630266681738211 422361411945400022607317)
            ·
              refine ⟨9899095592470313029859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 422361411945400022607317 9899095592470313029859)
              ·
                rfl

theorem cell21_390388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 2, 1, 7].length) (baseStart_390388 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_390388 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_390388 prefixEnd_390388 := by exact prefixLift 390388
  have htrace : WordTrace (prefixWord ++ tailWord_390388) baseStart_390388 baseEnd_390388 := by
    simpa [prefixWord, tailWord_390388, baseEnd_390388] using wordTrace_append hprefix tailTrace_390388
  have hstable : (prefixWord ++ tailWord_390388).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390388).length < 2 ^ (prefixWord ++ tailWord_390388).sum := by decide
  have hdescent : baseEnd_390388 < baseStart_390388 := by decide
  rcases family_descends (prefixWord ++ tailWord_390388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390402 : List Nat := [3, 4, 1, 1, 4, 1, 1, 1, 5]
def baseStart_390402 : Nat := 118140960795 + 390402 * 2 ^ 59
def prefixEnd_390402 : Nat := 4983230072969 + 3 ^ 40 * 390402 * 2
def baseEnd_390402 : Nat := 89095055322971904035369

theorem tailTrace_390402 : CollatzResearch.WordTrace tailWord_390402 prefixEnd_390402 89095055322971904035369 := by
  unfold tailWord_390402
  simp only [CollatzResearch.WordTrace]
  refine ⟨3559782682911926049603365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9492753821098469465608973 3559782682911926049603365)
  ·
    refine ⟨667459253045986134300631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3559782682911926049603365 667459253045986134300631)
    ·
      refine ⟨1001188879568979201450947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 667459253045986134300631 1001188879568979201450947)
      ·
        refine ⟨1501783319353468802176421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1001188879568979201450947 1501783319353468802176421)
        ·
          refine ⟨281584372378775400408079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1501783319353468802176421 281584372378775400408079)
          ·
            refine ⟨422376558568163100612119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281584372378775400408079 422376558568163100612119)
            ·
              refine ⟨633564837852244650918179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422376558568163100612119 633564837852244650918179)
              ·
                refine ⟨950347256778366976377269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 633564837852244650918179 950347256778366976377269)
                ·
                  refine ⟨89095055322971904035369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 950347256778366976377269 89095055322971904035369)
                  ·
                    rfl

theorem cell21_390402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 5].length) (baseStart_390402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_390402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_390402 prefixEnd_390402 := by exact prefixLift 390402
  have htrace : WordTrace (prefixWord ++ tailWord_390402) baseStart_390402 baseEnd_390402 := by
    simpa [prefixWord, tailWord_390402, baseEnd_390402] using wordTrace_append hprefix tailTrace_390402
  have hstable : (prefixWord ++ tailWord_390402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390402).length < 2 ^ (prefixWord ++ tailWord_390402).sum := by decide
  have hdescent : baseEnd_390402 < baseStart_390402 := by decide
  rcases family_descends (prefixWord ++ tailWord_390402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390458 : List Nat := [3, 1, 1, 1, 4, 1, 4, 2, 4]
def baseStart_390458 : Nat := 118140960795 + 390458 * 2 ^ 59
def prefixEnd_390458 : Nat := 4983230072969 + 3 ^ 40 * 390458 * 2
def baseEnd_390458 : Nat := 89107835285928251101921

theorem tailTrace_390458 : CollatzResearch.WordTrace tailWord_390458 prefixEnd_390458 89107835285928251101921 := by
  unfold tailWord_390458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3560293304861206440613007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9494115479629883841634685 3560293304861206440613007)
  ·
    refine ⟨5340439957291809660919511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3560293304861206440613007 5340439957291809660919511)
    ·
      refine ⟨8010659935937714491379267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5340439957291809660919511 8010659935937714491379267)
      ·
        refine ⟨12015989903906571737068901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8010659935937714491379267 12015989903906571737068901)
        ·
          refine ⟨2252998106982482200700419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12015989903906571737068901 2252998106982482200700419)
          ·
            refine ⟨3379497160473723301050629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2252998106982482200700419 3379497160473723301050629)
            ·
              refine ⟨633655717588823118946993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3379497160473723301050629 633655717588823118946993)
              ·
                refine ⟨475241788191617339210245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 633655717588823118946993 475241788191617339210245)
                ·
                  refine ⟨89107835285928251101921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 475241788191617339210245 89107835285928251101921)
                  ·
                    rfl

theorem cell21_390458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 4].length) (baseStart_390458 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_390458 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_390458 prefixEnd_390458 := by exact prefixLift 390458
  have htrace : WordTrace (prefixWord ++ tailWord_390458) baseStart_390458 baseEnd_390458 := by
    simpa [prefixWord, tailWord_390458, baseEnd_390458] using wordTrace_append hprefix tailTrace_390458
  have hstable : (prefixWord ++ tailWord_390458).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390458).length < 2 ^ (prefixWord ++ tailWord_390458).sum := by decide
  have hdescent : baseEnd_390458 < baseStart_390458 := by decide
  rcases family_descends (prefixWord ++ tailWord_390458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390579 : List Nat := [1, 1, 1, 2, 3, 1, 1, 8, 3]
def baseStart_390579 : Nat := 118140960795 + 390579 * 2 ^ 59
def prefixEnd_390579 : Nat := 4983230072969 + 3 ^ 40 * 390579 * 2
def baseEnd_390579 : Nat := 89135449134458929585007

theorem tailTrace_390579 : CollatzResearch.WordTrace tailWord_390579 prefixEnd_390579 89135449134458929585007 := by
  unfold tailWord_390579
  simp only [CollatzResearch.WordTrace]
  refine ⟨14245586452006463427606791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9497057634670975618404527 14245586452006463427606791)
  ·
    refine ⟨21368379678009695141410187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14245586452006463427606791 21368379678009695141410187)
    ·
      refine ⟨32052569517014542712115281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21368379678009695141410187 32052569517014542712115281)
      ·
        refine ⟨24039427137760907034086461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32052569517014542712115281 24039427137760907034086461)
        ·
          refine ⟨9014785176660340137782423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24039427137760907034086461 9014785176660340137782423)
          ·
            refine ⟨13522177764990510206673635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9014785176660340137782423 13522177764990510206673635)
            ·
              refine ⟨20283266647485765310010453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13522177764990510206673635 20283266647485765310010453)
              ·
                refine ⟨237694531025223812226685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 20283266647485765310010453 237694531025223812226685)
                ·
                  refine ⟨89135449134458929585007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 237694531025223812226685 89135449134458929585007)
                  ·
                    rfl

theorem cell21_390579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 8, 3].length) (baseStart_390579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_390579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_390579 prefixEnd_390579 := by exact prefixLift 390579
  have htrace : WordTrace (prefixWord ++ tailWord_390579) baseStart_390579 baseEnd_390579 := by
    simpa [prefixWord, tailWord_390579, baseEnd_390579] using wordTrace_append hprefix tailTrace_390579
  have hstable : (prefixWord ++ tailWord_390579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390579).length < 2 ^ (prefixWord ++ tailWord_390579).sum := by decide
  have hdescent : baseEnd_390579 < baseStart_390579 := by decide
  rcases family_descends (prefixWord ++ tailWord_390579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390607 : List Nat := [1, 1, 2, 1, 1, 4, 4, 7]
def baseStart_390607 : Nat := 118140960795 + 390607 * 2 ^ 59
def prefixEnd_390607 : Nat := 4983230072969 + 3 ^ 40 * 390607 * 2
def baseEnd_390607 : Nat := 29713946371979034372761

theorem tailTrace_390607 : CollatzResearch.WordTrace tailWord_390607 prefixEnd_390607 29713946371979034372761 := by
  unfold tailWord_390607
  simp only [CollatzResearch.WordTrace]
  refine ⟨14246607695905024209626075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9497738463936682806417383 14246607695905024209626075)
  ·
    refine ⟨21369911543857536314439113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14246607695905024209626075 21369911543857536314439113)
    ·
      refine ⟨16027433657893152235829335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21369911543857536314439113 16027433657893152235829335)
      ·
        refine ⟨24041150486839728353744003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16027433657893152235829335 24041150486839728353744003)
        ·
          refine ⟨36061725730259592530616005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24041150486839728353744003 36061725730259592530616005)
          ·
            refine ⟨6761573574423673599490501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36061725730259592530616005 6761573574423673599490501)
            ·
              refine ⟨1267795045204438799904469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6761573574423673599490501 1267795045204438799904469)
              ·
                refine ⟨29713946371979034372761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1267795045204438799904469 29713946371979034372761)
                ·
                  rfl

theorem cell21_390607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 7].length) (baseStart_390607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_390607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_390607 prefixEnd_390607 := by exact prefixLift 390607
  have htrace : WordTrace (prefixWord ++ tailWord_390607) baseStart_390607 baseEnd_390607 := by
    simpa [prefixWord, tailWord_390607, baseEnd_390607] using wordTrace_append hprefix tailTrace_390607
  have hstable : (prefixWord ++ tailWord_390607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390607).length < 2 ^ (prefixWord ++ tailWord_390607).sum := by decide
  have hdescent : baseEnd_390607 < baseStart_390607 := by decide
  rcases family_descends (prefixWord ++ tailWord_390607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390658 : List Nat := [3, 4, 1, 2, 1, 2, 3, 5]
def baseStart_390658 : Nat := 118140960795 + 390658 * 2 ^ 59
def prefixEnd_390658 : Nat := 4983230072969 + 3 ^ 40 * 390658 * 2
def baseEnd_390658 : Nat := 29717826003590782589393

theorem tailTrace_390658 : CollatzResearch.WordTrace tailWord_390658 prefixEnd_390658 29717826003590782589393 := by
  unfold tailWord_390658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3562116954680064979933157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9498978545813506613155085 3562116954680064979933157)
  ·
    refine ⟨667896929002512183737467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3562116954680064979933157 667896929002512183737467)
    ·
      refine ⟨1001845393503768275606201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 667896929002512183737467 1001845393503768275606201)
      ·
        refine ⟨751384045127826206704651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1001845393503768275606201 751384045127826206704651)
        ·
          refine ⟨1127076067691739310056977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751384045127826206704651 1127076067691739310056977)
          ·
            refine ⟨845307050768804482542733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1127076067691739310056977 845307050768804482542733)
            ·
              refine ⟨316990144038301680953525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 845307050768804482542733 316990144038301680953525)
              ·
                refine ⟨29717826003590782589393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 316990144038301680953525 29717826003590782589393)
                ·
                  rfl

theorem cell21_390658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 3, 5].length) (baseStart_390658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_390658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_390658 prefixEnd_390658 := by exact prefixLift 390658
  have htrace : WordTrace (prefixWord ++ tailWord_390658) baseStart_390658 baseEnd_390658 := by
    simpa [prefixWord, tailWord_390658, baseEnd_390658] using wordTrace_append hprefix tailTrace_390658
  have hstable : (prefixWord ++ tailWord_390658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390658).length < 2 ^ (prefixWord ++ tailWord_390658).sum := by decide
  have hdescent : baseEnd_390658 < baseStart_390658 := by decide
  rcases family_descends (prefixWord ++ tailWord_390658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390714 : List Nat := [3, 1, 1, 1, 3, 2, 1, 4, 5]
def baseStart_390714 : Nat := 118140960795 + 390714 * 2 ^ 59
def prefixEnd_390714 : Nat := 4983230072969 + 3 ^ 40 * 390714 * 2
def baseEnd_390714 : Nat := 89166257973728694834731

theorem tailTrace_390714 : CollatzResearch.WordTrace tailWord_390714 prefixEnd_390714 89166257973728694834731 := by
  unfold tailWord_390714
  simp only [CollatzResearch.WordTrace]
  refine ⟨3562627576629345370942799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9500340204344920989180797 3562627576629345370942799)
  ·
    refine ⟨5343941364944018056414199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3562627576629345370942799 5343941364944018056414199)
    ·
      refine ⟨8015912047416027084621299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5343941364944018056414199 8015912047416027084621299)
      ·
        refine ⟨12023868071124040626931949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8015912047416027084621299 12023868071124040626931949)
        ·
          refine ⟨4508950526671515235099481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12023868071124040626931949 4508950526671515235099481)
          ·
            refine ⟨3381712895003636426324611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4508950526671515235099481 3381712895003636426324611)
            ·
              refine ⟨5072569342505454639486917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3381712895003636426324611 5072569342505454639486917)
              ·
                refine ⟨951106751719772744903797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5072569342505454639486917 951106751719772744903797)
                ·
                  refine ⟨89166257973728694834731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 951106751719772744903797 89166257973728694834731)
                  ·
                    rfl

theorem cell21_390714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 4, 5].length) (baseStart_390714 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_390714 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_390714 prefixEnd_390714 := by exact prefixLift 390714
  have htrace : WordTrace (prefixWord ++ tailWord_390714) baseStart_390714 baseEnd_390714 := by
    simpa [prefixWord, tailWord_390714, baseEnd_390714] using wordTrace_append hprefix tailTrace_390714
  have hstable : (prefixWord ++ tailWord_390714).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390714).length < 2 ^ (prefixWord ++ tailWord_390714).sum := by decide
  have hdescent : baseEnd_390714 < baseStart_390714 := by decide
  rcases family_descends (prefixWord ++ tailWord_390714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390748 : List Nat := [2, 2, 4, 1, 2, 3, 1, 1, 5]
def baseStart_390748 : Nat := 118140960795 + 390748 * 2 ^ 59
def prefixEnd_390748 : Nat := 4983230072969 + 3 ^ 40 * 390748 * 2
def baseEnd_390748 : Nat := 89174017236952191267995

theorem tailTrace_390748 : CollatzResearch.WordTrace tailWord_390748 prefixEnd_390748 89174017236952191267995 := by
  unfold tailWord_390748
  simp only [CollatzResearch.WordTrace]
  refine ⟨7125875194197102645254449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9501166925596136860339265 7125875194197102645254449)
  ·
    refine ⟨5344406395647826983940837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7125875194197102645254449 5344406395647826983940837)
    ·
      refine ⟨1002076199183967559488907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5344406395647826983940837 1002076199183967559488907)
      ·
        refine ⟨1503114298775951339233361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1002076199183967559488907 1503114298775951339233361)
        ·
          refine ⟨1127335724081963504425021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1503114298775951339233361 1127335724081963504425021)
          ·
            refine ⟨422750896530736314159383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1127335724081963504425021 422750896530736314159383)
            ·
              refine ⟨634126344796104471239075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422750896530736314159383 634126344796104471239075)
              ·
                refine ⟨951189517194156706858613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634126344796104471239075 951189517194156706858613)
                ·
                  refine ⟨89174017236952191267995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 951189517194156706858613 89174017236952191267995)
                  ·
                    rfl

theorem cell21_390748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 3, 1, 1, 5].length) (baseStart_390748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_390748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_390748 prefixEnd_390748 := by exact prefixLift 390748
  have htrace : WordTrace (prefixWord ++ tailWord_390748) baseStart_390748 baseEnd_390748 := by
    simpa [prefixWord, tailWord_390748, baseEnd_390748] using wordTrace_append hprefix tailTrace_390748
  have hstable : (prefixWord ++ tailWord_390748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390748).length < 2 ^ (prefixWord ++ tailWord_390748).sum := by decide
  have hdescent : baseEnd_390748 < baseStart_390748 := by decide
  rcases family_descends (prefixWord ++ tailWord_390748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390759 : List Nat := [1, 1, 5, 1, 1, 1, 3, 8]
def baseStart_390759 : Nat := 118140960795 + 390759 * 2 ^ 59
def prefixEnd_390759 : Nat := 4983230072969 + 3 ^ 40 * 390759 * 2
def baseEnd_390759 : Nat := 29725509195606205528213

theorem tailTrace_390759 : CollatzResearch.WordTrace tailWord_390759 prefixEnd_390759 29725509195606205528213 := by
  unfold tailWord_390759
  simp only [CollatzResearch.WordTrace]
  refine ⟨14252151591354354169159331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9501434394236236112772887 14252151591354354169159331)
  ·
    refine ⟨21378227387031531253738997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14252151591354354169159331 21378227387031531253738997)
    ·
      refine ⟨2004208817534206055038031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21378227387031531253738997 2004208817534206055038031)
      ·
        refine ⟨3006313226301309082557047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2004208817534206055038031 3006313226301309082557047)
        ·
          refine ⟨4509469839451963623835571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3006313226301309082557047 4509469839451963623835571)
          ·
            refine ⟨6764204759177945435753357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4509469839451963623835571 6764204759177945435753357)
            ·
              refine ⟨2536576784691729538407509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6764204759177945435753357 2536576784691729538407509)
              ·
                refine ⟨29725509195606205528213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2536576784691729538407509 29725509195606205528213)
                ·
                  rfl

theorem cell21_390759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 3, 8].length) (baseStart_390759 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_390759 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_390759 prefixEnd_390759 := by exact prefixLift 390759
  have htrace : WordTrace (prefixWord ++ tailWord_390759) baseStart_390759 baseEnd_390759 := by
    simpa [prefixWord, tailWord_390759, baseEnd_390759] using wordTrace_append hprefix tailTrace_390759
  have hstable : (prefixWord ++ tailWord_390759).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390759).length < 2 ^ (prefixWord ++ tailWord_390759).sum := by decide
  have hdescent : baseEnd_390759 < baseStart_390759 := by decide
  rcases family_descends (prefixWord ++ tailWord_390759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390762 : List Nat := [3, 1, 3, 2, 1, 3, 1, 3, 4]
def baseStart_390762 : Nat := 118140960795 + 390762 * 2 ^ 59
def prefixEnd_390762 : Nat := 4983230072969 + 3 ^ 40 * 390762 * 2
def baseEnd_390762 : Nat := 89177212227691278034633

theorem tailTrace_390762 : CollatzResearch.WordTrace tailWord_390762 prefixEnd_390762 89177212227691278034633 := by
  unfold tailWord_390762
  simp only [CollatzResearch.WordTrace]
  refine ⟨3563065252585871420379635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9501507340228990454345693 3563065252585871420379635)
  ·
    refine ⟨5344597878878807130569453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3563065252585871420379635 5344597878878807130569453)
    ·
      refine ⟨2004224204579552673963545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5344597878878807130569453 2004224204579552673963545)
      ·
        refine ⟨1503168153434664505472659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2004224204579552673963545 1503168153434664505472659)
        ·
          refine ⟨2254752230151996758208989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503168153434664505472659 2254752230151996758208989)
          ·
            refine ⟨845532086306998784328371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2254752230151996758208989 845532086306998784328371)
            ·
              refine ⟨1268298129460498176492557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 845532086306998784328371 1268298129460498176492557)
              ·
                refine ⟨475611798547686816184709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1268298129460498176492557 475611798547686816184709)
                ·
                  refine ⟨89177212227691278034633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 475611798547686816184709 89177212227691278034633)
                  ·
                    rfl

theorem cell21_390762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 4].length) (baseStart_390762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_390762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_390762 prefixEnd_390762 := by exact prefixLift 390762
  have htrace : WordTrace (prefixWord ++ tailWord_390762) baseStart_390762 baseEnd_390762 := by
    simpa [prefixWord, tailWord_390762, baseEnd_390762] using wordTrace_append hprefix tailTrace_390762
  have hstable : (prefixWord ++ tailWord_390762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390762).length < 2 ^ (prefixWord ++ tailWord_390762).sum := by decide
  have hdescent : baseEnd_390762 < baseStart_390762 := by decide
  rcases family_descends (prefixWord ++ tailWord_390762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390821 : List Nat := [1, 3, 1, 2, 1, 2, 4, 3, 4]
def baseStart_390821 : Nat := 118140960795 + 390821 * 2 ^ 59
def prefixEnd_390821 : Nat := 4983230072969 + 3 ^ 40 * 390821 * 2
def baseEnd_390821 : Nat := 89190676831520286551179

theorem tailTrace_390821 : CollatzResearch.WordTrace tailWord_390821 prefixEnd_390821 89190676831520286551179 := by
  unfold tailWord_390821
  simp only [CollatzResearch.WordTrace]
  refine ⟨14254412917129738757916317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9502941944753159171944211 14254412917129738757916317)
  ·
    refine ⟨5345404843923652034218619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14254412917129738757916317 5345404843923652034218619)
    ·
      refine ⟨8018107265885478051327929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5345404843923652034218619 8018107265885478051327929)
      ·
        refine ⟨6013580449414108538495947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8018107265885478051327929 6013580449414108538495947)
        ·
          refine ⟨9020370674121162807743921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6013580449414108538495947 9020370674121162807743921)
          ·
            refine ⟨6765278005590872105807941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9020370674121162807743921 6765278005590872105807941)
            ·
              refine ⟨1268489626048288519838989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6765278005590872105807941 1268489626048288519838989)
              ·
                refine ⟨475683609768108194939621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1268489626048288519838989 475683609768108194939621)
                ·
                  refine ⟨89190676831520286551179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 475683609768108194939621 89190676831520286551179)
                  ·
                    rfl

theorem cell21_390821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 3, 4].length) (baseStart_390821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_390821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_390821 prefixEnd_390821 := by exact prefixLift 390821
  have htrace : WordTrace (prefixWord ++ tailWord_390821) baseStart_390821 baseEnd_390821 := by
    simpa [prefixWord, tailWord_390821, baseEnd_390821] using wordTrace_append hprefix tailTrace_390821
  have hstable : (prefixWord ++ tailWord_390821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390821).length < 2 ^ (prefixWord ++ tailWord_390821).sum := by decide
  have hdescent : baseEnd_390821 < baseStart_390821 := by decide
  rcases family_descends (prefixWord ++ tailWord_390821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390914 : List Nat := [3, 4, 1, 1, 1, 1, 2, 4, 4]
def baseStart_390914 : Nat := 118140960795 + 390914 * 2 ^ 59
def prefixEnd_390914 : Nat := 4983230072969 + 3 ^ 40 * 390914 * 2
def baseEnd_390914 : Nat := 89211900698572791500989

theorem tailTrace_390914 : CollatzResearch.WordTrace tailWord_390914 prefixEnd_390914 89211900698572791500989 := by
  unfold tailWord_390914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3564451226448203910262949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9505203270528543760701197 3564451226448203910262949)
  ·
    refine ⟨668334604959038233174303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3564451226448203910262949 668334604959038233174303)
    ·
      refine ⟨1002501907438557349761455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 668334604959038233174303 1002501907438557349761455)
      ·
        refine ⟨1503752861157836024642183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1002501907438557349761455 1503752861157836024642183)
        ·
          refine ⟨2255629291736754036963275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503752861157836024642183 2255629291736754036963275)
          ·
            refine ⟨3383443937605131055444913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2255629291736754036963275 3383443937605131055444913)
            ·
              refine ⟨2537582953203848291583685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3383443937605131055444913 2537582953203848291583685)
              ·
                refine ⟨475796803725721554671941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2537582953203848291583685 475796803725721554671941)
                ·
                  refine ⟨89211900698572791500989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 475796803725721554671941 89211900698572791500989)
                  ·
                    rfl

theorem cell21_390914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 4].length) (baseStart_390914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_390914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_390914 prefixEnd_390914 := by exact prefixLift 390914
  have htrace : WordTrace (prefixWord ++ tailWord_390914) baseStart_390914 baseEnd_390914 := by
    simpa [prefixWord, tailWord_390914, baseEnd_390914] using wordTrace_append hprefix tailTrace_390914
  have hstable : (prefixWord ++ tailWord_390914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390914).length < 2 ^ (prefixWord ++ tailWord_390914).sum := by decide
  have hdescent : baseEnd_390914 < baseStart_390914 := by decide
  rcases family_descends (prefixWord ++ tailWord_390914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391063 : List Nat := [1, 1, 3, 3, 1, 4, 1, 7]
def baseStart_391063 : Nat := 118140960795 + 391063 * 2 ^ 59
def prefixEnd_391063 : Nat := 4983230072969 + 3 ^ 40 * 391063 * 2
def baseEnd_391063 : Nat := 29748634842860547839117

theorem tailTrace_391063 : CollatzResearch.WordTrace tailWord_391063 prefixEnd_391063 29748634842860547839117 := by
  unfold tailWord_391063
  simp only [CollatzResearch.WordTrace]
  refine ⟨14263239382253014088225843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9508826254835342725483895 14263239382253014088225843)
  ·
    refine ⟨21394859073379521132338765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14263239382253014088225843 21394859073379521132338765)
    ·
      refine ⟨8023072152517320424627037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21394859073379521132338765 8023072152517320424627037)
      ·
        refine ⟨3008652057193995159235139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8023072152517320424627037 3008652057193995159235139)
        ·
          refine ⟨4512978085790992738852709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3008652057193995159235139 4512978085790992738852709)
          ·
            refine ⟨846183391085811138534883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4512978085790992738852709 846183391085811138534883)
            ·
              refine ⟨1269275086628716707802325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846183391085811138534883 1269275086628716707802325)
              ·
                refine ⟨29748634842860547839117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1269275086628716707802325 29748634842860547839117)
                ·
                  rfl

theorem cell21_391063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 1, 7].length) (baseStart_391063 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_391063 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_391063 prefixEnd_391063 := by exact prefixLift 391063
  have htrace : WordTrace (prefixWord ++ tailWord_391063) baseStart_391063 baseEnd_391063 := by
    simpa [prefixWord, tailWord_391063, baseEnd_391063] using wordTrace_append hprefix tailTrace_391063
  have hstable : (prefixWord ++ tailWord_391063).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391063).length < 2 ^ (prefixWord ++ tailWord_391063).sum := by decide
  have hdescent : baseEnd_391063 < baseStart_391063 := by decide
  rcases family_descends (prefixWord ++ tailWord_391063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391077 : List Nat := [1, 3, 1, 2, 1, 1, 1, 4, 7]
def baseStart_391077 : Nat := 118140960795 + 391077 * 2 ^ 59
def prefixEnd_391077 : Nat := 4983230072969 + 3 ^ 40 * 391077 * 2
def baseEnd_391077 : Nat := 89249099519320730283989

theorem tailTrace_391077 : CollatzResearch.WordTrace tailWord_391077 prefixEnd_391077 89249099519320730283989 := by
  unfold tailWord_391077
  simp only [CollatzResearch.WordTrace]
  refine ⟨14263750004202294479235485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9509166669468196319490323 14263750004202294479235485)
  ·
    refine ⟨5348906251575860429713307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14263750004202294479235485 5348906251575860429713307)
    ·
      refine ⟨8023359377363790644569961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5348906251575860429713307 8023359377363790644569961)
      ·
        refine ⟨6017519533022842983427471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8023359377363790644569961 6017519533022842983427471)
        ·
          refine ⟨9026279299534264475141207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6017519533022842983427471 9026279299534264475141207)
          ·
            refine ⟨13539418949301396712711811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9026279299534264475141207 13539418949301396712711811)
            ·
              refine ⟨20309128423952095069067717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13539418949301396712711811 20309128423952095069067717)
              ·
                refine ⟨3807961579491017825450197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20309128423952095069067717 3807961579491017825450197)
                ·
                  refine ⟨89249099519320730283989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3807961579491017825450197 89249099519320730283989)
                  ·
                    rfl

theorem cell21_391077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 4, 7].length) (baseStart_391077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_391077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_391077 prefixEnd_391077 := by exact prefixLift 391077
  have htrace : WordTrace (prefixWord ++ tailWord_391077) baseStart_391077 baseEnd_391077 := by
    simpa [prefixWord, tailWord_391077, baseEnd_391077] using wordTrace_append hprefix tailTrace_391077
  have hstable : (prefixWord ++ tailWord_391077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391077).length < 2 ^ (prefixWord ++ tailWord_391077).sum := by decide
  have hdescent : baseEnd_391077 < baseStart_391077 := by decide
  rcases family_descends (prefixWord ++ tailWord_391077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391086 : List Nat := [4, 1, 5, 1, 1, 2, 1, 1, 5]
def baseStart_391086 : Nat := 118140960795 + 391086 * 2 ^ 59
def prefixEnd_391086 : Nat := 4983230072969 + 3 ^ 40 * 391086 * 2
def baseEnd_391086 : Nat := 89251153441938714633971

theorem tailTrace_391086 : CollatzResearch.WordTrace tailWord_391086 prefixEnd_391086 89251153441938714633971 := by
  unfold tailWord_391086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1783009782646211127039139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9509385507446459344208741 1783009782646211127039139)
  ·
    refine ⟨2674514673969316690558709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1783009782646211127039139 2674514673969316690558709)
    ·
      refine ⟨250735750684623439739879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2674514673969316690558709 250735750684623439739879)
      ·
        refine ⟨376103626026935159609819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 250735750684623439739879 376103626026935159609819)
        ·
          refine ⟨564155439040402739414729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376103626026935159609819 564155439040402739414729)
          ·
            refine ⟨423116579280302054561047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 564155439040402739414729 423116579280302054561047)
            ·
              refine ⟨634674868920453081841571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423116579280302054561047 634674868920453081841571)
              ·
                refine ⟨952012303380679622762357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634674868920453081841571 952012303380679622762357)
                ·
                  refine ⟨89251153441938714633971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 952012303380679622762357 89251153441938714633971)
                  ·
                    rfl

theorem cell21_391086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_391086 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_391086 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_391086 prefixEnd_391086 := by exact prefixLift 391086
  have htrace : WordTrace (prefixWord ++ tailWord_391086) baseStart_391086 baseEnd_391086 := by
    simpa [prefixWord, tailWord_391086, baseEnd_391086] using wordTrace_append hprefix tailTrace_391086
  have hstable : (prefixWord ++ tailWord_391086).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391086).length < 2 ^ (prefixWord ++ tailWord_391086).sum := by decide
  have hdescent : baseEnd_391086 < baseStart_391086 := by decide
  rcases family_descends (prefixWord ++ tailWord_391086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391100 : List Nat := [2, 2, 2, 5, 1, 2, 2, 1, 4]
def baseStart_391100 : Nat := 118140960795 + 391100 * 2 ^ 59
def prefixEnd_391100 : Nat := 4983230072969 + 3 ^ 40 * 391100 * 2
def baseEnd_391100 : Nat := 89254348432677801400609

theorem tailTrace_391100 : CollatzResearch.WordTrace tailWord_391100 prefixEnd_391100 89254348432677801400609 := by
  unfold tailWord_391100
  simp only [CollatzResearch.WordTrace]
  refine ⟨7132294441559484703661377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9509725922079312938215169 7132294441559484703661377)
  ·
    refine ⟨5349220831169613527746033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7132294441559484703661377 5349220831169613527746033)
    ·
      refine ⟨4011915623377210145809525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5349220831169613527746033 4011915623377210145809525)
      ·
        refine ⟨376117089691613451169643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4011915623377210145809525 376117089691613451169643)
        ·
          refine ⟨564175634537420176754465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376117089691613451169643 564175634537420176754465)
          ·
            refine ⟨423131725903065132565849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 564175634537420176754465 423131725903065132565849)
            ·
              refine ⟨317348794427298849424387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423131725903065132565849 317348794427298849424387)
              ·
                refine ⟨476023191640948274136581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317348794427298849424387 476023191640948274136581)
                ·
                  refine ⟨89254348432677801400609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 476023191640948274136581 89254348432677801400609)
                  ·
                    rfl

theorem cell21_391100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 2, 1, 4].length) (baseStart_391100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_391100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_391100 prefixEnd_391100 := by exact prefixLift 391100
  have htrace : WordTrace (prefixWord ++ tailWord_391100) baseStart_391100 baseEnd_391100 := by
    simpa [prefixWord, tailWord_391100, baseEnd_391100] using wordTrace_append hprefix tailTrace_391100
  have hstable : (prefixWord ++ tailWord_391100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391100).length < 2 ^ (prefixWord ++ tailWord_391100).sum := by decide
  have hdescent : baseEnd_391100 < baseStart_391100 := by decide
  rcases family_descends (prefixWord ++ tailWord_391100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391201 : List Nat := [1, 2, 3, 2, 4, 1, 1, 1, 6]
def baseStart_391201 : Nat := 118140960795 + 391201 * 2 ^ 59
def prefixEnd_391201 : Nat := 4983230072969 + 3 ^ 40 * 391201 * 2
def baseEnd_391201 : Nat := 89277398008724070217069

theorem tailTrace_391201 : CollatzResearch.WordTrace tailWord_391201 prefixEnd_391201 89277398008724070217069 := by
  unfold tailWord_391201
  simp only [CollatzResearch.WordTrace]
  refine ⟨14268272655753063656749457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9512181770502042437832971 14268272655753063656749457)
  ·
    refine ⟨10701204491814797742562093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14268272655753063656749457 10701204491814797742562093)
    ·
      refine ⟨4012951684430549153460785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10701204491814797742562093 4012951684430549153460785)
      ·
        refine ⟨3009713763322911865095589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4012951684430549153460785 3009713763322911865095589)
        ·
          refine ⟨564321330623045974705423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3009713763322911865095589 564321330623045974705423)
          ·
            refine ⟨846481995934568962058135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564321330623045974705423 846481995934568962058135)
            ·
              refine ⟨1269722993901853443087203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846481995934568962058135 1269722993901853443087203)
              ·
                refine ⟨1904584490852780164630805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269722993901853443087203 1904584490852780164630805)
                ·
                  refine ⟨89277398008724070217069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1904584490852780164630805 89277398008724070217069)
                  ·
                    rfl

theorem cell21_391201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 1, 1, 6].length) (baseStart_391201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_391201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_391201 prefixEnd_391201 := by exact prefixLift 391201
  have htrace : WordTrace (prefixWord ++ tailWord_391201) baseStart_391201 baseEnd_391201 := by
    simpa [prefixWord, tailWord_391201, baseEnd_391201] using wordTrace_append hprefix tailTrace_391201
  have hstable : (prefixWord ++ tailWord_391201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391201).length < 2 ^ (prefixWord ++ tailWord_391201).sum := by decide
  have hdescent : baseEnd_391201 < baseStart_391201 := by decide
  rcases family_descends (prefixWord ++ tailWord_391201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391218 : List Nat := [3, 2, 1, 1, 2, 4, 3, 1, 4]
def baseStart_391218 : Nat := 118140960795 + 391218 * 2 ^ 59
def prefixEnd_391218 : Nat := 4983230072969 + 3 ^ 40 * 391218 * 2
def baseEnd_391218 : Nat := 89281277640335818433701

theorem tailTrace_391218 : CollatzResearch.WordTrace tailWord_391218 prefixEnd_391218 89281277640335818433701 := by
  unfold tailWord_391218
  simp only [CollatzResearch.WordTrace]
  refine ⟨3567223174172868890029577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9512595131127650373412205 3567223174172868890029577)
  ·
    refine ⟨2675417380629651667522183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3567223174172868890029577 2675417380629651667522183)
    ·
      refine ⟨4013126070944477501283275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2675417380629651667522183 4013126070944477501283275)
      ·
        refine ⟨6019689106416716251924913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4013126070944477501283275 6019689106416716251924913)
        ·
          refine ⟨4514766829812537188943685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6019689106416716251924913 4514766829812537188943685)
          ·
            refine ⟨846518780589850722926941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4514766829812537188943685 846518780589850722926941)
            ·
              refine ⟨317444542721194021097603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 846518780589850722926941 317444542721194021097603)
              ·
                refine ⟨476166814081791031646405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317444542721194021097603 476166814081791031646405)
                ·
                  refine ⟨89281277640335818433701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 476166814081791031646405 89281277640335818433701)
                  ·
                    rfl

theorem cell21_391218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_391218 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_391218 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_391218 prefixEnd_391218 := by exact prefixLift 391218
  have htrace : WordTrace (prefixWord ++ tailWord_391218) baseStart_391218 baseEnd_391218 := by
    simpa [prefixWord, tailWord_391218, baseEnd_391218] using wordTrace_append hprefix tailTrace_391218
  have hstable : (prefixWord ++ tailWord_391218).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391218).length < 2 ^ (prefixWord ++ tailWord_391218).sum := by decide
  have hdescent : baseEnd_391218 < baseStart_391218 := by decide
  rcases family_descends (prefixWord ++ tailWord_391218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391232 : List Nat := [2, 1, 1, 2, 2, 6, 2, 5]
def baseStart_391232 : Nat := 118140960795 + 391232 * 2 ^ 59
def prefixEnd_391232 : Nat := 4983230072969 + 3 ^ 40 * 391232 * 2
def baseEnd_391232 : Nat := 29761490877024968400113

theorem tailTrace_391232 : CollatzResearch.WordTrace tailWord_391232 prefixEnd_391232 29761490877024968400113 := by
  unfold tailWord_391232
  simp only [CollatzResearch.WordTrace]
  refine ⟨7134701659320377975563975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9512935545760503967418633 7134701659320377975563975)
  ·
    refine ⟨10702052488980566963345963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7134701659320377975563975 10702052488980566963345963)
    ·
      refine ⟨16053078733470850445018945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10702052488980566963345963 16053078733470850445018945)
      ·
        refine ⟨12039809050103137833764209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16053078733470850445018945 12039809050103137833764209)
        ·
          refine ⟨9029856787577353375323157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12039809050103137833764209 9029856787577353375323157)
          ·
            refine ⟨423274536917688439468273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9029856787577353375323157 423274536917688439468273)
            ·
              refine ⟨317455902688266329601205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423274536917688439468273 317455902688266329601205)
              ·
                refine ⟨29761490877024968400113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 317455902688266329601205 29761490877024968400113)
                ·
                  rfl

theorem cell21_391232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 2, 5].length) (baseStart_391232 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_391232 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_391232 prefixEnd_391232 := by exact prefixLift 391232
  have htrace : WordTrace (prefixWord ++ tailWord_391232) baseStart_391232 baseEnd_391232 := by
    simpa [prefixWord, tailWord_391232, baseEnd_391232] using wordTrace_append hprefix tailTrace_391232
  have hstable : (prefixWord ++ tailWord_391232).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391232).length < 2 ^ (prefixWord ++ tailWord_391232).sum := by decide
  have hdescent : baseEnd_391232 < baseStart_391232 := by decide
  rcases family_descends (prefixWord ++ tailWord_391232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391277 : List Nat := [1, 5, 1, 1, 2, 1, 3, 3, 4]
def baseStart_391277 : Nat := 118140960795 + 391277 * 2 ^ 59
def prefixEnd_391277 : Nat := 4983230072969 + 3 ^ 40 * 391277 * 2
def baseEnd_391277 : Nat := 89294742244164826950247

theorem tailTrace_391277 : CollatzResearch.WordTrace tailWord_391277 prefixEnd_391277 89294742244164826950247 := by
  unfold tailWord_391277
  simp only [CollatzResearch.WordTrace]
  refine ⟨14271044603477728636516085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9514029735651819091010723 14271044603477728636516085)
  ·
    refine ⟨1337910431576037059673383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14271044603477728636516085 1337910431576037059673383)
    ·
      refine ⟨2006865647364055589510075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1337910431576037059673383 2006865647364055589510075)
      ·
        refine ⟨3010298471046083384265113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2006865647364055589510075 3010298471046083384265113)
        ·
          refine ⟨2257723853284562538198835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3010298471046083384265113 2257723853284562538198835)
          ·
            refine ⟨3386585779926843807298253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2257723853284562538198835 3386585779926843807298253)
            ·
              refine ⟨1269969667472566427736845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3386585779926843807298253 1269969667472566427736845)
              ·
                refine ⟨476238625302212410401317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1269969667472566427736845 476238625302212410401317)
                ·
                  refine ⟨89294742244164826950247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 476238625302212410401317 89294742244164826950247)
                  ·
                    rfl

theorem cell21_391277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 3, 4].length) (baseStart_391277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_391277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_391277 prefixEnd_391277 := by exact prefixLift 391277
  have htrace : WordTrace (prefixWord ++ tailWord_391277) baseStart_391277 baseEnd_391277 := by
    simpa [prefixWord, tailWord_391277, baseEnd_391277] using wordTrace_append hprefix tailTrace_391277
  have hstable : (prefixWord ++ tailWord_391277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391277).length < 2 ^ (prefixWord ++ tailWord_391277).sum := by decide
  have hdescent : baseEnd_391277 < baseStart_391277 := by decide
  rcases family_descends (prefixWord ++ tailWord_391277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391342 : List Nat := [4, 1, 4, 2, 1, 1, 3, 5]
def baseStart_391342 : Nat := 118140960795 + 391342 * 2 ^ 59
def prefixEnd_391342 : Nat := 4983230072969 + 3 ^ 40 * 391342 * 2
def baseEnd_391342 : Nat := 29769858709913052788927

theorem tailTrace_391342 : CollatzResearch.WordTrace tailWord_391342 prefixEnd_391342 29769858709913052788927 := by
  unfold tailWord_391342
  simp only [CollatzResearch.WordTrace]
  refine ⟨1784176918530280592204035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9515610232161496491754853 1784176918530280592204035)
  ·
    refine ⟨2676265377795420888306053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1784176918530280592204035 2676265377795420888306053)
    ·
      refine ⟨501799758336641416557385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2676265377795420888306053 501799758336641416557385)
      ·
        refine ⟨376349818752481062418039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 501799758336641416557385 376349818752481062418039)
        ·
          refine ⟨564524728128721593627059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376349818752481062418039 564524728128721593627059)
          ·
            refine ⟨846787092193082390440589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564524728128721593627059 846787092193082390440589)
            ·
              refine ⟨317545159572405896415221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 846787092193082390440589 317545159572405896415221)
              ·
                refine ⟨29769858709913052788927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 317545159572405896415221 29769858709913052788927)
                ·
                  rfl

theorem cell21_391342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 3, 5].length) (baseStart_391342 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_391342 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_391342 prefixEnd_391342 := by exact prefixLift 391342
  have htrace : WordTrace (prefixWord ++ tailWord_391342) baseStart_391342 baseEnd_391342 := by
    simpa [prefixWord, tailWord_391342, baseEnd_391342] using wordTrace_append hprefix tailTrace_391342
  have hstable : (prefixWord ++ tailWord_391342).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391342).length < 2 ^ (prefixWord ++ tailWord_391342).sum := by decide
  have hdescent : baseEnd_391342 < baseStart_391342 := by decide
  rcases family_descends (prefixWord ++ tailWord_391342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391356 : List Nat := [2, 2, 2, 3, 3, 1, 2, 3, 3]
def baseStart_391356 : Nat := 118140960795 + 391356 * 2 ^ 59
def prefixEnd_391356 : Nat := 4983230072969 + 3 ^ 40 * 391356 * 2
def baseEnd_391356 : Nat := 89312771120478245133419

theorem tailTrace_391356 : CollatzResearch.WordTrace tailWord_391356 prefixEnd_391356 89312771120478245133419 := by
  unfold tailWord_391356
  simp only [CollatzResearch.WordTrace]
  refine ⟨7136962985095762564320961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9515950646794350085761281 7136962985095762564320961)
  ·
    refine ⟨5352722238821821923240721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7136962985095762564320961 5352722238821821923240721)
    ·
      refine ⟨4014541679116366442430541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5352722238821821923240721 4014541679116366442430541)
      ·
        refine ⟨1505453129668637415911453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4014541679116366442430541 1505453129668637415911453)
        ·
          refine ⟨564544923625739030966795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1505453129668637415911453 564544923625739030966795)
          ·
            refine ⟨846817385438608546450193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564544923625739030966795 846817385438608546450193)
            ·
              refine ⟨635113039078956409837645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 846817385438608546450193 635113039078956409837645)
              ·
                refine ⟨238167389654608653689117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 635113039078956409837645 238167389654608653689117)
                ·
                  refine ⟨89312771120478245133419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238167389654608653689117 89312771120478245133419)
                  ·
                    rfl

theorem cell21_391356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 2, 3, 3].length) (baseStart_391356 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_391356 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_391356 prefixEnd_391356 := by exact prefixLift 391356
  have htrace : WordTrace (prefixWord ++ tailWord_391356) baseStart_391356 baseEnd_391356 := by
    simpa [prefixWord, tailWord_391356, baseEnd_391356] using wordTrace_append hprefix tailTrace_391356
  have hstable : (prefixWord ++ tailWord_391356).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391356).length < 2 ^ (prefixWord ++ tailWord_391356).sum := by decide
  have hdescent : baseEnd_391356 < baseStart_391356 := by decide
  rcases family_descends (prefixWord ++ tailWord_391356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391432 : List Nat := [2, 1, 3, 2, 3, 2, 3, 2, 3]
def baseStart_391432 : Nat := 118140960795 + 391432 * 2 ^ 59
def prefixEnd_391432 : Nat := 4983230072969 + 3 ^ 40 * 391432 * 2
def baseEnd_391432 : Nat := 89330115355919001866597

theorem tailTrace_391432 : CollatzResearch.WordTrace tailWord_391432 prefixEnd_391432 89330115355919001866597 := by
  unfold tailWord_391432
  simp only [CollatzResearch.WordTrace]
  refine ⟨7138348958958095054204275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9517798611944126738939033 7138348958958095054204275)
  ·
    refine ⟨10707523438437142581306413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7138348958958095054204275 10707523438437142581306413)
    ·
      refine ⟨4015321289413928467989905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10707523438437142581306413 4015321289413928467989905)
      ·
        refine ⟨3011490967060446350992429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4015321289413928467989905 3011490967060446350992429)
        ·
          refine ⟨1129309112647667381622161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3011490967060446350992429 1129309112647667381622161)
          ·
            refine ⟨846981834485750536216621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1129309112647667381622161 846981834485750536216621)
            ·
              refine ⟨317618187932156451081233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 846981834485750536216621 317618187932156451081233)
              ·
                refine ⟨238213640949117338310925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317618187932156451081233 238213640949117338310925)
                ·
                  refine ⟨89330115355919001866597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238213640949117338310925 89330115355919001866597)
                  ·
                    rfl

theorem cell21_391432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 3, 2, 3].length) (baseStart_391432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_391432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_391432 prefixEnd_391432 := by exact prefixLift 391432
  have htrace : WordTrace (prefixWord ++ tailWord_391432) baseStart_391432 baseEnd_391432 := by
    simpa [prefixWord, tailWord_391432, baseEnd_391432] using wordTrace_append hprefix tailTrace_391432
  have hstable : (prefixWord ++ tailWord_391432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391432).length < 2 ^ (prefixWord ++ tailWord_391432).sum := by decide
  have hdescent : baseEnd_391432 < baseStart_391432 := by decide
  rcases family_descends (prefixWord ++ tailWord_391432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391457 : List Nat := [1, 2, 3, 2, 1, 1, 2, 4, 5]
def baseStart_391457 : Nat := 118140960795 + 391457 * 2 ^ 59
def prefixEnd_391457 : Nat := 4983230072969 + 3 ^ 40 * 391457 * 2
def baseEnd_391457 : Nat := 89335820696524513949879

theorem tailTrace_391457 : CollatzResearch.WordTrace tailWord_391457 prefixEnd_391457 89335820696524513949879 := by
  unfold tailWord_391457
  simp only [CollatzResearch.WordTrace]
  refine ⟨14277609742825619378068625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9518406495217079585379083 14277609742825619378068625)
  ·
    refine ⟨10708207307119214533551469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14277609742825619378068625 10708207307119214533551469)
    ·
      refine ⟨4015577740169705450081801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10708207307119214533551469 4015577740169705450081801)
      ·
        refine ⟨3011683305127279087561351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4015577740169705450081801 3011683305127279087561351)
        ·
          refine ⟨4517524957690918631342027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3011683305127279087561351 4517524957690918631342027)
          ·
            refine ⟨6776287436536377947013041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4517524957690918631342027 6776287436536377947013041)
            ·
              refine ⟨5082215577402283460259781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6776287436536377947013041 5082215577402283460259781)
              ·
                refine ⟨952915420762928148798709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5082215577402283460259781 952915420762928148798709)
                ·
                  refine ⟨89335820696524513949879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 952915420762928148798709 89335820696524513949879)
                  ·
                    rfl

theorem cell21_391457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 4, 5].length) (baseStart_391457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_391457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_391457 prefixEnd_391457 := by exact prefixLift 391457
  have htrace : WordTrace (prefixWord ++ tailWord_391457) baseStart_391457 baseEnd_391457 := by
    simpa [prefixWord, tailWord_391457, baseEnd_391457] using wordTrace_append hprefix tailTrace_391457
  have hstable : (prefixWord ++ tailWord_391457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391457).length < 2 ^ (prefixWord ++ tailWord_391457).sum := by decide
  have hdescent : baseEnd_391457 < baseStart_391457 := by decide
  rcases family_descends (prefixWord ++ tailWord_391457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391471 : List Nat := [1, 1, 2, 1, 2, 1, 4, 1, 8]
def baseStart_391471 : Nat := 118140960795 + 391471 * 2 ^ 59
def prefixEnd_391471 : Nat := 4983230072969 + 3 ^ 40 * 391471 * 2
def baseEnd_391471 : Nat := 89339015687263600716517

theorem tailTrace_391471 : CollatzResearch.WordTrace tailWord_391471 prefixEnd_391471 89339015687263600716517 := by
  unfold tailWord_391471
  simp only [CollatzResearch.WordTrace]
  refine ⟨14278120364774899769078267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9518746909849933179385511 14278120364774899769078267)
  ·
    refine ⟨21417180547162349653617401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14278120364774899769078267 21417180547162349653617401)
    ·
      refine ⟨16062885410371762240213051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21417180547162349653617401 16062885410371762240213051)
      ·
        refine ⟨24094328115557643360319577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16062885410371762240213051 24094328115557643360319577)
        ·
          refine ⟨18070746086668232520239683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24094328115557643360319577 18070746086668232520239683)
          ·
            refine ⟨27106119130002348780359525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18070746086668232520239683 27106119130002348780359525)
            ·
              refine ⟨5082397336875440396317411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27106119130002348780359525 5082397336875440396317411)
              ·
                refine ⟨7623596005313160594476117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5082397336875440396317411 7623596005313160594476117)
                ·
                  refine ⟨89339015687263600716517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7623596005313160594476117 89339015687263600716517)
                  ·
                    rfl

theorem cell21_391471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 4, 1, 8].length) (baseStart_391471 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_391471 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_391471 prefixEnd_391471 := by exact prefixLift 391471
  have htrace : WordTrace (prefixWord ++ tailWord_391471) baseStart_391471 baseEnd_391471 := by
    simpa [prefixWord, tailWord_391471, baseEnd_391471] using wordTrace_append hprefix tailTrace_391471
  have hstable : (prefixWord ++ tailWord_391471).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391471).length < 2 ^ (prefixWord ++ tailWord_391471).sum := by decide
  have hdescent : baseEnd_391471 < baseStart_391471 := by decide
  rcases family_descends (prefixWord ++ tailWord_391471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391491 : List Nat := [1, 1, 1, 3, 1, 3, 6, 2, 3]
def baseStart_391491 : Nat := 118140960795 + 391491 * 2 ^ 59
def prefixEnd_391491 : Nat := 4983230072969 + 3 ^ 40 * 391491 * 2
def baseEnd_391491 : Nat := 89343579959748010383143

theorem tailTrace_391491 : CollatzResearch.WordTrace tailWord_391491 prefixEnd_391491 89343579959748010383143 := by
  unfold tailWord_391491
  simp only [CollatzResearch.WordTrace]
  refine ⟨14278849824702443184806327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9519233216468295456537551 14278849824702443184806327)
  ·
    refine ⟨21418274737053664777209491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14278849824702443184806327 21418274737053664777209491)
    ·
      refine ⟨32127412105580497165814237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21418274737053664777209491 32127412105580497165814237)
      ·
        refine ⟨12047779539592686437180339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32127412105580497165814237 12047779539592686437180339)
        ·
          refine ⟨18071669309389029655770509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12047779539592686437180339 18071669309389029655770509)
          ·
            refine ⟨6776875991020886120913941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18071669309389029655770509 6776875991020886120913941)
            ·
              refine ⟨317666062079104036917841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6776875991020886120913941 317666062079104036917841)
              ·
                refine ⟨238249546559328027688381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317666062079104036917841 238249546559328027688381)
                ·
                  refine ⟨89343579959748010383143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238249546559328027688381 89343579959748010383143)
                  ·
                    rfl

theorem cell21_391491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 6, 2, 3].length) (baseStart_391491 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_391491 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_391491 prefixEnd_391491 := by exact prefixLift 391491
  have htrace : WordTrace (prefixWord ++ tailWord_391491) baseStart_391491 baseEnd_391491 := by
    simpa [prefixWord, tailWord_391491, baseEnd_391491] using wordTrace_append hprefix tailTrace_391491
  have hstable : (prefixWord ++ tailWord_391491).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391491).length < 2 ^ (prefixWord ++ tailWord_391491).sum := by decide
  have hdescent : baseEnd_391491 < baseStart_391491 := by decide
  rcases family_descends (prefixWord ++ tailWord_391491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391502 : List Nat := [4, 1, 1, 1, 1, 1, 2, 10]
def baseStart_391502 : Nat := 118140960795 + 391502 * 2 ^ 59
def prefixEnd_391502 : Nat := 4983230072969 + 3 ^ 40 * 391502 * 2
def baseEnd_391502 : Nat := 29782030103204811899929

theorem tailTrace_391502 : CollatzResearch.WordTrace tailWord_391502 prefixEnd_391502 29782030103204811899929 := by
  unfold tailWord_391502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1784906378457824007932095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9519500685108394708971173 1784906378457824007932095)
  ·
    refine ⟨2677359567686736011898143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1784906378457824007932095 2677359567686736011898143)
    ·
      refine ⟨4016039351530104017847215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2677359567686736011898143 4016039351530104017847215)
      ·
        refine ⟨6024059027295156026770823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4016039351530104017847215 6024059027295156026770823)
        ·
          refine ⟨9036088540942734040156235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6024059027295156026770823 9036088540942734040156235)
          ·
            refine ⟨13554132811414101060234353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9036088540942734040156235 13554132811414101060234353)
            ·
              refine ⟨10165599608560575795175765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13554132811414101060234353 10165599608560575795175765)
              ·
                refine ⟨29782030103204811899929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10165599608560575795175765 29782030103204811899929)
                ·
                  rfl

theorem cell21_391502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_391502 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_391502 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_391502 prefixEnd_391502 := by exact prefixLift 391502
  have htrace : WordTrace (prefixWord ++ tailWord_391502) baseStart_391502 baseEnd_391502 := by
    simpa [prefixWord, tailWord_391502, baseEnd_391502] using wordTrace_append hprefix tailTrace_391502
  have hstable : (prefixWord ++ tailWord_391502).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391502).length < 2 ^ (prefixWord ++ tailWord_391502).sum := by decide
  have hdescent : baseEnd_391502 < baseStart_391502 := by decide
  rcases family_descends (prefixWord ++ tailWord_391502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391533 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 7]
def baseStart_391533 : Nat := 118140960795 + 391533 * 2 ^ 59
def prefixEnd_391533 : Nat := 4983230072969 + 3 ^ 40 * 391533 * 2
def baseEnd_391533 : Nat := 89353164931965270683057

theorem tailTrace_391533 : CollatzResearch.WordTrace tailWord_391533 prefixEnd_391533 89353164931965270683057 := by
  unfold tailWord_391533
  simp only [CollatzResearch.WordTrace]
  refine ⟨14280381690550284357835253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9520254460366856238556835 14280381690550284357835253)
  ·
    refine ⟨1338785783489089158547055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14280381690550284357835253 1338785783489089158547055)
    ·
      refine ⟨2008178675233633737820583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1338785783489089158547055 2008178675233633737820583)
      ·
        refine ⟨3012268012850450606730875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2008178675233633737820583 3012268012850450606730875)
        ·
          refine ⟨4518402019275675910096313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3012268012850450606730875 4518402019275675910096313)
          ·
            refine ⟨3388801514456756932572235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4518402019275675910096313 3388801514456756932572235)
            ·
              refine ⟨5083202271685135398858353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3388801514456756932572235 5083202271685135398858353)
              ·
                refine ⟨3812401703763851549143765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5083202271685135398858353 3812401703763851549143765)
                ·
                  refine ⟨89353164931965270683057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3812401703763851549143765 89353164931965270683057)
                  ·
                    rfl

theorem cell21_391533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_391533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_391533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_391533 prefixEnd_391533 := by exact prefixLift 391533
  have htrace : WordTrace (prefixWord ++ tailWord_391533) baseStart_391533 baseEnd_391533 := by
    simpa [prefixWord, tailWord_391533, baseEnd_391533] using wordTrace_append hprefix tailTrace_391533
  have hstable : (prefixWord ++ tailWord_391533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391533).length < 2 ^ (prefixWord ++ tailWord_391533).sum := by decide
  have hdescent : baseEnd_391533 < baseStart_391533 := by decide
  rcases family_descends (prefixWord ++ tailWord_391533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391699 : List Nat := [1, 1, 1, 2, 1, 5, 2, 2, 6]
def baseStart_391699 : Nat := 118140960795 + 391699 * 2 ^ 59
def prefixEnd_391699 : Nat := 4983230072969 + 3 ^ 40 * 391699 * 2
def baseEnd_391699 : Nat := 89391048393585870916051

theorem tailTrace_391699 : CollatzResearch.WordTrace tailWord_391699 prefixEnd_391699 89391048393585870916051 := by
  unfold tailWord_391699
  simp only [CollatzResearch.WordTrace]
  refine ⟨14286436207948894708378151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9524290805299263138918767 14286436207948894708378151)
  ·
    refine ⟨21429654311923342062567227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14286436207948894708378151 21429654311923342062567227)
    ·
      refine ⟨32144481467885013093850841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21429654311923342062567227 32144481467885013093850841)
      ·
        refine ⟨24108361100913759820388131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32144481467885013093850841 24108361100913759820388131)
        ·
          refine ⟨36162541651370639730582197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24108361100913759820388131 36162541651370639730582197)
          ·
            refine ⟨3390238279815997474742081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 36162541651370639730582197 3390238279815997474742081)
            ·
              refine ⟨2542678709861998106056561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3390238279815997474742081 2542678709861998106056561)
              ·
                refine ⟨1907009032396498579542421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2542678709861998106056561 1907009032396498579542421)
                ·
                  refine ⟨89391048393585870916051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1907009032396498579542421 89391048393585870916051)
                  ·
                    rfl

theorem cell21_391699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 2, 6].length) (baseStart_391699 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_391699 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_391699 prefixEnd_391699 := by exact prefixLift 391699
  have htrace : WordTrace (prefixWord ++ tailWord_391699) baseStart_391699 baseEnd_391699 := by
    simpa [prefixWord, tailWord_391699, baseEnd_391699] using wordTrace_append hprefix tailTrace_391699
  have hstable : (prefixWord ++ tailWord_391699).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391699).length < 2 ^ (prefixWord ++ tailWord_391699).sum := by decide
  have hdescent : baseEnd_391699 < baseStart_391699 := by decide
  rcases family_descends (prefixWord ++ tailWord_391699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391733 : List Nat := [1, 3, 3, 1, 1, 2, 5, 1, 4]
def baseStart_391733 : Nat := 118140960795 + 391733 * 2 ^ 59
def prefixEnd_391733 : Nat := 4983230072969 + 3 ^ 40 * 391733 * 2
def baseEnd_391733 : Nat := 89398807656809367349315

theorem tailTrace_391733 : CollatzResearch.WordTrace tailWord_391733 prefixEnd_391733 89398807656809367349315 := by
  unfold tailWord_391733
  simp only [CollatzResearch.WordTrace]
  refine ⟨14287676289825718515115853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9525117526550479010077235 14287676289825718515115853)
  ·
    refine ⟨5357878608684644443168445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14287676289825718515115853 5357878608684644443168445)
    ·
      refine ⟨2009204478256741666188167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5357878608684644443168445 2009204478256741666188167)
      ·
        refine ⟨3013806717385112499282251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2009204478256741666188167 3013806717385112499282251)
        ·
          refine ⟨4520710076077668748923377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3013806717385112499282251 4520710076077668748923377)
          ·
            refine ⟨3390532557058251561692533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4520710076077668748923377 3390532557058251561692533)
            ·
              refine ⟨317862427224211083908675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3390532557058251561692533 317862427224211083908675)
              ·
                refine ⟨476793640836316625863013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317862427224211083908675 476793640836316625863013)
                ·
                  refine ⟨89398807656809367349315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 476793640836316625863013 89398807656809367349315)
                  ·
                    rfl

theorem cell21_391733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 5, 1, 4].length) (baseStart_391733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_391733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_391733 prefixEnd_391733 := by exact prefixLift 391733
  have htrace : WordTrace (prefixWord ++ tailWord_391733) baseStart_391733 baseEnd_391733 := by
    simpa [prefixWord, tailWord_391733, baseEnd_391733] using wordTrace_append hprefix tailTrace_391733
  have hstable : (prefixWord ++ tailWord_391733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391733).length < 2 ^ (prefixWord ++ tailWord_391733).sum := by decide
  have hdescent : baseEnd_391733 < baseStart_391733 := by decide
  rcases family_descends (prefixWord ++ tailWord_391733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391820 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 9]
def baseStart_391820 : Nat := 118140960795 + 391820 * 2 ^ 59
def prefixEnd_391820 : Nat := 4983230072969 + 3 ^ 40 * 391820 * 2
def baseEnd_391820 : Nat := 89418662242116549399137

theorem tailTrace_391820 : CollatzResearch.WordTrace tailWord_391820 prefixEnd_391820 89418662242116549399137 := by
  unfold tailWord_391820
  simp only [CollatzResearch.WordTrace]
  refine ⟨7145424720255266186766457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9527232960340354915688609 7145424720255266186766457)
  ·
    refine ⟨5359068540191449640074843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7145424720255266186766457 5359068540191449640074843)
    ·
      refine ⟨8038602810287174460112265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5359068540191449640074843 8038602810287174460112265)
      ·
        refine ⟨6028952107715380845084199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8038602810287174460112265 6028952107715380845084199)
        ·
          refine ⟨9043428161573071267626299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6028952107715380845084199 9043428161573071267626299)
          ·
            refine ⟨13565142242359606901439449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9043428161573071267626299 13565142242359606901439449)
            ·
              refine ⟨10173856681769705176079587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13565142242359606901439449 10173856681769705176079587)
              ·
                refine ⟨15260785022654557764119381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10173856681769705176079587 15260785022654557764119381)
                ·
                  refine ⟨89418662242116549399137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15260785022654557764119381 89418662242116549399137)
                  ·
                    rfl

theorem cell21_391820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 9].length) (baseStart_391820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_391820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_391820 prefixEnd_391820 := by exact prefixLift 391820
  have htrace : WordTrace (prefixWord ++ tailWord_391820) baseStart_391820 baseEnd_391820 := by
    simpa [prefixWord, tailWord_391820, baseEnd_391820] using wordTrace_append hprefix tailTrace_391820
  have hstable : (prefixWord ++ tailWord_391820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391820).length < 2 ^ (prefixWord ++ tailWord_391820).sum := by decide
  have hdescent : baseEnd_391820 < baseStart_391820 := by decide
  rcases family_descends (prefixWord ++ tailWord_391820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391840 : List Nat := [2, 1, 1, 4, 5, 1, 1, 6]
def baseStart_391840 : Nat := 118140960795 + 391840 * 2 ^ 59
def prefixEnd_391840 : Nat := 4983230072969 + 3 ^ 40 * 391840 * 2
def baseEnd_391840 : Nat := 29807742171533653021921

theorem tailTrace_391840 : CollatzResearch.WordTrace tailWord_391840 prefixEnd_391840 29807742171533653021921 := by
  unfold tailWord_391840
  simp only [CollatzResearch.WordTrace]
  refine ⟨7145789450219037894630487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9527719266958717192840649 7145789450219037894630487)
  ·
    refine ⟨10718684175328556841945731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7145789450219037894630487 10718684175328556841945731)
    ·
      refine ⟨16078026262992835262918597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10718684175328556841945731 16078026262992835262918597)
      ·
        refine ⟨3014629924311156611797237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16078026262992835262918597 3014629924311156611797237)
        ·
          refine ⟨282621555404170932355991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3014629924311156611797237 282621555404170932355991)
          ·
            refine ⟨423932333106256398533987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282621555404170932355991 423932333106256398533987)
            ·
              refine ⟨635898499659384597800981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423932333106256398533987 635898499659384597800981)
              ·
                refine ⟨29807742171533653021921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 635898499659384597800981 29807742171533653021921)
                ·
                  rfl

theorem cell21_391840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 1, 6].length) (baseStart_391840 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_391840 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_391840 prefixEnd_391840 := by exact prefixLift 391840
  have htrace : WordTrace (prefixWord ++ tailWord_391840) baseStart_391840 baseEnd_391840 := by
    simpa [prefixWord, tailWord_391840, baseEnd_391840] using wordTrace_append hprefix tailTrace_391840
  have hstable : (prefixWord ++ tailWord_391840).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391840).length < 2 ^ (prefixWord ++ tailWord_391840).sum := by decide
  have hdescent : baseEnd_391840 < baseStart_391840 := by decide
  rcases family_descends (prefixWord ++ tailWord_391840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391854 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 7]
def baseStart_391854 : Nat := 118140960795 + 391854 * 2 ^ 59
def prefixEnd_391854 : Nat := 4983230072969 + 3 ^ 40 * 391854 * 2
def baseEnd_391854 : Nat := 89426421505340045832401

theorem tailTrace_391854 : CollatzResearch.WordTrace tailWord_391854 prefixEnd_391854 89426421505340045832401 := by
  unfold tailWord_391854
  simp only [CollatzResearch.WordTrace]
  refine ⟨1786511190298419522533827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9528059681591570786847077 1786511190298419522533827)
  ·
    refine ⟨2679766785447629283800741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1786511190298419522533827 2679766785447629283800741)
    ·
      refine ⟨502456272271430490712639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2679766785447629283800741 502456272271430490712639)
      ·
        refine ⟨753684408407145736068959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 502456272271430490712639 753684408407145736068959)
        ·
          refine ⟨1130526612610718604103439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753684408407145736068959 1130526612610718604103439)
          ·
            refine ⟨1695789918916077906155159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1130526612610718604103439 1695789918916077906155159)
            ·
              refine ⟨2543684878374116859232739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1695789918916077906155159 2543684878374116859232739)
              ·
                refine ⟨3815527317561175288849109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2543684878374116859232739 3815527317561175288849109)
                ·
                  refine ⟨89426421505340045832401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3815527317561175288849109 89426421505340045832401)
                  ·
                    rfl

theorem cell21_391854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_391854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_391854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_391854 prefixEnd_391854 := by exact prefixLift 391854
  have htrace : WordTrace (prefixWord ++ tailWord_391854) baseStart_391854 baseEnd_391854 := by
    simpa [prefixWord, tailWord_391854, baseEnd_391854] using wordTrace_append hprefix tailTrace_391854
  have hstable : (prefixWord ++ tailWord_391854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391854).length < 2 ^ (prefixWord ++ tailWord_391854).sum := by decide
  have hdescent : baseEnd_391854 < baseStart_391854 := by decide
  rcases family_descends (prefixWord ++ tailWord_391854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391882 : List Nat := [3, 1, 2, 1, 4, 2, 8]
def baseStart_391882 : Nat := 118140960795 + 391882 * 2 ^ 59
def prefixEnd_391882 : Nat := 4983230072969 + 3 ^ 40 * 391882 * 2
def baseEnd_391882 : Nat := 9936979054090913262853

theorem tailTrace_391882 : CollatzResearch.WordTrace tailWord_391882 prefixEnd_391882 9936979054090913262853 := by
  unfold tailWord_391882
  simp only [CollatzResearch.WordTrace]
  refine ⟨3573277691571479240572475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9528740510857277974859933 3573277691571479240572475)
  ·
    refine ⟨5359916537357218860858713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3573277691571479240572475 5359916537357218860858713)
    ·
      refine ⟨4019937403017914145644035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5359916537357218860858713 4019937403017914145644035)
      ·
        refine ⟨6029906104526871218466053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4019937403017914145644035 6029906104526871218466053)
        ·
          refine ⟨1130607394598788353462385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6029906104526871218466053 1130607394598788353462385)
          ·
            refine ⟨847955545949091265096789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1130607394598788353462385 847955545949091265096789)
            ·
              refine ⟨9936979054090913262853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 847955545949091265096789 9936979054090913262853)
              ·
                rfl

theorem cell21_391882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 8].length) (baseStart_391882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_391882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_391882 prefixEnd_391882 := by exact prefixLift 391882
  have htrace : WordTrace (prefixWord ++ tailWord_391882) baseStart_391882 baseEnd_391882 := by
    simpa [prefixWord, tailWord_391882, baseEnd_391882] using wordTrace_append hprefix tailTrace_391882
  have hstable : (prefixWord ++ tailWord_391882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391882).length < 2 ^ (prefixWord ++ tailWord_391882).sum := by decide
  have hdescent : baseEnd_391882 < baseStart_391882 := by decide
  rcases family_descends (prefixWord ++ tailWord_391882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391930 : List Nat := [3, 1, 1, 1, 1, 3, 5, 3, 3]
def baseStart_391930 : Nat := 118140960795 + 391930 * 2 ^ 59
def prefixEnd_391930 : Nat := 4983230072969 + 3 ^ 40 * 391930 * 2
def baseEnd_391930 : Nat := 89443765740780802565579

theorem tailTrace_391930 : CollatzResearch.WordTrace tailWord_391930 prefixEnd_391930 89443765740780802565579 := by
  unfold tailWord_391930
  simp only [CollatzResearch.WordTrace]
  refine ⟨3573715367528005290009311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9529907646741347440024829 3573715367528005290009311)
  ·
    refine ⟨5360573051292007935013967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3573715367528005290009311 5360573051292007935013967)
    ·
      refine ⟨8040859576938011902520951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5360573051292007935013967 8040859576938011902520951)
      ·
        refine ⟨12061289365407017853781427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8040859576938011902520951 12061289365407017853781427)
        ·
          refine ⟨18091934048110526780672141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12061289365407017853781427 18091934048110526780672141)
          ·
            refine ⟨6784475268041447542752053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18091934048110526780672141 6784475268041447542752053)
            ·
              refine ⟨636044556378885707133005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6784475268041447542752053 636044556378885707133005)
              ·
                refine ⟨238516708642082140174877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 636044556378885707133005 238516708642082140174877)
                ·
                  refine ⟨89443765740780802565579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238516708642082140174877 89443765740780802565579)
                  ·
                    rfl

theorem cell21_391930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 5, 3, 3].length) (baseStart_391930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_391930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_391930 prefixEnd_391930 := by exact prefixLift 391930
  have htrace : WordTrace (prefixWord ++ tailWord_391930) baseStart_391930 baseEnd_391930 := by
    simpa [prefixWord, tailWord_391930, baseEnd_391930] using wordTrace_append hprefix tailTrace_391930
  have hstable : (prefixWord ++ tailWord_391930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391930).length < 2 ^ (prefixWord ++ tailWord_391930).sum := by decide
  have hdescent : baseEnd_391930 < baseStart_391930 := by decide
  rcases family_descends (prefixWord ++ tailWord_391930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392054 : List Nat := [5, 1, 1, 3, 1, 3, 1, 2, 4]
def baseStart_392054 : Nat := 118140960795 + 392054 * 2 ^ 59
def prefixEnd_392054 : Nat := 4983230072969 + 3 ^ 40 * 392054 * 2
def baseEnd_392054 : Nat := 89472064230184142498659

theorem tailTrace_392054 : CollatzResearch.WordTrace tailWord_392054 prefixEnd_392054 89472064230184142498659 := by
  unfold tailWord_392054
  simp only [CollatzResearch.WordTrace]
  refine ⟨893711507603924396096951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9532922747775193558367477 893711507603924396096951)
  ·
    refine ⟨1340567261405886594145427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 893711507603924396096951 1340567261405886594145427)
    ·
      refine ⟨2010850892108829891218141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1340567261405886594145427 2010850892108829891218141)
      ·
        refine ⟨754069084540811209206803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2010850892108829891218141 754069084540811209206803)
        ·
          refine ⟨1131103626811216813810205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754069084540811209206803 1131103626811216813810205)
          ·
            refine ⟨424163860054206305178827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1131103626811216813810205 424163860054206305178827)
            ·
              refine ⟨636245790081309457768241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424163860054206305178827 636245790081309457768241)
              ·
                refine ⟨477184342560982093326181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 636245790081309457768241 477184342560982093326181)
                ·
                  refine ⟨89472064230184142498659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 477184342560982093326181 89472064230184142498659)
                  ·
                    rfl

theorem cell21_392054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 3, 1, 2, 4].length) (baseStart_392054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392054 prefixEnd_392054 := by exact prefixLift 392054
  have htrace : WordTrace (prefixWord ++ tailWord_392054) baseStart_392054 baseEnd_392054 := by
    simpa [prefixWord, tailWord_392054, baseEnd_392054] using wordTrace_append hprefix tailTrace_392054
  have hstable : (prefixWord ++ tailWord_392054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392054).length < 2 ^ (prefixWord ++ tailWord_392054).sum := by decide
  have hdescent : baseEnd_392054 < baseStart_392054 := by decide
  rcases family_descends (prefixWord ++ tailWord_392054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392175 : List Nat := [1, 1, 2, 1, 4, 5, 2, 2, 3]
def baseStart_392175 : Nat := 118140960795 + 392175 * 2 ^ 59
def prefixEnd_392175 : Nat := 4983230072969 + 3 ^ 40 * 392175 * 2
def baseEnd_392175 : Nat := 89499678078714820981745

theorem tailTrace_392175 : CollatzResearch.WordTrace tailWord_392175 prefixEnd_392175 89499678078714820981745 := by
  unfold tailWord_392175
  simp only [CollatzResearch.WordTrace]
  refine ⟨14303797354224428002705979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9535864902816285335137319 14303797354224428002705979)
  ·
    refine ⟨21455696031336642004058969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14303797354224428002705979 21455696031336642004058969)
    ·
      refine ⟨16091772023502481503044227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21455696031336642004058969 16091772023502481503044227)
      ·
        refine ⟨24137658035253722254566341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16091772023502481503044227 24137658035253722254566341)
        ·
          refine ⟨4525810881610072922731189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24137658035253722254566341 4525810881610072922731189)
          ·
            refine ⟨424294770150944336506049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4525810881610072922731189 424294770150944336506049)
            ·
              refine ⟨318221077613208252379537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 424294770150944336506049 318221077613208252379537)
              ·
                refine ⟨238665808209906189284653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 318221077613208252379537 238665808209906189284653)
                ·
                  refine ⟨89499678078714820981745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238665808209906189284653 89499678078714820981745)
                  ·
                    rfl

theorem cell21_392175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 2, 2, 3].length) (baseStart_392175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392175 prefixEnd_392175 := by exact prefixLift 392175
  have htrace : WordTrace (prefixWord ++ tailWord_392175) baseStart_392175 baseEnd_392175 := by
    simpa [prefixWord, tailWord_392175, baseEnd_392175] using wordTrace_append hprefix tailTrace_392175
  have hstable : (prefixWord ++ tailWord_392175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392175).length < 2 ^ (prefixWord ++ tailWord_392175).sum := by decide
  have hdescent : baseEnd_392175 < baseStart_392175 := by decide
  rcases family_descends (prefixWord ++ tailWord_392175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392200 : List Nat := [2, 1, 3, 2, 1, 3, 1, 1, 7]
def baseStart_392200 : Nat := 118140960795 + 392200 * 2 ^ 59
def prefixEnd_392200 : Nat := 4983230072969 + 3 ^ 40 * 392200 * 2
def baseEnd_392200 : Nat := 89505383419320333065027

theorem tailTrace_392200 : CollatzResearch.WordTrace tailWord_392200 prefixEnd_392200 89505383419320333065027 := by
  unfold tailWord_392200
  simp only [CollatzResearch.WordTrace]
  refine ⟨7152354589566928636183027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9536472786089238181577369 7152354589566928636183027)
  ·
    refine ⟨10728531884350392954274541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7152354589566928636183027 10728531884350392954274541)
    ·
      refine ⟨4023199456631397357852953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10728531884350392954274541 4023199456631397357852953)
      ·
        refine ⟨3017399592473548018389715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4023199456631397357852953 3017399592473548018389715)
        ·
          refine ⟨4526099388710322027584573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3017399592473548018389715 4526099388710322027584573)
          ·
            refine ⟨1697287270766370760344215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4526099388710322027584573 1697287270766370760344215)
            ·
              refine ⟨2545930906149556140516323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1697287270766370760344215 2545930906149556140516323)
              ·
                refine ⟨3818896359224334210774485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2545930906149556140516323 3818896359224334210774485)
                ·
                  refine ⟨89505383419320333065027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3818896359224334210774485 89505383419320333065027)
                  ·
                    rfl

theorem cell21_392200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 1, 7].length) (baseStart_392200 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392200 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392200 prefixEnd_392200 := by exact prefixLift 392200
  have htrace : WordTrace (prefixWord ++ tailWord_392200) baseStart_392200 baseEnd_392200 := by
    simpa [prefixWord, tailWord_392200, baseEnd_392200] using wordTrace_append hprefix tailTrace_392200
  have hstable : (prefixWord ++ tailWord_392200).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392200).length < 2 ^ (prefixWord ++ tailWord_392200).sum := by decide
  have hdescent : baseEnd_392200 < baseStart_392200 := by decide
  rcases family_descends (prefixWord ++ tailWord_392200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392217 : List Nat := [1, 2, 1, 2, 1, 1, 5, 5, 3]
def baseStart_392217 : Nat := 118140960795 + 392217 * 2 ^ 59
def prefixEnd_392217 : Nat := 4983230072969 + 3 ^ 40 * 392217 * 2
def baseEnd_392217 : Nat := 89509263050932081281659

theorem tailTrace_392217 : CollatzResearch.WordTrace tailWord_392217 prefixEnd_392217 89509263050932081281659 := by
  unfold tailWord_392217
  simp only [CollatzResearch.WordTrace]
  refine ⟨14305329220072269175734905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9536886146714846117156603 14305329220072269175734905)
  ·
    refine ⟨10728996915054201881801179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14305329220072269175734905 10728996915054201881801179)
    ·
      refine ⟨16093495372581302822701769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10728996915054201881801179 16093495372581302822701769)
      ·
        refine ⟨12070121529435977117026327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16093495372581302822701769 12070121529435977117026327)
        ·
          refine ⟨18105182294153965675539491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12070121529435977117026327 18105182294153965675539491)
          ·
            refine ⟨27157773441230948513309237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18105182294153965675539491 27157773441230948513309237)
            ·
              refine ⟨2546041260115401423122741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27157773441230948513309237 2546041260115401423122741)
              ·
                refine ⟨238691368135818883417757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2546041260115401423122741 238691368135818883417757)
                ·
                  refine ⟨89509263050932081281659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238691368135818883417757 89509263050932081281659)
                  ·
                    rfl

theorem cell21_392217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 5, 3].length) (baseStart_392217 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392217 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392217 prefixEnd_392217 := by exact prefixLift 392217
  have htrace : WordTrace (prefixWord ++ tailWord_392217) baseStart_392217 baseEnd_392217 := by
    simpa [prefixWord, tailWord_392217, baseEnd_392217] using wordTrace_append hprefix tailTrace_392217
  have hstable : (prefixWord ++ tailWord_392217).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392217).length < 2 ^ (prefixWord ++ tailWord_392217).sum := by decide
  have hdescent : baseEnd_392217 < baseStart_392217 := by decide
  rcases family_descends (prefixWord ++ tailWord_392217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392234 : List Nat := [3, 1, 4, 1, 3, 1, 2, 1, 5]
def baseStart_392234 : Nat := 118140960795 + 392234 * 2 ^ 59
def prefixEnd_392234 : Nat := 4983230072969 + 3 ^ 40 * 392234 * 2
def baseEnd_392234 : Nat := 89513142682543829498291

theorem tailTrace_392234 : CollatzResearch.WordTrace tailWord_392234 prefixEnd_392234 89513142682543829498291 := by
  unfold tailWord_392234
  simp only [CollatzResearch.WordTrace]
  refine ⟨3576487315252670269775939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9537299507340454052735837 3576487315252670269775939)
  ·
    refine ⟨5364730972879005404663909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3576487315252670269775939 5364730972879005404663909)
    ·
      refine ⟨1005887057414813513374483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5364730972879005404663909 1005887057414813513374483)
      ·
        refine ⟨1508830586122220270061725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1005887057414813513374483 1508830586122220270061725)
        ·
          refine ⟨565811469795832601273147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1508830586122220270061725 565811469795832601273147)
          ·
            refine ⟨848717204693748901909721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565811469795832601273147 848717204693748901909721)
            ·
              refine ⟨636537903520311676432291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 848717204693748901909721 636537903520311676432291)
              ·
                refine ⟨954806855280467514648437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 636537903520311676432291 954806855280467514648437)
                ·
                  refine ⟨89513142682543829498291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 954806855280467514648437 89513142682543829498291)
                  ·
                    rfl

theorem cell21_392234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_392234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392234 prefixEnd_392234 := by exact prefixLift 392234
  have htrace : WordTrace (prefixWord ++ tailWord_392234) baseStart_392234 baseEnd_392234 := by
    simpa [prefixWord, tailWord_392234, baseEnd_392234] using wordTrace_append hprefix tailTrace_392234
  have hstable : (prefixWord ++ tailWord_392234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392234).length < 2 ^ (prefixWord ++ tailWord_392234).sum := by decide
  have hdescent : baseEnd_392234 < baseStart_392234 := by decide
  rcases family_descends (prefixWord ++ tailWord_392234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392245 : List Nat := [1, 3, 3, 1, 1, 1, 1, 10]
def baseStart_392245 : Nat := 118140960795 + 392245 * 2 ^ 59
def prefixEnd_392245 : Nat := 4983230072969 + 3 ^ 40 * 392245 * 2
def baseEnd_392245 : Nat := 29838551010803418271645

theorem tailTrace_392245 : CollatzResearch.WordTrace tailWord_392245 prefixEnd_392245 29838551010803418271645 := by
  unfold tailWord_392245
  simp only [CollatzResearch.WordTrace]
  refine ⟨14306350463970829957754189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9537566975980553305169459 14306350463970829957754189)
  ·
    refine ⟨5364881423989061234157821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14306350463970829957754189 5364881423989061234157821)
    ·
      refine ⟨2011830533995897962809183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5364881423989061234157821 2011830533995897962809183)
      ·
        refine ⟨3017745800993846944213775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2011830533995897962809183 3017745800993846944213775)
        ·
          refine ⟨4526618701490770416320663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3017745800993846944213775 4526618701490770416320663)
          ·
            refine ⟨6789928052236155624480995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4526618701490770416320663 6789928052236155624480995)
            ·
              refine ⟨10184892078354233436721493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6789928052236155624480995 10184892078354233436721493)
              ·
                refine ⟨29838551010803418271645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10184892078354233436721493 29838551010803418271645)
                ·
                  rfl

theorem cell21_392245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 10].length) (baseStart_392245 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392245 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392245 prefixEnd_392245 := by exact prefixLift 392245
  have htrace : WordTrace (prefixWord ++ tailWord_392245) baseStart_392245 baseEnd_392245 := by
    simpa [prefixWord, tailWord_392245, baseEnd_392245] using wordTrace_append hprefix tailTrace_392245
  have hstable : (prefixWord ++ tailWord_392245).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392245).length < 2 ^ (prefixWord ++ tailWord_392245).sum := by decide
  have hdescent : baseEnd_392245 < baseStart_392245 := by decide
  rcases family_descends (prefixWord ++ tailWord_392245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392276 : List Nat := [2, 4, 1, 1, 1, 1, 2, 2, 7]
def baseStart_392276 : Nat := 118140960795 + 392276 * 2 ^ 59
def prefixEnd_392276 : Nat := 4983230072969 + 3 ^ 40 * 392276 * 2
def baseEnd_392276 : Nat := 89522727654761089798205

theorem tailTrace_392276 : CollatzResearch.WordTrace tailWord_392276 prefixEnd_392276 89522727654761089798205 := by
  unfold tailWord_392276
  simp only [CollatzResearch.WordTrace]
  refine ⟨7153740563429261126066341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9538320751239014834755121 7153740563429261126066341)
  ·
    refine ⟨1341326355642986461137439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7153740563429261126066341 1341326355642986461137439)
    ·
      refine ⟨2011989533464479691706159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1341326355642986461137439 2011989533464479691706159)
      ·
        refine ⟨3017984300196719537559239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2011989533464479691706159 3017984300196719537559239)
        ·
          refine ⟨4526976450295079306338859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3017984300196719537559239 4526976450295079306338859)
          ·
            refine ⟨6790464675442618959508289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4526976450295079306338859 6790464675442618959508289)
            ·
              refine ⟨5092848506581964219631217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6790464675442618959508289 5092848506581964219631217)
              ·
                refine ⟨3819636379936473164723413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5092848506581964219631217 3819636379936473164723413)
                ·
                  refine ⟨89522727654761089798205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3819636379936473164723413 89522727654761089798205)
                  ·
                    rfl

theorem cell21_392276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_392276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392276 prefixEnd_392276 := by exact prefixLift 392276
  have htrace : WordTrace (prefixWord ++ tailWord_392276) baseStart_392276 baseEnd_392276 := by
    simpa [prefixWord, tailWord_392276, baseEnd_392276] using wordTrace_append hprefix tailTrace_392276
  have hstable : (prefixWord ++ tailWord_392276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392276).length < 2 ^ (prefixWord ++ tailWord_392276).sum := by decide
  have hdescent : baseEnd_392276 < baseStart_392276 := by decide
  rcases family_descends (prefixWord ++ tailWord_392276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392352 : List Nat := [2, 1, 1, 4, 2, 1, 2, 3, 5]
def baseStart_392352 : Nat := 118140960795 + 392352 * 2 ^ 59
def prefixEnd_392352 : Nat := 4983230072969 + 3 ^ 40 * 392352 * 2
def baseEnd_392352 : Nat := 89540071890201846531383

theorem tailTrace_392352 : CollatzResearch.WordTrace tailWord_392352 prefixEnd_392352 89540071890201846531383 := by
  unfold tailWord_392352
  simp only [CollatzResearch.WordTrace]
  refine ⟨7155126537291593615949655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9540168716388791487932873 7155126537291593615949655)
  ·
    refine ⟨10732689805937390423924483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7155126537291593615949655 10732689805937390423924483)
    ·
      refine ⟨16099034708906085635886725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10732689805937390423924483 16099034708906085635886725)
      ·
        refine ⟨3018569007919891056728761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16099034708906085635886725 3018569007919891056728761)
        ·
          refine ⟨2263926755939918292546571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3018569007919891056728761 2263926755939918292546571)
          ·
            refine ⟨3395890133909877438819857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2263926755939918292546571 3395890133909877438819857)
            ·
              refine ⟨2546917600432408079114893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3395890133909877438819857 2546917600432408079114893)
              ·
                refine ⟨955094100162153029668085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2546917600432408079114893 955094100162153029668085)
                ·
                  refine ⟨89540071890201846531383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 955094100162153029668085 89540071890201846531383)
                  ·
                    rfl

theorem cell21_392352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 5].length) (baseStart_392352 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392352 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392352 prefixEnd_392352 := by exact prefixLift 392352
  have htrace : WordTrace (prefixWord ++ tailWord_392352) baseStart_392352 baseEnd_392352 := by
    simpa [prefixWord, tailWord_392352, baseEnd_392352] using wordTrace_append hprefix tailTrace_392352
  have hstable : (prefixWord ++ tailWord_392352).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392352).length < 2 ^ (prefixWord ++ tailWord_392352).sum := by decide
  have hdescent : baseEnd_392352 < baseStart_392352 := by decide
  rcases family_descends (prefixWord ++ tailWord_392352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392369 : List Nat := [1, 2, 2, 5, 1, 2, 1, 2, 5]
def baseStart_392369 : Nat := 118140960795 + 392369 * 2 ^ 59
def prefixEnd_392369 : Nat := 4983230072969 + 3 ^ 40 * 392369 * 2
def baseEnd_392369 : Nat := 89543951521813594748015

theorem tailTrace_392369 : CollatzResearch.WordTrace tailWord_392369 prefixEnd_392369 89543951521813594748015 := by
  unfold tailWord_392369
  simp only [CollatzResearch.WordTrace]
  refine ⟨14310873115521599135268161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9540582077014399423512107 14310873115521599135268161)
  ·
    refine ⟨10733154836641199351451121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14310873115521599135268161 10733154836641199351451121)
    ·
      refine ⟨8049866127480899513588341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10733154836641199351451121 8049866127480899513588341)
      ·
        refine ⟨754674949451334329398907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8049866127480899513588341 754674949451334329398907)
        ·
          refine ⟨1132012424177001494098361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754674949451334329398907 1132012424177001494098361)
          ·
            refine ⟨849009318132751120573771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1132012424177001494098361 849009318132751120573771)
            ·
              refine ⟨1273513977199126680860657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849009318132751120573771 1273513977199126680860657)
              ·
                refine ⟨955135482899345010645493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1273513977199126680860657 955135482899345010645493)
                ·
                  refine ⟨89543951521813594748015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 955135482899345010645493 89543951521813594748015)
                  ·
                    rfl

theorem cell21_392369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 2, 5].length) (baseStart_392369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392369 prefixEnd_392369 := by exact prefixLift 392369
  have htrace : WordTrace (prefixWord ++ tailWord_392369) baseStart_392369 baseEnd_392369 := by
    simpa [prefixWord, tailWord_392369, baseEnd_392369] using wordTrace_append hprefix tailTrace_392369
  have hstable : (prefixWord ++ tailWord_392369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392369).length < 2 ^ (prefixWord ++ tailWord_392369).sum := by decide
  have hdescent : baseEnd_392369 < baseStart_392369 := by decide
  rcases family_descends (prefixWord ++ tailWord_392369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392428 : List Nat := [2, 2, 1, 1, 2, 4, 2, 2, 5]
def baseStart_392428 : Nat := 118140960795 + 392428 * 2 ^ 59
def prefixEnd_392428 : Nat := 4983230072969 + 3 ^ 40 * 392428 * 2
def baseEnd_392428 : Nat := 89557416125642603264561

theorem tailTrace_392428 : CollatzResearch.WordTrace tailWord_392428 prefixEnd_392428 89557416125642603264561 := by
  unfold tailWord_392428
  simp only [CollatzResearch.WordTrace]
  refine ⟨7156512511153926105832969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9542016681538568141110625 7156512511153926105832969)
  ·
    refine ⟨5367384383365444579374727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7156512511153926105832969 5367384383365444579374727)
    ·
      refine ⟨8051076575048166869062091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5367384383365444579374727 8051076575048166869062091)
      ·
        refine ⟨12076614862572250303593137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8051076575048166869062091 12076614862572250303593137)
        ·
          refine ⟨9057461146929187727694853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12076614862572250303593137 9057461146929187727694853)
          ·
            refine ⟨1698273965049222698942785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9057461146929187727694853 1698273965049222698942785)
            ·
              refine ⟨1273705473786917024207089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1698273965049222698942785 1273705473786917024207089)
              ·
                refine ⟨955279105340187768155317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1273705473786917024207089 955279105340187768155317)
                ·
                  refine ⟨89557416125642603264561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 955279105340187768155317 89557416125642603264561)
                  ·
                    rfl

theorem cell21_392428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 5].length) (baseStart_392428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392428 prefixEnd_392428 := by exact prefixLift 392428
  have htrace : WordTrace (prefixWord ++ tailWord_392428) baseStart_392428 baseEnd_392428 := by
    simpa [prefixWord, tailWord_392428, baseEnd_392428] using wordTrace_append hprefix tailTrace_392428
  have hstable : (prefixWord ++ tailWord_392428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392428).length < 2 ^ (prefixWord ++ tailWord_392428).sum := by decide
  have hdescent : baseEnd_392428 < baseStart_392428 := by decide
  rcases family_descends (prefixWord ++ tailWord_392428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392431 : List Nat := [1, 1, 2, 1, 7, 2, 2, 5]
def baseStart_392431 : Nat := 118140960795 + 392431 * 2 ^ 59
def prefixEnd_392431 : Nat := 4983230072969 + 3 ^ 40 * 392431 * 2
def baseEnd_392431 : Nat := 29852700255505088238185

theorem tailTrace_392431 : CollatzResearch.WordTrace tailWord_392431 prefixEnd_392431 29852700255505088238185 := by
  unfold tailWord_392431
  simp only [CollatzResearch.WordTrace]
  refine ⟨14313134441296983724025147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9542089627531322482683431 14313134441296983724025147)
  ·
    refine ⟨21469701661945475586037721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14313134441296983724025147 21469701661945475586037721)
    ·
      refine ⟨16102276246459106689528291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21469701661945475586037721 16102276246459106689528291)
      ·
        refine ⟨24153414369688660034292437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16102276246459106689528291 24153414369688660034292437)
        ·
          refine ⟨566095649289577969553729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 24153414369688660034292437 566095649289577969553729)
          ·
            refine ⟨424571736967183477165297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 566095649289577969553729 424571736967183477165297)
            ·
              refine ⟨318428802725387607873973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 424571736967183477165297 318428802725387607873973)
              ·
                refine ⟨29852700255505088238185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 318428802725387607873973 29852700255505088238185)
                ·
                  rfl

theorem cell21_392431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 2, 5].length) (baseStart_392431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392431 prefixEnd_392431 := by exact prefixLift 392431
  have htrace : WordTrace (prefixWord ++ tailWord_392431) baseStart_392431 baseEnd_392431 := by
    simpa [prefixWord, tailWord_392431, baseEnd_392431] using wordTrace_append hprefix tailTrace_392431
  have hstable : (prefixWord ++ tailWord_392431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392431).length < 2 ^ (prefixWord ++ tailWord_392431).sum := by decide
  have hdescent : baseEnd_392431 < baseStart_392431 := by decide
  rcases family_descends (prefixWord ++ tailWord_392431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392442 : List Nat := [3, 1, 1, 1, 1, 4, 1, 1, 8]
def baseStart_392442 : Nat := 118140960795 + 392442 * 2 ^ 59
def prefixEnd_392442 : Nat := 4983230072969 + 3 ^ 40 * 392442 * 2
def baseEnd_392442 : Nat := 89560611116381690031199

theorem tailTrace_392442 : CollatzResearch.WordTrace tailWord_392442 prefixEnd_392442 89560611116381690031199 := by
  unfold tailWord_392442
  simp only [CollatzResearch.WordTrace]
  refine ⟨3578383911064283150668895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9542357096171421735117053 3578383911064283150668895)
  ·
    refine ⟨5367575866596424726003343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3578383911064283150668895 5367575866596424726003343)
    ·
      refine ⟨8051363799894637089005015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5367575866596424726003343 8051363799894637089005015)
      ·
        refine ⟨12077045699841955633507523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8051363799894637089005015 12077045699841955633507523)
        ·
          refine ⟨18115568549762933450261285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12077045699841955633507523 18115568549762933450261285)
          ·
            refine ⟨3396669103080550021923991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18115568549762933450261285 3396669103080550021923991)
            ·
              refine ⟨5095003654620825032885987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3396669103080550021923991 5095003654620825032885987)
              ·
                refine ⟨7642505481931237549328981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5095003654620825032885987 7642505481931237549328981)
                ·
                  refine ⟨89560611116381690031199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7642505481931237549328981 89560611116381690031199)
                  ·
                    rfl

theorem cell21_392442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_392442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392442 prefixEnd_392442 := by exact prefixLift 392442
  have htrace : WordTrace (prefixWord ++ tailWord_392442) baseStart_392442 baseEnd_392442 := by
    simpa [prefixWord, tailWord_392442, baseEnd_392442] using wordTrace_append hprefix tailTrace_392442
  have hstable : (prefixWord ++ tailWord_392442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392442).length < 2 ^ (prefixWord ++ tailWord_392442).sum := by decide
  have hdescent : baseEnd_392442 < baseStart_392442 := by decide
  rcases family_descends (prefixWord ++ tailWord_392442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392476 : List Nat := [2, 2, 3, 1, 1, 1, 6, 1, 4]
def baseStart_392476 : Nat := 118140960795 + 392476 * 2 ^ 59
def prefixEnd_392476 : Nat := 4983230072969 + 3 ^ 40 * 392476 * 2
def baseEnd_392476 : Nat := 89568370379605186464463

theorem tailTrace_392476 : CollatzResearch.WordTrace tailWord_392476 prefixEnd_392476 89568370379605186464463 := by
  unfold tailWord_392476
  simp only [CollatzResearch.WordTrace]
  refine ⟨7157387863066978204706641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9543183817422637606275521 7157387863066978204706641)
  ·
    refine ⟨5368040897300233653529981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7157387863066978204706641 5368040897300233653529981)
    ·
      refine ⟨2013015336487587620073743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5368040897300233653529981 2013015336487587620073743)
      ·
        refine ⟨3019523004731381430110615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2013015336487587620073743 3019523004731381430110615)
        ·
          refine ⟨4529284507097072145165923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3019523004731381430110615 4529284507097072145165923)
          ·
            refine ⟨6793926760645608217748885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4529284507097072145165923 6793926760645608217748885)
            ·
              refine ⟨318465316905262885206979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6793926760645608217748885 318465316905262885206979)
              ·
                refine ⟨477697975357894327810469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318465316905262885206979 477697975357894327810469)
                ·
                  refine ⟨89568370379605186464463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 477697975357894327810469 89568370379605186464463)
                  ·
                    rfl

theorem cell21_392476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 6, 1, 4].length) (baseStart_392476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392476 prefixEnd_392476 := by exact prefixLift 392476
  have htrace : WordTrace (prefixWord ++ tailWord_392476) baseStart_392476 baseEnd_392476 := by
    simpa [prefixWord, tailWord_392476, baseEnd_392476] using wordTrace_append hprefix tailTrace_392476
  have hstable : (prefixWord ++ tailWord_392476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392476).length < 2 ^ (prefixWord ++ tailWord_392476).sum := by decide
  have hdescent : baseEnd_392476 < baseStart_392476 := by decide
  rcases family_descends (prefixWord ++ tailWord_392476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392490 : List Nat := [3, 1, 4, 2, 1, 1, 2, 7]
def baseStart_392490 : Nat := 118140960795 + 392490 * 2 ^ 59
def prefixEnd_392490 : Nat := 4983230072969 + 3 ^ 40 * 392490 * 2
def baseEnd_392490 : Nat := 29857188456781424410367

theorem tailTrace_392490 : CollatzResearch.WordTrace tailWord_392490 prefixEnd_392490 29857188456781424410367 := by
  unfold tailWord_392490
  simp only [CollatzResearch.WordTrace]
  refine ⟨3578821587020809200105731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9543524232055491200281949 3578821587020809200105731)
  ·
    refine ⟨5368232380531213800158597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3578821587020809200105731 5368232380531213800158597)
    ·
      refine ⟨1006543571349602587529737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5368232380531213800158597 1006543571349602587529737)
      ·
        refine ⟨754907678512201940647303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1006543571349602587529737 754907678512201940647303)
        ·
          refine ⟨1132361517768302910970955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754907678512201940647303 1132361517768302910970955)
          ·
            refine ⟨1698542276652454366456433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1132361517768302910970955 1698542276652454366456433)
            ·
              refine ⟨1273906707489340774842325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1698542276652454366456433 1273906707489340774842325)
              ·
                refine ⟨29857188456781424410367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1273906707489340774842325 29857188456781424410367)
                ·
                  rfl

theorem cell21_392490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_392490 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392490 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392490 prefixEnd_392490 := by exact prefixLift 392490
  have htrace : WordTrace (prefixWord ++ tailWord_392490) baseStart_392490 baseEnd_392490 := by
    simpa [prefixWord, tailWord_392490, baseEnd_392490] using wordTrace_append hprefix tailTrace_392490
  have hstable : (prefixWord ++ tailWord_392490).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392490).length < 2 ^ (prefixWord ++ tailWord_392490).sum := by decide
  have hdescent : baseEnd_392490 < baseStart_392490 := by decide
  rcases family_descends (prefixWord ++ tailWord_392490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392535 : List Nat := [1, 1, 3, 2, 3, 2, 2, 3, 4]
def baseStart_392535 : Nat := 118140960795 + 392535 * 2 ^ 59
def prefixEnd_392535 : Nat := 4983230072969 + 3 ^ 40 * 392535 * 2
def baseEnd_392535 : Nat := 89581834983434194981009

theorem tailTrace_392535 : CollatzResearch.WordTrace tailWord_392535 prefixEnd_392535 89581834983434194981009 := by
  unfold tailWord_392535
  simp only [CollatzResearch.WordTrace]
  refine ⟨14316927632920209485811059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9544618421946806323874039 14316927632920209485811059)
  ·
    refine ⟨21475391449380314228716589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14316927632920209485811059 21475391449380314228716589)
    ·
      refine ⟨8053271793517617835768721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21475391449380314228716589 8053271793517617835768721)
      ·
        refine ⟨6039953845138213376826541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8053271793517617835768721 6039953845138213376826541)
        ·
          refine ⟨2264982691926830016309953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6039953845138213376826541 2264982691926830016309953)
          ·
            refine ⟨1698737018945122512232465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2264982691926830016309953 1698737018945122512232465)
            ·
              refine ⟨1274052764208841884174349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1698737018945122512232465 1274052764208841884174349)
              ·
                refine ⟨477769786578315706565381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1274052764208841884174349 477769786578315706565381)
                ·
                  refine ⟨89581834983434194981009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 477769786578315706565381 89581834983434194981009)
                  ·
                    rfl

theorem cell21_392535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 3, 4].length) (baseStart_392535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392535 prefixEnd_392535 := by exact prefixLift 392535
  have htrace : WordTrace (prefixWord ++ tailWord_392535) baseStart_392535 baseEnd_392535 := by
    simpa [prefixWord, tailWord_392535, baseEnd_392535] using wordTrace_append hprefix tailTrace_392535
  have hstable : (prefixWord ++ tailWord_392535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392535).length < 2 ^ (prefixWord ++ tailWord_392535).sum := by decide
  have hdescent : baseEnd_392535 < baseStart_392535 := by decide
  rcases family_descends (prefixWord ++ tailWord_392535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392541 : List Nat := [1, 4, 5, 1, 1, 1, 3, 5]
def baseStart_392541 : Nat := 118140960795 + 392541 * 2 ^ 59
def prefixEnd_392541 : Nat := 4983230072969 + 3 ^ 40 * 392541 * 2
def baseEnd_392541 : Nat := 29861068088393172626999

theorem tailTrace_392541 : CollatzResearch.WordTrace tailWord_392541 prefixEnd_392541 29861068088393172626999 := by
  unfold tailWord_392541
  simp only [CollatzResearch.WordTrace]
  refine ⟨14317146470898472510529477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9544764313932315007019651 14317146470898472510529477)
  ·
    refine ⟨2684464963293463595724277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14317146470898472510529477 2684464963293463595724277)
    ·
      refine ⟨251668590308762212099151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2684464963293463595724277 251668590308762212099151)
      ·
        refine ⟨377502885463143318148727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251668590308762212099151 377502885463143318148727)
        ·
          refine ⟨566254328194714977223091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377502885463143318148727 566254328194714977223091)
          ·
            refine ⟨849381492292072465834637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566254328194714977223091 849381492292072465834637)
            ·
              refine ⟨318518059609527174687989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 849381492292072465834637 318518059609527174687989)
              ·
                refine ⟨29861068088393172626999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 318518059609527174687989 29861068088393172626999)
                ·
                  rfl

theorem cell21_392541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 3, 5].length) (baseStart_392541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392541 prefixEnd_392541 := by exact prefixLift 392541
  have htrace : WordTrace (prefixWord ++ tailWord_392541) baseStart_392541 baseEnd_392541 := by
    simpa [prefixWord, tailWord_392541, baseEnd_392541] using wordTrace_append hprefix tailTrace_392541
  have hstable : (prefixWord ++ tailWord_392541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392541).length < 2 ^ (prefixWord ++ tailWord_392541).sum := by decide
  have hdescent : baseEnd_392541 < baseStart_392541 := by decide
  rcases family_descends (prefixWord ++ tailWord_392541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392580 : List Nat := [2, 3, 2, 1, 1, 3, 1, 3, 5]
def baseStart_392580 : Nat := 118140960795 + 392580 * 2 ^ 59
def prefixEnd_392580 : Nat := 4983230072969 + 3 ^ 40 * 392580 * 2
def baseEnd_392580 : Nat := 89592104596524116730917

theorem tailTrace_392580 : CollatzResearch.WordTrace tailWord_392580 prefixEnd_392580 89592104596524116730917 := by
  unfold tailWord_392580
  simp only [CollatzResearch.WordTrace]
  refine ⟨7159284458878591085599597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9545712611838121447466129 7159284458878591085599597)
  ·
    refine ⟨2684731672079471657099849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7159284458878591085599597 2684731672079471657099849)
    ·
      refine ⟨2013548754059603742824887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2684731672079471657099849 2013548754059603742824887)
      ·
        refine ⟨3020323131089405614237331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2013548754059603742824887 3020323131089405614237331)
        ·
          refine ⟨4530484696634108421355997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3020323131089405614237331 4530484696634108421355997)
          ·
            refine ⟨1698931761237790658008499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4530484696634108421355997 1698931761237790658008499)
            ·
              refine ⟨2548397641856685987012749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1698931761237790658008499 2548397641856685987012749)
              ·
                refine ⟨955649115696257245129781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2548397641856685987012749 955649115696257245129781)
                ·
                  refine ⟨89592104596524116730917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 955649115696257245129781 89592104596524116730917)
                  ·
                    rfl

theorem cell21_392580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 3, 5].length) (baseStart_392580 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392580 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392580 prefixEnd_392580 := by exact prefixLift 392580
  have htrace : WordTrace (prefixWord ++ tailWord_392580) baseStart_392580 baseEnd_392580 := by
    simpa [prefixWord, tailWord_392580, baseEnd_392580] using wordTrace_append hprefix tailTrace_392580
  have hstable : (prefixWord ++ tailWord_392580).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392580).length < 2 ^ (prefixWord ++ tailWord_392580).sum := by decide
  have hdescent : baseEnd_392580 < baseStart_392580 := by decide
  rcases family_descends (prefixWord ++ tailWord_392580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392600 : List Nat := [2, 1, 2, 5, 3, 1, 2, 5]
def baseStart_392600 : Nat := 118140960795 + 392600 * 2 ^ 59
def prefixEnd_392600 : Nat := 4983230072969 + 3 ^ 40 * 392600 * 2
def baseEnd_392600 : Nat := 29865556289669508799181

theorem tailTrace_392600 : CollatzResearch.WordTrace tailWord_392600 prefixEnd_392600 29865556289669508799181 := by
  unfold tailWord_392600
  simp only [CollatzResearch.WordTrace]
  refine ⟨7159649188842362793463627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9546198918456483724618169 7159649188842362793463627)
  ·
    refine ⟨10739473783263544190195441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7159649188842362793463627 10739473783263544190195441)
    ·
      refine ⟨8054605337447658142646581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10739473783263544190195441 8054605337447658142646581)
      ·
        refine ⟨755119250385717950873117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8054605337447658142646581 755119250385717950873117)
        ·
          refine ⟨283169718894644231577419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 755119250385717950873117 283169718894644231577419)
          ·
            refine ⟨424754578341966347366129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283169718894644231577419 424754578341966347366129)
            ·
              refine ⟨318565933756474760524597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 424754578341966347366129 318565933756474760524597)
              ·
                refine ⟨29865556289669508799181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 318565933756474760524597 29865556289669508799181)
                ·
                  rfl

theorem cell21_392600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 3, 1, 2, 5].length) (baseStart_392600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392600 prefixEnd_392600 := by exact prefixLift 392600
  have htrace : WordTrace (prefixWord ++ tailWord_392600) baseStart_392600 baseEnd_392600 := by
    simpa [prefixWord, tailWord_392600, baseEnd_392600] using wordTrace_append hprefix tailTrace_392600
  have hstable : (prefixWord ++ tailWord_392600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392600).length < 2 ^ (prefixWord ++ tailWord_392600).sum := by decide
  have hdescent : baseEnd_392600 < baseStart_392600 := by decide
  rcases family_descends (prefixWord ++ tailWord_392600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392690 : List Nat := [3, 2, 1, 4, 1, 2, 1, 4, 3]
def baseStart_392690 : Nat := 118140960795 + 392690 * 2 ^ 59
def prefixEnd_392690 : Nat := 4983230072969 + 3 ^ 40 * 392690 * 2
def baseEnd_392690 : Nat := 89617208095188369897359

theorem tailTrace_392690 : CollatzResearch.WordTrace tailWord_392690 prefixEnd_392690 89617208095188369897359 := by
  unfold tailWord_392690
  simp only [CollatzResearch.WordTrace]
  refine ⟨3580645236839667739425881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9548387298239113971802349 3580645236839667739425881)
  ·
    refine ⟨2685483927629750804569411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3580645236839667739425881 2685483927629750804569411)
    ·
      refine ⟨4028225891444626206854117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2685483927629750804569411 4028225891444626206854117)
      ·
        refine ⟨755292354645867413785147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4028225891444626206854117 755292354645867413785147)
        ·
          refine ⟨1132938531968801120677721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 755292354645867413785147 1132938531968801120677721)
          ·
            refine ⟨849703898976600840508291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1132938531968801120677721 849703898976600840508291)
            ·
              refine ⟨1274555848464901260762437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 849703898976600840508291 1274555848464901260762437)
              ·
                refine ⟨238979221587168986392957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1274555848464901260762437 238979221587168986392957)
                ·
                  refine ⟨89617208095188369897359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 238979221587168986392957 89617208095188369897359)
                  ·
                    rfl

theorem cell21_392690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 1, 4, 3].length) (baseStart_392690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392690 prefixEnd_392690 := by exact prefixLift 392690
  have htrace : WordTrace (prefixWord ++ tailWord_392690) baseStart_392690 baseEnd_392690 := by
    simpa [prefixWord, tailWord_392690, baseEnd_392690] using wordTrace_append hprefix tailTrace_392690
  have hstable : (prefixWord ++ tailWord_392690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392690).length < 2 ^ (prefixWord ++ tailWord_392690).sum := by decide
  have hdescent : baseEnd_392690 < baseStart_392690 := by decide
  rcases family_descends (prefixWord ++ tailWord_392690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392701 : List Nat := [1, 4, 1, 1, 1, 4, 3, 6]
def baseStart_392701 : Nat := 118140960795 + 392701 * 2 ^ 59
def prefixEnd_392701 : Nat := 4983230072969 + 3 ^ 40 * 392701 * 2
def baseEnd_392701 : Nat := 29873239481684931738001

theorem tailTrace_392701 : CollatzResearch.WordTrace tailWord_392701 prefixEnd_392701 29873239481684931738001 := by
  unfold tailWord_392701
  simp only [CollatzResearch.WordTrace]
  refine ⟨14322982150318819836353957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9548654766879213224235971 14322982150318819836353957)
  ·
    refine ⟨2685559153184778719316367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14322982150318819836353957 2685559153184778719316367)
    ·
      refine ⟨4028338729777168078974551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2685559153184778719316367 4028338729777168078974551)
      ·
        refine ⟨6042508094665752118461827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4028338729777168078974551 6042508094665752118461827)
        ·
          refine ⟨9063762141998628177692741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6042508094665752118461827 9063762141998628177692741)
          ·
            refine ⟨1699455401624742783317389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9063762141998628177692741 1699455401624742783317389)
            ·
              refine ⟨637295775609278543744021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1699455401624742783317389 637295775609278543744021)
              ·
                refine ⟨29873239481684931738001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 637295775609278543744021 29873239481684931738001)
                ·
                  rfl

theorem cell21_392701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 3, 6].length) (baseStart_392701 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392701 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392701 prefixEnd_392701 := by exact prefixLift 392701
  have htrace : WordTrace (prefixWord ++ tailWord_392701) baseStart_392701 baseEnd_392701 := by
    simpa [prefixWord, tailWord_392701, baseEnd_392701] using wordTrace_append hprefix tailTrace_392701
  have hstable : (prefixWord ++ tailWord_392701).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392701).length < 2 ^ (prefixWord ++ tailWord_392701).sum := by decide
  have hdescent : baseEnd_392701 < baseStart_392701 := by decide
  rcases family_descends (prefixWord ++ tailWord_392701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392814 : List Nat := [4, 1, 2, 2, 4, 1, 2, 1, 4]
def baseStart_392814 : Nat := 118140960795 + 392814 * 2 ^ 59
def prefixEnd_392814 : Nat := 4983230072969 + 3 ^ 40 * 392814 * 2
def baseEnd_392814 : Nat := 89645506584591709830439

theorem tailTrace_392814 : CollatzResearch.WordTrace tailWord_392814 prefixEnd_392814 89645506584591709830439 := by
  unfold tailWord_392814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1790887949863680016902187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9551402399272960090144997 1790887949863680016902187)
  ·
    refine ⟨2686331924795520025353281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1790887949863680016902187 2686331924795520025353281)
    ·
      refine ⟨2014748943596640019014961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2686331924795520025353281 2014748943596640019014961)
      ·
        refine ⟨1511061707697480014261221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2014748943596640019014961 1511061707697480014261221)
        ·
          refine ⟨283324070193277502673979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1511061707697480014261221 283324070193277502673979)
          ·
            refine ⟨424986105289916254010969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283324070193277502673979 424986105289916254010969)
            ·
              refine ⟨318739578967437190508227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 424986105289916254010969 318739578967437190508227)
              ·
                refine ⟨478109368451155785762341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318739578967437190508227 478109368451155785762341)
                ·
                  refine ⟨89645506584591709830439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 478109368451155785762341 89645506584591709830439)
                  ·
                    rfl

theorem cell21_392814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_392814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392814 prefixEnd_392814 := by exact prefixLift 392814
  have htrace : WordTrace (prefixWord ++ tailWord_392814) baseStart_392814 baseEnd_392814 := by
    simpa [prefixWord, tailWord_392814, baseEnd_392814] using wordTrace_append hprefix tailTrace_392814
  have hstable : (prefixWord ++ tailWord_392814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392814).length < 2 ^ (prefixWord ++ tailWord_392814).sum := by decide
  have hdescent : baseEnd_392814 < baseStart_392814 := by decide
  rcases family_descends (prefixWord ++ tailWord_392814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392867 : List Nat := [1, 1, 1, 4, 1, 1, 4, 3, 5]
def baseStart_392867 : Nat := 118140960795 + 392867 * 2 ^ 59
def prefixEnd_392867 : Nat := 4983230072969 + 3 ^ 40 * 392867 * 2
def baseEnd_392867 : Nat := 89657601906675395446997

theorem tailTrace_392867 : CollatzResearch.WordTrace tailWord_392867 prefixEnd_392867 89657601906675395446997 := by
  unfold tailWord_392867
  simp only [CollatzResearch.WordTrace]
  refine ⟨14329036667717430186896855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9552691111811620124597903 14329036667717430186896855)
  ·
    refine ⟨21493555001576145280345283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14329036667717430186896855 21493555001576145280345283)
    ·
      refine ⟨32240332502364217920517925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21493555001576145280345283 32240332502364217920517925)
      ·
        refine ⟨6045062344193290860097111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32240332502364217920517925 6045062344193290860097111)
        ·
          refine ⟨9067593516289936290145667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6045062344193290860097111 9067593516289936290145667)
          ·
            refine ⟨13601390274434904435218501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9067593516289936290145667 13601390274434904435218501)
            ·
              refine ⟨2550260676456544581603469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13601390274434904435218501 2550260676456544581603469)
              ·
                refine ⟨956347753671204218101301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2550260676456544581603469 956347753671204218101301)
                ·
                  refine ⟨89657601906675395446997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 956347753671204218101301 89657601906675395446997)
                  ·
                    rfl

theorem cell21_392867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 3, 5].length) (baseStart_392867 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392867 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392867 prefixEnd_392867 := by exact prefixLift 392867
  have htrace : WordTrace (prefixWord ++ tailWord_392867) baseStart_392867 baseEnd_392867 := by
    simpa [prefixWord, tailWord_392867, baseEnd_392867] using wordTrace_append hprefix tailTrace_392867
  have hstable : (prefixWord ++ tailWord_392867).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392867).length < 2 ^ (prefixWord ++ tailWord_392867).sum := by decide
  have hdescent : baseEnd_392867 < baseStart_392867 := by decide
  rcases family_descends (prefixWord ++ tailWord_392867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392943 : List Nat := [1, 1, 2, 1, 5, 1, 1, 4, 5]
def baseStart_392943 : Nat := 118140960795 + 392943 * 2 ^ 59
def prefixEnd_392943 : Nat := 4983230072969 + 3 ^ 40 * 392943 * 2
def baseEnd_392943 : Nat := 89674946142116152180175

theorem tailTrace_392943 : CollatzResearch.WordTrace tailWord_392943 prefixEnd_392943 89674946142116152180175 := by
  unfold tailWord_392943
  simp only [CollatzResearch.WordTrace]
  refine ⟨14331808615442095166663483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9554539076961396777775655 14331808615442095166663483)
  ·
    refine ⟨21497712923163142749995225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14331808615442095166663483 21497712923163142749995225)
    ·
      refine ⟨16123284692372357062496419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21497712923163142749995225 16123284692372357062496419)
      ·
        refine ⟨24184927038558535593744629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16123284692372357062496419 24184927038558535593744629)
        ·
          refine ⟨2267336909864862711913559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24184927038558535593744629 2267336909864862711913559)
          ·
            refine ⟨3401005364797294067870339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2267336909864862711913559 3401005364797294067870339)
            ·
              refine ⟨5101508047195941101805509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3401005364797294067870339 5101508047195941101805509)
              ·
                refine ⟨956532758849238956588533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5101508047195941101805509 956532758849238956588533)
                ·
                  refine ⟨89674946142116152180175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 956532758849238956588533 89674946142116152180175)
                  ·
                    rfl

theorem cell21_392943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 5].length) (baseStart_392943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392943 prefixEnd_392943 := by exact prefixLift 392943
  have htrace : WordTrace (prefixWord ++ tailWord_392943) baseStart_392943 baseEnd_392943 := by
    simpa [prefixWord, tailWord_392943, baseEnd_392943] using wordTrace_append hprefix tailTrace_392943
  have hstable : (prefixWord ++ tailWord_392943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392943).length < 2 ^ (prefixWord ++ tailWord_392943).sum := by decide
  have hdescent : baseEnd_392943 < baseStart_392943 := by decide
  rcases family_descends (prefixWord ++ tailWord_392943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392974 : List Nat := [4, 1, 1, 2, 1, 1, 4, 1, 6]
def baseStart_392974 : Nat := 118140960795 + 392974 * 2 ^ 59
def prefixEnd_392974 : Nat := 4983230072969 + 3 ^ 40 * 392974 * 2
def baseEnd_392974 : Nat := 89682020764466987163445

theorem tailTrace_392974 : CollatzResearch.WordTrace tailWord_392974 prefixEnd_392974 89682020764466987163445 := by
  unfold tailWord_392974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1791617409791223432630247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9555292852219858307361317 1791617409791223432630247)
  ·
    refine ⟨2687426114686835148945371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1791617409791223432630247 2687426114686835148945371)
    ·
      refine ⟨4031139172030252723418057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2687426114686835148945371 4031139172030252723418057)
      ·
        refine ⟨3023354379022689542563543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4031139172030252723418057 3023354379022689542563543)
        ·
          refine ⟨4535031568534034313845315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3023354379022689542563543 4535031568534034313845315)
          ·
            refine ⟨6802547352801051470767973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4535031568534034313845315 6802547352801051470767973)
            ·
              refine ⟨1275477628650197150768995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6802547352801051470767973 1275477628650197150768995)
              ·
                refine ⟨1913216442975295726153493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1275477628650197150768995 1913216442975295726153493)
                ·
                  refine ⟨89682020764466987163445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1913216442975295726153493 89682020764466987163445)
                  ·
                    rfl

theorem cell21_392974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 4, 1, 6].length) (baseStart_392974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392974 prefixEnd_392974 := by exact prefixLift 392974
  have htrace : WordTrace (prefixWord ++ tailWord_392974) baseStart_392974 baseEnd_392974 := by
    simpa [prefixWord, tailWord_392974, baseEnd_392974] using wordTrace_append hprefix tailTrace_392974
  have hstable : (prefixWord ++ tailWord_392974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392974).length < 2 ^ (prefixWord ++ tailWord_392974).sum := by decide
  have hdescent : baseEnd_392974 < baseStart_392974 := by decide
  rcases family_descends (prefixWord ++ tailWord_392974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392980 : List Nat := [2, 4, 4, 1, 1, 1, 2, 6]
def baseStart_392980 : Nat := 118140960795 + 392980 * 2 ^ 59
def prefixEnd_392980 : Nat := 4983230072969 + 3 ^ 40 * 392980 * 2
def baseEnd_392980 : Nat := 29894463348737436687811

theorem tailTrace_392980 : CollatzResearch.WordTrace tailWord_392980 prefixEnd_392980 29894463348737436687811 := by
  unfold tailWord_392980
  simp only [CollatzResearch.WordTrace]
  refine ⟨7166579058154025242880197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9555438744205366990506929 7166579058154025242880197)
  ·
    refine ⟨1343733573403879733040037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7166579058154025242880197 1343733573403879733040037)
    ·
      refine ⟨251950045013227449945007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1343733573403879733040037 251950045013227449945007)
      ·
        refine ⟨377925067519841174917511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 251950045013227449945007 377925067519841174917511)
        ·
          refine ⟨566887601279761762376267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377925067519841174917511 566887601279761762376267)
          ·
            refine ⟨850331401919642643564401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566887601279761762376267 850331401919642643564401)
            ·
              refine ⟨637748551439731982673301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 850331401919642643564401 637748551439731982673301)
              ·
                refine ⟨29894463348737436687811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 637748551439731982673301 29894463348737436687811)
                ·
                  rfl

theorem cell21_392980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 6].length) (baseStart_392980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_392980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_392980 prefixEnd_392980 := by exact prefixLift 392980
  have htrace : WordTrace (prefixWord ++ tailWord_392980) baseStart_392980 baseEnd_392980 := by
    simpa [prefixWord, tailWord_392980, baseEnd_392980] using wordTrace_append hprefix tailTrace_392980
  have hstable : (prefixWord ++ tailWord_392980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392980).length < 2 ^ (prefixWord ++ tailWord_392980).sum := by decide
  have hdescent : baseEnd_392980 < baseStart_392980 := by decide
  rcases family_descends (prefixWord ++ tailWord_392980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393050 : List Nat := [3, 1, 1, 2, 1, 3, 1, 5, 4]
def baseStart_393050 : Nat := 118140960795 + 393050 * 2 ^ 59
def prefixEnd_393050 : Nat := 4983230072969 + 3 ^ 40 * 393050 * 2
def baseEnd_393050 : Nat := 89699364999907743896623

theorem tailTrace_393050 : CollatzResearch.WordTrace tailWord_393050 prefixEnd_393050 89699364999907743896623 := by
  unfold tailWord_393050
  simp only [CollatzResearch.WordTrace]
  refine ⟨3583927806513613110202151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9557140817369634960539069 3583927806513613110202151)
  ·
    refine ⟨5375891709770419665303227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3583927806513613110202151 5375891709770419665303227)
    ·
      refine ⟨8063837564655629497954841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5375891709770419665303227 8063837564655629497954841)
      ·
        refine ⟨6047878173491722123466131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8063837564655629497954841 6047878173491722123466131)
        ·
          refine ⟨9071817260237583185199197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6047878173491722123466131 9071817260237583185199197)
          ·
            refine ⟨3401931472589093694449699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9071817260237583185199197 3401931472589093694449699)
            ·
              refine ⟨5102897208883640541674549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3401931472589093694449699 5102897208883640541674549)
              ·
                refine ⟨478396613332841300781989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5102897208883640541674549 478396613332841300781989)
                ·
                  refine ⟨89699364999907743896623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 478396613332841300781989 89699364999907743896623)
                  ·
                    rfl

theorem cell21_393050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_393050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_393050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_393050 prefixEnd_393050 := by exact prefixLift 393050
  have htrace : WordTrace (prefixWord ++ tailWord_393050) baseStart_393050 baseEnd_393050 := by
    simpa [prefixWord, tailWord_393050, baseEnd_393050] using wordTrace_append hprefix tailTrace_393050
  have hstable : (prefixWord ++ tailWord_393050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393050).length < 2 ^ (prefixWord ++ tailWord_393050).sum := by decide
  have hdescent : baseEnd_393050 < baseStart_393050 := by decide
  rcases family_descends (prefixWord ++ tailWord_393050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393070 : List Nat := [4, 1, 2, 3, 1, 2, 2, 3, 3]
def baseStart_393070 : Nat := 118140960795 + 393070 * 2 ^ 59
def prefixEnd_393070 : Nat := 4983230072969 + 3 ^ 40 * 393070 * 2
def baseEnd_393070 : Nat := 89703929272392153563249

theorem tailTrace_393070 : CollatzResearch.WordTrace tailWord_393070 prefixEnd_393070 89703929272392153563249 := by
  unfold tailWord_393070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1792055085747749482067083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9557627123987997237691109 1792055085747749482067083)
  ·
    refine ⟨2688082628621624223100625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1792055085747749482067083 2688082628621624223100625)
    ·
      refine ⟨2016061971466218167325469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2688082628621624223100625 2016061971466218167325469)
      ·
        refine ⟨756023239299831812747051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2016061971466218167325469 756023239299831812747051)
        ·
          refine ⟨1134034858949747719120577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 756023239299831812747051 1134034858949747719120577)
          ·
            refine ⟨850526144212310789340433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1134034858949747719120577 850526144212310789340433)
            ·
              refine ⟨637894608159233092005325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 850526144212310789340433 637894608159233092005325)
              ·
                refine ⟨239210478059712409501997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 637894608159233092005325 239210478059712409501997)
                ·
                  refine ⟨89703929272392153563249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239210478059712409501997 89703929272392153563249)
                  ·
                    rfl

theorem cell21_393070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 2, 3, 3].length) (baseStart_393070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_393070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_393070 prefixEnd_393070 := by exact prefixLift 393070
  have htrace : WordTrace (prefixWord ++ tailWord_393070) baseStart_393070 baseEnd_393070 := by
    simpa [prefixWord, tailWord_393070, baseEnd_393070] using wordTrace_append hprefix tailTrace_393070
  have hstable : (prefixWord ++ tailWord_393070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393070).length < 2 ^ (prefixWord ++ tailWord_393070).sum := by decide
  have hdescent : baseEnd_393070 < baseStart_393070 := by decide
  rcases family_descends (prefixWord ++ tailWord_393070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393160 : List Nat := [2, 1, 3, 1, 4, 3, 2, 1, 4]
def baseStart_393160 : Nat := 118140960795 + 393160 * 2 ^ 59
def prefixEnd_393160 : Nat := 4983230072969 + 3 ^ 40 * 393160 * 2
def baseEnd_393160 : Nat := 89724468498571997063065

theorem tailTrace_393160 : CollatzResearch.WordTrace tailWord_393160 prefixEnd_393160 89724468498571997063065 := by
  unfold tailWord_393160
  simp only [CollatzResearch.WordTrace]
  refine ⟨7169861627827970613656467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9559815503770627484875289 7169861627827970613656467)
  ·
    refine ⟨10754792441741955920484701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7169861627827970613656467 10754792441741955920484701)
    ·
      refine ⟨4033047165653233470181763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10754792441741955920484701 4033047165653233470181763)
      ·
        refine ⟨6049570748479850205272645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4033047165653233470181763 6049570748479850205272645)
        ·
          refine ⟨1134294515339971913488621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6049570748479850205272645 1134294515339971913488621)
          ·
            refine ⟨425360443252489467558233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1134294515339971913488621 425360443252489467558233)
            ·
              refine ⟨319020332439367100668675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425360443252489467558233 319020332439367100668675)
              ·
                refine ⟨478530498659050651003013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319020332439367100668675 478530498659050651003013)
                ·
                  refine ⟨89724468498571997063065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 478530498659050651003013 89724468498571997063065)
                  ·
                    rfl

theorem cell21_393160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 2, 1, 4].length) (baseStart_393160 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_393160 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_393160 prefixEnd_393160 := by exact prefixLift 393160
  have htrace : WordTrace (prefixWord ++ tailWord_393160) baseStart_393160 baseEnd_393160 := by
    simpa [prefixWord, tailWord_393160, baseEnd_393160] using wordTrace_append hprefix tailTrace_393160
  have hstable : (prefixWord ++ tailWord_393160).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393160).length < 2 ^ (prefixWord ++ tailWord_393160).sum := by decide
  have hdescent : baseEnd_393160 < baseStart_393160 := by decide
  rcases family_descends (prefixWord ++ tailWord_393160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393185 : List Nat := [1, 2, 3, 1, 2, 1, 2, 1, 8]
def baseStart_393185 : Nat := 118140960795 + 393185 * 2 ^ 59
def prefixEnd_393185 : Nat := 4983230072969 + 3 ^ 40 * 393185 * 2
def baseEnd_393185 : Nat := 89730173839177509146347

theorem tailTrace_393185 : CollatzResearch.WordTrace tailWord_393185 prefixEnd_393185 89730173839177509146347 := by
  unfold tailWord_393185
  simp only [CollatzResearch.WordTrace]
  refine ⟨14340635080565370496973009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9560423387043580331315339 14340635080565370496973009)
  ·
    refine ⟨10755476310424027872729757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14340635080565370496973009 10755476310424027872729757)
    ·
      refine ⟨4033303616409010452273659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10755476310424027872729757 4033303616409010452273659)
      ·
        refine ⟨6049955424613515678410489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4033303616409010452273659 6049955424613515678410489)
        ·
          refine ⟨4537466568460136758807867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6049955424613515678410489 4537466568460136758807867)
          ·
            refine ⟨6806199852690205138211801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4537466568460136758807867 6806199852690205138211801)
            ·
              refine ⟨5104649889517653853658851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6806199852690205138211801 5104649889517653853658851)
              ·
                refine ⟨7656974834276480780488277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5104649889517653853658851 7656974834276480780488277)
                ·
                  refine ⟨89730173839177509146347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7656974834276480780488277 89730173839177509146347)
                  ·
                    rfl

theorem cell21_393185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 1, 8].length) (baseStart_393185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_393185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_393185 prefixEnd_393185 := by exact prefixLift 393185
  have htrace : WordTrace (prefixWord ++ tailWord_393185) baseStart_393185 baseEnd_393185 := by
    simpa [prefixWord, tailWord_393185, baseEnd_393185] using wordTrace_append hprefix tailTrace_393185
  have hstable : (prefixWord ++ tailWord_393185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393185).length < 2 ^ (prefixWord ++ tailWord_393185).sum := by decide
  have hdescent : baseEnd_393185 < baseStart_393185 := by decide
  rcases family_descends (prefixWord ++ tailWord_393185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393188 : List Nat := [2, 3, 1, 1, 1, 1, 4, 5, 3]
def baseStart_393188 : Nat := 118140960795 + 393188 * 2 ^ 59
def prefixEnd_393188 : Nat := 4983230072969 + 3 ^ 40 * 393188 * 2
def baseEnd_393188 : Nat := 89730858480050170596341

theorem tailTrace_393188 : CollatzResearch.WordTrace tailWord_393188 prefixEnd_393188 89730858480050170596341 := by
  unfold tailWord_393188
  simp only [CollatzResearch.WordTrace]
  refine ⟨7170372249777251004666109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9560496333036334672888145 7170372249777251004666109)
  ·
    refine ⟨2688889593666469126749791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7170372249777251004666109 2688889593666469126749791)
    ·
      refine ⟨4033334390499703690124687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2688889593666469126749791 4033334390499703690124687)
      ·
        refine ⟨6050001585749555535187031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4033334390499703690124687 6050001585749555535187031)
        ·
          refine ⟨9075002378624333302780547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6050001585749555535187031 9075002378624333302780547)
          ·
            refine ⟨13612503567936499954170821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9075002378624333302780547 13612503567936499954170821)
            ·
              refine ⟨2552344418988093741407029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13612503567936499954170821 2552344418988093741407029)
              ·
                refine ⟨239282289280133788256909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2552344418988093741407029 239282289280133788256909)
                ·
                  refine ⟨89730858480050170596341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239282289280133788256909 89730858480050170596341)
                  ·
                    rfl

theorem cell21_393188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 5, 3].length) (baseStart_393188 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_393188 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_393188 prefixEnd_393188 := by exact prefixLift 393188
  have htrace : WordTrace (prefixWord ++ tailWord_393188) baseStart_393188 baseEnd_393188 := by
    simpa [prefixWord, tailWord_393188, baseEnd_393188] using wordTrace_append hprefix tailTrace_393188
  have hstable : (prefixWord ++ tailWord_393188).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393188).length < 2 ^ (prefixWord ++ tailWord_393188).sum := by decide
  have hdescent : baseEnd_393188 < baseStart_393188 := by decide
  rcases family_descends (prefixWord ++ tailWord_393188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393264 : List Nat := [2, 1, 1, 1, 2, 5, 2, 4, 3]
def baseStart_393264 : Nat := 118140960795 + 393264 * 2 ^ 59
def prefixEnd_393264 : Nat := 4983230072969 + 3 ^ 40 * 393264 * 2
def baseEnd_393264 : Nat := 89748202715490927329519

theorem tailTrace_393264 : CollatzResearch.WordTrace tailWord_393264 prefixEnd_393264 89748202715490927329519 := by
  unfold tailWord_393264
  simp only [CollatzResearch.WordTrace]
  refine ⟨7171758223639583494549423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9562344298186111326065897 7171758223639583494549423)
  ·
    refine ⟨10757637335459375241824135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7171758223639583494549423 10757637335459375241824135)
    ·
      refine ⟨16136456003189062862736203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10757637335459375241824135 16136456003189062862736203)
      ·
        refine ⟨24204684004783594294104305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16136456003189062862736203 24204684004783594294104305)
        ·
          refine ⟨18153513003587695720578229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24204684004783594294104305 18153513003587695720578229)
          ·
            refine ⟨1701891844086346473804209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18153513003587695720578229 1701891844086346473804209)
            ·
              refine ⟨1276418883064759855353157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1701891844086346473804209 1276418883064759855353157)
              ·
                refine ⟨239328540574642472878717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1276418883064759855353157 239328540574642472878717)
                ·
                  refine ⟨89748202715490927329519, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239328540574642472878717 89748202715490927329519)
                  ·
                    rfl

theorem cell21_393264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 3].length) (baseStart_393264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_393264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_393264 prefixEnd_393264 := by exact prefixLift 393264
  have htrace : WordTrace (prefixWord ++ tailWord_393264) baseStart_393264 baseEnd_393264 := by
    simpa [prefixWord, tailWord_393264, baseEnd_393264] using wordTrace_append hprefix tailTrace_393264
  have hstable : (prefixWord ++ tailWord_393264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393264).length < 2 ^ (prefixWord ++ tailWord_393264).sum := by decide
  have hdescent : baseEnd_393264 < baseStart_393264 := by decide
  rcases family_descends (prefixWord ++ tailWord_393264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393298 : List Nat := [3, 2, 2, 1, 4, 2, 1, 3, 3]
def baseStart_393298 : Nat := 118140960795 + 393298 * 2 ^ 59
def prefixEnd_393298 : Nat := 4983230072969 + 3 ^ 40 * 393298 * 2
def baseEnd_393298 : Nat := 89755961978714423762783

theorem tailTrace_393298 : CollatzResearch.WordTrace tailWord_393298 prefixEnd_393298 89755961978714423762783 := by
  unfold tailWord_393298
  simp only [CollatzResearch.WordTrace]
  refine ⟨3586189132288997698959137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9563171019437327197224365 3586189132288997698959137)
  ·
    refine ⟨2689641849216748274219353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3586189132288997698959137 2689641849216748274219353)
    ·
      refine ⟨2017231386912561205664515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2689641849216748274219353 2017231386912561205664515)
      ·
        refine ⟨3025847080368841808496773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2017231386912561205664515 3025847080368841808496773)
        ·
          refine ⟨567346327569157839093145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3025847080368841808496773 567346327569157839093145)
          ·
            refine ⟨425509745676868379319859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 567346327569157839093145 425509745676868379319859)
            ·
              refine ⟨638264618515302568979789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425509745676868379319859 638264618515302568979789)
              ·
                refine ⟨239349231943238463367421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 638264618515302568979789 239349231943238463367421)
                ·
                  refine ⟨89755961978714423762783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239349231943238463367421 89755961978714423762783)
                  ·
                    rfl

theorem cell21_393298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 2, 1, 3, 3].length) (baseStart_393298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_393298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_393298 prefixEnd_393298 := by exact prefixLift 393298
  have htrace : WordTrace (prefixWord ++ tailWord_393298) baseStart_393298 baseEnd_393298 := by
    simpa [prefixWord, tailWord_393298, baseEnd_393298] using wordTrace_append hprefix tailTrace_393298
  have hstable : (prefixWord ++ tailWord_393298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393298).length < 2 ^ (prefixWord ++ tailWord_393298).sum := by decide
  have hdescent : baseEnd_393298 < baseStart_393298 := by decide
  rcases family_descends (prefixWord ++ tailWord_393298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393309 : List Nat := [1, 4, 4, 1, 1, 1, 9]
def baseStart_393309 : Nat := 118140960795 + 393309 * 2 ^ 59
def prefixEnd_393309 : Nat := 4983230072969 + 3 ^ 40 * 393309 * 2
def baseEnd_393309 : Nat := 9973163592064538786603

theorem tailTrace_393309 : CollatzResearch.WordTrace tailWord_393309 prefixEnd_393309 9973163592064538786603 := by
  unfold tailWord_393309
  simp only [CollatzResearch.WordTrace]
  refine ⟨14345157732116139674486981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9563438488077426449657987 14345157732116139674486981)
  ·
    refine ⟨2689717074771776188966309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14345157732116139674486981 2689717074771776188966309)
    ·
      refine ⟨504321951519708035431183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2689717074771776188966309 504321951519708035431183)
      ·
        refine ⟨756482927279562053146775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504321951519708035431183 756482927279562053146775)
        ·
          refine ⟨1134724390919343079720163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 756482927279562053146775 1134724390919343079720163)
          ·
            refine ⟨1702086586379014619580245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1134724390919343079720163 1702086586379014619580245)
            ·
              refine ⟨9973163592064538786603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1702086586379014619580245 9973163592064538786603)
              ·
                rfl

theorem cell21_393309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 9].length) (baseStart_393309 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_393309 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_393309 prefixEnd_393309 := by exact prefixLift 393309
  have htrace : WordTrace (prefixWord ++ tailWord_393309) baseStart_393309 baseEnd_393309 := by
    simpa [prefixWord, tailWord_393309, baseEnd_393309] using wordTrace_append hprefix tailTrace_393309
  have hstable : (prefixWord ++ tailWord_393309).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393309).length < 2 ^ (prefixWord ++ tailWord_393309).sum := by decide
  have hdescent : baseEnd_393309 < baseStart_393309 := by decide
  rcases family_descends (prefixWord ++ tailWord_393309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393366 : List Nat := [5, 3, 2, 1, 1, 2, 2, 2, 3]
def baseStart_393366 : Nat := 118140960795 + 393366 * 2 ^ 59
def prefixEnd_393366 : Nat := 4983230072969 + 3 ^ 40 * 393366 * 2
def baseEnd_393366 : Nat := 89771480505161416629311

theorem tailTrace_393366 : CollatzResearch.WordTrace tailWord_393366 prefixEnd_393366 89771480505161416629311 := by
  unfold tailWord_393366
  simp only [CollatzResearch.WordTrace]
  refine ⟨896702293306852400581997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9564824461939758939541301 896702293306852400581997)
  ·
    refine ⟨336263359990069650218249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 896702293306852400581997 336263359990069650218249)
    ·
      refine ⟨252197519992552237663687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 336263359990069650218249 252197519992552237663687)
      ·
        refine ⟨378296279988828356495531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252197519992552237663687 378296279988828356495531)
        ·
          refine ⟨567444419983242534743297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378296279988828356495531 567444419983242534743297)
          ·
            refine ⟨425583314987431901057473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 567444419983242534743297 425583314987431901057473)
            ·
              refine ⟨319187486240573925793105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425583314987431901057473 319187486240573925793105)
              ·
                refine ⟨239390614680430444344829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319187486240573925793105 239390614680430444344829)
                ·
                  refine ⟨89771480505161416629311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239390614680430444344829 89771480505161416629311)
                  ·
                    rfl

theorem cell21_393366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_393366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_393366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_393366 prefixEnd_393366 := by exact prefixLift 393366
  have htrace : WordTrace (prefixWord ++ tailWord_393366) baseStart_393366 baseEnd_393366 := by
    simpa [prefixWord, tailWord_393366, baseEnd_393366] using wordTrace_append hprefix tailTrace_393366
  have hstable : (prefixWord ++ tailWord_393366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393366).length < 2 ^ (prefixWord ++ tailWord_393366).sum := by decide
  have hdescent : baseEnd_393366 < baseStart_393366 := by decide
  rcases family_descends (prefixWord ++ tailWord_393366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393368 : List Nat := [2, 1, 2, 4, 3, 9]
def baseStart_393368 : Nat := 118140960795 + 393368 * 2 ^ 59
def prefixEnd_393368 : Nat := 4983230072969 + 3 ^ 40 * 393368 * 2
def baseEnd_393368 : Nat := 3324886553052216947999

theorem tailTrace_393368 : CollatzResearch.WordTrace tailWord_393368 prefixEnd_393368 3324886553052216947999 := by
  unfold tailWord_393368
  simp only [CollatzResearch.WordTrace]
  refine ⟨7173654819451196375442379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9564873092601595167256505 7173654819451196375442379)
  ·
    refine ⟨10760482229176794563163569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7173654819451196375442379 10760482229176794563163569)
    ·
      refine ⟨8070361671882595922372677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10760482229176794563163569 8070361671882595922372677)
      ·
        refine ⟨1513192813477986735444877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8070361671882595922372677 1513192813477986735444877)
        ·
          refine ⟨567447305054245025791829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1513192813477986735444877 567447305054245025791829)
          ·
            refine ⟨3324886553052216947999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 567447305054245025791829 3324886553052216947999)
            ·
              rfl

theorem cell21_393368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 9].length) (baseStart_393368 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_393368 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_393368 prefixEnd_393368 := by exact prefixLift 393368
  have htrace : WordTrace (prefixWord ++ tailWord_393368) baseStart_393368 baseEnd_393368 := by
    simpa [prefixWord, tailWord_393368, baseEnd_393368] using wordTrace_append hprefix tailTrace_393368
  have hstable : (prefixWord ++ tailWord_393368).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393368).length < 2 ^ (prefixWord ++ tailWord_393368).sum := by decide
  have hdescent : baseEnd_393368 < baseStart_393368 := by decide
  rcases family_descends (prefixWord ++ tailWord_393368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393374 : List Nat := [4, 3, 1, 1, 3, 1, 1, 4, 3]
def baseStart_393374 : Nat := 118140960795 + 393374 * 2 ^ 59
def prefixEnd_393374 : Nat := 4983230072969 + 3 ^ 40 * 393374 * 2
def baseEnd_393374 : Nat := 89773306214155180495961

theorem tailTrace_393374 : CollatzResearch.WordTrace tailWord_393374 prefixEnd_393374 89773306214155180495961 := by
  unfold tailWord_393374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1793441059610081971950397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9565018984587103850402117 1793441059610081971950397)
  ·
    refine ⟨672540397353780739481399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1793441059610081971950397 672540397353780739481399)
    ·
      refine ⟨1008810596030671109222099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 672540397353780739481399 1008810596030671109222099)
      ·
        refine ⟨1513215894046006663833149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1008810596030671109222099 1513215894046006663833149)
        ·
          refine ⟨567455960267252498937431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1513215894046006663833149 567455960267252498937431)
          ·
            refine ⟨851183940400878748406147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567455960267252498937431 851183940400878748406147)
            ·
              refine ⟨1276775910601318122609221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851183940400878748406147 1276775910601318122609221)
              ·
                refine ⟨239395483237747147989229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1276775910601318122609221 239395483237747147989229)
                ·
                  refine ⟨89773306214155180495961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239395483237747147989229 89773306214155180495961)
                  ·
                    rfl

theorem cell21_393374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_393374 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_393374 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_393374 prefixEnd_393374 := by exact prefixLift 393374
  have htrace : WordTrace (prefixWord ++ tailWord_393374) baseStart_393374 baseEnd_393374 := by
    simpa [prefixWord, tailWord_393374, baseEnd_393374] using wordTrace_append hprefix tailTrace_393374
  have hstable : (prefixWord ++ tailWord_393374).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393374).length < 2 ^ (prefixWord ++ tailWord_393374).sum := by decide
  have hdescent : baseEnd_393374 < baseStart_393374 := by decide
  rcases family_descends (prefixWord ++ tailWord_393374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393399 : List Nat := [1, 1, 3, 1, 4, 3, 1, 2, 5]
def baseStart_393399 : Nat := 118140960795 + 393399 * 2 ^ 59
def prefixEnd_393399 : Nat := 4983230072969 + 3 ^ 40 * 393399 * 2
def baseEnd_393399 : Nat := 89779011554760692579243

theorem tailTrace_393399 : CollatzResearch.WordTrace tailWord_393399 prefixEnd_393399 89779011554760692579243 := by
  unfold tailWord_393399
  simp only [CollatzResearch.WordTrace]
  refine ⟨14348440301790085045263251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9565626867860056696842167 14348440301790085045263251)
  ·
    refine ⟨21522660452685127567894877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14348440301790085045263251 21522660452685127567894877)
    ·
      refine ⟨8070997669756922837960579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21522660452685127567894877 8070997669756922837960579)
      ·
        refine ⟨12106496504635384256940869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8070997669756922837960579 12106496504635384256940869)
        ·
          refine ⟨2269968094619134548176413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12106496504635384256940869 2269968094619134548176413)
          ·
            refine ⟨851238035482175455566155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2269968094619134548176413 851238035482175455566155)
            ·
              refine ⟨1276857053223263183349233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851238035482175455566155 1276857053223263183349233)
              ·
                refine ⟨957642789917447387511925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1276857053223263183349233 957642789917447387511925)
                ·
                  refine ⟨89779011554760692579243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 957642789917447387511925 89779011554760692579243)
                  ·
                    rfl

theorem cell21_393399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 5].length) (baseStart_393399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_393399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_393399 prefixEnd_393399 := by exact prefixLift 393399
  have htrace : WordTrace (prefixWord ++ tailWord_393399) baseStart_393399 baseEnd_393399 := by
    simpa [prefixWord, tailWord_393399, baseEnd_393399] using wordTrace_append hprefix tailTrace_393399
  have hstable : (prefixWord ++ tailWord_393399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393399).length < 2 ^ (prefixWord ++ tailWord_393399).sum := by decide
  have hdescent : baseEnd_393399 < baseStart_393399 := by decide
  rcases family_descends (prefixWord ++ tailWord_393399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393489 : List Nat := [1, 2, 2, 1, 1, 5, 2, 1, 6]
def baseStart_393489 : Nat := 118140960795 + 393489 * 2 ^ 59
def prefixEnd_393489 : Nat := 4983230072969 + 3 ^ 40 * 393489 * 2
def baseEnd_393489 : Nat := 89799550780940536079059

theorem tailTrace_393489 : CollatzResearch.WordTrace tailWord_393489 prefixEnd_393489 89799550780940536079059 := by
  unfold tailWord_393489
  simp only [CollatzResearch.WordTrace]
  refine ⟨14351722871464030416039521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9567815247642686944026347 14351722871464030416039521)
  ·
    refine ⟨10763792153598022812029641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14351722871464030416039521 10763792153598022812029641)
    ·
      refine ⟨8072844115198517109022231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10763792153598022812029641 8072844115198517109022231)
      ·
        refine ⟨12109266172797775663533347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8072844115198517109022231 12109266172797775663533347)
        ·
          refine ⟨18163899259196663495300021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12109266172797775663533347 18163899259196663495300021)
          ·
            refine ⟨1702865555549687202684377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18163899259196663495300021 1702865555549687202684377)
            ·
              refine ⟨1277149166662265402013283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1702865555549687202684377 1277149166662265402013283)
              ·
                refine ⟨1915723749993398103019925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1277149166662265402013283 1915723749993398103019925)
                ·
                  refine ⟨89799550780940536079059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1915723749993398103019925 89799550780940536079059)
                  ·
                    rfl

theorem cell21_393489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 6].length) (baseStart_393489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_393489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_393489 prefixEnd_393489 := by exact prefixLift 393489
  have htrace : WordTrace (prefixWord ++ tailWord_393489) baseStart_393489 baseEnd_393489 := by
    simpa [prefixWord, tailWord_393489, baseEnd_393489] using wordTrace_append hprefix tailTrace_393489
  have hstable : (prefixWord ++ tailWord_393489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393489).length < 2 ^ (prefixWord ++ tailWord_393489).sum := by decide
  have hdescent : baseEnd_393489 < baseStart_393489 := by decide
  rcases family_descends (prefixWord ++ tailWord_393489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393537 : List Nat := [1, 2, 5, 2, 3, 8]
def baseStart_393537 : Nat := 118140960795 + 393537 * 2 ^ 59
def prefixEnd_393537 : Nat := 4983230072969 + 3 ^ 40 * 393537 * 2
def baseEnd_393537 : Nat := 3326315001292708121443

theorem tailTrace_393537 : CollatzResearch.WordTrace tailWord_393537 prefixEnd_393537 3326315001292708121443 := by
  unfold tailWord_393537
  simp only [CollatzResearch.WordTrace]
  refine ⟨14353473575290134613786865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9568982383526756409191243 14353473575290134613786865)
  ·
    refine ⟨10765105181467600960340149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14353473575290134613786865 10765105181467600960340149)
    ·
      refine ⟨1009228610762587590031889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10765105181467600960340149 1009228610762587590031889)
      ·
        refine ⟨756921458071940692523917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1009228610762587590031889 756921458071940692523917)
        ·
          refine ⟨283845546776977759696469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 756921458071940692523917 283845546776977759696469)
          ·
            refine ⟨3326315001292708121443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 283845546776977759696469 3326315001292708121443)
            ·
              rfl

theorem cell21_393537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 8].length) (baseStart_393537 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_393537 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_393537 prefixEnd_393537 := by exact prefixLift 393537
  have htrace : WordTrace (prefixWord ++ tailWord_393537) baseStart_393537 baseEnd_393537 := by
    simpa [prefixWord, tailWord_393537, baseEnd_393537] using wordTrace_append hprefix tailTrace_393537
  have hstable : (prefixWord ++ tailWord_393537).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393537).length < 2 ^ (prefixWord ++ tailWord_393537).sum := by decide
  have hdescent : baseEnd_393537 < baseStart_393537 := by decide
  rcases family_descends (prefixWord ++ tailWord_393537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393540 : List Nat := [2, 3, 4, 1, 2, 1, 2, 2, 4]
def baseStart_393540 : Nat := 118140960795 + 393540 * 2 ^ 59
def prefixEnd_393540 : Nat := 4983230072969 + 3 ^ 40 * 393540 * 2
def baseEnd_393540 : Nat := 89811189675775780728955

theorem tailTrace_393540 : CollatzResearch.WordTrace tailWord_393540 prefixEnd_393540 89811189675775780728955 := by
  unfold tailWord_393540
  simp only [CollatzResearch.WordTrace]
  refine ⟨7176791497139633063073037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9569055329519510750764049 7176791497139633063073037)
  ·
    refine ⟨2691296811427362398652389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7176791497139633063073037 2691296811427362398652389)
    ·
      refine ⟨504618152142630449747323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2691296811427362398652389 504618152142630449747323)
      ·
        refine ⟨756927228213945674620985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504618152142630449747323 756927228213945674620985)
        ·
          refine ⟨567695421160459255965739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 756927228213945674620985 567695421160459255965739)
          ·
            refine ⟨851543131740688883948609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567695421160459255965739 851543131740688883948609)
            ·
              refine ⟨638657348805516662961457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 851543131740688883948609 638657348805516662961457)
              ·
                refine ⟨478993011604137497221093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 638657348805516662961457 478993011604137497221093)
                ·
                  refine ⟨89811189675775780728955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 478993011604137497221093 89811189675775780728955)
                  ·
                    rfl

theorem cell21_393540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 4].length) (baseStart_393540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_393540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_393540 prefixEnd_393540 := by exact prefixLift 393540
  have htrace : WordTrace (prefixWord ++ tailWord_393540) baseStart_393540 baseEnd_393540 := by
    simpa [prefixWord, tailWord_393540, baseEnd_393540] using wordTrace_append hprefix tailTrace_393540
  have hstable : (prefixWord ++ tailWord_393540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393540).length < 2 ^ (prefixWord ++ tailWord_393540).sum := by decide
  have hdescent : baseEnd_393540 < baseStart_393540 := by decide
  rcases family_descends (prefixWord ++ tailWord_393540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393630 : List Nat := [4, 3, 1, 2, 1, 1, 4, 5]
def baseStart_393630 : Nat := 118140960795 + 393630 * 2 ^ 59
def prefixEnd_393630 : Nat := 4983230072969 + 3 ^ 40 * 393630 * 2
def baseEnd_393630 : Nat := 29943909633985208076257

theorem tailTrace_393630 : CollatzResearch.WordTrace tailWord_393630 prefixEnd_393630 29943909633985208076257 := by
  unfold tailWord_393630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1794608195494151437115293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9571243709302140997948229 1794608195494151437115293)
  ·
    refine ⟨672978073310306788918235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1794608195494151437115293 672978073310306788918235)
    ·
      refine ⟨1009467109965460183377353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 672978073310306788918235 1009467109965460183377353)
      ·
        refine ⟨757100332474095137533015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1009467109965460183377353 757100332474095137533015)
        ·
          refine ⟨1135650498711142706299523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 757100332474095137533015 1135650498711142706299523)
          ·
            refine ⟨1703475748066714059449285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1135650498711142706299523 1703475748066714059449285)
            ·
              refine ⟨319401702762508886146741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1703475748066714059449285 319401702762508886146741)
              ·
                refine ⟨29943909633985208076257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 319401702762508886146741 29943909633985208076257)
                ·
                  rfl

theorem cell21_393630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 4, 5].length) (baseStart_393630 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_393630 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_393630 prefixEnd_393630 := by exact prefixLift 393630
  have htrace : WordTrace (prefixWord ++ tailWord_393630) baseStart_393630 baseEnd_393630 := by
    simpa [prefixWord, tailWord_393630, baseEnd_393630] using wordTrace_append hprefix tailTrace_393630
  have hstable : (prefixWord ++ tailWord_393630).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393630).length < 2 ^ (prefixWord ++ tailWord_393630).sum := by decide
  have hdescent : baseEnd_393630 < baseStart_393630 := by decide
  rcases family_descends (prefixWord ++ tailWord_393630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393655 : List Nat := [1, 1, 3, 1, 3, 3, 9]
def baseStart_393655 : Nat := 118140960795 + 393655 * 2 ^ 59
def prefixEnd_393655 : Nat := 4983230072969 + 3 ^ 40 * 393655 * 2
def baseEnd_393655 : Nat := 9981937138062348479117

theorem tailTrace_393655 : CollatzResearch.WordTrace tailWord_393655 prefixEnd_393655 9981937138062348479117 := by
  unfold tailWord_393655
  simp only [CollatzResearch.WordTrace]
  refine ⟨14357777388862640766582419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9571851592575093844388279 14357777388862640766582419)
  ·
    refine ⟨21536666083293961149873629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14357777388862640766582419 21536666083293961149873629)
    ·
      refine ⟨8076249781235235431202611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21536666083293961149873629 8076249781235235431202611)
      ·
        refine ⟨12114374671852853146803917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8076249781235235431202611 12114374671852853146803917)
        ·
          refine ⟨4542890501944819930051469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12114374671852853146803917 4542890501944819930051469)
          ·
            refine ⟨1703583938229307473769301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4542890501944819930051469 1703583938229307473769301)
            ·
              refine ⟨9981937138062348479117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1703583938229307473769301 9981937138062348479117)
              ·
                rfl

theorem cell21_393655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 9].length) (baseStart_393655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_393655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_393655 prefixEnd_393655 := by exact prefixLift 393655
  have htrace : WordTrace (prefixWord ++ tailWord_393655) baseStart_393655 baseEnd_393655 := by
    simpa [prefixWord, tailWord_393655, baseEnd_393655] using wordTrace_append hprefix tailTrace_393655
  have hstable : (prefixWord ++ tailWord_393655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393655).length < 2 ^ (prefixWord ++ tailWord_393655).sum := by decide
  have hdescent : baseEnd_393655 < baseStart_393655 := by decide
  rcases family_descends (prefixWord ++ tailWord_393655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393661 : List Nat := [1, 4, 1, 2, 2, 3, 3, 2, 3]
def baseStart_393661 : Nat := 118140960795 + 393661 * 2 ^ 59
def prefixEnd_393661 : Nat := 4983230072969 + 3 ^ 40 * 393661 * 2
def baseEnd_393661 : Nat := 89838803524306459212041

theorem tailTrace_393661 : CollatzResearch.WordTrace tailWord_393661 prefixEnd_393661 89838803524306459212041 := by
  unfold tailWord_393661
  simp only [CollatzResearch.WordTrace]
  refine ⟨14357996226840903791300837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9571997484560602527533891 14357996226840903791300837)
  ·
    refine ⟨2692124292532669460868907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14357996226840903791300837 2692124292532669460868907)
    ·
      refine ⟨4038186438799004191303361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2692124292532669460868907 4038186438799004191303361)
      ·
        refine ⟨3028639829099253143477521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4038186438799004191303361 3028639829099253143477521)
        ·
          refine ⟨2271479871824439857608141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3028639829099253143477521 2271479871824439857608141)
          ·
            refine ⟨851804951934164946603053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2271479871824439857608141 851804951934164946603053)
            ·
              refine ⟨319426856975311854976145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 851804951934164946603053 319426856975311854976145)
              ·
                refine ⟨239570142731483891232109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319426856975311854976145 239570142731483891232109)
                ·
                  refine ⟨89838803524306459212041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239570142731483891232109 89838803524306459212041)
                  ·
                    rfl

theorem cell21_393661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_393661 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_393661 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_393661 prefixEnd_393661 := by exact prefixLift 393661
  have htrace : WordTrace (prefixWord ++ tailWord_393661) baseStart_393661 baseEnd_393661 := by
    simpa [prefixWord, tailWord_393661, baseEnd_393661] using wordTrace_append hprefix tailTrace_393661
  have hstable : (prefixWord ++ tailWord_393661).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393661).length < 2 ^ (prefixWord ++ tailWord_393661).sum := by decide
  have hdescent : baseEnd_393661 < baseStart_393661 := by decide
  rcases family_descends (prefixWord ++ tailWord_393661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393672 : List Nat := [2, 1, 3, 1, 3, 3, 2, 6]
def baseStart_393672 : Nat := 118140960795 + 393672 * 2 ^ 59
def prefixEnd_393672 : Nat := 4983230072969 + 3 ^ 40 * 393672 * 2
def baseEnd_393672 : Nat := 29947104624724294842895

theorem tailTrace_393672 : CollatzResearch.WordTrace tailWord_393672 prefixEnd_393672 29947104624724294842895 := by
  unfold tailWord_393672
  simp only [CollatzResearch.WordTrace]
  refine ⟨7179198714900526334975635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9572264953200701779967513 7179198714900526334975635)
  ·
    refine ⟨10768798072350789502463453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7179198714900526334975635 10768798072350789502463453)
    ·
      refine ⟨4038299277131546063423795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10768798072350789502463453 4038299277131546063423795)
      ·
        refine ⟨6057448915697319095135693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4038299277131546063423795 6057448915697319095135693)
        ·
          refine ⟨2271543343386494660675885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6057448915697319095135693 2271543343386494660675885)
          ·
            refine ⟨851828753769935497753457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2271543343386494660675885 851828753769935497753457)
            ·
              refine ⟨638871565327451623315093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 851828753769935497753457 638871565327451623315093)
              ·
                refine ⟨29947104624724294842895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 638871565327451623315093 29947104624724294842895)
                ·
                  rfl

theorem cell21_393672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 2, 6].length) (baseStart_393672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_393672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_393672 prefixEnd_393672 := by exact prefixLift 393672
  have htrace : WordTrace (prefixWord ++ tailWord_393672) baseStart_393672 baseEnd_393672 := by
    simpa [prefixWord, tailWord_393672, baseEnd_393672] using wordTrace_append hprefix tailTrace_393672
  have hstable : (prefixWord ++ tailWord_393672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393672).length < 2 ^ (prefixWord ++ tailWord_393672).sum := by decide
  have hdescent : baseEnd_393672 < baseStart_393672 := by decide
  rcases family_descends (prefixWord ++ tailWord_393672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393762 : List Nat := [3, 3, 1, 1, 1, 1, 1, 1, 9]
def baseStart_393762 : Nat := 118140960795 + 393762 * 2 ^ 59
def prefixEnd_393762 : Nat := 4983230072969 + 3 ^ 40 * 393762 * 2
def baseEnd_393762 : Nat := 89861853100352728028501

theorem tailTrace_393762 : CollatzResearch.WordTrace tailWord_393762 prefixEnd_393762 89861853100352728028501 := by
  unfold tailWord_393762
  simp only [CollatzResearch.WordTrace]
  refine ⟨3590419999868749510181885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9574453332983332027151693 3590419999868749510181885)
  ·
    refine ⟨1346407499950781066318207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3590419999868749510181885 1346407499950781066318207)
    ·
      refine ⟨2019611249926171599477311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1346407499950781066318207 2019611249926171599477311)
      ·
        refine ⟨3029416874889257399215967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2019611249926171599477311 3029416874889257399215967)
        ·
          refine ⟨4544125312333886098823951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3029416874889257399215967 4544125312333886098823951)
          ·
            refine ⟨6816187968500829148235927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4544125312333886098823951 6816187968500829148235927)
            ·
              refine ⟨10224281952751243722353891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6816187968500829148235927 10224281952751243722353891)
              ·
                refine ⟨15336422929126865583530837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10224281952751243722353891 15336422929126865583530837)
                ·
                  refine ⟨89861853100352728028501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15336422929126865583530837 89861853100352728028501)
                  ·
                    rfl

theorem cell21_393762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_393762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_393762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_393762 prefixEnd_393762 := by exact prefixLift 393762
  have htrace : WordTrace (prefixWord ++ tailWord_393762) baseStart_393762 baseEnd_393762 := by
    simpa [prefixWord, tailWord_393762, baseEnd_393762] using wordTrace_append hprefix tailTrace_393762
  have hstable : (prefixWord ++ tailWord_393762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393762).length < 2 ^ (prefixWord ++ tailWord_393762).sum := by decide
  have hdescent : baseEnd_393762 < baseStart_393762 := by decide
  rcases family_descends (prefixWord ++ tailWord_393762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393779 : List Nat := [1, 1, 1, 2, 4, 2, 1, 6, 3]
def baseStart_393779 : Nat := 118140960795 + 393779 * 2 ^ 59
def prefixEnd_393779 : Nat := 4983230072969 + 3 ^ 40 * 393779 * 2
def baseEnd_393779 : Nat := 89865732731964476245133

theorem tailTrace_393779 : CollatzResearch.WordTrace tailWord_393779 prefixEnd_393779 89865732731964476245133 := by
  unfold tailWord_393779
  simp only [CollatzResearch.WordTrace]
  refine ⟨14362300040413409944096391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9574866693608939962730927 14362300040413409944096391)
  ·
    refine ⟨21543450060620114916144587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14362300040413409944096391 21543450060620114916144587)
    ·
      refine ⟨32315175090930172374216881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21543450060620114916144587 32315175090930172374216881)
      ·
        refine ⟨24236381318197629280662661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32315175090930172374216881 24236381318197629280662661)
        ·
          refine ⟨4544321497162055490124249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24236381318197629280662661 4544321497162055490124249)
          ·
            refine ⟨3408241122871541617593187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4544321497162055490124249 3408241122871541617593187)
            ·
              refine ⟨5112361684307312426389781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3408241122871541617593187 5112361684307312426389781)
              ·
                refine ⟨239641953951905269987021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5112361684307312426389781 239641953951905269987021)
                ·
                  refine ⟨89865732731964476245133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239641953951905269987021 89865732731964476245133)
                  ·
                    rfl

theorem cell21_393779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 6, 3].length) (baseStart_393779 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_393779 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_393779 prefixEnd_393779 := by exact prefixLift 393779
  have htrace : WordTrace (prefixWord ++ tailWord_393779) baseStart_393779 baseEnd_393779 := by
    simpa [prefixWord, tailWord_393779, baseEnd_393779] using wordTrace_append hprefix tailTrace_393779
  have hstable : (prefixWord ++ tailWord_393779).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393779).length < 2 ^ (prefixWord ++ tailWord_393779).sum := by decide
  have hdescent : baseEnd_393779 < baseStart_393779 := by decide
  rcases family_descends (prefixWord ++ tailWord_393779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393914 : List Nat := [3, 1, 1, 1, 2, 3, 3, 2, 5]
def baseStart_393914 : Nat := 118140960795 + 393914 * 2 ^ 59
def prefixEnd_393914 : Nat := 4983230072969 + 3 ^ 40 * 393914 * 2
def baseEnd_393914 : Nat := 89896541571234241494857

theorem tailTrace_393914 : CollatzResearch.WordTrace tailWord_393914 prefixEnd_393914 89896541571234241494857 := by
  unfold tailWord_393914
  simp only [CollatzResearch.WordTrace]
  refine ⟨3591805973731082000065199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9578149263282885333507197 3591805973731082000065199)
  ·
    refine ⟨5387708960596623000097799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3591805973731082000065199 5387708960596623000097799)
    ·
      refine ⟨8081563440894934500146699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5387708960596623000097799 8081563440894934500146699)
      ·
        refine ⟨12122345161342401750220049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8081563440894934500146699 12122345161342401750220049)
        ·
          refine ⟨9091758871006801312665037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12122345161342401750220049 9091758871006801312665037)
          ·
            refine ⟨3409409576627550492249389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9091758871006801312665037 3409409576627550492249389)
            ·
              refine ⟨1278528591235331434593521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3409409576627550492249389 1278528591235331434593521)
              ·
                refine ⟨958896443426498575945141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1278528591235331434593521 958896443426498575945141)
                ·
                  refine ⟨89896541571234241494857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 958896443426498575945141 89896541571234241494857)
                  ·
                    rfl

theorem cell21_393914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_393914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_393914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_393914 prefixEnd_393914 := by exact prefixLift 393914
  have htrace : WordTrace (prefixWord ++ tailWord_393914) baseStart_393914 baseEnd_393914 := by
    simpa [prefixWord, tailWord_393914, baseEnd_393914] using wordTrace_append hprefix tailTrace_393914
  have hstable : (prefixWord ++ tailWord_393914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393914).length < 2 ^ (prefixWord ++ tailWord_393914).sum := by decide
  have hdescent : baseEnd_393914 < baseStart_393914 := by decide
  rcases family_descends (prefixWord ++ tailWord_393914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393948 : List Nat := [2, 2, 5, 1, 1, 2, 2, 1, 5]
def baseStart_393948 : Nat := 118140960795 + 393948 * 2 ^ 59
def prefixEnd_393948 : Nat := 4983230072969 + 3 ^ 40 * 393948 * 2
def baseEnd_393948 : Nat := 89904300834457737928121

theorem tailTrace_393948 : CollatzResearch.WordTrace tailWord_393948 prefixEnd_393948 89904300834457737928121 := by
  unfold tailWord_393948
  simp only [CollatzResearch.WordTrace]
  refine ⟨7184231988400575903499249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9578975984534101204665665 7184231988400575903499249)
  ·
    refine ⟨5388173991300431927624437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7184231988400575903499249 5388173991300431927624437)
    ·
      refine ⟨505141311684415493214791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5388173991300431927624437 505141311684415493214791)
      ·
        refine ⟨757711967526623239822187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505141311684415493214791 757711967526623239822187)
        ·
          refine ⟨1136567951289934859733281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 757711967526623239822187 1136567951289934859733281)
          ·
            refine ⟨852425963467451144799961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1136567951289934859733281 852425963467451144799961)
            ·
              refine ⟨639319472600588358599971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 852425963467451144799961 639319472600588358599971)
              ·
                refine ⟨958979208900882537899957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 639319472600588358599971 958979208900882537899957)
                ·
                  refine ⟨89904300834457737928121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 958979208900882537899957 89904300834457737928121)
                  ·
                    rfl

theorem cell21_393948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 2, 1, 5].length) (baseStart_393948 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_393948 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_393948 prefixEnd_393948 := by exact prefixLift 393948
  have htrace : WordTrace (prefixWord ++ tailWord_393948) baseStart_393948 baseEnd_393948 := by
    simpa [prefixWord, tailWord_393948, baseEnd_393948] using wordTrace_append hprefix tailTrace_393948
  have hstable : (prefixWord ++ tailWord_393948).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393948).length < 2 ^ (prefixWord ++ tailWord_393948).sum := by decide
  have hdescent : baseEnd_393948 < baseStart_393948 := by decide
  rcases family_descends (prefixWord ++ tailWord_393948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394013 : List Nat := [1, 4, 2, 4, 2, 1, 2, 1, 4]
def baseStart_394013 : Nat := 118140960795 + 394013 * 2 ^ 59
def prefixEnd_394013 : Nat := 4983230072969 + 3 ^ 40 * 394013 * 2
def baseEnd_394013 : Nat := 89919134720032069344655

theorem tailTrace_394013 : CollatzResearch.WordTrace tailWord_394013 prefixEnd_394013 89919134720032069344655 := by
  unfold tailWord_394013
  simp only [CollatzResearch.WordTrace]
  refine ⟨14370834721565667908114693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9580556481043778605409795 14370834721565667908114693)
  ·
    refine ⟨2694531510293562732771505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14370834721565667908114693 2694531510293562732771505)
    ·
      refine ⟨2020898632720172049578629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2694531510293562732771505 2020898632720172049578629)
      ·
        refine ⟨378918493635032259295993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2020898632720172049578629 378918493635032259295993)
        ·
          refine ⟨284188870226274194471995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 378918493635032259295993 284188870226274194471995)
          ·
            refine ⟨426283305339411291707993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284188870226274194471995 426283305339411291707993)
            ·
              refine ⟨319712479004558468780995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 426283305339411291707993 319712479004558468780995)
              ·
                refine ⟨479568718506837703171493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319712479004558468780995 479568718506837703171493)
                ·
                  refine ⟨89919134720032069344655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 479568718506837703171493 89919134720032069344655)
                  ·
                    rfl

theorem cell21_394013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 2, 1, 4].length) (baseStart_394013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394013 prefixEnd_394013 := by exact prefixLift 394013
  have htrace : WordTrace (prefixWord ++ tailWord_394013) baseStart_394013 baseEnd_394013 := by
    simpa [prefixWord, tailWord_394013, baseEnd_394013] using wordTrace_append hprefix tailTrace_394013
  have hstable : (prefixWord ++ tailWord_394013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394013).length < 2 ^ (prefixWord ++ tailWord_394013).sum := by decide
  have hdescent : baseEnd_394013 < baseStart_394013 := by decide
  rcases family_descends (prefixWord ++ tailWord_394013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394021 : List Nat := [1, 3, 1, 2, 3, 1, 3, 3, 4]
def baseStart_394021 : Nat := 118140960795 + 394021 * 2 ^ 59
def prefixEnd_394021 : Nat := 4983230072969 + 3 ^ 40 * 394021 * 2
def baseEnd_394021 : Nat := 89920960429025833211305

theorem tailTrace_394021 : CollatzResearch.WordTrace tailWord_394021 prefixEnd_394021 89920960429025833211305 := by
  unfold tailWord_394021
  simp only [CollatzResearch.WordTrace]
  refine ⟨14371126505536685274405917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9580751003691123516270611 14371126505536685274405917)
  ·
    refine ⟨5389172439576256977902219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14371126505536685274405917 5389172439576256977902219)
    ·
      refine ⟨8083758659364385466853329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5389172439576256977902219 8083758659364385466853329)
      ·
        refine ⟨6062818994523289100139997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8083758659364385466853329 6062818994523289100139997)
        ·
          refine ⟨2273557122946233412552499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6062818994523289100139997 2273557122946233412552499)
          ·
            refine ⟨3410335684419350118828749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2273557122946233412552499 3410335684419350118828749)
            ·
              refine ⟨1278875881657256294560781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3410335684419350118828749 1278875881657256294560781)
              ·
                refine ⟨479578455621471110460293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1278875881657256294560781 479578455621471110460293)
                ·
                  refine ⟨89920960429025833211305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 479578455621471110460293 89920960429025833211305)
                  ·
                    rfl

theorem cell21_394021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_394021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394021 prefixEnd_394021 := by exact prefixLift 394021
  have htrace : WordTrace (prefixWord ++ tailWord_394021) baseStart_394021 baseEnd_394021 := by
    simpa [prefixWord, tailWord_394021, baseEnd_394021] using wordTrace_append hprefix tailTrace_394021
  have hstable : (prefixWord ++ tailWord_394021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394021).length < 2 ^ (prefixWord ++ tailWord_394021).sum := by decide
  have hdescent : baseEnd_394021 < baseStart_394021 := by decide
  rcases family_descends (prefixWord ++ tailWord_394021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394035 : List Nat := [1, 1, 1, 2, 6, 1, 2, 7]
def baseStart_394035 : Nat := 118140960795 + 394035 * 2 ^ 59
def prefixEnd_394035 : Nat := 4983230072969 + 3 ^ 40 * 394035 * 2
def baseEnd_394035 : Nat := 29974718473254973325981

theorem tailTrace_394035 : CollatzResearch.WordTrace tailWord_394035 prefixEnd_394035 29974718473254973325981 := by
  unfold tailWord_394035
  simp only [CollatzResearch.WordTrace]
  refine ⟨14371637127485965665415559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9581091418323977110277039 14371637127485965665415559)
  ·
    refine ⟨21557455691228948498123339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14371637127485965665415559 21557455691228948498123339)
    ·
      refine ⟨32336183536843422747185009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21557455691228948498123339 32336183536843422747185009)
      ·
        refine ⟨24252137652632567060388757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32336183536843422747185009 24252137652632567060388757)
        ·
          refine ⟨1136818952467151580955723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24252137652632567060388757 1136818952467151580955723)
          ·
            refine ⟨1705228428700727371433585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1136818952467151580955723 1705228428700727371433585)
            ·
              refine ⟨1278921321525545528575189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1705228428700727371433585 1278921321525545528575189)
              ·
                refine ⟨29974718473254973325981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1278921321525545528575189 29974718473254973325981)
                ·
                  rfl

theorem cell21_394035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 2, 7].length) (baseStart_394035 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394035 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394035 prefixEnd_394035 := by exact prefixLift 394035
  have htrace : WordTrace (prefixWord ++ tailWord_394035) baseStart_394035 baseEnd_394035 := by
    simpa [prefixWord, tailWord_394035, baseEnd_394035] using wordTrace_append hprefix tailTrace_394035
  have hstable : (prefixWord ++ tailWord_394035).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394035).length < 2 ^ (prefixWord ++ tailWord_394035).sum := by decide
  have hdescent : baseEnd_394035 < baseStart_394035 := by decide
  rcases family_descends (prefixWord ++ tailWord_394035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394052 : List Nat := [2, 3, 4, 2, 10]
def baseStart_394052 : Nat := 118140960795 + 394052 * 2 ^ 59
def prefixEnd_394052 : Nat := 4983230072969 + 3 ^ 40 * 394052 * 2
def baseEnd_394052 : Nat := 1110222654955267508575

theorem tailTrace_394052 : CollatzResearch.WordTrace tailWord_394052 prefixEnd_394052 1110222654955267508575 := by
  unfold tailWord_394052
  simp only [CollatzResearch.WordTrace]
  refine ⟨7186128584212188784392205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9581504778949585045856273 7186128584212188784392205)
  ·
    refine ⟨2694798219079570794147077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7186128584212188784392205 2694798219079570794147077)
    ·
      refine ⟨505274666077419523902577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2694798219079570794147077 505274666077419523902577)
      ·
        refine ⟨378955999558064642926933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 505274666077419523902577 378955999558064642926933)
        ·
          refine ⟨1110222654955267508575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 378955999558064642926933 1110222654955267508575)
          ·
            rfl

theorem cell21_394052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 10].length) (baseStart_394052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394052 prefixEnd_394052 := by exact prefixLift 394052
  have htrace : WordTrace (prefixWord ++ tailWord_394052) baseStart_394052 baseEnd_394052 := by
    simpa [prefixWord, tailWord_394052, baseEnd_394052] using wordTrace_append hprefix tailTrace_394052
  have hstable : (prefixWord ++ tailWord_394052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394052).length < 2 ^ (prefixWord ++ tailWord_394052).sum := by decide
  have hdescent : baseEnd_394052 < baseStart_394052 := by decide
  rcases family_descends (prefixWord ++ tailWord_394052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394066 : List Nat := [3, 2, 2, 1, 1, 2, 2, 3, 5]
def baseStart_394066 : Nat := 118140960795 + 394066 * 2 ^ 59
def prefixEnd_394066 : Nat := 4983230072969 + 3 ^ 40 * 394066 * 2
def baseEnd_394066 : Nat := 89931230042115754961213

theorem tailTrace_394066 : CollatzResearch.WordTrace tailWord_394066 prefixEnd_394066 89931230042115754961213 := by
  unfold tailWord_394066
  simp only [CollatzResearch.WordTrace]
  refine ⟨3593191947593414489948513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9581845193582438639862701 3593191947593414489948513)
  ·
    refine ⟨2694893960695060867461385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3593191947593414489948513 2694893960695060867461385)
    ·
      refine ⟨2021170470521295650596039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2694893960695060867461385 2021170470521295650596039)
      ·
        refine ⟨3031755705781943475894059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2021170470521295650596039 3031755705781943475894059)
        ·
          refine ⟨4547633558672915213841089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3031755705781943475894059 4547633558672915213841089)
          ·
            refine ⟨3410725169004686410380817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4547633558672915213841089 3410725169004686410380817)
            ·
              refine ⟨2558043876753514807785613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3410725169004686410380817 2558043876753514807785613)
              ·
                refine ⟨959266453782568052919605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2558043876753514807785613 959266453782568052919605)
                ·
                  refine ⟨89931230042115754961213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 959266453782568052919605 89931230042115754961213)
                  ·
                    rfl

theorem cell21_394066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 3, 5].length) (baseStart_394066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394066 prefixEnd_394066 := by exact prefixLift 394066
  have htrace : WordTrace (prefixWord ++ tailWord_394066) baseStart_394066 baseEnd_394066 := by
    simpa [prefixWord, tailWord_394066, baseEnd_394066] using wordTrace_append hprefix tailTrace_394066
  have hstable : (prefixWord ++ tailWord_394066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394066).length < 2 ^ (prefixWord ++ tailWord_394066).sum := by decide
  have hdescent : baseEnd_394066 < baseStart_394066 := by decide
  rcases family_descends (prefixWord ++ tailWord_394066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394145 : List Nat := [1, 2, 3, 4, 1, 3, 2, 5]
def baseStart_394145 : Nat := 118140960795 + 394145 * 2 ^ 59
def prefixEnd_394145 : Nat := 4983230072969 + 3 ^ 40 * 394145 * 2
def baseEnd_394145 : Nat := 29983086306143057714795

theorem tailTrace_394145 : CollatzResearch.WordTrace tailWord_394145 prefixEnd_394145 29983086306143057714795 := by
  unfold tailWord_394145
  simp only [CollatzResearch.WordTrace]
  refine ⟨14375649157087454451919889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9583766104724969634613259 14375649157087454451919889)
  ·
    refine ⟨10781736867815590838939917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14375649157087454451919889 10781736867815590838939917)
    ·
      refine ⟨4043151325430846564602469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10781736867815590838939917 4043151325430846564602469)
      ·
        refine ⟨758090873518283730862963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4043151325430846564602469 758090873518283730862963)
        ·
          refine ⟨1137136310277425596294445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758090873518283730862963 1137136310277425596294445)
          ·
            refine ⟨426426116354034598610417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1137136310277425596294445 426426116354034598610417)
            ·
              refine ⟨319819587265525948957813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 426426116354034598610417 319819587265525948957813)
              ·
                refine ⟨29983086306143057714795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 319819587265525948957813 29983086306143057714795)
                ·
                  rfl

theorem cell21_394145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 5].length) (baseStart_394145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394145 prefixEnd_394145 := by exact prefixLift 394145
  have htrace : WordTrace (prefixWord ++ tailWord_394145) baseStart_394145 baseEnd_394145 := by
    simpa [prefixWord, tailWord_394145, baseEnd_394145] using wordTrace_append hprefix tailTrace_394145
  have hstable : (prefixWord ++ tailWord_394145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394145).length < 2 ^ (prefixWord ++ tailWord_394145).sum := by decide
  have hdescent : baseEnd_394145 < baseStart_394145 := by decide
  rcases family_descends (prefixWord ++ tailWord_394145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394176 : List Nat := [2, 1, 1, 2, 3, 4, 3, 2, 3]
def baseStart_394176 : Nat := 118140960795 + 394176 * 2 ^ 59
def prefixEnd_394176 : Nat := 4983230072969 + 3 ^ 40 * 394176 * 2
def baseEnd_394176 : Nat := 89956333540780008127655

theorem tailTrace_394176 : CollatzResearch.WordTrace tailWord_394176 prefixEnd_394176 89956333540780008127655 := by
  unfold tailWord_394176
  simp only [CollatzResearch.WordTrace]
  refine ⟨7188389909987573373149191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9584519879983431164198921 7188389909987573373149191)
  ·
    refine ⟨10782584864981360059723787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7188389909987573373149191 10782584864981360059723787)
    ·
      refine ⟨16173877297472040089585681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10782584864981360059723787 16173877297472040089585681)
      ·
        refine ⟨12130407973104030067189261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16173877297472040089585681 12130407973104030067189261)
        ·
          refine ⟨4548902989914011275195973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12130407973104030067189261 4548902989914011275195973)
          ·
            refine ⟨852919310608877114099245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4548902989914011275195973 852919310608877114099245)
            ·
              refine ⟨319844741478328917787217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 852919310608877114099245 319844741478328917787217)
              ·
                refine ⟨239883556108746688340413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319844741478328917787217 239883556108746688340413)
                ·
                  refine ⟨89956333540780008127655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 239883556108746688340413 89956333540780008127655)
                  ·
                    rfl

theorem cell21_394176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 3].length) (baseStart_394176 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394176 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394176 prefixEnd_394176 := by exact prefixLift 394176
  have htrace : WordTrace (prefixWord ++ tailWord_394176) baseStart_394176 baseEnd_394176 := by
    simpa [prefixWord, tailWord_394176, baseEnd_394176] using wordTrace_append hprefix tailTrace_394176
  have hstable : (prefixWord ++ tailWord_394176).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394176).length < 2 ^ (prefixWord ++ tailWord_394176).sum := by decide
  have hdescent : baseEnd_394176 < baseStart_394176 := by decide
  rcases family_descends (prefixWord ++ tailWord_394176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394187 : List Nat := [1, 1, 1, 1, 3, 6, 2, 6]
def baseStart_394187 : Nat := 118140960795 + 394187 * 2 ^ 59
def prefixEnd_394187 : Nat := 4983230072969 + 3 ^ 40 * 394187 * 2
def baseEnd_394187 : Nat := 29986281296882144481433

theorem tailTrace_394187 : CollatzResearch.WordTrace tailWord_394187 prefixEnd_394187 29986281296882144481433 := by
  unfold tailWord_394187
  simp only [CollatzResearch.WordTrace]
  refine ⟨14377181022935295624948815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9584787348623530416632543 14377181022935295624948815)
  ·
    refine ⟨21565771534402943437423223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14377181022935295624948815 21565771534402943437423223)
    ·
      refine ⟨32348657301604415156134835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21565771534402943437423223 32348657301604415156134835)
      ·
        refine ⟨48522985952406622734202253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32348657301604415156134835 48522985952406622734202253)
        ·
          refine ⟨18196119732152483525325845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48522985952406622734202253 18196119732152483525325845)
          ·
            refine ⟨852943112444647665249649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18196119732152483525325845 852943112444647665249649)
            ·
              refine ⟨639707334333485748937237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 852943112444647665249649 639707334333485748937237)
              ·
                refine ⟨29986281296882144481433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 639707334333485748937237 29986281296882144481433)
                ·
                  rfl

theorem cell21_394187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 2, 6].length) (baseStart_394187 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394187 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394187 prefixEnd_394187 := by exact prefixLift 394187
  have htrace : WordTrace (prefixWord ++ tailWord_394187) baseStart_394187 baseEnd_394187 := by
    simpa [prefixWord, tailWord_394187, baseEnd_394187] using wordTrace_append hprefix tailTrace_394187
  have hstable : (prefixWord ++ tailWord_394187).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394187).length < 2 ^ (prefixWord ++ tailWord_394187).sum := by decide
  have hdescent : baseEnd_394187 < baseStart_394187 := by decide
  rcases family_descends (prefixWord ++ tailWord_394187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394190 : List Nat := [4, 1, 1, 1, 2, 3, 4, 1, 4]
def baseStart_394190 : Nat := 118140960795 + 394190 * 2 ^ 59
def prefixEnd_394190 : Nat := 4983230072969 + 3 ^ 40 * 394190 * 2
def baseEnd_394190 : Nat := 89959528531519094894293

theorem tailTrace_394190 : CollatzResearch.WordTrace tailWord_394190 prefixEnd_394190 89959528531519094894293 := by
  unfold tailWord_394190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1797161305240553392163503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9584860294616284758205349 1797161305240553392163503)
  ·
    refine ⟨2695741957860830088245255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1797161305240553392163503 2695741957860830088245255)
    ·
      refine ⟨4043612936791245132367883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2695741957860830088245255 4043612936791245132367883)
      ·
        refine ⟨6065419405186867698551825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4043612936791245132367883 6065419405186867698551825)
        ·
          refine ⟨4549064553890150773913869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6065419405186867698551825 4549064553890150773913869)
          ·
            refine ⟨1705899207708806540217701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4549064553890150773913869 1705899207708806540217701)
            ·
              refine ⟨319856101445401226290819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1705899207708806540217701 319856101445401226290819)
              ·
                refine ⟨479784152168101839436229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319856101445401226290819 479784152168101839436229)
                ·
                  refine ⟨89959528531519094894293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 479784152168101839436229 89959528531519094894293)
                  ·
                    rfl

theorem cell21_394190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_394190 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394190 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394190 prefixEnd_394190 := by exact prefixLift 394190
  have htrace : WordTrace (prefixWord ++ tailWord_394190) baseStart_394190 baseEnd_394190 := by
    simpa [prefixWord, tailWord_394190, baseEnd_394190] using wordTrace_append hprefix tailTrace_394190
  have hstable : (prefixWord ++ tailWord_394190).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394190).length < 2 ^ (prefixWord ++ tailWord_394190).sum := by decide
  have hdescent : baseEnd_394190 < baseStart_394190 := by decide
  rcases family_descends (prefixWord ++ tailWord_394190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394238 : List Nat := [4, 2, 2, 2, 3, 1, 1, 6]
def baseStart_394238 : Nat := 118140960795 + 394238 * 2 ^ 59
def prefixEnd_394238 : Nat := 4983230072969 + 3 ^ 40 * 394238 * 2
def baseEnd_394238 : Nat := 29990160928493892698065

theorem tailTrace_394238 : CollatzResearch.WordTrace tailWord_394238 prefixEnd_394238 29990160928493892698065 := by
  unfold tailWord_394238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1797380143218816416881921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9586027430500354223370245 1797380143218816416881921)
  ·
    refine ⟨1348035107414112312661441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1797380143218816416881921 1348035107414112312661441)
    ·
      refine ⟨1011026330560584234496081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1348035107414112312661441 1011026330560584234496081)
      ·
        refine ⟨758269747920438175872061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1011026330560584234496081 758269747920438175872061)
        ·
          refine ⟨284351155470164315952023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 758269747920438175872061 284351155470164315952023)
          ·
            refine ⟨426526733205246473928035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284351155470164315952023 426526733205246473928035)
            ·
              refine ⟨639790099807869710892053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426526733205246473928035 639790099807869710892053)
              ·
                refine ⟨29990160928493892698065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 639790099807869710892053 29990160928493892698065)
                ·
                  rfl

theorem cell21_394238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 1, 6].length) (baseStart_394238 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394238 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394238 prefixEnd_394238 := by exact prefixLift 394238
  have htrace : WordTrace (prefixWord ++ tailWord_394238) baseStart_394238 baseEnd_394238 := by
    simpa [prefixWord, tailWord_394238, baseEnd_394238] using wordTrace_append hprefix tailTrace_394238
  have hstable : (prefixWord ++ tailWord_394238).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394238).length < 2 ^ (prefixWord ++ tailWord_394238).sum := by decide
  have hdescent : baseEnd_394238 < baseStart_394238 := by decide
  rcases family_descends (prefixWord ++ tailWord_394238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394277 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 7]
def baseStart_394277 : Nat := 118140960795 + 394277 * 2 ^ 59
def prefixEnd_394277 : Nat := 4983230072969 + 3 ^ 40 * 394277 * 2
def baseEnd_394277 : Nat := 89979383116826276944115

theorem tailTrace_394277 : CollatzResearch.WordTrace tailWord_394277 prefixEnd_394277 89979383116826276944115 := by
  unfold tailWord_394277
  simp only [CollatzResearch.WordTrace]
  refine ⟨14380463592609240995725085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9586975728406160663816723 14380463592609240995725085)
  ·
    refine ⟨5392673847228465373396907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14380463592609240995725085 5392673847228465373396907)
    ·
      refine ⟨8089010770842698060095361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5392673847228465373396907 8089010770842698060095361)
      ·
        refine ⟨6066758078132023545071521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8089010770842698060095361 6066758078132023545071521)
        ·
          refine ⟨4550068558599017658803641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6066758078132023545071521 4550068558599017658803641)
          ·
            refine ⟨3412551418949263244102731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4550068558599017658803641 3412551418949263244102731)
            ·
              refine ⟨5118827128423894866154097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3412551418949263244102731 5118827128423894866154097)
              ·
                refine ⟨3839120346317921149615573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5118827128423894866154097 3839120346317921149615573)
                ·
                  refine ⟨89979383116826276944115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3839120346317921149615573 89979383116826276944115)
                  ·
                    rfl

theorem cell21_394277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 7].length) (baseStart_394277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394277 prefixEnd_394277 := by exact prefixLift 394277
  have htrace : WordTrace (prefixWord ++ tailWord_394277) baseStart_394277 baseEnd_394277 := by
    simpa [prefixWord, tailWord_394277, baseEnd_394277] using wordTrace_append hprefix tailTrace_394277
  have hstable : (prefixWord ++ tailWord_394277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394277).length < 2 ^ (prefixWord ++ tailWord_394277).sum := by decide
  have hdescent : baseEnd_394277 < baseStart_394277 := by decide
  rcases family_descends (prefixWord ++ tailWord_394277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394353 : List Nat := [1, 2, 2, 2, 1, 1, 2, 5, 5]
def baseStart_394353 : Nat := 118140960795 + 394353 * 2 ^ 59
def prefixEnd_394353 : Nat := 4983230072969 + 3 ^ 40 * 394353 * 2
def baseEnd_394353 : Nat := 89996727352267033677293

theorem tailTrace_394353 : CollatzResearch.WordTrace tailWord_394353 prefixEnd_394353 89996727352267033677293 := by
  unfold tailWord_394353
  simp only [CollatzResearch.WordTrace]
  refine ⟨14383235540333905975491713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9588823693555937316994475 14383235540333905975491713)
  ·
    refine ⟨10787426655250429481618785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14383235540333905975491713 10787426655250429481618785)
    ·
      refine ⟨8090569991437822111214089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10787426655250429481618785 8090569991437822111214089)
      ·
        refine ⟨6067927493578366583410567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8090569991437822111214089 6067927493578366583410567)
        ·
          refine ⟨9101891240367549875115851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6067927493578366583410567 9101891240367549875115851)
          ·
            refine ⟨13652836860551324812673777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9101891240367549875115851 13652836860551324812673777)
            ·
              refine ⟨10239627645413493609505333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13652836860551324812673777 10239627645413493609505333)
              ·
                refine ⟨959965091757515025891125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10239627645413493609505333 959965091757515025891125)
                ·
                  refine ⟨89996727352267033677293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 959965091757515025891125 89996727352267033677293)
                  ·
                    rfl

theorem cell21_394353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 5, 5].length) (baseStart_394353 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394353 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394353 prefixEnd_394353 := by exact prefixLift 394353
  have htrace : WordTrace (prefixWord ++ tailWord_394353) baseStart_394353 baseEnd_394353 := by
    simpa [prefixWord, tailWord_394353, baseEnd_394353] using wordTrace_append hprefix tailTrace_394353
  have hstable : (prefixWord ++ tailWord_394353).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394353).length < 2 ^ (prefixWord ++ tailWord_394353).sum := by decide
  have hdescent : baseEnd_394353 < baseStart_394353 := by decide
  rcases family_descends (prefixWord ++ tailWord_394353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394401 : List Nat := [1, 2, 3, 3, 1, 1, 4, 2, 4]
def baseStart_394401 : Nat := 118140960795 + 394401 * 2 ^ 59
def prefixEnd_394401 : Nat := 4983230072969 + 3 ^ 40 * 394401 * 2
def baseEnd_394401 : Nat := 90007681606229616877195

theorem tailTrace_394401 : CollatzResearch.WordTrace tailWord_394401 prefixEnd_394401 90007681606229616877195 := by
  unfold tailWord_394401
  simp only [CollatzResearch.WordTrace]
  refine ⟨14384986244160010173239057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9589990829440006782159371 14384986244160010173239057)
  ·
    refine ⟨10788739683120007629929293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14384986244160010173239057 10788739683120007629929293)
    ·
      refine ⟨4045777381170002861223485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10788739683120007629929293 4045777381170002861223485)
      ·
        refine ⟨1517166517938751072958807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4045777381170002861223485 1517166517938751072958807)
        ·
          refine ⟨2275749776908126609438211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1517166517938751072958807 2275749776908126609438211)
          ·
            refine ⟨3413624665362189914157317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2275749776908126609438211 3413624665362189914157317)
            ·
              refine ⟨640054624755410608904497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3413624665362189914157317 640054624755410608904497)
              ·
                refine ⟨480040968566557956678373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640054624755410608904497 480040968566557956678373)
                ·
                  refine ⟨90007681606229616877195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 480040968566557956678373 90007681606229616877195)
                  ·
                    rfl

theorem cell21_394401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 4].length) (baseStart_394401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394401 prefixEnd_394401 := by exact prefixLift 394401
  have htrace : WordTrace (prefixWord ++ tailWord_394401) baseStart_394401 baseEnd_394401 := by
    simpa [prefixWord, tailWord_394401, baseEnd_394401] using wordTrace_append hprefix tailTrace_394401
  have hstable : (prefixWord ++ tailWord_394401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394401).length < 2 ^ (prefixWord ++ tailWord_394401).sum := by decide
  have hdescent : baseEnd_394401 < baseStart_394401 := by decide
  rcases family_descends (prefixWord ++ tailWord_394401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394404 : List Nat := [2, 3, 1, 2, 3, 1, 4, 2, 3]
def baseStart_394404 : Nat := 118140960795 + 394404 * 2 ^ 59
def prefixEnd_394404 : Nat := 4983230072969 + 3 ^ 40 * 394404 * 2
def baseEnd_394404 : Nat := 90008366247102278327189

theorem tailTrace_394404 : CollatzResearch.WordTrace tailWord_394404 prefixEnd_394404 90008366247102278327189 := by
  unfold tailWord_394404
  simp only [CollatzResearch.WordTrace]
  refine ⟨7192547831574570842799133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9590063775432761123732177 7192547831574570842799133)
  ·
    refine ⟨2697205436840464066049675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7192547831574570842799133 2697205436840464066049675)
    ·
      refine ⟨4045808155260696099074513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2697205436840464066049675 4045808155260696099074513)
      ·
        refine ⟨3034356116445522074305885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4045808155260696099074513 3034356116445522074305885)
        ·
          refine ⟨1137883543667070777864707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3034356116445522074305885 1137883543667070777864707)
          ·
            refine ⟨1706825315500606166797061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137883543667070777864707 1706825315500606166797061)
            ·
              refine ⟨320029746656363656274449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1706825315500606166797061 320029746656363656274449)
              ·
                refine ⟨240022309992272742205837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320029746656363656274449 240022309992272742205837)
                ·
                  refine ⟨90008366247102278327189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240022309992272742205837 90008366247102278327189)
                  ·
                    rfl

theorem cell21_394404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 4, 2, 3].length) (baseStart_394404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394404 prefixEnd_394404 := by exact prefixLift 394404
  have htrace : WordTrace (prefixWord ++ tailWord_394404) baseStart_394404 baseEnd_394404 := by
    simpa [prefixWord, tailWord_394404, baseEnd_394404] using wordTrace_append hprefix tailTrace_394404
  have hstable : (prefixWord ++ tailWord_394404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394404).length < 2 ^ (prefixWord ++ tailWord_394404).sum := by decide
  have hdescent : baseEnd_394404 < baseStart_394404 := by decide
  rcases family_descends (prefixWord ++ tailWord_394404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394429 : List Nat := [1, 4, 1, 2, 1, 1, 3, 1, 7]
def baseStart_394429 : Nat := 118140960795 + 394429 * 2 ^ 59
def prefixEnd_394429 : Nat := 4983230072969 + 3 ^ 40 * 394429 * 2
def baseEnd_394429 : Nat := 90014071587707790410471

theorem tailTrace_394429 : CollatzResearch.WordTrace tailWord_394429 prefixEnd_394429 90014071587707790410471 := by
  unfold tailWord_394429
  simp only [CollatzResearch.WordTrace]
  refine ⟨14386007488058570955258341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9590671658705713970172227 14386007488058570955258341)
  ·
    refine ⟨2697376404010982054110939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14386007488058570955258341 2697376404010982054110939)
    ·
      refine ⟨4046064606016473081166409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2697376404010982054110939 4046064606016473081166409)
      ·
        refine ⟨3034548454512354810874807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4046064606016473081166409 3034548454512354810874807)
        ·
          refine ⟨4551822681768532216312211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3034548454512354810874807 4551822681768532216312211)
          ·
            refine ⟨6827734022652798324468317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4551822681768532216312211 6827734022652798324468317)
            ·
              refine ⟨2560400258494799371675619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6827734022652798324468317 2560400258494799371675619)
              ·
                refine ⟨3840600387742199057513429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2560400258494799371675619 3840600387742199057513429)
                ·
                  refine ⟨90014071587707790410471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3840600387742199057513429 90014071587707790410471)
                  ·
                    rfl

theorem cell21_394429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_394429 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394429 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394429 prefixEnd_394429 := by exact prefixLift 394429
  have htrace : WordTrace (prefixWord ++ tailWord_394429) baseStart_394429 baseEnd_394429 := by
    simpa [prefixWord, tailWord_394429, baseEnd_394429] using wordTrace_append hprefix tailTrace_394429
  have hstable : (prefixWord ++ tailWord_394429).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394429).length < 2 ^ (prefixWord ++ tailWord_394429).sum := by decide
  have hdescent : baseEnd_394429 < baseStart_394429 := by decide
  rcases family_descends (prefixWord ++ tailWord_394429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394432 : List Nat := [2, 1, 1, 2, 6, 1, 3, 5]
def baseStart_394432 : Nat := 118140960795 + 394432 * 2 ^ 59
def prefixEnd_394432 : Nat := 4983230072969 + 3 ^ 40 * 394432 * 2
def baseEnd_394432 : Nat := 30004918742860150620155

theorem tailTrace_394432 : CollatzResearch.WordTrace tailWord_394432 prefixEnd_394432 30004918742860150620155 := by
  unfold tailWord_394432
  simp only [CollatzResearch.WordTrace]
  refine ⟨7193058453523851233808775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9590744604698468311745033 7193058453523851233808775)
  ·
    refine ⟨10789587680285776850713163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7193058453523851233808775 10789587680285776850713163)
    ·
      refine ⟨16184381520428665276069745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10789587680285776850713163 16184381520428665276069745)
      ·
        refine ⟨12138286140321498957052309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16184381520428665276069745 12138286140321498957052309)
        ·
          refine ⟨568982162827570263611827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12138286140321498957052309 568982162827570263611827)
          ·
            refine ⟨853473244241355395417741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568982162827570263611827 853473244241355395417741)
            ·
              refine ⟨320052466590508273281653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 853473244241355395417741 320052466590508273281653)
              ·
                refine ⟨30004918742860150620155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 320052466590508273281653 30004918742860150620155)
                ·
                  rfl

theorem cell21_394432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 5].length) (baseStart_394432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394432 prefixEnd_394432 := by exact prefixLift 394432
  have htrace : WordTrace (prefixWord ++ tailWord_394432) baseStart_394432 baseEnd_394432 := by
    simpa [prefixWord, tailWord_394432, baseEnd_394432] using wordTrace_append hprefix tailTrace_394432
  have hstable : (prefixWord ++ tailWord_394432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394432).length < 2 ^ (prefixWord ++ tailWord_394432).sum := by decide
  have hdescent : baseEnd_394432 < baseStart_394432 := by decide
  rcases family_descends (prefixWord ++ tailWord_394432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394452 : List Nat := [2, 4, 1, 4, 2, 1, 1, 2, 4]
def baseStart_394452 : Nat := 118140960795 + 394452 * 2 ^ 59
def prefixEnd_394452 : Nat := 4983230072969 + 3 ^ 40 * 394452 * 2
def baseEnd_394452 : Nat := 90019320501064861527091

theorem tailTrace_394452 : CollatzResearch.WordTrace tailWord_394452 prefixEnd_394452 90019320501064861527091 := by
  unfold tailWord_394452
  simp only [CollatzResearch.WordTrace]
  refine ⟨7193423183487622941672805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9591230911316830588897073 7193423183487622941672805)
  ·
    refine ⟨1348766846903929301563651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7193423183487622941672805 1348766846903929301563651)
    ·
      refine ⟨2023150270355893952345477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1348766846903929301563651 2023150270355893952345477)
      ·
        refine ⟨379340675691730116064777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2023150270355893952345477 379340675691730116064777)
        ·
          refine ⟨284505506768797587048583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 379340675691730116064777 284505506768797587048583)
          ·
            refine ⟨426758260153196380572875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284505506768797587048583 426758260153196380572875)
            ·
              refine ⟨640137390229794570859313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426758260153196380572875 640137390229794570859313)
              ·
                refine ⟨480103042672345928144485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640137390229794570859313 480103042672345928144485)
                ·
                  refine ⟨90019320501064861527091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 480103042672345928144485 90019320501064861527091)
                  ·
                    rfl

theorem cell21_394452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 4].length) (baseStart_394452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394452 prefixEnd_394452 := by exact prefixLift 394452
  have htrace : WordTrace (prefixWord ++ tailWord_394452) baseStart_394452 baseEnd_394452 := by
    simpa [prefixWord, tailWord_394452, baseEnd_394452] using wordTrace_append hprefix tailTrace_394452
  have hstable : (prefixWord ++ tailWord_394452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394452).length < 2 ^ (prefixWord ++ tailWord_394452).sum := by decide
  have hdescent : baseEnd_394452 < baseStart_394452 := by decide
  rcases family_descends (prefixWord ++ tailWord_394452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394514 : List Nat := [3, 2, 4, 2, 1, 1, 3, 2, 3]
def baseStart_394514 : Nat := 118140960795 + 394514 * 2 ^ 59
def prefixEnd_394514 : Nat := 4983230072969 + 3 ^ 40 * 394514 * 2
def baseEnd_394514 : Nat := 90033469745766531493631

theorem tailTrace_394514 : CollatzResearch.WordTrace tailWord_394514 prefixEnd_394514 90033469745766531493631 := by
  unfold tailWord_394514
  simp only [CollatzResearch.WordTrace]
  refine ⟨3597276923187657618025649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9592738461833753648068397 3597276923187657618025649)
  ·
    refine ⟨2697957692390743213519237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3597276923187657618025649 2697957692390743213519237)
    ·
      refine ⟨505867067323264352534857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2697957692390743213519237 505867067323264352534857)
      ·
        refine ⟨379400300492448264401143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 505867067323264352534857 379400300492448264401143)
        ·
          refine ⟨569100450738672396601715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379400300492448264401143 569100450738672396601715)
          ·
            refine ⟨853650676108008594902573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569100450738672396601715 853650676108008594902573)
            ·
              refine ⟨320119003540503223088465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 853650676108008594902573 320119003540503223088465)
              ·
                refine ⟨240089252655377417316349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320119003540503223088465 240089252655377417316349)
                ·
                  refine ⟨90033469745766531493631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240089252655377417316349 90033469745766531493631)
                  ·
                    rfl

theorem cell21_394514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 3, 2, 3].length) (baseStart_394514 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394514 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394514 prefixEnd_394514 := by exact prefixLift 394514
  have htrace : WordTrace (prefixWord ++ tailWord_394514) baseStart_394514 baseEnd_394514 := by
    simpa [prefixWord, tailWord_394514, baseEnd_394514] using wordTrace_append hprefix tailTrace_394514
  have hstable : (prefixWord ++ tailWord_394514).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394514).length < 2 ^ (prefixWord ++ tailWord_394514).sum := by decide
  have hdescent : baseEnd_394514 < baseStart_394514 := by decide
  rcases family_descends (prefixWord ++ tailWord_394514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394522 : List Nat := [3, 1, 1, 3, 3, 1, 3, 1, 5]
def baseStart_394522 : Nat := 118140960795 + 394522 * 2 ^ 59
def prefixEnd_394522 : Nat := 4983230072969 + 3 ^ 40 * 394522 * 2
def baseEnd_394522 : Nat := 90035295454760295360281

theorem tailTrace_394522 : CollatzResearch.WordTrace tailWord_394522 prefixEnd_394522 90035295454760295360281 := by
  unfold tailWord_394522
  simp only [CollatzResearch.WordTrace]
  refine ⟨3597349869180411959598455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9592932984481098558929213 3597349869180411959598455)
  ·
    refine ⟨5396024803770617939397683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3597349869180411959598455 5396024803770617939397683)
    ·
      refine ⟨8094037205655926909096525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5396024803770617939397683 8094037205655926909096525)
      ·
        refine ⟨3035263952120972590911197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8094037205655926909096525 3035263952120972590911197)
        ·
          refine ⟨1138223982045364721591699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3035263952120972590911197 1138223982045364721591699)
          ·
            refine ⟨1707335973068047082387549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1138223982045364721591699 1707335973068047082387549)
            ·
              refine ⟨640250989900517655895331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1707335973068047082387549 640250989900517655895331)
              ·
                refine ⟨960376484850776483842997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640250989900517655895331 960376484850776483842997)
                ·
                  refine ⟨90035295454760295360281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 960376484850776483842997 90035295454760295360281)
                  ·
                    rfl

theorem cell21_394522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 3, 1, 5].length) (baseStart_394522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394522 prefixEnd_394522 := by exact prefixLift 394522
  have htrace : WordTrace (prefixWord ++ tailWord_394522) baseStart_394522 baseEnd_394522 := by
    simpa [prefixWord, tailWord_394522, baseEnd_394522] using wordTrace_append hprefix tailTrace_394522
  have hstable : (prefixWord ++ tailWord_394522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394522).length < 2 ^ (prefixWord ++ tailWord_394522).sum := by decide
  have hdescent : baseEnd_394522 < baseStart_394522 := by decide
  rcases family_descends (prefixWord ++ tailWord_394522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394573 : List Nat := [1, 6, 1, 3, 1, 1, 1, 4, 3]
def baseStart_394573 : Nat := 118140960795 + 394573 * 2 ^ 59
def prefixEnd_394573 : Nat := 4983230072969 + 3 ^ 40 * 394573 * 2
def baseEnd_394573 : Nat := 90046934349595540010177

theorem tailTrace_394573 : CollatzResearch.WordTrace tailWord_394573 prefixEnd_394573 90046934349595540010177 := by
  unfold tailWord_394573
  simp only [CollatzResearch.WordTrace]
  refine ⟨14391259599536883548500373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9594173066357922365666915 14391259599536883548500373)
  ·
    refine ⟨674590293728291416335955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14391259599536883548500373 674590293728291416335955)
    ·
      refine ⟨1011885440592437124503933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 674590293728291416335955 1011885440592437124503933)
      ·
        refine ⟨379457040222163921688975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1011885440592437124503933 379457040222163921688975)
        ·
          refine ⟨569185560333245882533463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379457040222163921688975 569185560333245882533463)
          ·
            refine ⟨853778340499868823800195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569185560333245882533463 853778340499868823800195)
            ·
              refine ⟨1280667510749803235700293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853778340499868823800195 1280667510749803235700293)
              ·
                refine ⟨240125158265588106693805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1280667510749803235700293 240125158265588106693805)
                ·
                  refine ⟨90046934349595540010177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240125158265588106693805 90046934349595540010177)
                  ·
                    rfl

theorem cell21_394573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_394573 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394573 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394573 prefixEnd_394573 := by exact prefixLift 394573
  have htrace : WordTrace (prefixWord ++ tailWord_394573) baseStart_394573 baseEnd_394573 := by
    simpa [prefixWord, tailWord_394573, baseEnd_394573] using wordTrace_append hprefix tailTrace_394573
  have hstable : (prefixWord ++ tailWord_394573).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394573).length < 2 ^ (prefixWord ++ tailWord_394573).sum := by decide
  have hdescent : baseEnd_394573 < baseStart_394573 := by decide
  rcases family_descends (prefixWord ++ tailWord_394573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394674 : List Nat := [3, 2, 1, 1, 1, 1, 2, 7, 3]
def baseStart_394674 : Nat := 118140960795 + 394674 * 2 ^ 59
def prefixEnd_394674 : Nat := 4983230072969 + 3 ^ 40 * 394674 * 2
def baseEnd_394674 : Nat := 90069983925641808826637

theorem tailTrace_394674 : CollatzResearch.WordTrace tailWord_394674 prefixEnd_394674 90069983925641808826637 := by
  unfold tailWord_394674
  simp only [CollatzResearch.WordTrace]
  refine ⟨3598735843042744449481769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9596628914780651865284717 3598735843042744449481769)
  ·
    refine ⟨2699051882282058337111327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3598735843042744449481769 2699051882282058337111327)
    ·
      refine ⟨4048577823423087505666991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2699051882282058337111327 4048577823423087505666991)
      ·
        refine ⟨6072866735134631258500487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4048577823423087505666991 6072866735134631258500487)
        ·
          refine ⟨9109300102701946887750731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6072866735134631258500487 9109300102701946887750731)
          ·
            refine ⟨13663950154052920331626097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9109300102701946887750731 13663950154052920331626097)
            ·
              refine ⟨10247962615539690248719573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13663950154052920331626097 10247962615539690248719573)
              ·
                refine ⟨240186623801711490204365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 10247962615539690248719573 240186623801711490204365)
                ·
                  refine ⟨90069983925641808826637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240186623801711490204365 90069983925641808826637)
                  ·
                    rfl

theorem cell21_394674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 7, 3].length) (baseStart_394674 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394674 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394674 prefixEnd_394674 := by exact prefixLift 394674
  have htrace : WordTrace (prefixWord ++ tailWord_394674) baseStart_394674 baseEnd_394674 := by
    simpa [prefixWord, tailWord_394674, baseEnd_394674] using wordTrace_append hprefix tailTrace_394674
  have hstable : (prefixWord ++ tailWord_394674).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394674).length < 2 ^ (prefixWord ++ tailWord_394674).sum := by decide
  have hdescent : baseEnd_394674 < baseStart_394674 := by decide
  rcases family_descends (prefixWord ++ tailWord_394674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394702 : List Nat := [4, 1, 1, 1, 2, 1, 3, 8]
def baseStart_394702 : Nat := 118140960795 + 394702 * 2 ^ 59
def prefixEnd_394702 : Nat := 4983230072969 + 3 ^ 40 * 394702 * 2
def baseEnd_394702 : Nat := 30025457969039994119971

theorem tailTrace_394702 : CollatzResearch.WordTrace tailWord_394702 prefixEnd_394702 30025457969039994119971 := by
  unfold tailWord_394702
  simp only [CollatzResearch.WordTrace]
  refine ⟨1799495577008692322493295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9597309744046359053297573 1799495577008692322493295)
  ·
    refine ⟨2699243365513038483739943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1799495577008692322493295 2699243365513038483739943)
    ·
      refine ⟨4048865048269557725609915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2699243365513038483739943 4048865048269557725609915)
      ·
        refine ⟨6073297572404336588414873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4048865048269557725609915 6073297572404336588414873)
        ·
          refine ⟨4554973179303252441311155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6073297572404336588414873 4554973179303252441311155)
          ·
            refine ⟨6832459768954878661966733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4554973179303252441311155 6832459768954878661966733)
            ·
              refine ⟨2562172413358079498237525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6832459768954878661966733 2562172413358079498237525)
              ·
                refine ⟨30025457969039994119971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2562172413358079498237525 30025457969039994119971)
                ·
                  rfl

theorem cell21_394702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 8].length) (baseStart_394702 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394702 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394702 prefixEnd_394702 := by exact prefixLift 394702
  have htrace : WordTrace (prefixWord ++ tailWord_394702) baseStart_394702 baseEnd_394702 := by
    simpa [prefixWord, tailWord_394702, baseEnd_394702] using wordTrace_append hprefix tailTrace_394702
  have hstable : (prefixWord ++ tailWord_394702).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394702).length < 2 ^ (prefixWord ++ tailWord_394702).sum := by decide
  have hdescent : baseEnd_394702 < baseStart_394702 := by decide
  rcases family_descends (prefixWord ++ tailWord_394702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394798 : List Nat := [4, 1, 3, 1, 2, 3, 1, 2, 4]
def baseStart_394798 : Nat := 118140960795 + 394798 * 2 ^ 59
def prefixEnd_394798 : Nat := 4983230072969 + 3 ^ 40 * 394798 * 2
def baseEnd_394798 : Nat := 90098282415045148759717

theorem tailTrace_394798 : CollatzResearch.WordTrace tailWord_394798 prefixEnd_394798 90098282415045148759717 := by
  unfold tailWord_394798
  simp only [CollatzResearch.WordTrace]
  refine ⟨1799933252965218371930131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9599644015814497983627365 1799933252965218371930131)
  ·
    refine ⟨2699899879447827557895197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1799933252965218371930131 2699899879447827557895197)
    ·
      refine ⟨1012462454792935334210699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2699899879447827557895197 1012462454792935334210699)
      ·
        refine ⟨1518693682189403001316049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012462454792935334210699 1518693682189403001316049)
        ·
          refine ⟨1139020261642052250987037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1518693682189403001316049 1139020261642052250987037)
          ·
            refine ⟨427132598115769594120139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1139020261642052250987037 427132598115769594120139)
            ·
              refine ⟨640698897173654391180209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427132598115769594120139 640698897173654391180209)
              ·
                refine ⟨480524172880240793385157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640698897173654391180209 480524172880240793385157)
                ·
                  refine ⟨90098282415045148759717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 480524172880240793385157 90098282415045148759717)
                  ·
                    rfl

theorem cell21_394798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 3, 1, 2, 4].length) (baseStart_394798 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394798 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394798 prefixEnd_394798 := by exact prefixLift 394798
  have htrace : WordTrace (prefixWord ++ tailWord_394798) baseStart_394798 baseEnd_394798 := by
    simpa [prefixWord, tailWord_394798, baseEnd_394798] using wordTrace_append hprefix tailTrace_394798
  have hstable : (prefixWord ++ tailWord_394798).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394798).length < 2 ^ (prefixWord ++ tailWord_394798).sum := by decide
  have hdescent : baseEnd_394798 < baseStart_394798 := by decide
  rcases family_descends (prefixWord ++ tailWord_394798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394809 : List Nat := [1, 2, 1, 5, 1, 2, 1, 3, 5]
def baseStart_394809 : Nat := 118140960795 + 394809 * 2 ^ 59
def prefixEnd_394809 : Nat := 4983230072969 + 3 ^ 40 * 394809 * 2
def baseEnd_394809 : Nat := 90100792764911574076361

theorem tailTrace_394809 : CollatzResearch.WordTrace tailWord_394809 prefixEnd_394809 90100792764911574076361 := by
  unfold tailWord_394809
  simp only [CollatzResearch.WordTrace]
  refine ⟨14399867226681895854091481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9599911484454597236060987 14399867226681895854091481)
  ·
    refine ⟨10799900420011421890568611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14399867226681895854091481 10799900420011421890568611)
    ·
      refine ⟨16199850630017132835852917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10799900420011421890568611 16199850630017132835852917)
      ·
        refine ⟨1518735996564106203361211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16199850630017132835852917 1518735996564106203361211)
        ·
          refine ⟨2278103994846159305041817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1518735996564106203361211 2278103994846159305041817)
          ·
            refine ⟨1708577996134619478781363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2278103994846159305041817 1708577996134619478781363)
            ·
              refine ⟨2562866994201929218172045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1708577996134619478781363 2562866994201929218172045)
              ·
                refine ⟨961075122825723456814517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2562866994201929218172045 961075122825723456814517)
                ·
                  refine ⟨90100792764911574076361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 961075122825723456814517 90100792764911574076361)
                  ·
                    rfl

theorem cell21_394809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 3, 5].length) (baseStart_394809 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394809 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394809 prefixEnd_394809 := by exact prefixLift 394809
  have htrace : WordTrace (prefixWord ++ tailWord_394809) baseStart_394809 baseEnd_394809 := by
    simpa [prefixWord, tailWord_394809, baseEnd_394809] using wordTrace_append hprefix tailTrace_394809
  have hstable : (prefixWord ++ tailWord_394809).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394809).length < 2 ^ (prefixWord ++ tailWord_394809).sum := by decide
  have hdescent : baseEnd_394809 < baseStart_394809 := by decide
  rcases family_descends (prefixWord ++ tailWord_394809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394829 : List Nat := [1, 6, 1, 1, 3, 2, 2, 5]
def baseStart_394829 : Nat := 118140960795 + 394829 * 2 ^ 59
def prefixEnd_394829 : Nat := 4983230072969 + 3 ^ 40 * 394829 * 2
def baseEnd_394829 : Nat := 30035119012465327914329

theorem tailTrace_394829 : CollatzResearch.WordTrace tailWord_394829 prefixEnd_394829 30035119012465327914329 := by
  unfold tailWord_394829
  simp only [CollatzResearch.WordTrace]
  refine ⟨14400596686609439269819541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9600397791072959513213027 14400596686609439269819541)
  ·
    refine ⟨675027969684817465772791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14400596686609439269819541 675027969684817465772791)
    ·
      refine ⟨1012541954527226198659187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 675027969684817465772791 1012541954527226198659187)
      ·
        refine ⟨1518812931790839297988781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1012541954527226198659187 1518812931790839297988781)
        ·
          refine ⟨569554849421564736745793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1518812931790839297988781 569554849421564736745793)
          ·
            refine ⟨427166137066173552559345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 569554849421564736745793 427166137066173552559345)
            ·
              refine ⟨320374602799630164419509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427166137066173552559345 320374602799630164419509)
              ·
                refine ⟨30035119012465327914329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 320374602799630164419509 30035119012465327914329)
                ·
                  rfl

theorem cell21_394829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 2, 5].length) (baseStart_394829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394829 prefixEnd_394829 := by exact prefixLift 394829
  have htrace : WordTrace (prefixWord ++ tailWord_394829) baseStart_394829 baseEnd_394829 := by
    simpa [prefixWord, tailWord_394829, baseEnd_394829] using wordTrace_append hprefix tailTrace_394829
  have hstable : (prefixWord ++ tailWord_394829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394829).length < 2 ^ (prefixWord ++ tailWord_394829).sum := by decide
  have hdescent : baseEnd_394829 < baseStart_394829 := by decide
  rcases family_descends (prefixWord ++ tailWord_394829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394916 : List Nat := [2, 3, 1, 2, 2, 2, 1, 4, 4]
def baseStart_394916 : Nat := 118140960795 + 394916 * 2 ^ 59
def prefixEnd_394916 : Nat := 4983230072969 + 3 ^ 40 * 394916 * 2
def baseEnd_394916 : Nat := 90125211622703165792809

theorem tailTrace_394916 : CollatzResearch.WordTrace tailWord_394916 prefixEnd_394916 90125211622703165792809 := by
  unfold tailWord_394916
  simp only [CollatzResearch.WordTrace]
  refine ⟨7201884918647126564118301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9602513224862835418824401 7201884918647126564118301)
  ·
    refine ⟨2700706844492672461544363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7201884918647126564118301 2700706844492672461544363)
    ·
      refine ⟨4051060266739008692316545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2700706844492672461544363 4051060266739008692316545)
      ·
        refine ⟨3038295200054256519237409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4051060266739008692316545 3038295200054256519237409)
        ·
          refine ⟨2278721400040692389428057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3038295200054256519237409 2278721400040692389428057)
          ·
            refine ⟨1709041050030519292071043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2278721400040692389428057 1709041050030519292071043)
            ·
              refine ⟨2563561575045778938106565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709041050030519292071043 2563561575045778938106565)
              ·
                refine ⟨480667795321083550894981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2563561575045778938106565 480667795321083550894981)
                ·
                  refine ⟨90125211622703165792809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 480667795321083550894981 90125211622703165792809)
                  ·
                    rfl

theorem cell21_394916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_394916 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394916 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394916 prefixEnd_394916 := by exact prefixLift 394916
  have htrace : WordTrace (prefixWord ++ tailWord_394916) baseStart_394916 baseEnd_394916 := by
    simpa [prefixWord, tailWord_394916, baseEnd_394916] using wordTrace_append hprefix tailTrace_394916
  have hstable : (prefixWord ++ tailWord_394916).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394916).length < 2 ^ (prefixWord ++ tailWord_394916).sum := by decide
  have hdescent : baseEnd_394916 < baseStart_394916 := by decide
  rcases family_descends (prefixWord ++ tailWord_394916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394930 : List Nat := [3, 2, 1, 1, 1, 2, 5, 6]
def baseStart_394930 : Nat := 118140960795 + 394930 * 2 ^ 59
def prefixEnd_394930 : Nat := 4983230072969 + 3 ^ 40 * 394930 * 2
def baseEnd_394930 : Nat := 30042802204480750853149

theorem tailTrace_394930 : CollatzResearch.WordTrace tailWord_394930 prefixEnd_394930 30042802204480750853149 := by
  unfold tailWord_394930
  simp only [CollatzResearch.WordTrace]
  refine ⟨3601070114810883379811561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9602853639495689012830829 3601070114810883379811561)
  ·
    refine ⟨2700802586108162534858671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3601070114810883379811561 2700802586108162534858671)
    ·
      refine ⟨4051203879162243802288007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2700802586108162534858671 4051203879162243802288007)
      ·
        refine ⟨6076805818743365703432011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4051203879162243802288007 6076805818743365703432011)
        ·
          refine ⟨9115208728115048555148017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6076805818743365703432011 9115208728115048555148017)
          ·
            refine ⟨6836406546086286416361013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9115208728115048555148017 6836406546086286416361013)
            ·
              refine ⟨640913113695589351533845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6836406546086286416361013 640913113695589351533845)
              ·
                refine ⟨30042802204480750853149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 640913113695589351533845 30042802204480750853149)
                ·
                  rfl

theorem cell21_394930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_394930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394930 prefixEnd_394930 := by exact prefixLift 394930
  have htrace : WordTrace (prefixWord ++ tailWord_394930) baseStart_394930 baseEnd_394930 := by
    simpa [prefixWord, tailWord_394930, baseEnd_394930] using wordTrace_append hprefix tailTrace_394930
  have hstable : (prefixWord ++ tailWord_394930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394930).length < 2 ^ (prefixWord ++ tailWord_394930).sum := by decide
  have hdescent : baseEnd_394930 < baseStart_394930 := by decide
  rcases family_descends (prefixWord ++ tailWord_394930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394975 : List Nat := [1, 1, 2, 3, 2, 2, 3, 1, 6]
def baseStart_394975 : Nat := 118140960795 + 394975 * 2 ^ 59
def prefixEnd_394975 : Nat := 4983230072969 + 3 ^ 40 * 394975 * 2
def baseEnd_394975 : Nat := 90138676226532174309355

theorem tailTrace_394975 : CollatzResearch.WordTrace tailWord_394975 prefixEnd_394975 90138676226532174309355 := by
  unfold tailWord_394975
  simp only [CollatzResearch.WordTrace]
  refine ⟨14405921744080506204634379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9603947829387004136422919 14405921744080506204634379)
  ·
    refine ⟨21608882616120759306951569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14405921744080506204634379 21608882616120759306951569)
    ·
      refine ⟨16206661962090569480213677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21608882616120759306951569 16206661962090569480213677)
      ·
        refine ⟨6077498235783963555080129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16206661962090569480213677 6077498235783963555080129)
        ·
          refine ⟨4558123676837972666310097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6077498235783963555080129 4558123676837972666310097)
          ·
            refine ⟨3418592757628479499732573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4558123676837972666310097 3418592757628479499732573)
            ·
              refine ⟨1281972284110679812399715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3418592757628479499732573 1281972284110679812399715)
              ·
                refine ⟨1922958426166019718599573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1281972284110679812399715 1922958426166019718599573)
                ·
                  refine ⟨90138676226532174309355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1922958426166019718599573 90138676226532174309355)
                  ·
                    rfl

theorem cell21_394975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 1, 6].length) (baseStart_394975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_394975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_394975 prefixEnd_394975 := by exact prefixLift 394975
  have htrace : WordTrace (prefixWord ++ tailWord_394975) baseStart_394975 baseEnd_394975 := by
    simpa [prefixWord, tailWord_394975, baseEnd_394975] using wordTrace_append hprefix tailTrace_394975
  have hstable : (prefixWord ++ tailWord_394975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394975).length < 2 ^ (prefixWord ++ tailWord_394975).sum := by decide
  have hdescent : baseEnd_394975 < baseStart_394975 := by decide
  rcases family_descends (prefixWord ++ tailWord_394975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395020 : List Nat := [2, 2, 1, 2, 2, 1, 2, 2, 7]
def baseStart_395020 : Nat := 118140960795 + 395020 * 2 ^ 59
def prefixEnd_395020 : Nat := 4983230072969 + 3 ^ 40 * 395020 * 2
def baseEnd_395020 : Nat := 90148945839622096059263

theorem tailTrace_395020 : CollatzResearch.WordTrace tailWord_395020 prefixEnd_395020 90148945839622096059263 := by
  unfold tailWord_395020
  simp only [CollatzResearch.WordTrace]
  refine ⟨7203781514458739445011257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9605042019278319260015009 7203781514458739445011257)
  ·
    refine ⟨5402836135844054583758443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7203781514458739445011257 5402836135844054583758443)
    ·
      refine ⟨8104254203766081875637665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5402836135844054583758443 8104254203766081875637665)
      ·
        refine ⟨6078190652824561406728249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8104254203766081875637665 6078190652824561406728249)
        ·
          refine ⟨4558642989618421055046187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6078190652824561406728249 4558642989618421055046187)
          ·
            refine ⟨6837964484427631582569281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4558642989618421055046187 6837964484427631582569281)
            ·
              refine ⟨5128473363320723686926961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6837964484427631582569281 5128473363320723686926961)
              ·
                refine ⟨3846355022490542765195221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5128473363320723686926961 3846355022490542765195221)
                ·
                  refine ⟨90148945839622096059263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3846355022490542765195221 90148945839622096059263)
                  ·
                    rfl

theorem cell21_395020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_395020 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_395020 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_395020 prefixEnd_395020 := by exact prefixLift 395020
  have htrace : WordTrace (prefixWord ++ tailWord_395020) baseStart_395020 baseEnd_395020 := by
    simpa [prefixWord, tailWord_395020, baseEnd_395020] using wordTrace_append hprefix tailTrace_395020
  have hstable : (prefixWord ++ tailWord_395020).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395020).length < 2 ^ (prefixWord ++ tailWord_395020).sum := by decide
  have hdescent : baseEnd_395020 < baseStart_395020 := by decide
  rcases family_descends (prefixWord ++ tailWord_395020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395085 : List Nat := [1, 6, 1, 2, 1, 1, 1, 4, 4]
def baseStart_395085 : Nat := 118140960795 + 395085 * 2 ^ 59
def prefixEnd_395085 : Nat := 4983230072969 + 3 ^ 40 * 395085 * 2
def baseEnd_395085 : Nat := 90163779725196427475797

theorem tailTrace_395085 : CollatzResearch.WordTrace tailWord_395085 prefixEnd_395085 90163779725196427475797 := by
  unfold tailWord_395085
  simp only [CollatzResearch.WordTrace]
  refine ⟨14409933773681994991138709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9606622515787996660759139 14409933773681994991138709)
  ·
    refine ⟨675465645641343515209627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14409933773681994991138709 675465645641343515209627)
    ·
      refine ⟨1013198468462015272814441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 675465645641343515209627 1013198468462015272814441)
      ·
        refine ⟨759898851346511454610831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1013198468462015272814441 759898851346511454610831)
        ·
          refine ⟨1139848277019767181916247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759898851346511454610831 1139848277019767181916247)
          ·
            refine ⟨1709772415529650772874371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139848277019767181916247 1709772415529650772874371)
            ·
              refine ⟨2564658623294476159311557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709772415529650772874371 2564658623294476159311557)
              ·
                refine ⟨480873491867714279870917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2564658623294476159311557 480873491867714279870917)
                ·
                  refine ⟨90163779725196427475797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 480873491867714279870917 90163779725196427475797)
                  ·
                    rfl

theorem cell21_395085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_395085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_395085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_395085 prefixEnd_395085 := by exact prefixLift 395085
  have htrace : WordTrace (prefixWord ++ tailWord_395085) baseStart_395085 baseEnd_395085 := by
    simpa [prefixWord, tailWord_395085, baseEnd_395085] using wordTrace_append hprefix tailTrace_395085
  have hstable : (prefixWord ++ tailWord_395085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395085).length < 2 ^ (prefixWord ++ tailWord_395085).sum := by decide
  have hdescent : baseEnd_395085 < baseStart_395085 := by decide
  rcases family_descends (prefixWord ++ tailWord_395085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395141 : List Nat := [1, 3, 1, 1, 3, 2, 10]
def baseStart_395141 : Nat := 118140960795 + 395141 * 2 ^ 59
def prefixEnd_395141 : Nat := 4983230072969 + 3 ^ 40 * 395141 * 2
def baseEnd_395141 : Nat := 10019617743128086060261

theorem tailTrace_395141 : CollatzResearch.WordTrace tailWord_395141 prefixEnd_395141 10019617743128086060261 := by
  unfold tailWord_395141
  simp only [CollatzResearch.WordTrace]
  refine ⟨14411976261479116555177277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9607984174319411036784851 14411976261479116555177277)
  ·
    refine ⟨5404491098054668708191479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14411976261479116555177277 5404491098054668708191479)
    ·
      refine ⟨8106736647082003062287219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5404491098054668708191479 8106736647082003062287219)
      ·
        refine ⟨12160104970623004593430829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8106736647082003062287219 12160104970623004593430829)
        ·
          refine ⟨4560039363983626722536561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12160104970623004593430829 4560039363983626722536561)
          ·
            refine ⟨3420029522987720041902421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4560039363983626722536561 3420029522987720041902421)
            ·
              refine ⟨10019617743128086060261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3420029522987720041902421 10019617743128086060261)
              ·
                rfl

theorem cell21_395141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 10].length) (baseStart_395141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_395141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_395141 prefixEnd_395141 := by exact prefixLift 395141
  have htrace : WordTrace (prefixWord ++ tailWord_395141) baseStart_395141 baseEnd_395141 := by
    simpa [prefixWord, tailWord_395141, baseEnd_395141] using wordTrace_append hprefix tailTrace_395141
  have hstable : (prefixWord ++ tailWord_395141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395141).length < 2 ^ (prefixWord ++ tailWord_395141).sum := by decide
  have hdescent : baseEnd_395141 < baseStart_395141 := by decide
  rcases family_descends (prefixWord ++ tailWord_395141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395144 : List Nat := [2, 1, 3, 3, 3, 1, 1, 1, 6]
def baseStart_395144 : Nat := 118140960795 + 395144 * 2 ^ 59
def prefixEnd_395144 : Nat := 4983230072969 + 3 ^ 40 * 395144 * 2
def baseEnd_395144 : Nat := 90177244329025435992343

theorem tailTrace_395144 : CollatzResearch.WordTrace tailWord_395144 prefixEnd_395144 90177244329025435992343 := by
  unfold tailWord_395144
  simp only [CollatzResearch.WordTrace]
  refine ⟨7206042840234124033768243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9608057120312165378357657 7206042840234124033768243)
  ·
    refine ⟨10809064260351186050652365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7206042840234124033768243 10809064260351186050652365)
    ·
      refine ⟨4053399097631694768994637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10809064260351186050652365 4053399097631694768994637)
      ·
        refine ⟨1520024661611885538372989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4053399097631694768994637 1520024661611885538372989)
        ·
          refine ⟨570009248104457076889871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1520024661611885538372989 570009248104457076889871)
          ·
            refine ⟨855013872156685615334807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570009248104457076889871 855013872156685615334807)
            ·
              refine ⟨1282520808235028423002211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855013872156685615334807 1282520808235028423002211)
              ·
                refine ⟨1923781212352542634503317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1282520808235028423002211 1923781212352542634503317)
                ·
                  refine ⟨90177244329025435992343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1923781212352542634503317 90177244329025435992343)
                  ·
                    rfl

theorem cell21_395144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 1, 1, 1, 6].length) (baseStart_395144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_395144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_395144 prefixEnd_395144 := by exact prefixLift 395144
  have htrace : WordTrace (prefixWord ++ tailWord_395144) baseStart_395144 baseEnd_395144 := by
    simpa [prefixWord, tailWord_395144, baseEnd_395144] using wordTrace_append hprefix tailTrace_395144
  have hstable : (prefixWord ++ tailWord_395144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395144).length < 2 ^ (prefixWord ++ tailWord_395144).sum := by decide
  have hdescent : baseEnd_395144 < baseStart_395144 := by decide
  rcases family_descends (prefixWord ++ tailWord_395144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395175 : List Nat := [1, 1, 6, 1, 2, 1, 4, 5]
def baseStart_395175 : Nat := 118140960795 + 395175 * 2 ^ 59
def prefixEnd_395175 : Nat := 4983230072969 + 3 ^ 40 * 395175 * 2
def baseEnd_395175 : Nat := 30061439650458756991871

theorem tailTrace_395175 : CollatzResearch.WordTrace tailWord_395175 prefixEnd_395175 30061439650458756991871 := by
  unfold tailWord_395175
  simp only [CollatzResearch.WordTrace]
  refine ⟨14413216343355940361914979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9608810895570626907943319 14413216343355940361914979)
  ·
    refine ⟨21619824515033910542872469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14413216343355940361914979 21619824515033910542872469)
    ·
      refine ⟨1013429274142214556697147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21619824515033910542872469 1013429274142214556697147)
      ·
        refine ⟨1520143911213321835045721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1013429274142214556697147 1520143911213321835045721)
        ·
          refine ⟨1140107933409991376284291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1520143911213321835045721 1140107933409991376284291)
          ·
            refine ⟨1710161900114987064426437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1140107933409991376284291 1710161900114987064426437)
            ·
              refine ⟨320655356271560074579957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1710161900114987064426437 320655356271560074579957)
              ·
                refine ⟨30061439650458756991871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 320655356271560074579957 30061439650458756991871)
                ·
                  rfl

theorem cell21_395175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 4, 5].length) (baseStart_395175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_395175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_395175 prefixEnd_395175 := by exact prefixLift 395175
  have htrace : WordTrace (prefixWord ++ tailWord_395175) baseStart_395175 baseEnd_395175 := by
    simpa [prefixWord, tailWord_395175, baseEnd_395175] using wordTrace_append hprefix tailTrace_395175
  have hstable : (prefixWord ++ tailWord_395175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395175).length < 2 ^ (prefixWord ++ tailWord_395175).sum := by decide
  have hdescent : baseEnd_395175 < baseStart_395175 := by decide
  rcases family_descends (prefixWord ++ tailWord_395175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395220 : List Nat := [2, 4, 1, 2, 1, 1, 3, 3, 4]
def baseStart_395220 : Nat := 118140960795 + 395220 * 2 ^ 59
def prefixEnd_395220 : Nat := 4983230072969 + 3 ^ 40 * 395220 * 2
def baseEnd_395220 : Nat := 90194588564466192725521

theorem tailTrace_395220 : CollatzResearch.WordTrace tailWord_395220 prefixEnd_395220 90194588564466192725521 := by
  unfold tailWord_395220
  simp only [CollatzResearch.WordTrace]
  refine ⟨7207428814096456523651557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9609905085461942031535409 7207428814096456523651557)
  ·
    refine ⟨1351392902643085598184667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7207428814096456523651557 1351392902643085598184667)
    ·
      refine ⟨2027089353964628397277001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1351392902643085598184667 2027089353964628397277001)
      ·
        refine ⟨1520317015473471297957751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2027089353964628397277001 1520317015473471297957751)
        ·
          refine ⟨2280475523210206946936627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1520317015473471297957751 2280475523210206946936627)
          ·
            refine ⟨3420713284815310420404941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2280475523210206946936627 3420713284815310420404941)
            ·
              refine ⟨1282767481805741407651853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3420713284815310420404941 1282767481805741407651853)
              ·
                refine ⟨481037805677153027869445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1282767481805741407651853 481037805677153027869445)
                ·
                  refine ⟨90194588564466192725521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 481037805677153027869445 90194588564466192725521)
                  ·
                    rfl

theorem cell21_395220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_395220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_395220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_395220 prefixEnd_395220 := by exact prefixLift 395220
  have htrace : WordTrace (prefixWord ++ tailWord_395220) baseStart_395220 baseEnd_395220 := by
    simpa [prefixWord, tailWord_395220, baseEnd_395220] using wordTrace_append hprefix tailTrace_395220
  have hstable : (prefixWord ++ tailWord_395220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395220).length < 2 ^ (prefixWord ++ tailWord_395220).sum := by decide
  have hdescent : baseEnd_395220 < baseStart_395220 := by decide
  rcases family_descends (prefixWord ++ tailWord_395220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395268 : List Nat := [2, 3, 2, 4, 1, 2, 1, 6]
def baseStart_395268 : Nat := 118140960795 + 395268 * 2 ^ 59
def prefixEnd_395268 : Nat := 4983230072969 + 3 ^ 40 * 395268 * 2
def baseEnd_395268 : Nat := 30068514272809591975141

theorem tailTrace_395268 : CollatzResearch.WordTrace tailWord_395268 prefixEnd_395268 30068514272809591975141 := by
  unfold tailWord_395268
  simp only [CollatzResearch.WordTrace]
  refine ⟨7208304166009508622525229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9611072221346011496700305 7208304166009508622525229)
  ·
    refine ⟨2703114062253565733446961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7208304166009508622525229 2703114062253565733446961)
    ·
      refine ⟨2027335546690174300085221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2703114062253565733446961 2027335546690174300085221)
      ·
        refine ⟨380125415004407681265979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2027335546690174300085221 380125415004407681265979)
        ·
          refine ⟨570188122506611521898969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380125415004407681265979 570188122506611521898969)
          ·
            refine ⟨427641091879958641424227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 570188122506611521898969 427641091879958641424227)
            ·
              refine ⟨641461637819937962136341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427641091879958641424227 641461637819937962136341)
              ·
                refine ⟨30068514272809591975141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 641461637819937962136341 30068514272809591975141)
                ·
                  rfl

theorem cell21_395268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 2, 1, 6].length) (baseStart_395268 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_395268 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_395268 prefixEnd_395268 := by exact prefixLift 395268
  have htrace : WordTrace (prefixWord ++ tailWord_395268) baseStart_395268 baseEnd_395268 := by
    simpa [prefixWord, tailWord_395268, baseEnd_395268] using wordTrace_append hprefix tailTrace_395268
  have hstable : (prefixWord ++ tailWord_395268).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395268).length < 2 ^ (prefixWord ++ tailWord_395268).sum := by decide
  have hdescent : baseEnd_395268 < baseStart_395268 := by decide
  rcases family_descends (prefixWord ++ tailWord_395268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395310 : List Nat := [4, 1, 3, 1, 1, 3, 8]
def baseStart_395310 : Nat := 118140960795 + 395310 * 2 ^ 59
def prefixEnd_395310 : Nat := 4983230072969 + 3 ^ 40 * 395310 * 2
def baseEnd_395310 : Nat := 10023903087849559580593

theorem tailTrace_395310 : CollatzResearch.WordTrace tailWord_395310 prefixEnd_395310 10023903087849559580593 := by
  unfold tailWord_395310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802267524733357302259923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9612093465244572278719589 1802267524733357302259923)
  ·
    refine ⟨2703401287100035953389885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1802267524733357302259923 2703401287100035953389885)
    ·
      refine ⟨1013775482662513482521207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2703401287100035953389885 1013775482662513482521207)
      ·
        refine ⟨1520663223993770223781811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1013775482662513482521207 1520663223993770223781811)
        ·
          refine ⟨2280994835990655335672717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1520663223993770223781811 2280994835990655335672717)
          ·
            refine ⟨855373063496495750877269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2280994835990655335672717 855373063496495750877269)
            ·
              refine ⟨10023903087849559580593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 855373063496495750877269 10023903087849559580593)
              ·
                rfl

theorem cell21_395310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 8].length) (baseStart_395310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_395310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_395310 prefixEnd_395310 := by exact prefixLift 395310
  have htrace : WordTrace (prefixWord ++ tailWord_395310) baseStart_395310 baseEnd_395310 := by
    simpa [prefixWord, tailWord_395310, baseEnd_395310] using wordTrace_append hprefix tailTrace_395310
  have hstable : (prefixWord ++ tailWord_395310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395310).length < 2 ^ (prefixWord ++ tailWord_395310).sum := by decide
  have hdescent : baseEnd_395310 < baseStart_395310 := by decide
  rcases family_descends (prefixWord ++ tailWord_395310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395341 : List Nat := [1, 6, 1, 1, 1, 1, 1, 4, 5]
def baseStart_395341 : Nat := 118140960795 + 395341 * 2 ^ 59
def prefixEnd_395341 : Nat := 4983230072969 + 3 ^ 40 * 395341 * 2
def baseEnd_395341 : Nat := 90222202412996871208607

theorem tailTrace_395341 : CollatzResearch.WordTrace tailWord_395341 prefixEnd_395341 90222202412996871208607 := by
  unfold tailWord_395341
  simp only [CollatzResearch.WordTrace]
  refine ⟨14419270860754550712457877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9612847240503033808305251 14419270860754550712457877)
  ·
    refine ⟨675903321597869564646463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14419270860754550712457877 675903321597869564646463)
    ·
      refine ⟨1013854982396804346969695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 675903321597869564646463 1013854982396804346969695)
      ·
        refine ⟨1520782473595206520454543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1013854982396804346969695 1520782473595206520454543)
        ·
          refine ⟨2281173710392809780681815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1520782473595206520454543 2281173710392809780681815)
          ·
            refine ⟨3421760565589214671022723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2281173710392809780681815 3421760565589214671022723)
            ·
              refine ⟨5132640848383822006534085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3421760565589214671022723 5132640848383822006534085)
              ·
                refine ⟨962370159071966626225141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5132640848383822006534085 962370159071966626225141)
                ·
                  refine ⟨90222202412996871208607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 962370159071966626225141 90222202412996871208607)
                  ·
                    rfl

theorem cell21_395341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_395341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_395341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_395341 prefixEnd_395341 := by exact prefixLift 395341
  have htrace : WordTrace (prefixWord ++ tailWord_395341) baseStart_395341 baseEnd_395341 := by
    simpa [prefixWord, tailWord_395341, baseEnd_395341] using wordTrace_append hprefix tailTrace_395341
  have hstable : (prefixWord ++ tailWord_395341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395341).length < 2 ^ (prefixWord ++ tailWord_395341).sum := by decide
  have hdescent : baseEnd_395341 < baseStart_395341 := by decide
  rcases family_descends (prefixWord ++ tailWord_395341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395389 : List Nat := [1, 4, 1, 1, 3, 4, 2, 1, 4]
def baseStart_395389 : Nat := 118140960795 + 395389 * 2 ^ 59
def prefixEnd_395389 : Nat := 4983230072969 + 3 ^ 40 * 395389 * 2
def baseEnd_395389 : Nat := 90233156666959454408509

theorem tailTrace_395389 : CollatzResearch.WordTrace tailWord_395389 prefixEnd_395389 90233156666959454408509 := by
  unfold tailWord_395389
  simp only [CollatzResearch.WordTrace]
  refine ⟨14421021564580654910205221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9614014376387103273470147 14421021564580654910205221)
  ·
    refine ⟨2703941543358872795663479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14421021564580654910205221 2703941543358872795663479)
    ·
      refine ⟨4055912315038309193495219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2703941543358872795663479 4055912315038309193495219)
      ·
        refine ⟨6083868472557463790242829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4055912315038309193495219 6083868472557463790242829)
        ·
          refine ⟨2281450677209048921341061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6083868472557463790242829 2281450677209048921341061)
          ·
            refine ⟨427772001976696672751449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2281450677209048921341061 427772001976696672751449)
            ·
              refine ⟨320829001482522504563587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 427772001976696672751449 320829001482522504563587)
              ·
                refine ⟨481243502223783756845381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320829001482522504563587 481243502223783756845381)
                ·
                  refine ⟨90233156666959454408509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 481243502223783756845381 90233156666959454408509)
                  ·
                    rfl

theorem cell21_395389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_395389 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_395389 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_395389 prefixEnd_395389 := by exact prefixLift 395389
  have htrace : WordTrace (prefixWord ++ tailWord_395389) baseStart_395389 baseEnd_395389 := by
    simpa [prefixWord, tailWord_395389, baseEnd_395389] using wordTrace_append hprefix tailTrace_395389
  have hstable : (prefixWord ++ tailWord_395389).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395389).length < 2 ^ (prefixWord ++ tailWord_395389).sum := by decide
  have hdescent : baseEnd_395389 < baseStart_395389 := by decide
  rcases family_descends (prefixWord ++ tailWord_395389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395493 : List Nat := [1, 3, 1, 4, 2, 2, 2, 1, 5]
def baseStart_395493 : Nat := 118140960795 + 395493 * 2 ^ 59
def prefixEnd_395493 : Nat := 4983230072969 + 3 ^ 40 * 395493 * 2
def baseEnd_395493 : Nat := 90256890883878384674963

theorem tailTrace_395493 : CollatzResearch.WordTrace tailWord_395493 prefixEnd_395493 90256890883878384674963 := by
  unfold tailWord_395493
  simp only [CollatzResearch.WordTrace]
  refine ⟨14424814756203880671991133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9616543170802587114660755 14424814756203880671991133)
  ·
    refine ⟨5409305533576455251996675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14424814756203880671991133 5409305533576455251996675)
    ·
      refine ⟨8113958300364682877995013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5409305533576455251996675 8113958300364682877995013)
      ·
        refine ⟨1521367181318378039624065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8113958300364682877995013 1521367181318378039624065)
        ·
          refine ⟨1141025385988783529718049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1521367181318378039624065 1141025385988783529718049)
          ·
            refine ⟨855769039491587647288537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1141025385988783529718049 855769039491587647288537)
            ·
              refine ⟨641826779618690735466403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 855769039491587647288537 641826779618690735466403)
              ·
                refine ⟨962740169428036103199605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641826779618690735466403 962740169428036103199605)
                ·
                  refine ⟨90256890883878384674963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 962740169428036103199605 90256890883878384674963)
                  ·
                    rfl

theorem cell21_395493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_395493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_395493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_395493 prefixEnd_395493 := by exact prefixLift 395493
  have htrace : WordTrace (prefixWord ++ tailWord_395493) baseStart_395493 baseEnd_395493 := by
    simpa [prefixWord, tailWord_395493, baseEnd_395493] using wordTrace_append hprefix tailTrace_395493
  have hstable : (prefixWord ++ tailWord_395493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395493).length < 2 ^ (prefixWord ++ tailWord_395493).sum := by decide
  have hdescent : baseEnd_395493 < baseStart_395493 := by decide
  rcases family_descends (prefixWord ++ tailWord_395493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395521 : List Nat := [1, 2, 4, 1, 1, 2, 3, 7]
def baseStart_395521 : Nat := 118140960795 + 395521 * 2 ^ 59
def prefixEnd_395521 : Nat := 4983230072969 + 3 ^ 40 * 395521 * 2
def baseEnd_395521 : Nat := 30087760288452186069413

theorem tailTrace_395521 : CollatzResearch.WordTrace tailWord_395521 prefixEnd_395521 30087760288452186069413 := by
  unfold tailWord_395521
  simp only [CollatzResearch.WordTrace]
  refine ⟨14425836000102441454010417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9617224000068294302673611 14425836000102441454010417)
  ·
    refine ⟨10819377000076831090507813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14425836000102441454010417 10819377000076831090507813)
    ·
      refine ⟨2028633187514405829470215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10819377000076831090507813 2028633187514405829470215)
      ·
        refine ⟨3042949781271608744205323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2028633187514405829470215 3042949781271608744205323)
        ·
          refine ⟨4564424671907413116307985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3042949781271608744205323 4564424671907413116307985)
          ·
            refine ⟨3423318503930559837230989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4564424671907413116307985 3423318503930559837230989)
            ·
              refine ⟨1283744438973959938961621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3423318503930559837230989 1283744438973959938961621)
              ·
                refine ⟨30087760288452186069413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1283744438973959938961621 30087760288452186069413)
                ·
                  rfl

theorem cell21_395521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 3, 7].length) (baseStart_395521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_395521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_395521 prefixEnd_395521 := by exact prefixLift 395521
  have htrace : WordTrace (prefixWord ++ tailWord_395521) baseStart_395521 baseEnd_395521 := by
    simpa [prefixWord, tailWord_395521, baseEnd_395521] using wordTrace_append hprefix tailTrace_395521
  have hstable : (prefixWord ++ tailWord_395521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395521).length < 2 ^ (prefixWord ++ tailWord_395521).sum := by decide
  have hdescent : baseEnd_395521 < baseStart_395521 := by decide
  rcases family_descends (prefixWord ++ tailWord_395521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395535 : List Nat := [1, 1, 2, 1, 1, 1, 3, 4, 7]
def baseStart_395535 : Nat := 118140960795 + 395535 * 2 ^ 59
def prefixEnd_395535 : Nat := 4983230072969 + 3 ^ 40 * 395535 * 2
def baseEnd_395535 : Nat := 90266475856095644974877

theorem tailTrace_395535 : CollatzResearch.WordTrace tailWord_395535 prefixEnd_395535 90266475856095644974877 := by
  unfold tailWord_395535
  simp only [CollatzResearch.WordTrace]
  refine ⟨14426346622051721845020059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9617564414701147896680039 14426346622051721845020059)
  ·
    refine ⟨21639519933077582767530089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14426346622051721845020059 21639519933077582767530089)
    ·
      refine ⟨16229639949808187075647567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21639519933077582767530089 16229639949808187075647567)
      ·
        refine ⟨24344459924712280613471351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16229639949808187075647567 24344459924712280613471351)
        ·
          refine ⟨36516689887068420920207027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24344459924712280613471351 36516689887068420920207027)
          ·
            refine ⟨54775034830602631380310541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36516689887068420920207027 54775034830602631380310541)
            ·
              refine ⟨20540638061475986767616453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54775034830602631380310541 20540638061475986767616453)
              ·
                refine ⟨3851369636526747518928085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20540638061475986767616453 3851369636526747518928085)
                ·
                  refine ⟨90266475856095644974877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3851369636526747518928085 90266475856095644974877)
                  ·
                    rfl

theorem cell21_395535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 4, 7].length) (baseStart_395535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_395535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_395535 prefixEnd_395535 := by exact prefixLift 395535
  have htrace : WordTrace (prefixWord ++ tailWord_395535) baseStart_395535 baseEnd_395535 := by
    simpa [prefixWord, tailWord_395535, baseEnd_395535] using wordTrace_append hprefix tailTrace_395535
  have hstable : (prefixWord ++ tailWord_395535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395535).length < 2 ^ (prefixWord ++ tailWord_395535).sum := by decide
  have hdescent : baseEnd_395535 < baseStart_395535 := by decide
  rcases family_descends (prefixWord ++ tailWord_395535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395597 : List Nat := [1, 6, 1, 13]
def baseStart_395597 : Nat := 118140960795 + 395597 * 2 ^ 59
def prefixEnd_395597 : Nat := 4983230072969 + 3 ^ 40 * 395597 * 2
def baseEnd_395597 : Nat := 371525206176120637619

theorem tailTrace_395597 : CollatzResearch.WordTrace tailWord_395597 prefixEnd_395597 371525206176120637619 := by
  unfold tailWord_395597
  simp only [CollatzResearch.WordTrace]
  refine ⟨14428607947827106433777045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9619071965218070955851363 14428607947827106433777045)
  ·
    refine ⟨676340997554395614083299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14428607947827106433777045 676340997554395614083299)
    ·
      refine ⟨1014511496331593421124949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 676340997554395614083299 1014511496331593421124949)
      ·
        refine ⟨371525206176120637619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 1014511496331593421124949 371525206176120637619)
        ·
          rfl

theorem cell21_395597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 13].length) (baseStart_395597 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_395597 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_395597 prefixEnd_395597 := by exact prefixLift 395597
  have htrace : WordTrace (prefixWord ++ tailWord_395597) baseStart_395597 baseEnd_395597 := by
    simpa [prefixWord, tailWord_395597, baseEnd_395597] using wordTrace_append hprefix tailTrace_395597
  have hstable : (prefixWord ++ tailWord_395597).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395597).length < 2 ^ (prefixWord ++ tailWord_395597).sum := by decide
  have hdescent : baseEnd_395597 < baseStart_395597 := by decide
  rcases family_descends (prefixWord ++ tailWord_395597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395645 : List Nat := [1, 4, 1, 1, 2, 3, 1, 5, 3]
def baseStart_395645 : Nat := 118140960795 + 395645 * 2 ^ 59
def prefixEnd_395645 : Nat := 4983230072969 + 3 ^ 40 * 395645 * 2
def baseEnd_395645 : Nat := 90291579354759898141319

theorem tailTrace_395645 : CollatzResearch.WordTrace tailWord_395645 prefixEnd_395645 90291579354759898141319 := by
  unfold tailWord_395645
  simp only [CollatzResearch.WordTrace]
  refine ⟨14430358651653210631524389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9620239101102140421016259 14430358651653210631524389)
  ·
    refine ⟨2705692247184976993410823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14430358651653210631524389 2705692247184976993410823)
    ·
      refine ⟨4058538370777465490116235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2705692247184976993410823 4058538370777465490116235)
      ·
        refine ⟨6087807556166198235174353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4058538370777465490116235 6087807556166198235174353)
        ·
          refine ⟨4565855667124648676380765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6087807556166198235174353 4565855667124648676380765)
          ·
            refine ⟨1712195875171743253642787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4565855667124648676380765 1712195875171743253642787)
            ·
              refine ⟨2568293812757614880464181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1712195875171743253642787 2568293812757614880464181)
              ·
                refine ⟨240777544946026395043517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2568293812757614880464181 240777544946026395043517)
                ·
                  refine ⟨90291579354759898141319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240777544946026395043517 90291579354759898141319)
                  ·
                    rfl

theorem cell21_395645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 5, 3].length) (baseStart_395645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_395645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_395645 prefixEnd_395645 := by exact prefixLift 395645
  have htrace : WordTrace (prefixWord ++ tailWord_395645) baseStart_395645 baseEnd_395645 := by
    simpa [prefixWord, tailWord_395645, baseEnd_395645] using wordTrace_append hprefix tailTrace_395645
  have hstable : (prefixWord ++ tailWord_395645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395645).length < 2 ^ (prefixWord ++ tailWord_395645).sum := by decide
  have hdescent : baseEnd_395645 < baseStart_395645 := by decide
  rcases family_descends (prefixWord ++ tailWord_395645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395659 : List Nat := [1, 1, 1, 1, 4, 4, 3, 2, 4]
def baseStart_395659 : Nat := 118140960795 + 395659 * 2 ^ 59
def prefixEnd_395659 : Nat := 4983230072969 + 3 ^ 40 * 395659 * 2
def baseEnd_395659 : Nat := 90294774345498984907957

theorem tailTrace_395659 : CollatzResearch.WordTrace tailWord_395659 prefixEnd_395659 90294774345498984907957 := by
  unfold tailWord_395659
  simp only [CollatzResearch.WordTrace]
  refine ⟨14430869273602491022534031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9620579515734994015022687 14430869273602491022534031)
  ·
    refine ⟨21646303910403736533801047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14430869273602491022534031 21646303910403736533801047)
    ·
      refine ⟨32469455865605604800701571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21646303910403736533801047 32469455865605604800701571)
      ·
        refine ⟨48704183798408407201052357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32469455865605604800701571 48704183798408407201052357)
        ·
          refine ⟨9132034462201576350197317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48704183798408407201052357 9132034462201576350197317)
          ·
            refine ⟨1712256461662795565661997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9132034462201576350197317 1712256461662795565661997)
            ·
              refine ⟨642096173123548337123249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1712256461662795565661997 642096173123548337123249)
              ·
                refine ⟨481572129842661252842437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 642096173123548337123249 481572129842661252842437)
                ·
                  refine ⟨90294774345498984907957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 481572129842661252842437 90294774345498984907957)
                  ·
                    rfl

theorem cell21_395659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 3, 2, 4].length) (baseStart_395659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_395659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_395659 prefixEnd_395659 := by exact prefixLift 395659
  have htrace : WordTrace (prefixWord ++ tailWord_395659) baseStart_395659 baseEnd_395659 := by
    simpa [prefixWord, tailWord_395659, baseEnd_395659] using wordTrace_append hprefix tailTrace_395659
  have hstable : (prefixWord ++ tailWord_395659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395659).length < 2 ^ (prefixWord ++ tailWord_395659).sum := by decide
  have hdescent : baseEnd_395659 < baseStart_395659 := by decide
  rcases family_descends (prefixWord ++ tailWord_395659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395662 : List Nat := [4, 1, 1, 4, 1, 1, 2, 4, 3]
def baseStart_395662 : Nat := 118140960795 + 395662 * 2 ^ 59
def prefixEnd_395662 : Nat := 4983230072969 + 3 ^ 40 * 395662 * 2
def baseEnd_395662 : Nat := 90295458986371646357951

theorem tailTrace_395662 : CollatzResearch.WordTrace tailWord_395662 prefixEnd_395662 90295458986371646357951 := by
  unfold tailWord_395662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1803872336573952816861655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9620652461727748356595493 1803872336573952816861655)
  ·
    refine ⟨2705808504860929225292483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1803872336573952816861655 2705808504860929225292483)
    ·
      refine ⟨4058712757291393837938725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2705808504860929225292483 4058712757291393837938725)
      ·
        refine ⟨761008641992136344613511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4058712757291393837938725 761008641992136344613511)
        ·
          refine ⟨1141512962988204516920267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 761008641992136344613511 1141512962988204516920267)
          ·
            refine ⟨1712269444482306775380401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1141512962988204516920267 1712269444482306775380401)
            ·
              refine ⟨1284202083361730081535301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1712269444482306775380401 1284202083361730081535301)
              ·
                refine ⟨240787890630324390287869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1284202083361730081535301 240787890630324390287869)
                ·
                  refine ⟨90295458986371646357951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240787890630324390287869 90295458986371646357951)
                  ·
                    rfl

theorem cell21_395662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 2, 4, 3].length) (baseStart_395662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_395662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_395662 prefixEnd_395662 := by exact prefixLift 395662
  have htrace : WordTrace (prefixWord ++ tailWord_395662) baseStart_395662 baseEnd_395662 := by
    simpa [prefixWord, tailWord_395662, baseEnd_395662] using wordTrace_append hprefix tailTrace_395662
  have hstable : (prefixWord ++ tailWord_395662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395662).length < 2 ^ (prefixWord ++ tailWord_395662).sum := by decide
  have hdescent : baseEnd_395662 < baseStart_395662 := by decide
  rcases family_descends (prefixWord ++ tailWord_395662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395713 : List Nat := [1, 2, 7, 1, 1, 1, 3, 2, 3]
def baseStart_395713 : Nat := 118140960795 + 395713 * 2 ^ 59
def prefixEnd_395713 : Nat := 4983230072969 + 3 ^ 40 * 395713 * 2
def baseEnd_395713 : Nat := 90307097881206891007847

theorem tailTrace_395713 : CollatzResearch.WordTrace tailWord_395713 prefixEnd_395713 90307097881206891007847 := by
  unfold tailWord_395713
  simp only [CollatzResearch.WordTrace]
  refine ⟨14432838815406858244999793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9621892543604572163333195 14432838815406858244999793)
  ·
    refine ⟨10824629111555143683749845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14432838815406858244999793 10824629111555143683749845)
    ·
      refine ⟨253702244802073680087887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 10824629111555143683749845 253702244802073680087887)
      ·
        refine ⟨380553367203110520131831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 253702244802073680087887 380553367203110520131831)
        ·
          refine ⟨570830050804665780197747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380553367203110520131831 570830050804665780197747)
          ·
            refine ⟨856245076206998670296621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570830050804665780197747 856245076206998670296621)
            ·
              refine ⟨321091903577624501361233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 856245076206998670296621 321091903577624501361233)
              ·
                refine ⟨240818927683218376020925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321091903577624501361233 240818927683218376020925)
                ·
                  refine ⟨90307097881206891007847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240818927683218376020925 90307097881206891007847)
                  ·
                    rfl

theorem cell21_395713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 3, 2, 3].length) (baseStart_395713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_395713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_395713 prefixEnd_395713 := by exact prefixLift 395713
  have htrace : WordTrace (prefixWord ++ tailWord_395713) baseStart_395713 baseEnd_395713 := by
    simpa [prefixWord, tailWord_395713, baseEnd_395713] using wordTrace_append hprefix tailTrace_395713
  have hstable : (prefixWord ++ tailWord_395713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395713).length < 2 ^ (prefixWord ++ tailWord_395713).sum := by decide
  have hdescent : baseEnd_395713 < baseStart_395713 := by decide
  rcases family_descends (prefixWord ++ tailWord_395713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395783 : List Nat := [1, 1, 4, 3, 4, 1, 1, 6]
def baseStart_395783 : Nat := 118140960795 + 395783 * 2 ^ 59
def prefixEnd_395783 : Nat := 4983230072969 + 3 ^ 40 * 395783 * 2
def baseEnd_395783 : Nat := 30107690944967441613679

theorem tailTrace_395783 : CollatzResearch.WordTrace tailWord_395783 prefixEnd_395783 30107690944967441613679 := by
  unfold tailWord_395783
  simp only [CollatzResearch.WordTrace]
  refine ⟨14435391925153260200048003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9623594616768840133365335 14435391925153260200048003)
  ·
    refine ⟨21653087887729890300072005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14435391925153260200048003 21653087887729890300072005)
    ·
      refine ⟨4059953978949354431263501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21653087887729890300072005 4059953978949354431263501)
      ·
        refine ⟨1522482742106007911723813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4059953978949354431263501 1522482742106007911723813)
        ·
          refine ⟨285465514144876483448215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1522482742106007911723813 285465514144876483448215)
          ·
            refine ⟨428198271217314725172323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285465514144876483448215 428198271217314725172323)
            ·
              refine ⟨642297406825972087758485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428198271217314725172323 642297406825972087758485)
              ·
                refine ⟨30107690944967441613679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 642297406825972087758485 30107690944967441613679)
                ·
                  rfl

theorem cell21_395783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 4, 1, 1, 6].length) (baseStart_395783 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_395783 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_395783 prefixEnd_395783 := by exact prefixLift 395783
  have htrace : WordTrace (prefixWord ++ tailWord_395783) baseStart_395783 baseEnd_395783 := by
    simpa [prefixWord, tailWord_395783, baseEnd_395783] using wordTrace_append hprefix tailTrace_395783
  have hstable : (prefixWord ++ tailWord_395783).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395783).length < 2 ^ (prefixWord ++ tailWord_395783).sum := by decide
  have hdescent : baseEnd_395783 < baseStart_395783 := by decide
  rcases family_descends (prefixWord ++ tailWord_395783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395873 : List Nat := [1, 2, 3, 1, 1, 4, 3, 3, 3]
def baseStart_395873 : Nat := 118140960795 + 395873 * 2 ^ 59
def prefixEnd_395873 : Nat := 4983230072969 + 3 ^ 40 * 395873 * 2
def baseEnd_395873 : Nat := 90343612061082168340853

theorem tailTrace_395873 : CollatzResearch.WordTrace tailWord_395873 prefixEnd_395873 90343612061082168340853 := by
  unfold tailWord_395873
  simp only [CollatzResearch.WordTrace]
  refine ⟨14438674494827205570824273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9625782996551470380549515 14438674494827205570824273)
  ·
    refine ⟨10829005871120404178118205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14438674494827205570824273 10829005871120404178118205)
    ·
      refine ⟨4060877201670151566794327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10829005871120404178118205 4060877201670151566794327)
      ·
        refine ⟨6091315802505227350191491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4060877201670151566794327 6091315802505227350191491)
        ·
          refine ⟨9136973703757841025287237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6091315802505227350191491 9136973703757841025287237)
          ·
            refine ⟨1713182569454595192241357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9136973703757841025287237 1713182569454595192241357)
            ·
              refine ⟨642443463545473197090509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1713182569454595192241357 642443463545473197090509)
              ·
                refine ⟨240916298829552448908941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 642443463545473197090509 240916298829552448908941)
                ·
                  refine ⟨90343612061082168340853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 240916298829552448908941 90343612061082168340853)
                  ·
                    rfl

theorem cell21_395873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 3, 3, 3].length) (baseStart_395873 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_395873 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_395873 prefixEnd_395873 := by exact prefixLift 395873
  have htrace : WordTrace (prefixWord ++ tailWord_395873) baseStart_395873 baseEnd_395873 := by
    simpa [prefixWord, tailWord_395873, baseEnd_395873] using wordTrace_append hprefix tailTrace_395873
  have hstable : (prefixWord ++ tailWord_395873).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395873).length < 2 ^ (prefixWord ++ tailWord_395873).sum := by decide
  have hdescent : baseEnd_395873 < baseStart_395873 := by decide
  rcases family_descends (prefixWord ++ tailWord_395873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395884 : List Nat := [2, 2, 1, 1, 3, 1, 11]
def baseStart_395884 : Nat := 118140960795 + 395884 * 2 ^ 59
def prefixEnd_395884 : Nat := 4983230072969 + 3 ^ 40 * 395884 * 2
def baseEnd_395884 : Nat := 10038458045660954850833

theorem tailTrace_395884 : CollatzResearch.WordTrace tailWord_395884 prefixEnd_395884 10038458045660954850833 := by
  unfold tailWord_395884
  simp only [CollatzResearch.WordTrace]
  refine ⟨7219537848893677224737353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9626050465191569632983137 7219537848893677224737353)
  ·
    refine ⟨5414653386670257918553015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7219537848893677224737353 5414653386670257918553015)
    ·
      refine ⟨8121980080005386877829523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5414653386670257918553015 8121980080005386877829523)
      ·
        refine ⟨12182970120008080316744285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8121980080005386877829523 12182970120008080316744285)
        ·
          refine ⟨4568613795003030118779107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12182970120008080316744285 4568613795003030118779107)
          ·
            refine ⟨6852920692504545178168661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4568613795003030118779107 6852920692504545178168661)
            ·
              refine ⟨10038458045660954850833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6852920692504545178168661 10038458045660954850833)
              ·
                rfl

theorem cell21_395884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 11].length) (baseStart_395884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_395884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_395884 prefixEnd_395884 := by exact prefixLift 395884
  have htrace : WordTrace (prefixWord ++ tailWord_395884) baseStart_395884 baseEnd_395884 := by
    simpa [prefixWord, tailWord_395884, baseEnd_395884] using wordTrace_append hprefix tailTrace_395884
  have hstable : (prefixWord ++ tailWord_395884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395884).length < 2 ^ (prefixWord ++ tailWord_395884).sum := by decide
  have hdescent : baseEnd_395884 < baseStart_395884 := by decide
  rcases family_descends (prefixWord ++ tailWord_395884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395890 : List Nat := [3, 2, 1, 2, 5, 1, 1, 1, 5]
def baseStart_395890 : Nat := 118140960795 + 395890 * 2 ^ 59
def prefixEnd_395890 : Nat := 4983230072969 + 3 ^ 40 * 395890 * 2
def baseEnd_395890 : Nat := 90347491692693916557485

theorem tailTrace_395890 : CollatzResearch.WordTrace tailWord_395890 prefixEnd_395890 90347491692693916557485 := by
  unfold tailWord_395890
  simp only [CollatzResearch.WordTrace]
  refine ⟨3609823633941404368548281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9626196357177078316128749 3609823633941404368548281)
  ·
    refine ⟨2707367725456053276411211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3609823633941404368548281 2707367725456053276411211)
    ·
      refine ⟨4061051588184079914616817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2707367725456053276411211 4061051588184079914616817)
      ·
        refine ⟨3045788691138059935962613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4061051588184079914616817 3045788691138059935962613)
        ·
          refine ⟨285542689794193118996495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3045788691138059935962613 285542689794193118996495)
          ·
            refine ⟨428314034691289678494743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 285542689794193118996495 428314034691289678494743)
            ·
              refine ⟨642471052036934517742115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428314034691289678494743 642471052036934517742115)
              ·
                refine ⟨963706578055401776613173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 642471052036934517742115 963706578055401776613173)
                ·
                  refine ⟨90347491692693916557485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 963706578055401776613173 90347491692693916557485)
                  ·
                    rfl

theorem cell21_395890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 5, 1, 1, 1, 5].length) (baseStart_395890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_395890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_395890 prefixEnd_395890 := by exact prefixLift 395890
  have htrace : WordTrace (prefixWord ++ tailWord_395890) baseStart_395890 baseEnd_395890 := by
    simpa [prefixWord, tailWord_395890, baseEnd_395890] using wordTrace_append hprefix tailTrace_395890
  have hstable : (prefixWord ++ tailWord_395890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395890).length < 2 ^ (prefixWord ++ tailWord_395890).sum := by decide
  have hdescent : baseEnd_395890 < baseStart_395890 := by decide
  rcases family_descends (prefixWord ++ tailWord_395890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395904 : List Nat := [2, 1, 1, 2, 1, 7, 2, 1, 4]
def baseStart_395904 : Nat := 118140960795 + 395904 * 2 ^ 59
def prefixEnd_395904 : Nat := 4983230072969 + 3 ^ 40 * 395904 * 2
def baseEnd_395904 : Nat := 90350686683433003324123

theorem tailTrace_395904 : CollatzResearch.WordTrace tailWord_395904 prefixEnd_395904 90350686683433003324123 := by
  unfold tailWord_395904
  simp only [CollatzResearch.WordTrace]
  refine ⟨7219902578857448932601383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9626536771809931910135177 7219902578857448932601383)
  ·
    refine ⟨10829853868286173398902075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7219902578857448932601383 10829853868286173398902075)
    ·
      refine ⟨16244780802429260098353113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10829853868286173398902075 16244780802429260098353113)
      ·
        refine ⟨12183585601821945073764835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16244780802429260098353113 12183585601821945073764835)
        ·
          refine ⟨18275378402732917610647253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12183585601821945073764835 18275378402732917610647253)
          ·
            refine ⟨428329181314052756499545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 18275378402732917610647253 428329181314052756499545)
            ·
              refine ⟨321246885985539567374659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428329181314052756499545 321246885985539567374659)
              ·
                refine ⟨481870328978309351061989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321246885985539567374659 481870328978309351061989)
                ·
                  refine ⟨90350686683433003324123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 481870328978309351061989 90350686683433003324123)
                  ·
                    rfl

theorem cell21_395904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 4].length) (baseStart_395904 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_395904 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_395904 prefixEnd_395904 := by exact prefixLift 395904
  have htrace : WordTrace (prefixWord ++ tailWord_395904) baseStart_395904 baseEnd_395904 := by
    simpa [prefixWord, tailWord_395904, baseEnd_395904] using wordTrace_append hprefix tailTrace_395904
  have hstable : (prefixWord ++ tailWord_395904).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395904).length < 2 ^ (prefixWord ++ tailWord_395904).sum := by decide
  have hdescent : baseEnd_395904 < baseStart_395904 := by decide
  rcases family_descends (prefixWord ++ tailWord_395904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396264 : List Nat := [2, 1, 4, 1, 1, 1, 4, 7]
def baseStart_396264 : Nat := 118140960795 + 396264 * 2 ^ 59
def prefixEnd_396264 : Nat := 4983230072969 + 3 ^ 40 * 396264 * 2
def baseEnd_396264 : Nat := 30144281196050792441129

theorem tailTrace_396264 : CollatzResearch.WordTrace tailWord_396264 prefixEnd_396264 30144281196050792441129 := by
  unfold tailWord_396264
  simp only [CollatzResearch.WordTrace]
  refine ⟨7226467718205339674153923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9635290290940452898871897 7226467718205339674153923)
  ·
    refine ⟨10839701577308009511230885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7226467718205339674153923 10839701577308009511230885)
    ·
      refine ⟨2032444045745251783355791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10839701577308009511230885 2032444045745251783355791)
      ·
        refine ⟨3048666068617877675033687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2032444045745251783355791 3048666068617877675033687)
        ·
          refine ⟨4572999102926816512550531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3048666068617877675033687 4572999102926816512550531)
          ·
            refine ⟨6859498654390224768825797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4572999102926816512550531 6859498654390224768825797)
            ·
              refine ⟨1286155997698167144154837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6859498654390224768825797 1286155997698167144154837)
              ·
                refine ⟨30144281196050792441129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1286155997698167144154837 30144281196050792441129)
                ·
                  rfl

theorem cell21_396264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 7].length) (baseStart_396264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_396264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_396264 prefixEnd_396264 := by exact prefixLift 396264
  have htrace : WordTrace (prefixWord ++ tailWord_396264) baseStart_396264 baseEnd_396264 := by
    simpa [prefixWord, tailWord_396264, baseEnd_396264] using wordTrace_append hprefix tailTrace_396264
  have hstable : (prefixWord ++ tailWord_396264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396264).length < 2 ^ (prefixWord ++ tailWord_396264).sum := by decide
  have hdescent : baseEnd_396264 < baseStart_396264 := by decide
  rcases family_descends (prefixWord ++ tailWord_396264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396295 : List Nat := [1, 1, 4, 3, 1, 1, 2, 3, 5]
def baseStart_396295 : Nat := 118140960795 + 396295 * 2 ^ 59
def prefixEnd_396295 : Nat := 4983230072969 + 3 ^ 40 * 396295 * 2
def baseEnd_396295 : Nat := 90439918210503212306657

theorem tailTrace_396295 : CollatzResearch.WordTrace tailWord_396295 prefixEnd_396295 90439918210503212306657 := by
  unfold tailWord_396295
  simp only [CollatzResearch.WordTrace]
  refine ⟨14454066099298371642686339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9636044066198914428457559 14454066099298371642686339)
  ·
    refine ⟨21681099148947557464029509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14454066099298371642686339 21681099148947557464029509)
    ·
      refine ⟨4065206090427667024505533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21681099148947557464029509 4065206090427667024505533)
      ·
        refine ⟨1524452283910375134189575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4065206090427667024505533 1524452283910375134189575)
        ·
          refine ⟨2286678425865562701284363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1524452283910375134189575 2286678425865562701284363)
          ·
            refine ⟨3430017638798344051926545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2286678425865562701284363 3430017638798344051926545)
            ·
              refine ⟨2572513229098758038944909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3430017638798344051926545 2572513229098758038944909)
              ·
                refine ⟨964692460912034264604341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2572513229098758038944909 964692460912034264604341)
                ·
                  refine ⟨90439918210503212306657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 964692460912034264604341 90439918210503212306657)
                  ·
                    rfl

theorem cell21_396295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3, 5].length) (baseStart_396295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_396295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_396295 prefixEnd_396295 := by exact prefixLift 396295
  have htrace : WordTrace (prefixWord ++ tailWord_396295) baseStart_396295 baseEnd_396295 := by
    simpa [prefixWord, tailWord_396295, baseEnd_396295] using wordTrace_append hprefix tailTrace_396295
  have hstable : (prefixWord ++ tailWord_396295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396295).length < 2 ^ (prefixWord ++ tailWord_396295).sum := by decide
  have hdescent : baseEnd_396295 < baseStart_396295 := by decide
  rcases family_descends (prefixWord ++ tailWord_396295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396385 : List Nat := [1, 2, 3, 1, 1, 2, 3, 2, 6]
def baseStart_396385 : Nat := 118140960795 + 396385 * 2 ^ 59
def prefixEnd_396385 : Nat := 4983230072969 + 3 ^ 40 * 396385 * 2
def baseEnd_396385 : Nat := 90460457436683055806473

theorem tailTrace_396385 : CollatzResearch.WordTrace tailWord_396385 prefixEnd_396385 90460457436683055806473 := by
  unfold tailWord_396385
  simp only [CollatzResearch.WordTrace]
  refine ⟨14457348668972317013462609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9638232445981544675641739 14457348668972317013462609)
  ·
    refine ⟨10843011501729237760096957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14457348668972317013462609 10843011501729237760096957)
    ·
      refine ⟨4066129313148464160036359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10843011501729237760096957 4066129313148464160036359)
      ·
        refine ⟨6099193969722696240054539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4066129313148464160036359 6099193969722696240054539)
        ·
          refine ⟨9148790954584044360081809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6099193969722696240054539 9148790954584044360081809)
          ·
            refine ⟨6861593215938033270061357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9148790954584044360081809 6861593215938033270061357)
            ·
              refine ⟨2573097455976762476273009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6861593215938033270061357 2573097455976762476273009)
              ·
                refine ⟨1929823091982571857204757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2573097455976762476273009 1929823091982571857204757)
                ·
                  refine ⟨90460457436683055806473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1929823091982571857204757 90460457436683055806473)
                  ·
                    rfl

theorem cell21_396385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_396385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_396385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_396385 prefixEnd_396385 := by exact prefixLift 396385
  have htrace : WordTrace (prefixWord ++ tailWord_396385) baseStart_396385 baseEnd_396385 := by
    simpa [prefixWord, tailWord_396385, baseEnd_396385] using wordTrace_append hprefix tailTrace_396385
  have hstable : (prefixWord ++ tailWord_396385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396385).length < 2 ^ (prefixWord ++ tailWord_396385).sum := by decide
  have hdescent : baseEnd_396385 < baseStart_396385 := by decide
  rcases family_descends (prefixWord ++ tailWord_396385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396402 : List Nat := [3, 2, 1, 2, 2, 1, 2, 4, 4]
def baseStart_396402 : Nat := 118140960795 + 396402 * 2 ^ 59
def prefixEnd_396402 : Nat := 4983230072969 + 3 ^ 40 * 396402 * 2
def baseEnd_396402 : Nat := 90464337068294804023105

theorem tailTrace_396402 : CollatzResearch.WordTrace tailWord_396402 prefixEnd_396402 90464337068294804023105 := by
  unfold tailWord_396402
  simp only [CollatzResearch.WordTrace]
  refine ⟨3614492177477682229207865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9638645806607152611220973 3614492177477682229207865)
  ·
    refine ⟨2710869133108261671905899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3614492177477682229207865 2710869133108261671905899)
    ·
      refine ⟨4066303699662392507858849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2710869133108261671905899 4066303699662392507858849)
      ·
        refine ⟨3049727774746794380894137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4066303699662392507858849 3049727774746794380894137)
        ·
          refine ⟨2287295831060095785670603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3049727774746794380894137 2287295831060095785670603)
          ·
            refine ⟨3430943746590143678505905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2287295831060095785670603 3430943746590143678505905)
            ·
              refine ⟨2573207809942607758879429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3430943746590143678505905 2573207809942607758879429)
              ·
                refine ⟨482476464364238954789893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2573207809942607758879429 482476464364238954789893)
                ·
                  refine ⟨90464337068294804023105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 482476464364238954789893 90464337068294804023105)
                  ·
                    rfl

theorem cell21_396402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_396402 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_396402 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_396402 prefixEnd_396402 := by exact prefixLift 396402
  have htrace : WordTrace (prefixWord ++ tailWord_396402) baseStart_396402 baseEnd_396402 := by
    simpa [prefixWord, tailWord_396402, baseEnd_396402] using wordTrace_append hprefix tailTrace_396402
  have hstable : (prefixWord ++ tailWord_396402).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396402).length < 2 ^ (prefixWord ++ tailWord_396402).sum := by decide
  have hdescent : baseEnd_396402 < baseStart_396402 := by decide
  rcases family_descends (prefixWord ++ tailWord_396402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396475 : List Nat := [1, 1, 1, 1, 1, 2, 4, 10]
def baseStart_396475 : Nat := 118140960795 + 396475 * 2 ^ 59
def prefixEnd_396475 : Nat := 4983230072969 + 3 ^ 40 * 396475 * 2
def baseEnd_396475 : Nat := 30160332220954299768763

theorem tailTrace_396475 : CollatzResearch.WordTrace tailWord_396475 prefixEnd_396475 30160332220954299768763 := by
  unfold tailWord_396475
  simp only [CollatzResearch.WordTrace]
  refine ⟨14460631238646262384238879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9640420825764174922825919 14460631238646262384238879)
  ·
    refine ⟨21690946857969393576358319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14460631238646262384238879 21690946857969393576358319)
    ·
      refine ⟨32536420286954090364537479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21690946857969393576358319 32536420286954090364537479)
      ·
        refine ⟨48804630430431135546806219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32536420286954090364537479 48804630430431135546806219)
        ·
          refine ⟨73206945645646703320209329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48804630430431135546806219 73206945645646703320209329)
          ·
            refine ⟨54905209234235027490156997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 73206945645646703320209329 54905209234235027490156997)
            ·
              refine ⟨10294726731419067654404437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54905209234235027490156997 10294726731419067654404437)
              ·
                refine ⟨30160332220954299768763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10294726731419067654404437 30160332220954299768763)
                ·
                  rfl

theorem cell21_396475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 10].length) (baseStart_396475 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_396475 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_396475 prefixEnd_396475 := by exact prefixLift 396475
  have htrace : WordTrace (prefixWord ++ tailWord_396475) baseStart_396475 baseEnd_396475 := by
    simpa [prefixWord, tailWord_396475, baseEnd_396475] using wordTrace_append hprefix tailTrace_396475
  have hstable : (prefixWord ++ tailWord_396475).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396475).length < 2 ^ (prefixWord ++ tailWord_396475).sum := by decide
  have hdescent : baseEnd_396475 < baseStart_396475 := by decide
  rcases family_descends (prefixWord ++ tailWord_396475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396506 : List Nat := [3, 1, 1, 2, 2, 1, 1, 1, 9]
def baseStart_396506 : Nat := 118140960795 + 396506 * 2 ^ 59
def prefixEnd_396506 : Nat := 4983230072969 + 3 ^ 40 * 396506 * 2
def baseEnd_396506 : Nat := 90488071285213734289559

theorem tailTrace_396506 : CollatzResearch.WordTrace tailWord_396506 prefixEnd_396506 90488071285213734289559 := by
  unfold tailWord_396506
  simp only [CollatzResearch.WordTrace]
  refine ⟨3615440475383488669654343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9641174601022636452411581 3615440475383488669654343)
  ·
    refine ⟨5423160713075233004481515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3615440475383488669654343 5423160713075233004481515)
    ·
      refine ⟨8134741069612849506722273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5423160713075233004481515 8134741069612849506722273)
      ·
        refine ⟨6101055802209637130041705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8134741069612849506722273 6101055802209637130041705)
        ·
          refine ⟨4575791851657227847531279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6101055802209637130041705 4575791851657227847531279)
          ·
            refine ⟨6863687777485841771296919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4575791851657227847531279 6863687777485841771296919)
            ·
              refine ⟨10295531666228762656945379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6863687777485841771296919 10295531666228762656945379)
              ·
                refine ⟨15443297499343143985418069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10295531666228762656945379 15443297499343143985418069)
                ·
                  refine ⟨90488071285213734289559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15443297499343143985418069 90488071285213734289559)
                  ·
                    rfl

theorem cell21_396506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_396506 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_396506 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_396506 prefixEnd_396506 := by exact prefixLift 396506
  have htrace : WordTrace (prefixWord ++ tailWord_396506) baseStart_396506 baseEnd_396506 := by
    simpa [prefixWord, tailWord_396506, baseEnd_396506] using wordTrace_append hprefix tailTrace_396506
  have hstable : (prefixWord ++ tailWord_396506).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396506).length < 2 ^ (prefixWord ++ tailWord_396506).sum := by decide
  have hdescent : baseEnd_396506 < baseStart_396506 := by decide
  rcases family_descends (prefixWord ++ tailWord_396506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396509 : List Nat := [1, 4, 3, 2, 2, 1, 8]
def baseStart_396509 : Nat := 118140960795 + 396509 * 2 ^ 59
def prefixEnd_396509 : Nat := 4983230072969 + 3 ^ 40 * 396509 * 2
def baseEnd_396509 : Nat := 10054306214009599526617

theorem tailTrace_396509 : CollatzResearch.WordTrace tailWord_396509 prefixEnd_396509 10054306214009599526617 := by
  unfold tailWord_396509
  simp only [CollatzResearch.WordTrace]
  refine ⟨14461871320523086190976581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9641247547015390793984387 14461871320523086190976581)
  ·
    refine ⟨2711600872598078660808109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14461871320523086190976581 2711600872598078660808109)
    ·
      refine ⟨1016850327224279497803041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2711600872598078660808109 1016850327224279497803041)
      ·
        refine ⟨762637745418209623352281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1016850327224279497803041 762637745418209623352281)
        ·
          refine ⟨571978309063657217514211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 762637745418209623352281 571978309063657217514211)
          ·
            refine ⟨857967463595485826271317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571978309063657217514211 857967463595485826271317)
            ·
              refine ⟨10054306214009599526617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 857967463595485826271317 10054306214009599526617)
              ·
                rfl

theorem cell21_396509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 8].length) (baseStart_396509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_396509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_396509 prefixEnd_396509 := by exact prefixLift 396509
  have htrace : WordTrace (prefixWord ++ tailWord_396509) baseStart_396509 baseEnd_396509 := by
    simpa [prefixWord, tailWord_396509, baseEnd_396509] using wordTrace_append hprefix tailTrace_396509
  have hstable : (prefixWord ++ tailWord_396509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396509).length < 2 ^ (prefixWord ++ tailWord_396509).sum := by decide
  have hdescent : baseEnd_396509 < baseStart_396509 := by decide
  rcases family_descends (prefixWord ++ tailWord_396509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396523 : List Nat := [1, 1, 1, 1, 2, 7, 2, 1, 5]
def baseStart_396523 : Nat := 118140960795 + 396523 * 2 ^ 59
def prefixEnd_396523 : Nat := 4983230072969 + 3 ^ 40 * 396523 * 2
def baseEnd_396523 : Nat := 90491950916825482506191

theorem tailTrace_396523 : CollatzResearch.WordTrace tailWord_396523 prefixEnd_396523 90491950916825482506191 := by
  unfold tailWord_396523
  simp only [CollatzResearch.WordTrace]
  refine ⟨14462381942472366581986223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9641587961648244387990815 14462381942472366581986223)
  ·
    refine ⟨21693572913708549872979335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14462381942472366581986223 21693572913708549872979335)
    ·
      refine ⟨32540359370562824809469003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21693572913708549872979335 32540359370562824809469003)
      ·
        refine ⟨48810539055844237214203505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32540359370562824809469003 48810539055844237214203505)
        ·
          refine ⟨36607904291883177910652629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48810539055844237214203505 36607904291883177910652629)
          ·
            refine ⟨857997756841011982280921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 36607904291883177910652629 857997756841011982280921)
            ·
              refine ⟨643498317630758986710691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 857997756841011982280921 643498317630758986710691)
              ·
                refine ⟨965247476446138480066037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643498317630758986710691 965247476446138480066037)
                ·
                  refine ⟨90491950916825482506191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 965247476446138480066037 90491950916825482506191)
                  ·
                    rfl

theorem cell21_396523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7, 2, 1, 5].length) (baseStart_396523 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_396523 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_396523 prefixEnd_396523 := by exact prefixLift 396523
  have htrace : WordTrace (prefixWord ++ tailWord_396523) baseStart_396523 baseEnd_396523 := by
    simpa [prefixWord, tailWord_396523, baseEnd_396523] using wordTrace_append hprefix tailTrace_396523
  have hstable : (prefixWord ++ tailWord_396523).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396523).length < 2 ^ (prefixWord ++ tailWord_396523).sum := by decide
  have hdescent : baseEnd_396523 < baseStart_396523 := by decide
  rcases family_descends (prefixWord ++ tailWord_396523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396568 : List Nat := [2, 1, 2, 3, 1, 5, 7]
def baseStart_396568 : Nat := 118140960795 + 396568 * 2 ^ 59
def prefixEnd_396568 : Nat := 4983230072969 + 3 ^ 40 * 396568 * 2
def baseEnd_396568 : Nat := 10055802281101711584011

theorem tailTrace_396568 : CollatzResearch.WordTrace tailWord_396568 prefixEnd_396568 10055802281101711584011 := by
  unfold tailWord_396568
  simp only [CollatzResearch.WordTrace]
  refine ⟨7232011613654669633687179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9642682151539559511582905 7232011613654669633687179)
  ·
    refine ⟨10848017420482004450530769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7232011613654669633687179 10848017420482004450530769)
    ·
      refine ⟨8136013065361503337898077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10848017420482004450530769 8136013065361503337898077)
      ·
        refine ⟨3051004899510563751711779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8136013065361503337898077 3051004899510563751711779)
        ·
          refine ⟨4576507349265845627567669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3051004899510563751711779 4576507349265845627567669)
          ·
            refine ⟨429047563993673027584469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4576507349265845627567669 429047563993673027584469)
            ·
              refine ⟨10055802281101711584011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 429047563993673027584469 10055802281101711584011)
              ·
                rfl

theorem cell21_396568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 5, 7].length) (baseStart_396568 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_396568 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_396568 prefixEnd_396568 := by exact prefixLift 396568
  have htrace : WordTrace (prefixWord ++ tailWord_396568) baseStart_396568 baseEnd_396568 := by
    simpa [prefixWord, tailWord_396568, baseEnd_396568] using wordTrace_append hprefix tailTrace_396568
  have hstable : (prefixWord ++ tailWord_396568).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396568).length < 2 ^ (prefixWord ++ tailWord_396568).sum := by decide
  have hdescent : baseEnd_396568 < baseStart_396568 := by decide
  rcases family_descends (prefixWord ++ tailWord_396568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396574 : List Nat := [4, 3, 2, 1, 2, 2, 1, 1, 5]
def baseStart_396574 : Nat := 118140960795 + 396574 * 2 ^ 59
def prefixEnd_396574 : Nat := 4983230072969 + 3 ^ 40 * 396574 * 2
def baseEnd_396574 : Nat := 90503589811660727156087

theorem tailTrace_396574 : CollatzResearch.WordTrace tailWord_396574 prefixEnd_396574 90503589811660727156087 := by
  unfold tailWord_396574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1808030258160950286511597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9642828043525068194728517 1808030258160950286511597)
  ·
    refine ⟨678011346810356357441849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1808030258160950286511597 678011346810356357441849)
    ·
      refine ⟨508508510107767268081387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 678011346810356357441849 508508510107767268081387)
      ·
        refine ⟨762762765161650902122081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 508508510107767268081387 762762765161650902122081)
        ·
          refine ⟨572072073871238176591561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 762762765161650902122081 572072073871238176591561)
          ·
            refine ⟨429054055403428632443671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 572072073871238176591561 429054055403428632443671)
            ·
              refine ⟨643581083105142948665507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429054055403428632443671 643581083105142948665507)
              ·
                refine ⟨965371624657714422998261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643581083105142948665507 965371624657714422998261)
                ·
                  refine ⟨90503589811660727156087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 965371624657714422998261 90503589811660727156087)
                  ·
                    rfl

theorem cell21_396574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 2, 1, 1, 5].length) (baseStart_396574 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_396574 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_396574 prefixEnd_396574 := by exact prefixLift 396574
  have htrace : WordTrace (prefixWord ++ tailWord_396574) baseStart_396574 baseEnd_396574 := by
    simpa [prefixWord, tailWord_396574, baseEnd_396574] using wordTrace_append hprefix tailTrace_396574
  have hstable : (prefixWord ++ tailWord_396574).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396574).length < 2 ^ (prefixWord ++ tailWord_396574).sum := by decide
  have hdescent : baseEnd_396574 < baseStart_396574 := by decide
  rcases family_descends (prefixWord ++ tailWord_396574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396644 : List Nat := [2, 3, 1, 1, 3, 2, 3, 6]
def baseStart_396644 : Nat := 118140960795 + 396644 * 2 ^ 59
def prefixEnd_396644 : Nat := 4983230072969 + 3 ^ 40 * 396644 * 2
def baseEnd_396644 : Nat := 30173188255118720329759

theorem tailTrace_396644 : CollatzResearch.WordTrace tailWord_396644 prefixEnd_396644 30173188255118720329759 := by
  unfold tailWord_396644
  simp only [CollatzResearch.WordTrace]
  refine ⟨7233397587517002123570493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9644530116689336164760657 7233397587517002123570493)
  ·
    refine ⟨2712524095318875796338935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7233397587517002123570493 2712524095318875796338935)
    ·
      refine ⟨4068786142978313694508403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2712524095318875796338935 4068786142978313694508403)
      ·
        refine ⟨6103179214467470541762605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4068786142978313694508403 6103179214467470541762605)
        ·
          refine ⟨2288692205425301453160977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6103179214467470541762605 2288692205425301453160977)
          ·
            refine ⟨1716519154068976089870733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2288692205425301453160977 1716519154068976089870733)
            ·
              refine ⟨643694682775866033701525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1716519154068976089870733 643694682775866033701525)
              ·
                refine ⟨30173188255118720329759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 643694682775866033701525 30173188255118720329759)
                ·
                  rfl

theorem cell21_396644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 3, 6].length) (baseStart_396644 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_396644 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_396644 prefixEnd_396644 := by exact prefixLift 396644
  have htrace : WordTrace (prefixWord ++ tailWord_396644) baseStart_396644 baseEnd_396644 := by
    simpa [prefixWord, tailWord_396644, baseEnd_396644] using wordTrace_append hprefix tailTrace_396644
  have hstable : (prefixWord ++ tailWord_396644).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396644).length < 2 ^ (prefixWord ++ tailWord_396644).sum := by decide
  have hdescent : baseEnd_396644 < baseStart_396644 := by decide
  rcases family_descends (prefixWord ++ tailWord_396644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396692 : List Nat := [2, 4, 2, 1, 2, 2, 2, 1, 5]
def baseStart_396692 : Nat := 118140960795 + 396692 * 2 ^ 59
def prefixEnd_396692 : Nat := 4983230072969 + 3 ^ 40 * 396692 * 2
def baseEnd_396692 : Nat := 90530519019318744189179

theorem tailTrace_396692 : CollatzResearch.WordTrace tailWord_396692 prefixEnd_396692 90530519019318744189179 := by
  unfold tailWord_396692
  simp only [CollatzResearch.WordTrace]
  refine ⟨7234272939430054222444165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9645697252573405629925553 7234272939430054222444165)
  ·
    refine ⟨1356426176143135166708281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7234272939430054222444165 1356426176143135166708281)
    ·
      refine ⟨1017319632107351375031211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1356426176143135166708281 1017319632107351375031211)
      ·
        refine ⟨1525979448161027062546817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1017319632107351375031211 1525979448161027062546817)
        ·
          refine ⟨1144484586120770296910113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1525979448161027062546817 1144484586120770296910113)
          ·
            refine ⟨858363439590577722682585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1144484586120770296910113 858363439590577722682585)
            ·
              refine ⟨643772579692933292011939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 858363439590577722682585 643772579692933292011939)
              ·
                refine ⟨965658869539399938017909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 643772579692933292011939 965658869539399938017909)
                ·
                  refine ⟨90530519019318744189179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 965658869539399938017909 90530519019318744189179)
                  ·
                    rfl

theorem cell21_396692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_396692 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_396692 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_396692 prefixEnd_396692 := by exact prefixLift 396692
  have htrace : WordTrace (prefixWord ++ tailWord_396692) baseStart_396692 baseEnd_396692 := by
    simpa [prefixWord, tailWord_396692, baseEnd_396692] using wordTrace_append hprefix tailTrace_396692
  have hstable : (prefixWord ++ tailWord_396692).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396692).length < 2 ^ (prefixWord ++ tailWord_396692).sum := by decide
  have hdescent : baseEnd_396692 < baseStart_396692 := by decide
  rcases family_descends (prefixWord ++ tailWord_396692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396751 : List Nat := [1, 1, 2, 1, 1, 4, 2, 6, 3]
def baseStart_396751 : Nat := 118140960795 + 396751 * 2 ^ 59
def prefixEnd_396751 : Nat := 4983230072969 + 3 ^ 40 * 396751 * 2
def baseEnd_396751 : Nat := 90543983623147752705725

theorem tailTrace_396751 : CollatzResearch.WordTrace tailWord_396751 prefixEnd_396751 90543983623147752705725 := by
  unfold tailWord_396751
  simp only [CollatzResearch.WordTrace]
  refine ⟨14470697785646361521286107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9647131857097574347524071 14470697785646361521286107)
  ·
    refine ⟨21706046678469542281929161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14470697785646361521286107 21706046678469542281929161)
    ·
      refine ⟨16279535008852156711446871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21706046678469542281929161 16279535008852156711446871)
      ·
        refine ⟨24419302513278235067170307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16279535008852156711446871 24419302513278235067170307)
        ·
          refine ⟨36628953769917352600755461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24419302513278235067170307 36628953769917352600755461)
          ·
            refine ⟨6867928831859503612641649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36628953769917352600755461 6867928831859503612641649)
            ·
              refine ⟨5150946623894627709481237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6867928831859503612641649 5150946623894627709481237)
              ·
                refine ⟨241450622995060673881933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5150946623894627709481237 241450622995060673881933)
                ·
                  refine ⟨90543983623147752705725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241450622995060673881933 90543983623147752705725)
                  ·
                    rfl

theorem cell21_396751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 6, 3].length) (baseStart_396751 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_396751 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_396751 prefixEnd_396751 := by exact prefixLift 396751
  have htrace : WordTrace (prefixWord ++ tailWord_396751) baseStart_396751 baseEnd_396751 := by
    simpa [prefixWord, tailWord_396751, baseEnd_396751] using wordTrace_append hprefix tailTrace_396751
  have hstable : (prefixWord ++ tailWord_396751).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396751).length < 2 ^ (prefixWord ++ tailWord_396751).sum := by decide
  have hdescent : baseEnd_396751 < baseStart_396751 := by decide
  rcases family_descends (prefixWord ++ tailWord_396751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396802 : List Nat := [3, 4, 1, 2, 1, 1, 4, 2, 3]
def baseStart_396802 : Nat := 118140960795 + 396802 * 2 ^ 59
def prefixEnd_396802 : Nat := 4983230072969 + 3 ^ 40 * 396802 * 2
def baseEnd_396802 : Nat := 90555622517982997355621

theorem tailTrace_396802 : CollatzResearch.WordTrace tailWord_396802 prefixEnd_396802 90555622517982997355621 := by
  unfold tailWord_396802
  simp only [CollatzResearch.WordTrace]
  refine ⟨3618139477115399307848165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9648371938974398154261773 3618139477115399307848165)
  ·
    refine ⟨678401151959137370221531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3618139477115399307848165 678401151959137370221531)
    ·
      refine ⟨1017601727938706055332297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 678401151959137370221531 1017601727938706055332297)
      ·
        refine ⟨763201295954029541499223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1017601727938706055332297 763201295954029541499223)
        ·
          refine ⟨1144801943931044312248835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 763201295954029541499223 1144801943931044312248835)
          ·
            refine ⟨1717202915896566468373253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1144801943931044312248835 1717202915896566468373253)
            ·
              refine ⟨321975546730606212819985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1717202915896566468373253 321975546730606212819985)
              ·
                refine ⟨241481660047954659614989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321975546730606212819985 241481660047954659614989)
                ·
                  refine ⟨90555622517982997355621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241481660047954659614989 90555622517982997355621)
                  ·
                    rfl

theorem cell21_396802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_396802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_396802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_396802 prefixEnd_396802 := by exact prefixLift 396802
  have htrace : WordTrace (prefixWord ++ tailWord_396802) baseStart_396802 baseEnd_396802 := by
    simpa [prefixWord, tailWord_396802, baseEnd_396802] using wordTrace_append hprefix tailTrace_396802
  have hstable : (prefixWord ++ tailWord_396802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396802).length < 2 ^ (prefixWord ++ tailWord_396802).sum := by decide
  have hdescent : baseEnd_396802 < baseStart_396802 := by decide
  rcases family_descends (prefixWord ++ tailWord_396802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396855 : List Nat := [1, 1, 3, 1, 2, 5, 8]
def baseStart_396855 : Nat := 118140960795 + 396855 * 2 ^ 59
def prefixEnd_396855 : Nat := 4983230072969 + 3 ^ 40 * 396855 * 2
def baseEnd_396855 : Nat := 10063079760007409219131

theorem tailTrace_396855 : CollatzResearch.WordTrace tailWord_396855 prefixEnd_396855 10063079760007409219131 := by
  unfold tailWord_396855
  simp only [CollatzResearch.WordTrace]
  refine ⟨14474490977269587283072019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9649660651513058188714679 14474490977269587283072019)
  ·
    refine ⟨21711736465904380924608029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14474490977269587283072019 21711736465904380924608029)
    ·
      refine ⟨8141901174714142846728011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21711736465904380924608029 8141901174714142846728011)
      ·
        refine ⟨12212851762071214270092017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8141901174714142846728011 12212851762071214270092017)
        ·
          refine ⟨9159638821553410702569013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12212851762071214270092017 9159638821553410702569013)
          ·
            refine ⟨858716139520632253365845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9159638821553410702569013 858716139520632253365845)
            ·
              refine ⟨10063079760007409219131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 858716139520632253365845 10063079760007409219131)
              ·
                rfl

theorem cell21_396855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 8].length) (baseStart_396855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_396855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_396855 prefixEnd_396855 := by exact prefixLift 396855
  have htrace : WordTrace (prefixWord ++ tailWord_396855) baseStart_396855 baseEnd_396855 := by
    simpa [prefixWord, tailWord_396855, baseEnd_396855] using wordTrace_append hprefix tailTrace_396855
  have hstable : (prefixWord ++ tailWord_396855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396855).length < 2 ^ (prefixWord ++ tailWord_396855).sum := by decide
  have hdescent : baseEnd_396855 < baseStart_396855 := by decide
  rcases family_descends (prefixWord ++ tailWord_396855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396976 : List Nat := [2, 1, 1, 1, 2, 1, 4, 3, 6]
def baseStart_396976 : Nat := 118140960795 + 396976 * 2 ^ 59
def prefixEnd_396976 : Nat := 4983230072969 + 3 ^ 40 * 396976 * 2
def baseEnd_396976 : Nat := 90595331688597361455265

theorem tailTrace_396976 : CollatzResearch.WordTrace tailWord_396976 prefixEnd_396976 90595331688597361455265 := by
  unfold tailWord_396976
  simp only [CollatzResearch.WordTrace]
  refine ⟨7239452104915612474113391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9652602806554149965484521 7239452104915612474113391)
  ·
    refine ⟨10859178157373418711170087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7239452104915612474113391 10859178157373418711170087)
    ·
      refine ⟨16288767236060128066755131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10859178157373418711170087 16288767236060128066755131)
      ·
        refine ⟨24433150854090192100132697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16288767236060128066755131 24433150854090192100132697)
        ·
          refine ⟨18324863140567644075099523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24433150854090192100132697 18324863140567644075099523)
          ·
            refine ⟨27487294710851466112649285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18324863140567644075099523 27487294710851466112649285)
            ·
              refine ⟨5153867758284649896121741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27487294710851466112649285 5153867758284649896121741)
              ·
                refine ⟨1932700409356743711045653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5153867758284649896121741 1932700409356743711045653)
                ·
                  refine ⟨90595331688597361455265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1932700409356743711045653 90595331688597361455265)
                  ·
                    rfl

theorem cell21_396976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_396976 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_396976 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_396976 prefixEnd_396976 := by exact prefixLift 396976
  have htrace : WordTrace (prefixWord ++ tailWord_396976) baseStart_396976 baseEnd_396976 := by
    simpa [prefixWord, tailWord_396976, baseEnd_396976] using wordTrace_append hprefix tailTrace_396976
  have hstable : (prefixWord ++ tailWord_396976).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396976).length < 2 ^ (prefixWord ++ tailWord_396976).sum := by decide
  have hdescent : baseEnd_396976 < baseStart_396976 := by decide
  rcases family_descends (prefixWord ++ tailWord_396976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396979 : List Nat := [1, 1, 1, 2, 3, 3, 3, 4, 3]
def baseStart_396979 : Nat := 118140960795 + 396979 * 2 ^ 59
def prefixEnd_396979 : Nat := 4983230072969 + 3 ^ 40 * 396979 * 2
def baseEnd_396979 : Nat := 90596016329470022905259

theorem tailTrace_396979 : CollatzResearch.WordTrace tailWord_396979 prefixEnd_396979 90596016329470022905259 := by
  unfold tailWord_396979
  simp only [CollatzResearch.WordTrace]
  refine ⟨14479013628820356460585991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9652675752546904307057327 14479013628820356460585991)
  ·
    refine ⟨21718520443230534690878987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14479013628820356460585991 21718520443230534690878987)
    ·
      refine ⟨32577780664845802036318481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21718520443230534690878987 32577780664845802036318481)
      ·
        refine ⟨24433335498634351527238861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32577780664845802036318481 24433335498634351527238861)
        ·
          refine ⟨9162500811987881822714573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24433335498634351527238861 9162500811987881822714573)
          ·
            refine ⟨3435937804495455683517965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9162500811987881822714573 3435937804495455683517965)
            ·
              refine ⟨1288476676685795881319237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3435937804495455683517965 1288476676685795881319237)
              ·
                refine ⟨241589376878586727747357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1288476676685795881319237 241589376878586727747357)
                ·
                  refine ⟨90596016329470022905259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241589376878586727747357 90596016329470022905259)
                  ·
                    rfl

theorem cell21_396979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 3, 4, 3].length) (baseStart_396979 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_396979 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_396979 prefixEnd_396979 := by exact prefixLift 396979
  have htrace : WordTrace (prefixWord ++ tailWord_396979) baseStart_396979 baseEnd_396979 := by
    simpa [prefixWord, tailWord_396979, baseEnd_396979] using wordTrace_append hprefix tailTrace_396979
  have hstable : (prefixWord ++ tailWord_396979).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396979).length < 2 ^ (prefixWord ++ tailWord_396979).sum := by decide
  have hdescent : baseEnd_396979 < baseStart_396979 := by decide
  rcases family_descends (prefixWord ++ tailWord_396979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396982 : List Nat := [5, 1, 3, 1, 1, 3, 1, 6]
def baseStart_396982 : Nat := 118140960795 + 396982 * 2 ^ 59
def prefixEnd_396982 : Nat := 4983230072969 + 3 ^ 40 * 396982 * 2
def baseEnd_396982 : Nat := 30198900323447561451751

theorem tailTrace_396982 : CollatzResearch.WordTrace tailWord_396982 prefixEnd_396982 30198900323447561451751 := by
  unfold tailWord_396982
  simp only [CollatzResearch.WordTrace]
  refine ⟨904945190488092998309075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9652748698539658648630133 904945190488092998309075)
  ·
    refine ⟨1357417785732139497463613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 904945190488092998309075 1357417785732139497463613)
    ·
      refine ⟨509031669649552311548855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1357417785732139497463613 509031669649552311548855)
      ·
        refine ⟨763547504474328467323283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 509031669649552311548855 763547504474328467323283)
        ·
          refine ⟨1145321256711492700984925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 763547504474328467323283 1145321256711492700984925)
          ·
            refine ⟨429495471266809762869347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1145321256711492700984925 429495471266809762869347)
            ·
              refine ⟨644243206900214644304021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429495471266809762869347 644243206900214644304021)
              ·
                refine ⟨30198900323447561451751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 644243206900214644304021 30198900323447561451751)
                ·
                  rfl

theorem cell21_396982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_396982 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_396982 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_396982 prefixEnd_396982 := by exact prefixLift 396982
  have htrace : WordTrace (prefixWord ++ tailWord_396982) baseStart_396982 baseEnd_396982 := by
    simpa [prefixWord, tailWord_396982, baseEnd_396982] using wordTrace_append hprefix tailTrace_396982
  have hstable : (prefixWord ++ tailWord_396982).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396982).length < 2 ^ (prefixWord ++ tailWord_396982).sum := by decide
  have hdescent : baseEnd_396982 < baseStart_396982 := by decide
  rcases family_descends (prefixWord ++ tailWord_396982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397027 : List Nat := [1, 1, 1, 7, 2, 2, 1, 2, 4]
def baseStart_397027 : Nat := 118140960795 + 397027 * 2 ^ 59
def prefixEnd_397027 : Nat := 4983230072969 + 3 ^ 40 * 397027 * 2
def baseEnd_397027 : Nat := 90606970583432606105161

theorem tailTrace_397027 : CollatzResearch.WordTrace tailWord_397027 prefixEnd_397027 90606970583432606105161 := by
  unfold tailWord_397027
  simp only [CollatzResearch.WordTrace]
  refine ⟨14480764332646460658333335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9653842888430973772222223 14480764332646460658333335)
  ·
    refine ⟨21721146498969690987500003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14480764332646460658333335 21721146498969690987500003)
    ·
      refine ⟨32581719748454536481250005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21721146498969690987500003 32581719748454536481250005)
      ·
        refine ⟨763634056604403198779297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 32581719748454536481250005 763634056604403198779297)
        ·
          refine ⟨572725542453302399084473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 763634056604403198779297 572725542453302399084473)
          ·
            refine ⟨429544156839976799313355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 572725542453302399084473 429544156839976799313355)
            ·
              refine ⟨644316235259965198970033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429544156839976799313355 644316235259965198970033)
              ·
                refine ⟨483237176444973899227525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 644316235259965198970033 483237176444973899227525)
                ·
                  refine ⟨90606970583432606105161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 483237176444973899227525 90606970583432606105161)
                  ·
                    rfl

theorem cell21_397027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 2, 4].length) (baseStart_397027 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_397027 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_397027 prefixEnd_397027 := by exact prefixLift 397027
  have htrace : WordTrace (prefixWord ++ tailWord_397027) baseStart_397027 baseEnd_397027 := by
    simpa [prefixWord, tailWord_397027, baseEnd_397027] using wordTrace_append hprefix tailTrace_397027
  have hstable : (prefixWord ++ tailWord_397027).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397027).length < 2 ^ (prefixWord ++ tailWord_397027).sum := by decide
  have hdescent : baseEnd_397027 < baseStart_397027 := by decide
  rcases family_descends (prefixWord ++ tailWord_397027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397145 : List Nat := [1, 2, 1, 2, 2, 3, 4, 2, 4]
def baseStart_397145 : Nat := 118140960795 + 397145 * 2 ^ 59
def prefixEnd_397145 : Nat := 4983230072969 + 3 ^ 40 * 397145 * 2
def baseEnd_397145 : Nat := 90633899791090623138253

theorem tailTrace_397145 : CollatzResearch.WordTrace tailWord_397145 prefixEnd_397145 90633899791090623138253 := by
  unfold tailWord_397145
  simp only [CollatzResearch.WordTrace]
  refine ⟨14485068146218966811128889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9656712097479311207419259 14485068146218966811128889)
  ·
    refine ⟨10863801109664225108346667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14485068146218966811128889 10863801109664225108346667)
    ·
      refine ⟨16295701664496337662520001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10863801109664225108346667 16295701664496337662520001)
      ·
        refine ⟨12221776248372253246890001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16295701664496337662520001 12221776248372253246890001)
        ·
          refine ⟨9166332186279189935167501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12221776248372253246890001 9166332186279189935167501)
          ·
            refine ⟨3437374569854696225687813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9166332186279189935167501 3437374569854696225687813)
            ·
              refine ⟨644507731847755542316465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3437374569854696225687813 644507731847755542316465)
              ·
                refine ⟨483380798885816656737349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 644507731847755542316465 483380798885816656737349)
                ·
                  refine ⟨90633899791090623138253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 483380798885816656737349 90633899791090623138253)
                  ·
                    rfl

theorem cell21_397145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 4, 2, 4].length) (baseStart_397145 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_397145 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_397145 prefixEnd_397145 := by exact prefixLift 397145
  have htrace : WordTrace (prefixWord ++ tailWord_397145) baseStart_397145 baseEnd_397145 := by
    simpa [prefixWord, tailWord_397145, baseEnd_397145] using wordTrace_append hprefix tailTrace_397145
  have hstable : (prefixWord ++ tailWord_397145).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397145).length < 2 ^ (prefixWord ++ tailWord_397145).sum := by decide
  have hdescent : baseEnd_397145 < baseStart_397145 := by decide
  rcases family_descends (prefixWord ++ tailWord_397145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397207 : List Nat := [1, 1, 3, 3, 1, 3, 2, 4, 3]
def baseStart_397207 : Nat := 118140960795 + 397207 * 2 ^ 59
def prefixEnd_397207 : Nat := 4983230072969 + 3 ^ 40 * 397207 * 2
def baseEnd_397207 : Nat := 90648049035792293104793

theorem tailTrace_397207 : CollatzResearch.WordTrace tailWord_397207 prefixEnd_397207 90648049035792293104793 := by
  unfold tailWord_397207
  simp only [CollatzResearch.WordTrace]
  refine ⟨14487329471994351399885875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9658219647996234266590583 14487329471994351399885875)
  ·
    refine ⟨21730994207991527099828813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14487329471994351399885875 21730994207991527099828813)
    ·
      refine ⟨8149122827996822662435805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21730994207991527099828813 8149122827996822662435805)
      ·
        refine ⟨3055921060498808498413427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8149122827996822662435805 3055921060498808498413427)
        ·
          refine ⟨4583881590748212747620141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3055921060498808498413427 4583881590748212747620141)
          ·
            refine ⟨1718955596530579780357553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4583881590748212747620141 1718955596530579780357553)
            ·
              refine ⟨1289216697397934835268165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1718955596530579780357553 1289216697397934835268165)
              ·
                refine ⟨241728130762112781612781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1289216697397934835268165 241728130762112781612781)
                ·
                  refine ⟨90648049035792293104793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241728130762112781612781 90648049035792293104793)
                  ·
                    rfl

theorem cell21_397207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 4, 3].length) (baseStart_397207 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_397207 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_397207 prefixEnd_397207 := by exact prefixLift 397207
  have htrace : WordTrace (prefixWord ++ tailWord_397207) baseStart_397207 baseEnd_397207 := by
    simpa [prefixWord, tailWord_397207, baseEnd_397207] using wordTrace_append hprefix tailTrace_397207
  have hstable : (prefixWord ++ tailWord_397207).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397207).length < 2 ^ (prefixWord ++ tailWord_397207).sum := by decide
  have hdescent : baseEnd_397207 < baseStart_397207 := by decide
  rcases family_descends (prefixWord ++ tailWord_397207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397390 : List Nat := [4, 1, 1, 1, 1, 5, 3, 1, 4]
def baseStart_397390 : Nat := 118140960795 + 397390 * 2 ^ 59
def prefixEnd_397390 : Nat := 4983230072969 + 3 ^ 40 * 397390 * 2
def baseEnd_397390 : Nat := 90689812129024641554419

theorem tailTrace_397390 : CollatzResearch.WordTrace tailWord_397390 prefixEnd_397390 90689812129024641554419 := by
  unfold tailWord_397390
  simp only [CollatzResearch.WordTrace]
  refine ⟨1811750503791421706724703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9662669353554249102531749 1811750503791421706724703)
  ·
    refine ⟨2717625755687132560087055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1811750503791421706724703 2717625755687132560087055)
    ·
      refine ⟨4076438633530698840130583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2717625755687132560087055 4076438633530698840130583)
      ·
        refine ⟨6114657950296048260195875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4076438633530698840130583 6114657950296048260195875)
        ·
          refine ⟨9171986925444072390293813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6114657950296048260195875 9171986925444072390293813)
          ·
            refine ⟨859873774260381786590045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9171986925444072390293813 859873774260381786590045)
            ·
              refine ⟨322452665347643169971267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 859873774260381786590045 322452665347643169971267)
              ·
                refine ⟨483678998021464754956901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322452665347643169971267 483678998021464754956901)
                ·
                  refine ⟨90689812129024641554419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 483678998021464754956901 90689812129024641554419)
                  ·
                    rfl

theorem cell21_397390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 4].length) (baseStart_397390 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_397390 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_397390 prefixEnd_397390 := by exact prefixLift 397390
  have htrace : WordTrace (prefixWord ++ tailWord_397390) baseStart_397390 baseEnd_397390 := by
    simpa [prefixWord, tailWord_397390, baseEnd_397390] using wordTrace_append hprefix tailTrace_397390
  have hstable : (prefixWord ++ tailWord_397390).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397390).length < 2 ^ (prefixWord ++ tailWord_397390).sum := by decide
  have hdescent : baseEnd_397390 < baseStart_397390 := by decide
  rcases family_descends (prefixWord ++ tailWord_397390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397401 : List Nat := [1, 2, 1, 2, 2, 1, 3, 4, 5]
def baseStart_397401 : Nat := 118140960795 + 397401 * 2 ^ 59
def prefixEnd_397401 : Nat := 4983230072969 + 3 ^ 40 * 397401 * 2
def baseEnd_397401 : Nat := 90692322478891066871063

theorem tailTrace_397401 : CollatzResearch.WordTrace tailWord_397401 prefixEnd_397401 90692322478891066871063 := by
  unfold tailWord_397401
  simp only [CollatzResearch.WordTrace]
  refine ⟨14494405233291522532448057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9662936822194348354965371 14494405233291522532448057)
  ·
    refine ⟨10870803924968641899336043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14494405233291522532448057 10870803924968641899336043)
    ·
      refine ⟨16306205887452962849004065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10870803924968641899336043 16306205887452962849004065)
      ·
        refine ⟨12229654415589722136753049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16306205887452962849004065 12229654415589722136753049)
        ·
          refine ⟨9172240811692291602564787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12229654415589722136753049 9172240811692291602564787)
          ·
            refine ⟨13758361217538437403847181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9172240811692291602564787 13758361217538437403847181)
            ·
              refine ⟨5159385456576914026442693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13758361217538437403847181 5159385456576914026442693)
              ·
                refine ⟨967384773108171379958005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5159385456576914026442693 967384773108171379958005)
                ·
                  refine ⟨90692322478891066871063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 967384773108171379958005 90692322478891066871063)
                  ·
                    rfl

theorem cell21_397401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_397401 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_397401 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_397401 prefixEnd_397401 := by exact prefixLift 397401
  have htrace : WordTrace (prefixWord ++ tailWord_397401) baseStart_397401 baseEnd_397401 := by
    simpa [prefixWord, tailWord_397401, baseEnd_397401] using wordTrace_append hprefix tailTrace_397401
  have hstable : (prefixWord ++ tailWord_397401).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397401).length < 2 ^ (prefixWord ++ tailWord_397401).sum := by decide
  have hdescent : baseEnd_397401 < baseStart_397401 := by decide
  rcases family_descends (prefixWord ++ tailWord_397401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397404 : List Nat := [2, 2, 4, 1, 1, 2, 4, 5]
def baseStart_397404 : Nat := 118140960795 + 397404 * 2 ^ 59
def prefixEnd_397404 : Nat := 4983230072969 + 3 ^ 40 * 397404 * 2
def baseEnd_397404 : Nat := 30231002373254576107019

theorem tailTrace_397404 : CollatzResearch.WordTrace tailWord_397404 prefixEnd_397404 30231002373254576107019 := by
  unfold tailWord_397404
  simp only [CollatzResearch.WordTrace]
  refine ⟨7247257326140327022403633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9663009768187102696538177 7247257326140327022403633)
  ·
    refine ⟨5435442994605245266802725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7247257326140327022403633 5435442994605245266802725)
    ·
      refine ⟨1019145561488483487525511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5435442994605245266802725 1019145561488483487525511)
      ·
        refine ⟨1528718342232725231288267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1019145561488483487525511 1528718342232725231288267)
        ·
          refine ⟨2293077513349087846932401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1528718342232725231288267 2293077513349087846932401)
          ·
            refine ⟨1719808135011815885199301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2293077513349087846932401 1719808135011815885199301)
            ·
              refine ⟨322464025314715478474869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1719808135011815885199301 322464025314715478474869)
              ·
                refine ⟨30231002373254576107019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 322464025314715478474869 30231002373254576107019)
                ·
                  rfl

theorem cell21_397404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 4, 5].length) (baseStart_397404 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_397404 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_397404 prefixEnd_397404 := by exact prefixLift 397404
  have htrace : WordTrace (prefixWord ++ tailWord_397404) baseStart_397404 baseEnd_397404 := by
    simpa [prefixWord, tailWord_397404, baseEnd_397404] using wordTrace_append hprefix tailTrace_397404
  have hstable : (prefixWord ++ tailWord_397404).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397404).length < 2 ^ (prefixWord ++ tailWord_397404).sum := by decide
  have hdescent : baseEnd_397404 < baseStart_397404 := by decide
  rcases family_descends (prefixWord ++ tailWord_397404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397410 : List Nat := [3, 3, 2, 2, 3, 1, 1, 3, 3]
def baseStart_397410 : Nat := 118140960795 + 397410 * 2 ^ 59
def prefixEnd_397410 : Nat := 4983230072969 + 3 ^ 40 * 397410 * 2
def baseEnd_397410 : Nat := 90694376401509051221045

theorem tailTrace_397410 : CollatzResearch.WordTrace tailWord_397410 prefixEnd_397410 90694376401509051221045 := by
  unfold tailWord_397410
  simp only [CollatzResearch.WordTrace]
  refine ⟨3623683372564729267381421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9663155660172611379683789 3623683372564729267381421)
  ·
    refine ⟨1358881264711773475268033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3623683372564729267381421 1358881264711773475268033)
    ·
      refine ⟨1019160948533830106451025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1358881264711773475268033 1019160948533830106451025)
      ·
        refine ⟨764370711400372579838269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1019160948533830106451025 764370711400372579838269)
        ·
          refine ⟨286639016775139717439351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 764370711400372579838269 286639016775139717439351)
          ·
            refine ⟨429958525162709576159027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 286639016775139717439351 429958525162709576159027)
            ·
              refine ⟨644937787744064364238541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 429958525162709576159027 644937787744064364238541)
              ·
                refine ⟨241851670404024136589453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 644937787744064364238541 241851670404024136589453)
                ·
                  refine ⟨90694376401509051221045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241851670404024136589453 90694376401509051221045)
                  ·
                    rfl

theorem cell21_397410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_397410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_397410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_397410 prefixEnd_397410 := by exact prefixLift 397410
  have htrace : WordTrace (prefixWord ++ tailWord_397410) baseStart_397410 baseEnd_397410 := by
    simpa [prefixWord, tailWord_397410, baseEnd_397410] using wordTrace_append hprefix tailTrace_397410
  have hstable : (prefixWord ++ tailWord_397410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397410).length < 2 ^ (prefixWord ++ tailWord_397410).sum := by decide
  have hdescent : baseEnd_397410 < baseStart_397410 := by decide
  rcases family_descends (prefixWord ++ tailWord_397410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397432 : List Nat := [2, 1, 2, 1, 1, 1, 3, 6, 4]
def baseStart_397432 : Nat := 118140960795 + 397432 * 2 ^ 59
def prefixEnd_397432 : Nat := 4983230072969 + 3 ^ 40 * 397432 * 2
def baseEnd_397432 : Nat := 90699397101241901854333

theorem tailTrace_397432 : CollatzResearch.WordTrace tailWord_397432 prefixEnd_397432 90699397101241901854333 := by
  unfold tailWord_397432
  simp only [CollatzResearch.WordTrace]
  refine ⟨7247767948089607413413275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9663690597452809884551033 7247767948089607413413275)
  ·
    refine ⟨10871651922134411120119913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7247767948089607413413275 10871651922134411120119913)
    ·
      refine ⟨8153738941600808340089935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10871651922134411120119913 8153738941600808340089935)
      ·
        refine ⟨12230608412401212510134903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8153738941600808340089935 12230608412401212510134903)
        ·
          refine ⟨18345912618601818765202355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12230608412401212510134903 18345912618601818765202355)
          ·
            refine ⟨27518868927902728147803533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18345912618601818765202355 27518868927902728147803533)
            ·
              refine ⟨10319575847963523055426325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27518868927902728147803533 10319575847963523055426325)
              ·
                refine ⟨483730117873290143223109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10319575847963523055426325 483730117873290143223109)
                ·
                  refine ⟨90699397101241901854333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 483730117873290143223109 90699397101241901854333)
                  ·
                    rfl

theorem cell21_397432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 6, 4].length) (baseStart_397432 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_397432 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_397432 prefixEnd_397432 := by exact prefixLift 397432
  have htrace : WordTrace (prefixWord ++ tailWord_397432) baseStart_397432 baseEnd_397432 := by
    simpa [prefixWord, tailWord_397432, baseEnd_397432] using wordTrace_append hprefix tailTrace_397432
  have hstable : (prefixWord ++ tailWord_397432).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397432).length < 2 ^ (prefixWord ++ tailWord_397432).sum := by decide
  have hdescent : baseEnd_397432 < baseStart_397432 := by decide
  rcases family_descends (prefixWord ++ tailWord_397432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397553 : List Nat := [1, 2, 2, 2, 2, 1, 3, 3, 5]
def baseStart_397553 : Nat := 118140960795 + 397553 * 2 ^ 59
def prefixEnd_397553 : Nat := 4983230072969 + 3 ^ 40 * 397553 * 2
def baseEnd_397553 : Nat := 90727010949772580337419

theorem tailTrace_397553 : CollatzResearch.WordTrace tailWord_397553 prefixEnd_397553 90727010949772580337419 := by
  unfold tailWord_397553
  simp only [CollatzResearch.WordTrace]
  refine ⟨14499949128740852491981313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9666632752493901661320875 14499949128740852491981313)
  ·
    refine ⟨10874961846555639368985985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14499949128740852491981313 10874961846555639368985985)
    ·
      refine ⟨8156221384916729526739489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10874961846555639368985985 8156221384916729526739489)
      ·
        refine ⟨6117166038687547145054617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8156221384916729526739489 6117166038687547145054617)
        ·
          refine ⟨4587874529015660358790963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6117166038687547145054617 4587874529015660358790963)
          ·
            refine ⟨6881811793523490538186445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4587874529015660358790963 6881811793523490538186445)
            ·
              refine ⟨2580679422571308951819917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6881811793523490538186445 2580679422571308951819917)
              ·
                refine ⟨967754783464240856932469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2580679422571308951819917 967754783464240856932469)
                ·
                  refine ⟨90727010949772580337419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 967754783464240856932469 90727010949772580337419)
                  ·
                    rfl

theorem cell21_397553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_397553 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_397553 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_397553 prefixEnd_397553 := by exact prefixLift 397553
  have htrace : WordTrace (prefixWord ++ tailWord_397553) baseStart_397553 baseEnd_397553 := by
    simpa [prefixWord, tailWord_397553, baseEnd_397553] using wordTrace_append hprefix tailTrace_397553
  have hstable : (prefixWord ++ tailWord_397553).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397553).length < 2 ^ (prefixWord ++ tailWord_397553).sum := by decide
  have hdescent : baseEnd_397553 < baseStart_397553 := by decide
  rcases family_descends (prefixWord ++ tailWord_397553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397604 : List Nat := [2, 3, 1, 3, 1, 3, 3, 2, 3]
def baseStart_397604 : Nat := 118140960795 + 397604 * 2 ^ 59
def prefixEnd_397604 : Nat := 4983230072969 + 3 ^ 40 * 397604 * 2
def baseEnd_397604 : Nat := 90738649844607824987315

theorem tailTrace_397604 : CollatzResearch.WordTrace tailWord_397604 prefixEnd_397604 90738649844607824987315 := by
  unfold tailWord_397604
  simp only [CollatzResearch.WordTrace]
  refine ⟨7250904625778044101043933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9667872834370725468058577 7250904625778044101043933)
  ·
    refine ⟨2719089234666766537891475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7250904625778044101043933 2719089234666766537891475)
    ·
      refine ⟨4078633852000149806837213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2719089234666766537891475 4078633852000149806837213)
      ·
        refine ⟨1529487694500056177563955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4078633852000149806837213 1529487694500056177563955)
        ·
          refine ⟨2294231541750084266345933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1529487694500056177563955 2294231541750084266345933)
          ·
            refine ⟨860336828156281599879725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2294231541750084266345933 860336828156281599879725)
            ·
              refine ⟨322626310558605599954897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 860336828156281599879725 322626310558605599954897)
              ·
                refine ⟨241969732918954199966173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322626310558605599954897 241969732918954199966173)
                ·
                  refine ⟨90738649844607824987315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 241969732918954199966173 90738649844607824987315)
                  ·
                    rfl

theorem cell21_397604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 3, 2, 3].length) (baseStart_397604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_397604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_397604 prefixEnd_397604 := by exact prefixLift 397604
  have htrace : WordTrace (prefixWord ++ tailWord_397604) baseStart_397604 baseEnd_397604 := by
    simpa [prefixWord, tailWord_397604, baseEnd_397604] using wordTrace_append hprefix tailTrace_397604
  have hstable : (prefixWord ++ tailWord_397604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397604).length < 2 ^ (prefixWord ++ tailWord_397604).sum := by decide
  have hdescent : baseEnd_397604 < baseStart_397604 := by decide
  rcases family_descends (prefixWord ++ tailWord_397604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397643 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 6]
def baseStart_397643 : Nat := 118140960795 + 397643 * 2 ^ 59
def prefixEnd_397643 : Nat := 4983230072969 + 3 ^ 40 * 397643 * 2
def baseEnd_397643 : Nat := 90747550175952423837235

theorem tailTrace_397643 : CollatzResearch.WordTrace tailWord_397643 prefixEnd_397643 90747550175952423837235 := by
  unfold tailWord_397643
  simp only [CollatzResearch.WordTrace]
  refine ⟨14503231698414797862757583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9668821132276531908505055 14503231698414797862757583)
  ·
    refine ⟨21754847547622196794136375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14503231698414797862757583 21754847547622196794136375)
    ·
      refine ⟨32632271321433295191204563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21754847547622196794136375 32632271321433295191204563)
      ·
        refine ⟨48948406982149942786806845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32632271321433295191204563 48948406982149942786806845)
        ·
          refine ⟨18355652618306228545052567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48948406982149942786806845 18355652618306228545052567)
          ·
            refine ⟨27533478927459342817578851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18355652618306228545052567 27533478927459342817578851)
            ·
              refine ⟨41300218391189014226368277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27533478927459342817578851 41300218391189014226368277)
              ·
                refine ⟨1935947737086985041861013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 41300218391189014226368277 1935947737086985041861013)
                ·
                  refine ⟨90747550175952423837235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1935947737086985041861013 90747550175952423837235)
                  ·
                    rfl

theorem cell21_397643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 6].length) (baseStart_397643 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_397643 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_397643 prefixEnd_397643 := by exact prefixLift 397643
  have htrace : WordTrace (prefixWord ++ tailWord_397643) baseStart_397643 baseEnd_397643 := by
    simpa [prefixWord, tailWord_397643, baseEnd_397643] using wordTrace_append hprefix tailTrace_397643
  have hstable : (prefixWord ++ tailWord_397643).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397643).length < 2 ^ (prefixWord ++ tailWord_397643).sum := by decide
  have hdescent : baseEnd_397643 < baseStart_397643 := by decide
  rcases family_descends (prefixWord ++ tailWord_397643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397663 : List Nat := [1, 1, 2, 3, 1, 2, 6, 2, 3]
def baseStart_397663 : Nat := 118140960795 + 397663 * 2 ^ 59
def prefixEnd_397663 : Nat := 4983230072969 + 3 ^ 40 * 397663 * 2
def baseEnd_397663 : Nat := 90752114448436833503861

theorem tailTrace_397663 : CollatzResearch.WordTrace tailWord_397663 prefixEnd_397663 90752114448436833503861 := by
  unfold tailWord_397663
  simp only [CollatzResearch.WordTrace]
  refine ⟨14503961158342341278485643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9669307438894894185657095 14503961158342341278485643)
  ·
    refine ⟨21755941737513511917728465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14503961158342341278485643 21755941737513511917728465)
    ·
      refine ⟨16316956303135133938296349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21755941737513511917728465 16316956303135133938296349)
      ·
        refine ⟨6118858613675675226861131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16316956303135133938296349 6118858613675675226861131)
        ·
          refine ⟨9178287920513512840291697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6118858613675675226861131 9178287920513512840291697)
          ·
            refine ⟨6883715940385134630218773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9178287920513512840291697 6883715940385134630218773)
            ·
              refine ⟨322674184705553185791505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6883715940385134630218773 322674184705553185791505)
              ·
                refine ⟨242005638529164889343629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322674184705553185791505 242005638529164889343629)
                ·
                  refine ⟨90752114448436833503861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242005638529164889343629 90752114448436833503861)
                  ·
                    rfl

theorem cell21_397663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 6, 2, 3].length) (baseStart_397663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_397663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_397663 prefixEnd_397663 := by exact prefixLift 397663
  have htrace : WordTrace (prefixWord ++ tailWord_397663) baseStart_397663 baseEnd_397663 := by
    simpa [prefixWord, tailWord_397663, baseEnd_397663] using wordTrace_append hprefix tailTrace_397663
  have hstable : (prefixWord ++ tailWord_397663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397663).length < 2 ^ (prefixWord ++ tailWord_397663).sum := by decide
  have hdescent : baseEnd_397663 < baseStart_397663 := by decide
  rcases family_descends (prefixWord ++ tailWord_397663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397691 : List Nat := [1, 1, 1, 1, 1, 8, 3, 5]
def baseStart_397691 : Nat := 118140960795 + 397691 * 2 ^ 59
def prefixEnd_397691 : Nat := 4983230072969 + 3 ^ 40 * 397691 * 2
def baseEnd_397691 : Nat := 30252834809971669012379

theorem tailTrace_397691 : CollatzResearch.WordTrace tailWord_397691 prefixEnd_397691 30252834809971669012379 := by
  unfold tailWord_397691
  simp only [CollatzResearch.WordTrace]
  refine ⟨14504982402240902060504927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9669988268160601373669951 14504982402240902060504927)
  ·
    refine ⟨21757473603361353090757391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14504982402240902060504927 21757473603361353090757391)
    ·
      refine ⟨32636210405042029636136087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21757473603361353090757391 32636210405042029636136087)
      ·
        refine ⟨48954315607563044454204131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32636210405042029636136087 48954315607563044454204131)
        ·
          refine ⟨73431473411344566681306197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48954315607563044454204131 73431473411344566681306197)
          ·
            refine ⟨860525079039194140796557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 73431473411344566681306197 860525079039194140796557)
            ·
              refine ⟨322696904639697802798709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 860525079039194140796557 322696904639697802798709)
              ·
                refine ⟨30252834809971669012379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 322696904639697802798709 30252834809971669012379)
                ·
                  rfl

theorem cell21_397691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 3, 5].length) (baseStart_397691 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_397691 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_397691 prefixEnd_397691 := by exact prefixLift 397691
  have htrace : WordTrace (prefixWord ++ tailWord_397691) baseStart_397691 baseEnd_397691 := by
    simpa [prefixWord, tailWord_397691, baseEnd_397691] using wordTrace_append hprefix tailTrace_397691
  have hstable : (prefixWord ++ tailWord_397691).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397691).length < 2 ^ (prefixWord ++ tailWord_397691).sum := by decide
  have hdescent : baseEnd_397691 < baseStart_397691 := by decide
  rcases family_descends (prefixWord ++ tailWord_397691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397722 : List Nat := [3, 1, 1, 4, 1, 3, 2, 1, 5]
def baseStart_397722 : Nat := 118140960795 + 397722 * 2 ^ 59
def prefixEnd_397722 : Nat := 4983230072969 + 3 ^ 40 * 397722 * 2
def baseEnd_397722 : Nat := 90765579052265842020407

theorem tailTrace_397722 : CollatzResearch.WordTrace tailWord_397722 prefixEnd_397722 90765579052265842020407 := by
  unfold tailWord_397722
  simp only [CollatzResearch.WordTrace]
  refine ⟨3626528266282148588720855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9670742043419062903255613 3626528266282148588720855)
  ·
    refine ⟨5439792399423222883081283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3626528266282148588720855 5439792399423222883081283)
    ·
      refine ⟨8159688599134834324621925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5439792399423222883081283 8159688599134834324621925)
      ·
        refine ⟨1529941612337781435866611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8159688599134834324621925 1529941612337781435866611)
        ·
          refine ⟨2294912418506672153799917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1529941612337781435866611 2294912418506672153799917)
          ·
            refine ⟨860592156940002057674969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2294912418506672153799917 860592156940002057674969)
            ·
              refine ⟨645444117705001543256227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 860592156940002057674969 645444117705001543256227)
              ·
                refine ⟨968166176557502314884341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 645444117705001543256227 968166176557502314884341)
                ·
                  refine ⟨90765579052265842020407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 968166176557502314884341 90765579052265842020407)
                  ·
                    rfl

theorem cell21_397722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_397722 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_397722 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_397722 prefixEnd_397722 := by exact prefixLift 397722
  have htrace : WordTrace (prefixWord ++ tailWord_397722) baseStart_397722 baseEnd_397722 := by
    simpa [prefixWord, tailWord_397722, baseEnd_397722] using wordTrace_append hprefix tailTrace_397722
  have hstable : (prefixWord ++ tailWord_397722).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397722).length < 2 ^ (prefixWord ++ tailWord_397722).sum := by decide
  have hdescent : baseEnd_397722 < baseStart_397722 := by decide
  rcases family_descends (prefixWord ++ tailWord_397722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397756 : List Nat := [2, 2, 2, 4, 1, 3, 1, 3, 3]
def baseStart_397756 : Nat := 118140960795 + 397756 * 2 ^ 59
def prefixEnd_397756 : Nat := 4983230072969 + 3 ^ 40 * 397756 * 2
def baseEnd_397756 : Nat := 90773338315489338453671

theorem tailTrace_397756 : CollatzResearch.WordTrace tailWord_397756 prefixEnd_397756 90773338315489338453671 := by
  unfold tailWord_397756
  simp only [CollatzResearch.WordTrace]
  refine ⟨7253676573502709080810561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9671568764670278774414081 7253676573502709080810561)
  ·
    refine ⟨5440257430127031810607921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7253676573502709080810561 5440257430127031810607921)
    ·
      refine ⟨4080193072595273857955941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5440257430127031810607921 4080193072595273857955941)
      ·
        refine ⟨765036201111613848366739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4080193072595273857955941 765036201111613848366739)
        ·
          refine ⟨1147554301667420772550109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765036201111613848366739 1147554301667420772550109)
          ·
            refine ⟨430332863125282789706291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1147554301667420772550109 430332863125282789706291)
            ·
              refine ⟨645499294687924184559437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430332863125282789706291 645499294687924184559437)
              ·
                refine ⟨242062235507971569209789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 645499294687924184559437 242062235507971569209789)
                ·
                  refine ⟨90773338315489338453671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242062235507971569209789 90773338315489338453671)
                  ·
                    rfl

theorem cell21_397756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 3, 1, 3, 3].length) (baseStart_397756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_397756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_397756 prefixEnd_397756 := by exact prefixLift 397756
  have htrace : WordTrace (prefixWord ++ tailWord_397756) baseStart_397756 baseEnd_397756 := by
    simpa [prefixWord, tailWord_397756, baseEnd_397756] using wordTrace_append hprefix tailTrace_397756
  have hstable : (prefixWord ++ tailWord_397756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397756).length < 2 ^ (prefixWord ++ tailWord_397756).sum := by decide
  have hdescent : baseEnd_397756 < baseStart_397756 := by decide
  rcases family_descends (prefixWord ++ tailWord_397756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397857 : List Nat := [1, 2, 3, 2, 2, 1, 3, 2, 5]
def baseStart_397857 : Nat := 118140960795 + 397857 * 2 ^ 59
def prefixEnd_397857 : Nat := 4983230072969 + 3 ^ 40 * 397857 * 2
def baseEnd_397857 : Nat := 90796387891535607270131

theorem tailTrace_397857 : CollatzResearch.WordTrace tailWord_397857 prefixEnd_397857 90796387891535607270131 := by
  unfold tailWord_397857
  simp only [CollatzResearch.WordTrace]
  refine ⟨14511036919639512411047825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9674024613093008274031883 14511036919639512411047825)
  ·
    refine ⟨10883277689729634308285869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14511036919639512411047825 10883277689729634308285869)
    ·
      refine ⟨4081229133648612865607201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10883277689729634308285869 4081229133648612865607201)
      ·
        refine ⟨3060921850236459649205401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4081229133648612865607201 3060921850236459649205401)
        ·
          refine ⟨2295691387677344736904051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3060921850236459649205401 2295691387677344736904051)
          ·
            refine ⟨3443537081516017105356077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2295691387677344736904051 3443537081516017105356077)
            ·
              refine ⟨1291326405568506414508529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3443537081516017105356077 1291326405568506414508529)
              ·
                refine ⟨968494804176379810881397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1291326405568506414508529 968494804176379810881397)
                ·
                  refine ⟨90796387891535607270131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 968494804176379810881397 90796387891535607270131)
                  ·
                    rfl

theorem cell21_397857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_397857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_397857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_397857 prefixEnd_397857 := by exact prefixLift 397857
  have htrace : WordTrace (prefixWord ++ tailWord_397857) baseStart_397857 baseEnd_397857 := by
    simpa [prefixWord, tailWord_397857, baseEnd_397857] using wordTrace_append hprefix tailTrace_397857
  have hstable : (prefixWord ++ tailWord_397857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397857).length < 2 ^ (prefixWord ++ tailWord_397857).sum := by decide
  have hdescent : baseEnd_397857 < baseStart_397857 := by decide
  rcases family_descends (prefixWord ++ tailWord_397857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397874 : List Nat := [3, 2, 1, 1, 2, 1, 3, 5, 3]
def baseStart_397874 : Nat := 118140960795 + 397874 * 2 ^ 59
def prefixEnd_397874 : Nat := 4983230072969 + 3 ^ 40 * 397874 * 2
def baseEnd_397874 : Nat := 90800267523147355486763

theorem tailTrace_397874 : CollatzResearch.WordTrace tailWord_397874 prefixEnd_397874 90800267523147355486763 := by
  unfold tailWord_397874
  simp only [CollatzResearch.WordTrace]
  refine ⟨3627914240144481078604169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9674437973718616209611117 3627914240144481078604169)
  ·
    refine ⟨2720935680108360808953127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3627914240144481078604169 2720935680108360808953127)
    ·
      refine ⟨4081403520162541213429691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2720935680108360808953127 4081403520162541213429691)
      ·
        refine ⟨6122105280243811820144537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4081403520162541213429691 6122105280243811820144537)
        ·
          refine ⟨4591578960182858865108403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6122105280243811820144537 4591578960182858865108403)
          ·
            refine ⟨6887368440274288297662605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4591578960182858865108403 6887368440274288297662605)
            ·
              refine ⟨2582763165102858111623477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6887368440274288297662605 2582763165102858111623477)
              ·
                refine ⟨242134046728392947964701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2582763165102858111623477 242134046728392947964701)
                ·
                  refine ⟨90800267523147355486763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242134046728392947964701 90800267523147355486763)
                  ·
                    rfl

theorem cell21_397874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 5, 3].length) (baseStart_397874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_397874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_397874 prefixEnd_397874 := by exact prefixLift 397874
  have htrace : WordTrace (prefixWord ++ tailWord_397874) baseStart_397874 baseEnd_397874 := by
    simpa [prefixWord, tailWord_397874, baseEnd_397874] using wordTrace_append hprefix tailTrace_397874
  have hstable : (prefixWord ++ tailWord_397874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397874).length < 2 ^ (prefixWord ++ tailWord_397874).sum := by decide
  have hdescent : baseEnd_397874 < baseStart_397874 := by decide
  rcases family_descends (prefixWord ++ tailWord_397874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397888 : List Nat := [2, 1, 1, 2, 2, 2, 5, 2, 4]
def baseStart_397888 : Nat := 118140960795 + 397888 * 2 ^ 59
def prefixEnd_397888 : Nat := 4983230072969 + 3 ^ 40 * 397888 * 2
def baseEnd_397888 : Nat := 90803462513886442253401

theorem tailTrace_397888 : CollatzResearch.WordTrace tailWord_397888 prefixEnd_397888 90803462513886442253401 := by
  unfold tailWord_397888
  simp only [CollatzResearch.WordTrace]
  refine ⟨7256083791263602352713159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9674778388351469803617545 7256083791263602352713159)
  ·
    refine ⟨10884125686895403529069739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7256083791263602352713159 10884125686895403529069739)
    ·
      refine ⟨16326188530343105293604609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10884125686895403529069739 16326188530343105293604609)
      ·
        refine ⟨12244641397757328970203457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16326188530343105293604609 12244641397757328970203457)
        ·
          refine ⟨9183481048317996727652593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12244641397757328970203457 9183481048317996727652593)
          ·
            refine ⟨6887610786238497545739445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9183481048317996727652593 6887610786238497545739445)
            ·
              refine ⟨645713511209859144913073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6887610786238497545739445 645713511209859144913073)
              ·
                refine ⟨484285133407394358684805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 645713511209859144913073 484285133407394358684805)
                ·
                  refine ⟨90803462513886442253401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 484285133407394358684805 90803462513886442253401)
                  ·
                    rfl

theorem cell21_397888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 2, 4].length) (baseStart_397888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_397888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_397888 prefixEnd_397888 := by exact prefixLift 397888
  have htrace : WordTrace (prefixWord ++ tailWord_397888) baseStart_397888 baseEnd_397888 := by
    simpa [prefixWord, tailWord_397888, baseEnd_397888] using wordTrace_append hprefix tailTrace_397888
  have hstable : (prefixWord ++ tailWord_397888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397888).length < 2 ^ (prefixWord ++ tailWord_397888).sum := by decide
  have hdescent : baseEnd_397888 < baseStart_397888 := by decide
  rcases family_descends (prefixWord ++ tailWord_397888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397905 : List Nat := [1, 2, 2, 1, 3, 4, 3, 1, 4]
def baseStart_397905 : Nat := 118140960795 + 397905 * 2 ^ 59
def prefixEnd_397905 : Nat := 4983230072969 + 3 ^ 40 * 397905 * 2
def baseEnd_397905 : Nat := 90807342145498190470033

theorem tailTrace_397905 : CollatzResearch.WordTrace tailWord_397905 prefixEnd_397905 90807342145498190470033 := by
  unfold tailWord_397905
  simp only [CollatzResearch.WordTrace]
  refine ⟨14512787623465616608795169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9675191748977077739196779 14512787623465616608795169)
  ·
    refine ⟨10884590717599212456596377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14512787623465616608795169 10884590717599212456596377)
    ·
      refine ⟨8163443038199409342447283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10884590717599212456596377 8163443038199409342447283)
      ·
        refine ⟨12245164557299114013670925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8163443038199409342447283 12245164557299114013670925)
        ·
          refine ⟨4591936708987167755126597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12245164557299114013670925 4591936708987167755126597)
          ·
            refine ⟨860988132935093954086237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4591936708987167755126597 860988132935093954086237)
            ·
              refine ⟨322870549850660232782339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 860988132935093954086237 322870549850660232782339)
              ·
                refine ⟨484305824775990349173509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 322870549850660232782339 484305824775990349173509)
                ·
                  refine ⟨90807342145498190470033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 484305824775990349173509 90807342145498190470033)
                  ·
                    rfl

theorem cell21_397905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 3, 1, 4].length) (baseStart_397905 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_397905 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_397905 prefixEnd_397905 := by exact prefixLift 397905
  have htrace : WordTrace (prefixWord ++ tailWord_397905) baseStart_397905 baseEnd_397905 := by
    simpa [prefixWord, tailWord_397905, baseEnd_397905] using wordTrace_append hprefix tailTrace_397905
  have hstable : (prefixWord ++ tailWord_397905).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397905).length < 2 ^ (prefixWord ++ tailWord_397905).sum := by decide
  have hdescent : baseEnd_397905 < baseStart_397905 := by decide
  rcases family_descends (prefixWord ++ tailWord_397905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_397998 : List Nat := [4, 1, 4, 1, 1, 2, 2, 2, 4]
def baseStart_397998 : Nat := 118140960795 + 397998 * 2 ^ 59
def prefixEnd_397998 : Nat := 4983230072969 + 3 ^ 40 * 397998 * 2
def baseEnd_397998 : Nat := 90828566012550695419843

theorem tailTrace_397998 : CollatzResearch.WordTrace tailWord_397998 prefixEnd_397998 90828566012550695419843 := by
  unfold tailWord_397998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1814522451516086686491331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9677453074752462327953765 1814522451516086686491331)
  ·
    refine ⟨2721783677274130029736997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1814522451516086686491331 2721783677274130029736997)
    ·
      refine ⟨510334439488899380575687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2721783677274130029736997 510334439488899380575687)
      ·
        refine ⟨765501659233349070863531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510334439488899380575687 765501659233349070863531)
        ·
          refine ⟨1148252488850023606295297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 765501659233349070863531 1148252488850023606295297)
          ·
            refine ⟨861189366637517704721473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1148252488850023606295297 861189366637517704721473)
            ·
              refine ⟨645892024978138278541105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 861189366637517704721473 645892024978138278541105)
              ·
                refine ⟨484419018733603708905829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 645892024978138278541105 484419018733603708905829)
                ·
                  refine ⟨90828566012550695419843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 484419018733603708905829 90828566012550695419843)
                  ·
                    rfl

theorem cell21_397998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_397998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_397998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_397998 prefixEnd_397998 := by exact prefixLift 397998
  have htrace : WordTrace (prefixWord ++ tailWord_397998) baseStart_397998 baseEnd_397998 := by
    simpa [prefixWord, tailWord_397998, baseEnd_397998] using wordTrace_append hprefix tailTrace_397998
  have hstable : (prefixWord ++ tailWord_397998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_397998).length < 2 ^ (prefixWord ++ tailWord_397998).sum := by decide
  have hdescent : baseEnd_397998 < baseStart_397998 := by decide
  rcases family_descends (prefixWord ++ tailWord_397998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398001 : List Nat := [1, 2, 2, 6, 1, 2, 2, 2, 3]
def baseStart_398001 : Nat := 118140960795 + 398001 * 2 ^ 59
def prefixEnd_398001 : Nat := 4983230072969 + 3 ^ 40 * 398001 * 2
def baseEnd_398001 : Nat := 90829250653423356869837

theorem tailTrace_398001 : CollatzResearch.WordTrace tailWord_398001 prefixEnd_398001 90829250653423356869837 := by
  unfold tailWord_398001
  simp only [CollatzResearch.WordTrace]
  refine ⟨14516289031117825004289857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9677526020745216669526571 14516289031117825004289857)
  ·
    refine ⟨10887216773338368753217393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14516289031117825004289857 10887216773338368753217393)
    ·
      refine ⟨8165412580003776564913045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10887216773338368753217393 8165412580003776564913045)
      ·
        refine ⟨382753714687677026480299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8165412580003776564913045 382753714687677026480299)
        ·
          refine ⟨574130572031515539720449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 382753714687677026480299 574130572031515539720449)
          ·
            refine ⟨430597929023636654790337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 574130572031515539720449 430597929023636654790337)
            ·
              refine ⟨322948446767727491092753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430597929023636654790337 322948446767727491092753)
              ·
                refine ⟨242211335075795618319565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 322948446767727491092753 242211335075795618319565)
                ·
                  refine ⟨90829250653423356869837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242211335075795618319565 90829250653423356869837)
                  ·
                    rfl

theorem cell21_398001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 2, 2, 3].length) (baseStart_398001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398001 prefixEnd_398001 := by exact prefixLift 398001
  have htrace : WordTrace (prefixWord ++ tailWord_398001) baseStart_398001 baseEnd_398001 := by
    simpa [prefixWord, tailWord_398001, baseEnd_398001] using wordTrace_append hprefix tailTrace_398001
  have hstable : (prefixWord ++ tailWord_398001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398001).length < 2 ^ (prefixWord ++ tailWord_398001).sum := by decide
  have hdescent : baseEnd_398001 < baseStart_398001 := by decide
  rcases family_descends (prefixWord ++ tailWord_398001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398029 : List Nat := [1, 6, 2, 1, 2, 1, 3, 5]
def baseStart_398029 : Nat := 118140960795 + 398029 * 2 ^ 59
def prefixEnd_398029 : Nat := 4983230072969 + 3 ^ 40 * 398029 * 2
def baseEnd_398029 : Nat := 30278546878300510134371

theorem tailTrace_398029 : CollatzResearch.WordTrace tailWord_398029 prefixEnd_398029 30278546878300510134371 := by
  unfold tailWord_398029
  simp only [CollatzResearch.WordTrace]
  refine ⟨14517310275016385786309141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9678206850010923857539427 14517310275016385786309141)
  ·
    refine ⟨680498919141393083733241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14517310275016385786309141 680498919141393083733241)
    ·
      refine ⟨510374189356044812799931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 680498919141393083733241 510374189356044812799931)
      ·
        refine ⟨765561284034067219199897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 510374189356044812799931 765561284034067219199897)
        ·
          refine ⟨574170963025550414399923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 765561284034067219199897 574170963025550414399923)
          ·
            refine ⟨861256444538325621599885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 574170963025550414399923 861256444538325621599885)
            ·
              refine ⟨322971166701872108099957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 861256444538325621599885 322971166701872108099957)
              ·
                refine ⟨30278546878300510134371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 322971166701872108099957 30278546878300510134371)
                ·
                  rfl

theorem cell21_398029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 3, 5].length) (baseStart_398029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398029 prefixEnd_398029 := by exact prefixLift 398029
  have htrace : WordTrace (prefixWord ++ tailWord_398029) baseStart_398029 baseEnd_398029 := by
    simpa [prefixWord, tailWord_398029, baseEnd_398029] using wordTrace_append hprefix tailTrace_398029
  have hstable : (prefixWord ++ tailWord_398029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398029).length < 2 ^ (prefixWord ++ tailWord_398029).sum := by decide
  have hdescent : baseEnd_398029 < baseStart_398029 := by decide
  rcases family_descends (prefixWord ++ tailWord_398029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398130 : List Nat := [3, 2, 1, 1, 3, 1, 4, 6]
def baseStart_398130 : Nat := 118140960795 + 398130 * 2 ^ 59
def prefixEnd_398130 : Nat := 4983230072969 + 3 ^ 40 * 398130 * 2
def baseEnd_398130 : Nat := 30286230070315933073191

theorem tailTrace_398130 : CollatzResearch.WordTrace tailWord_398130 prefixEnd_398130 30286230070315933073191 := by
  unfold tailWord_398130
  simp only [CollatzResearch.WordTrace]
  refine ⟨3630248511912620008933961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9680662698433653357157229 3630248511912620008933961)
  ·
    refine ⟨2722686383934465006700471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3630248511912620008933961 2722686383934465006700471)
    ·
      refine ⟨4084029575901697510050707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2722686383934465006700471 4084029575901697510050707)
      ·
        refine ⟨6126044363852546265076061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4084029575901697510050707 6126044363852546265076061)
        ·
          refine ⟨2297266636444704849403523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6126044363852546265076061 2297266636444704849403523)
          ·
            refine ⟨3445899954667057274105285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2297266636444704849403523 3445899954667057274105285)
            ·
              refine ⟨646106241500073238894741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3445899954667057274105285 646106241500073238894741)
              ·
                refine ⟨30286230070315933073191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 646106241500073238894741 30286230070315933073191)
                ·
                  rfl

theorem cell21_398130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_398130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398130 prefixEnd_398130 := by exact prefixLift 398130
  have htrace : WordTrace (prefixWord ++ tailWord_398130) baseStart_398130 baseEnd_398130 := by
    simpa [prefixWord, tailWord_398130, baseEnd_398130] using wordTrace_append hprefix tailTrace_398130
  have hstable : (prefixWord ++ tailWord_398130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398130).length < 2 ^ (prefixWord ++ tailWord_398130).sum := by decide
  have hdescent : baseEnd_398130 < baseStart_398130 := by decide
  rcases family_descends (prefixWord ++ tailWord_398130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398133 : List Nat := [1, 3, 3, 1, 3, 1, 4, 1, 4]
def baseStart_398133 : Nat := 118140960795 + 398133 * 2 ^ 59
def prefixEnd_398133 : Nat := 4983230072969 + 3 ^ 40 * 398133 * 2
def baseEnd_398133 : Nat := 90859374851820460669567

theorem tailTrace_398133 : CollatzResearch.WordTrace tailWord_398133 prefixEnd_398133 90859374851820460669567 := by
  unfold tailWord_398133
  simp only [CollatzResearch.WordTrace]
  refine ⟨14521103466639611548095053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9680735644426407698730035 14521103466639611548095053)
  ·
    refine ⟨5445413799989854330535645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14521103466639611548095053 5445413799989854330535645)
    ·
      refine ⟨2042030174996195373950867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5445413799989854330535645 2042030174996195373950867)
      ·
        refine ⟨3063045262494293060926301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2042030174996195373950867 3063045262494293060926301)
        ·
          refine ⟨1148641973435359897847363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3063045262494293060926301 1148641973435359897847363)
          ·
            refine ⟨1722962960153039846771045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1148641973435359897847363 1722962960153039846771045)
            ·
              refine ⟨323055555028694971269571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1722962960153039846771045 323055555028694971269571)
              ·
                refine ⟨484583332543042456904357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 323055555028694971269571 484583332543042456904357)
                ·
                  refine ⟨90859374851820460669567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 484583332543042456904357 90859374851820460669567)
                  ·
                    rfl

theorem cell21_398133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 4].length) (baseStart_398133 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398133 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398133 prefixEnd_398133 := by exact prefixLift 398133
  have htrace : WordTrace (prefixWord ++ tailWord_398133) baseStart_398133 baseEnd_398133 := by
    simpa [prefixWord, tailWord_398133, baseEnd_398133] using wordTrace_append hprefix tailTrace_398133
  have hstable : (prefixWord ++ tailWord_398133).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398133).length < 2 ^ (prefixWord ++ tailWord_398133).sum := by decide
  have hdescent : baseEnd_398133 < baseStart_398133 := by decide
  rcases family_descends (prefixWord ++ tailWord_398133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398144 : List Nat := [2, 1, 1, 2, 2, 1, 1, 6, 5]
def baseStart_398144 : Nat := 118140960795 + 398144 * 2 ^ 59
def prefixEnd_398144 : Nat := 4983230072969 + 3 ^ 40 * 398144 * 2
def baseEnd_398144 : Nat := 90861885201686885986211

theorem tailTrace_398144 : CollatzResearch.WordTrace tailWord_398144 prefixEnd_398144 90861885201686885986211 := by
  unfold tailWord_398144
  simp only [CollatzResearch.WordTrace]
  refine ⟨7260752334799880213372743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9681003113066506951163657 7260752334799880213372743)
  ·
    refine ⟨10891128502199820320059115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7260752334799880213372743 10891128502199820320059115)
    ·
      refine ⟨16336692753299730480088673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10891128502199820320059115 16336692753299730480088673)
      ·
        refine ⟨12252519564974797860066505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16336692753299730480088673 12252519564974797860066505)
        ·
          refine ⟨9189389673731098395049879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12252519564974797860066505 9189389673731098395049879)
          ·
            refine ⟨13784084510596647592574819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9189389673731098395049879 13784084510596647592574819)
            ·
              refine ⟨20676126765894971388862229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13784084510596647592574819 20676126765894971388862229)
              ·
                refine ⟨969193442151326783852917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 20676126765894971388862229 969193442151326783852917)
                ·
                  refine ⟨90861885201686885986211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 969193442151326783852917 90861885201686885986211)
                  ·
                    rfl

theorem cell21_398144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_398144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398144 prefixEnd_398144 := by exact prefixLift 398144
  have htrace : WordTrace (prefixWord ++ tailWord_398144) baseStart_398144 baseEnd_398144 := by
    simpa [prefixWord, tailWord_398144, baseEnd_398144] using wordTrace_append hprefix tailTrace_398144
  have hstable : (prefixWord ++ tailWord_398144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398144).length < 2 ^ (prefixWord ++ tailWord_398144).sum := by decide
  have hdescent : baseEnd_398144 < baseStart_398144 := by decide
  rcases family_descends (prefixWord ++ tailWord_398144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398226 : List Nat := [3, 2, 3, 2, 2, 2, 1, 2, 4]
def baseStart_398226 : Nat := 118140960795 + 398226 * 2 ^ 59
def prefixEnd_398226 : Nat := 4983230072969 + 3 ^ 40 * 398226 * 2
def baseEnd_398226 : Nat := 90880598718872965619377

theorem tailTrace_398226 : CollatzResearch.WordTrace tailWord_398226 prefixEnd_398226 90880598718872965619377 := by
  unfold tailWord_398226
  simp only [CollatzResearch.WordTrace]
  refine ⟨3631123863825672107807633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9682996970201792287487021 3631123863825672107807633)
  ·
    refine ⟨2723342897869254080855725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3631123863825672107807633 2723342897869254080855725)
    ·
      refine ⟨1021253586700970280320897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2723342897869254080855725 1021253586700970280320897)
      ·
        refine ⟨765940190025727710240673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1021253586700970280320897 765940190025727710240673)
        ·
          refine ⟨574455142519295782680505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 765940190025727710240673 574455142519295782680505)
          ·
            refine ⟨430841356889471837010379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 574455142519295782680505 430841356889471837010379)
            ·
              refine ⟨646262035334207755515569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 430841356889471837010379 646262035334207755515569)
              ·
                refine ⟨484696526500655816636677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 646262035334207755515569 484696526500655816636677)
                ·
                  refine ⟨90880598718872965619377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 484696526500655816636677 90880598718872965619377)
                  ·
                    rfl

theorem cell21_398226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_398226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398226 prefixEnd_398226 := by exact prefixLift 398226
  have htrace : WordTrace (prefixWord ++ tailWord_398226) baseStart_398226 baseEnd_398226 := by
    simpa [prefixWord, tailWord_398226, baseEnd_398226] using wordTrace_append hprefix tailTrace_398226
  have hstable : (prefixWord ++ tailWord_398226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398226).length < 2 ^ (prefixWord ++ tailWord_398226).sum := by decide
  have hdescent : baseEnd_398226 < baseStart_398226 := by decide
  rcases family_descends (prefixWord ++ tailWord_398226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398237 : List Nat := [1, 4, 2, 1, 2, 1, 4, 1, 5]
def baseStart_398237 : Nat := 118140960795 + 398237 * 2 ^ 59
def prefixEnd_398237 : Nat := 4983230072969 + 3 ^ 40 * 398237 * 2
def baseEnd_398237 : Nat := 90883109068739390936021

theorem tailTrace_398237 : CollatzResearch.WordTrace tailWord_398237 prefixEnd_398237 90883109068739390936021 := by
  unfold tailWord_398237
  simp only [CollatzResearch.WordTrace]
  refine ⟨14524896658262837309880965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9683264438841891539920643 14524896658262837309880965)
  ·
    refine ⟨2723418123424281995602681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14524896658262837309880965 2723418123424281995602681)
    ·
      refine ⟨2042563592568211496702011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2723418123424281995602681 2042563592568211496702011)
      ·
        refine ⟨3063845388852317245053017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2042563592568211496702011 3063845388852317245053017)
        ·
          refine ⟨2297884041639237933789763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3063845388852317245053017 2297884041639237933789763)
          ·
            refine ⟨3446826062458856900684645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2297884041639237933789763 3446826062458856900684645)
            ·
              refine ⟨646279886711035668878371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3446826062458856900684645 646279886711035668878371)
              ·
                refine ⟨969419830066553503317557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646279886711035668878371 969419830066553503317557)
                ·
                  refine ⟨90883109068739390936021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 969419830066553503317557 90883109068739390936021)
                  ·
                    rfl

theorem cell21_398237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_398237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398237 prefixEnd_398237 := by exact prefixLift 398237
  have htrace : WordTrace (prefixWord ++ tailWord_398237) baseStart_398237 baseEnd_398237 := by
    simpa [prefixWord, tailWord_398237, baseEnd_398237] using wordTrace_append hprefix tailTrace_398237
  have hstable : (prefixWord ++ tailWord_398237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398237).length < 2 ^ (prefixWord ++ tailWord_398237).sum := by decide
  have hdescent : baseEnd_398237 < baseStart_398237 := by decide
  rcases family_descends (prefixWord ++ tailWord_398237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398344 : List Nat := [2, 1, 3, 2, 1, 4, 2, 2, 4]
def baseStart_398344 : Nat := 118140960795 + 398344 * 2 ^ 59
def prefixEnd_398344 : Nat := 4983230072969 + 3 ^ 40 * 398344 * 2
def baseEnd_398344 : Nat := 90907527926530982652469

theorem tailTrace_398344 : CollatzResearch.WordTrace tailWord_398344 prefixEnd_398344 90907527926530982652469 := by
  unfold tailWord_398344
  simp only [CollatzResearch.WordTrace]
  refine ⟨7264399634437597292013043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9685866179250129722684057 7264399634437597292013043)
  ·
    refine ⟨10896599451656395938019565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7264399634437597292013043 10896599451656395938019565)
    ·
      refine ⟨4086224794371148476757337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10896599451656395938019565 4086224794371148476757337)
      ·
        refine ⟨3064668595778361357568003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4086224794371148476757337 3064668595778361357568003)
        ·
          refine ⟨4597002893667542036352005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3064668595778361357568003 4597002893667542036352005)
          ·
            refine ⟨861938042562664131816001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4597002893667542036352005 861938042562664131816001)
            ·
              refine ⟨646453531921998098862001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 861938042562664131816001 646453531921998098862001)
              ·
                refine ⟨484840148941498574146501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 646453531921998098862001 484840148941498574146501)
                ·
                  refine ⟨90907527926530982652469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 484840148941498574146501 90907527926530982652469)
                  ·
                    rfl

theorem cell21_398344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 2, 2, 4].length) (baseStart_398344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398344 prefixEnd_398344 := by exact prefixLift 398344
  have htrace : WordTrace (prefixWord ++ tailWord_398344) baseStart_398344 baseEnd_398344 := by
    simpa [prefixWord, tailWord_398344, baseEnd_398344] using wordTrace_append hprefix tailTrace_398344
  have hstable : (prefixWord ++ tailWord_398344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398344).length < 2 ^ (prefixWord ++ tailWord_398344).sum := by decide
  have hdescent : baseEnd_398344 < baseStart_398344 := by decide
  rcases family_descends (prefixWord ++ tailWord_398344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398347 : List Nat := [1, 1, 1, 1, 6, 4, 2, 2, 3]
def baseStart_398347 : Nat := 118140960795 + 398347 * 2 ^ 59
def prefixEnd_398347 : Nat := 4983230072969 + 3 ^ 40 * 398347 * 2
def baseEnd_398347 : Nat := 90908212567403644102463

theorem tailTrace_398347 : CollatzResearch.WordTrace tailWord_398347 prefixEnd_398347 90908212567403644102463 := by
  unfold tailWord_398347
  simp only [CollatzResearch.WordTrace]
  refine ⟨14528908687864326096385295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9685939125242884064256863 14528908687864326096385295)
  ·
    refine ⟨21793363031796489144577943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14528908687864326096385295 21793363031796489144577943)
    ·
      refine ⟨32690044547694733716866915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21793363031796489144577943 32690044547694733716866915)
      ·
        refine ⟨49035066821542100575300373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32690044547694733716866915 49035066821542100575300373)
        ·
          refine ⟨2298518757259785964467205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 49035066821542100575300373 2298518757259785964467205)
          ·
            refine ⟨430972266986209868337601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2298518757259785964467205 430972266986209868337601)
            ·
              refine ⟨323229200239657401253201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 430972266986209868337601 323229200239657401253201)
              ·
                refine ⟨242421900179743050939901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323229200239657401253201 242421900179743050939901)
                ·
                  refine ⟨90908212567403644102463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242421900179743050939901 90908212567403644102463)
                  ·
                    rfl

theorem cell21_398347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 2, 2, 3].length) (baseStart_398347 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398347 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398347 prefixEnd_398347 := by exact prefixLift 398347
  have htrace : WordTrace (prefixWord ++ tailWord_398347) baseStart_398347 baseEnd_398347 := by
    simpa [prefixWord, tailWord_398347, baseEnd_398347] using wordTrace_append hprefix tailTrace_398347
  have hstable : (prefixWord ++ tailWord_398347).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398347).length < 2 ^ (prefixWord ++ tailWord_398347).sum := by decide
  have hdescent : baseEnd_398347 < baseStart_398347 := by decide
  rcases family_descends (prefixWord ++ tailWord_398347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398406 : List Nat := [6, 1, 1, 1, 1, 2, 1, 3, 5]
def baseStart_398406 : Nat := 118140960795 + 398406 * 2 ^ 59
def prefixEnd_398406 : Nat := 4983230072969 + 3 ^ 40 * 398406 * 2
def baseEnd_398406 : Nat := 90921677171232652619009

theorem tailTrace_398406 : CollatzResearch.WordTrace tailWord_398406 prefixEnd_398406 90921677171232652619009 := by
  unfold tailWord_398406
  simp only [CollatzResearch.WordTrace]
  refine ⟨454095643582830599149471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9687373729767052781855381 454095643582830599149471)
  ·
    refine ⟨681143465374245898724207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 454095643582830599149471 681143465374245898724207)
    ·
      refine ⟨1021715198061368848086311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 681143465374245898724207 1021715198061368848086311)
      ·
        refine ⟨1532572797092053272129467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1021715198061368848086311 1532572797092053272129467)
        ·
          refine ⟨2298859195638079908194201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1532572797092053272129467 2298859195638079908194201)
          ·
            refine ⟨1724144396728559931145651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2298859195638079908194201 1724144396728559931145651)
            ·
              refine ⟨2586216595092839896718477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1724144396728559931145651 2586216595092839896718477)
              ·
                refine ⟨969831223159814961269429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2586216595092839896718477 969831223159814961269429)
                ·
                  refine ⟨90921677171232652619009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 969831223159814961269429 90921677171232652619009)
                  ·
                    rfl

theorem cell21_398406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_398406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398406 prefixEnd_398406 := by exact prefixLift 398406
  have htrace : WordTrace (prefixWord ++ tailWord_398406) baseStart_398406 baseEnd_398406 := by
    simpa [prefixWord, tailWord_398406, baseEnd_398406] using wordTrace_append hprefix tailTrace_398406
  have hstable : (prefixWord ++ tailWord_398406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398406).length < 2 ^ (prefixWord ++ tailWord_398406).sum := by decide
  have hdescent : baseEnd_398406 < baseStart_398406 := by decide
  rcases family_descends (prefixWord ++ tailWord_398406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398440 : List Nat := [2, 1, 4, 4, 1, 2, 1, 3, 3]
def baseStart_398440 : Nat := 118140960795 + 398440 * 2 ^ 59
def prefixEnd_398440 : Nat := 4983230072969 + 3 ^ 40 * 398440 * 2
def baseEnd_398440 : Nat := 90929436434456149052273

theorem tailTrace_398440 : CollatzResearch.WordTrace tailWord_398440 prefixEnd_398440 90929436434456149052273 := by
  unfold tailWord_398440
  simp only [CollatzResearch.WordTrace]
  refine ⟨7266150338263701489760387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9688200451018268653013849 7266150338263701489760387)
  ·
    refine ⟨10899225507395552234640581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7266150338263701489760387 10899225507395552234640581)
    ·
      refine ⟨2043604782636666043995109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10899225507395552234640581 2043604782636666043995109)
      ·
        refine ⟨383175896744374883249083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2043604782636666043995109 383175896744374883249083)
        ·
          refine ⟨574763845116562324873625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 383175896744374883249083 574763845116562324873625)
          ·
            refine ⟨431072883837421743655219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 574763845116562324873625 431072883837421743655219)
            ·
              refine ⟨646609325756132615482829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431072883837421743655219 646609325756132615482829)
              ·
                refine ⟨242478497158549730806061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 646609325756132615482829 242478497158549730806061)
                ·
                  refine ⟨90929436434456149052273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242478497158549730806061 90929436434456149052273)
                  ·
                    rfl

theorem cell21_398440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 3, 3].length) (baseStart_398440 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398440 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398440 prefixEnd_398440 := by exact prefixLift 398440
  have htrace : WordTrace (prefixWord ++ tailWord_398440) baseStart_398440 baseEnd_398440 := by
    simpa [prefixWord, tailWord_398440, baseEnd_398440] using wordTrace_append hprefix tailTrace_398440
  have hstable : (prefixWord ++ tailWord_398440).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398440).length < 2 ^ (prefixWord ++ tailWord_398440).sum := by decide
  have hdescent : baseEnd_398440 < baseStart_398440 := by decide
  rcases family_descends (prefixWord ++ tailWord_398440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398465 : List Nat := [1, 2, 4, 2, 2, 1, 3, 1, 5]
def baseStart_398465 : Nat := 118140960795 + 398465 * 2 ^ 59
def prefixEnd_398465 : Nat := 4983230072969 + 3 ^ 40 * 398465 * 2
def baseEnd_398465 : Nat := 90935141775061661135555

theorem tailTrace_398465 : CollatzResearch.WordTrace tailWord_398465 prefixEnd_398465 90935141775061661135555 := by
  unfold tailWord_398465
  simp only [CollatzResearch.WordTrace]
  refine ⟨14533212501436832249180849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9688808334291221499453899 14533212501436832249180849)
  ·
    refine ⟨10899909376077624186885637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14533212501436832249180849 10899909376077624186885637)
    ·
      refine ⟨2043733008014554535041057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10899909376077624186885637 2043733008014554535041057)
      ·
        refine ⟨1532799756010915901280793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2043733008014554535041057 1532799756010915901280793)
        ·
          refine ⟨1149599817008186925960595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1532799756010915901280793 1149599817008186925960595)
          ·
            refine ⟨1724399725512280388940893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1149599817008186925960595 1724399725512280388940893)
            ·
              refine ⟨646649897067105145852835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1724399725512280388940893 646649897067105145852835)
              ·
                refine ⟨969974845600657718779253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646649897067105145852835 969974845600657718779253)
                ·
                  refine ⟨90935141775061661135555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 969974845600657718779253 90935141775061661135555)
                  ·
                    rfl

theorem cell21_398465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 5].length) (baseStart_398465 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398465 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398465 prefixEnd_398465 := by exact prefixLift 398465
  have htrace : WordTrace (prefixWord ++ tailWord_398465) baseStart_398465 baseEnd_398465 := by
    simpa [prefixWord, tailWord_398465, baseEnd_398465] using wordTrace_append hprefix tailTrace_398465
  have hstable : (prefixWord ++ tailWord_398465).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398465).length < 2 ^ (prefixWord ++ tailWord_398465).sum := by decide
  have hdescent : baseEnd_398465 < baseStart_398465 := by decide
  rcases family_descends (prefixWord ++ tailWord_398465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398493 : List Nat := [1, 4, 2, 1, 1, 2, 1, 9]
def baseStart_398493 : Nat := 118140960795 + 398493 * 2 ^ 59
def prefixEnd_398493 : Nat := 4983230072969 + 3 ^ 40 * 398493 * 2
def baseEnd_398493 : Nat := 30313843918846611556277

theorem tailTrace_398493 : CollatzResearch.WordTrace tailWord_398493 prefixEnd_398493 30313843918846611556277 := by
  unfold tailWord_398493
  simp only [CollatzResearch.WordTrace]
  refine ⟨14534233745335393031200133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9689489163556928687466755 14534233745335393031200133)
  ·
    refine ⟨2725168827250386193350025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14534233745335393031200133 2725168827250386193350025)
    ·
      refine ⟨2043876620437789645012519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2725168827250386193350025 2043876620437789645012519)
      ·
        refine ⟨3065814930656684467518779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2043876620437789645012519 3065814930656684467518779)
        ·
          refine ⟨4598722395985026701278169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3065814930656684467518779 4598722395985026701278169)
          ·
            refine ⟨3449041796988770025958627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4598722395985026701278169 3449041796988770025958627)
            ·
              refine ⟨5173562695483155038937941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3449041796988770025958627 5173562695483155038937941)
              ·
                refine ⟨30313843918846611556277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5173562695483155038937941 30313843918846611556277)
                ·
                  rfl

theorem cell21_398493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 9].length) (baseStart_398493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398493 prefixEnd_398493 := by exact prefixLift 398493
  have htrace : WordTrace (prefixWord ++ tailWord_398493) baseStart_398493 baseEnd_398493 := by
    simpa [prefixWord, tailWord_398493, baseEnd_398493] using wordTrace_append hprefix tailTrace_398493
  have hstable : (prefixWord ++ tailWord_398493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398493).length < 2 ^ (prefixWord ++ tailWord_398493).sum := by decide
  have hdescent : baseEnd_398493 < baseStart_398493 := by decide
  rcases family_descends (prefixWord ++ tailWord_398493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398572 : List Nat := [2, 2, 1, 1, 2, 6, 1, 2, 4]
def baseStart_398572 : Nat := 118140960795 + 398572 * 2 ^ 59
def prefixEnd_398572 : Nat := 4983230072969 + 3 ^ 40 * 398572 * 2
def baseEnd_398572 : Nat := 90959560632853252852003

theorem tailTrace_398572 : CollatzResearch.WordTrace tailWord_398572 prefixEnd_398572 90959560632853252852003 := by
  unfold tailWord_398572
  simp only [CollatzResearch.WordTrace]
  refine ⟨7268557556024594761662985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9691410074699459682217313 7268557556024594761662985)
  ·
    refine ⟨5451418167018446071247239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7268557556024594761662985 5451418167018446071247239)
    ·
      refine ⟨8177127250527669106870859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5451418167018446071247239 8177127250527669106870859)
      ·
        refine ⟨12265690875791503660306289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8177127250527669106870859 12265690875791503660306289)
        ·
          refine ⟨9199268156843627745229717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12265690875791503660306289 9199268156843627745229717)
          ·
            refine ⟨431215694852045050557643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9199268156843627745229717 431215694852045050557643)
            ·
              refine ⟨646823542278067575836465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431215694852045050557643 646823542278067575836465)
              ·
                refine ⟨485117656708550681877349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 646823542278067575836465 485117656708550681877349)
                ·
                  refine ⟨90959560632853252852003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 485117656708550681877349 90959560632853252852003)
                  ·
                    rfl

theorem cell21_398572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_398572 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398572 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398572 prefixEnd_398572 := by exact prefixLift 398572
  have htrace : WordTrace (prefixWord ++ tailWord_398572) baseStart_398572 baseEnd_398572 := by
    simpa [prefixWord, tailWord_398572, baseEnd_398572] using wordTrace_append hprefix tailTrace_398572
  have hstable : (prefixWord ++ tailWord_398572).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398572).length < 2 ^ (prefixWord ++ tailWord_398572).sum := by decide
  have hdescent : baseEnd_398572 < baseStart_398572 := by decide
  rcases family_descends (prefixWord ++ tailWord_398572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398583 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 9]
def baseStart_398583 : Nat := 118140960795 + 398583 * 2 ^ 59
def prefixEnd_398583 : Nat := 4983230072969 + 3 ^ 40 * 398583 * 2
def baseEnd_398583 : Nat := 90962070982719678168647

theorem tailTrace_398583 : CollatzResearch.WordTrace tailWord_398583 prefixEnd_398583 90962070982719678168647 := by
  unfold tailWord_398583
  simp only [CollatzResearch.WordTrace]
  refine ⟨14537516315009338401976403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9691677543339558934650935 14537516315009338401976403)
  ·
    refine ⟨21806274472514007602964605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14537516315009338401976403 21806274472514007602964605)
    ·
      refine ⟨8177352927192752851111727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21806274472514007602964605 8177352927192752851111727)
      ·
        refine ⟨12266029390789129276667591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8177352927192752851111727 12266029390789129276667591)
        ·
          refine ⟨18399044086183693915001387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12266029390789129276667591 18399044086183693915001387)
          ·
            refine ⟨27598566129275540872502081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18399044086183693915001387 27598566129275540872502081)
            ·
              refine ⟨20698924596956655654376561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27598566129275540872502081 20698924596956655654376561)
              ·
                refine ⟨15524193447717491740782421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20698924596956655654376561 15524193447717491740782421)
                ·
                  refine ⟨90962070982719678168647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 15524193447717491740782421 90962070982719678168647)
                  ·
                    rfl

theorem cell21_398583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 9].length) (baseStart_398583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398583 prefixEnd_398583 := by exact prefixLift 398583
  have htrace : WordTrace (prefixWord ++ tailWord_398583) baseStart_398583 baseEnd_398583 := by
    simpa [prefixWord, tailWord_398583, baseEnd_398583] using wordTrace_append hprefix tailTrace_398583
  have hstable : (prefixWord ++ tailWord_398583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398583).length < 2 ^ (prefixWord ++ tailWord_398583).sum := by decide
  have hdescent : baseEnd_398583 < baseStart_398583 := by decide
  rcases family_descends (prefixWord ++ tailWord_398583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398634 : List Nat := [3, 1, 4, 2, 1, 3, 1, 1, 5]
def baseStart_398634 : Nat := 118140960795 + 398634 * 2 ^ 59
def prefixEnd_398634 : Nat := 4983230072969 + 3 ^ 40 * 398634 * 2
def baseEnd_398634 : Nat := 90973709877554922818543

theorem tailTrace_398634 : CollatzResearch.WordTrace tailWord_398634 prefixEnd_398634 90973709877554922818543 := by
  unfold tailWord_398634
  simp only [CollatzResearch.WordTrace]
  refine ⟨3634844109456143528020739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9692917625216382741388637 3634844109456143528020739)
  ·
    refine ⟨5452266164184215292031109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3634844109456143528020739 5452266164184215292031109)
    ·
      refine ⟨1022299905784540367255833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5452266164184215292031109 1022299905784540367255833)
      ·
        refine ⟨766724929338405275441875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1022299905784540367255833 766724929338405275441875)
        ·
          refine ⟨1150087394007607913162813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 766724929338405275441875 1150087394007607913162813)
          ·
            refine ⟨431282772752852967436055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1150087394007607913162813 431282772752852967436055)
            ·
              refine ⟨646924159129279451154083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 431282772752852967436055 646924159129279451154083)
              ·
                refine ⟨970386238693919176731125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 646924159129279451154083 970386238693919176731125)
                ·
                  refine ⟨90973709877554922818543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 970386238693919176731125 90973709877554922818543)
                  ·
                    rfl

theorem cell21_398634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 5].length) (baseStart_398634 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398634 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398634 prefixEnd_398634 := by exact prefixLift 398634
  have htrace : WordTrace (prefixWord ++ tailWord_398634) baseStart_398634 baseEnd_398634 := by
    simpa [prefixWord, tailWord_398634, baseEnd_398634] using wordTrace_append hprefix tailTrace_398634
  have hstable : (prefixWord ++ tailWord_398634).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398634).length < 2 ^ (prefixWord ++ tailWord_398634).sum := by decide
  have hdescent : baseEnd_398634 < baseStart_398634 := by decide
  rcases family_descends (prefixWord ++ tailWord_398634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398645 : List Nat := [1, 3, 3, 1, 2, 2, 1, 8]
def baseStart_398645 : Nat := 118140960795 + 398645 * 2 ^ 59
def prefixEnd_398645 : Nat := 4983230072969 + 3 ^ 40 * 398645 * 2
def baseEnd_398645 : Nat := 30325406742473782711729

theorem tailTrace_398645 : CollatzResearch.WordTrace tailWord_398645 prefixEnd_398645 30325406742473782711729 := by
  unfold tailWord_398645
  simp only [CollatzResearch.WordTrace]
  refine ⟨14539777640784722990733389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9693185093856481993822259 14539777640784722990733389)
  ·
    refine ⟨5452416615294271121525021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14539777640784722990733389 5452416615294271121525021)
    ·
      refine ⟨2044656230735351670571883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5452416615294271121525021 2044656230735351670571883)
      ·
        refine ⟨3066984346103027505857825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2044656230735351670571883 3066984346103027505857825)
        ·
          refine ⟨2300238259577270629393369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3066984346103027505857825 2300238259577270629393369)
          ·
            refine ⟨1725178694682952972045027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2300238259577270629393369 1725178694682952972045027)
            ·
              refine ⟨2587768042024429458067541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1725178694682952972045027 2587768042024429458067541)
              ·
                refine ⟨30325406742473782711729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2587768042024429458067541 30325406742473782711729)
                ·
                  rfl

theorem cell21_398645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 8].length) (baseStart_398645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398645 prefixEnd_398645 := by exact prefixLift 398645
  have htrace : WordTrace (prefixWord ++ tailWord_398645) baseStart_398645 baseEnd_398645 := by
    simpa [prefixWord, tailWord_398645, baseEnd_398645] using wordTrace_append hprefix tailTrace_398645
  have hstable : (prefixWord ++ tailWord_398645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398645).length < 2 ^ (prefixWord ++ tailWord_398645).sum := by decide
  have hdescent : baseEnd_398645 < baseStart_398645 := by decide
  rcases family_descends (prefixWord ++ tailWord_398645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398659 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 7]
def baseStart_398659 : Nat := 118140960795 + 398659 * 2 ^ 59
def prefixEnd_398659 : Nat := 4983230072969 + 3 ^ 40 * 398659 * 2
def baseEnd_398659 : Nat := 90979415218160434901825

theorem tailTrace_398659 : CollatzResearch.WordTrace tailWord_398659 prefixEnd_398659 90979415218160434901825 := by
  unfold tailWord_398659
  simp only [CollatzResearch.WordTrace]
  refine ⟨14540288262734003381743031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9693525508489335587828687 14540288262734003381743031)
  ·
    refine ⟨21810432394101005072614547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14540288262734003381743031 21810432394101005072614547)
    ·
      refine ⟨32715648591151507608921821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21810432394101005072614547 32715648591151507608921821)
      ·
        refine ⟨12268368221681815353345683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32715648591151507608921821 12268368221681815353345683)
        ·
          refine ⟨18402552332522723030018525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12268368221681815353345683 18402552332522723030018525)
          ·
            refine ⟨6900957124696021136256947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18402552332522723030018525 6900957124696021136256947)
            ·
              refine ⟨10351435687044031704385421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6900957124696021136256947 10351435687044031704385421)
              ·
                refine ⟨3881788382641511889144533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10351435687044031704385421 3881788382641511889144533)
                ·
                  refine ⟨90979415218160434901825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3881788382641511889144533 90979415218160434901825)
                  ·
                    rfl

theorem cell21_398659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 7].length) (baseStart_398659 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398659 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398659 prefixEnd_398659 := by exact prefixLift 398659
  have htrace : WordTrace (prefixWord ++ tailWord_398659) baseStart_398659 baseEnd_398659 := by
    simpa [prefixWord, tailWord_398659, baseEnd_398659] using wordTrace_append hprefix tailTrace_398659
  have hstable : (prefixWord ++ tailWord_398659).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398659).length < 2 ^ (prefixWord ++ tailWord_398659).sum := by decide
  have hdescent : baseEnd_398659 < baseStart_398659 := by decide
  rcases family_descends (prefixWord ++ tailWord_398659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398693 : List Nat := [1, 3, 1, 3, 1, 2, 3, 4, 3]
def baseStart_398693 : Nat := 118140960795 + 398693 * 2 ^ 59
def prefixEnd_398693 : Nat := 4983230072969 + 3 ^ 40 * 398693 * 2
def baseEnd_398693 : Nat := 90987174481383931335089

theorem tailTrace_398693 : CollatzResearch.WordTrace tailWord_398693 prefixEnd_398693 90987174481383931335089 := by
  unfold tailWord_398693
  simp only [CollatzResearch.WordTrace]
  refine ⟨14541528344610827188480733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9694352229740551458987155 14541528344610827188480733)
  ·
    refine ⟨5453073129229060195680275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14541528344610827188480733 5453073129229060195680275)
    ·
      refine ⟨8179609693843590293520413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5453073129229060195680275 8179609693843590293520413)
      ·
        refine ⟨3067353635191346360070155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8179609693843590293520413 3067353635191346360070155)
        ·
          refine ⟨4601030452787019540105233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3067353635191346360070155 4601030452787019540105233)
          ·
            refine ⟨3450772839590264655078925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4601030452787019540105233 3450772839590264655078925)
            ·
              refine ⟨1294039814846349245654597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3450772839590264655078925 1294039814846349245654597)
              ·
                refine ⟨242632465283690483560237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1294039814846349245654597 242632465283690483560237)
                ·
                  refine ⟨90987174481383931335089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242632465283690483560237 90987174481383931335089)
                  ·
                    rfl

theorem cell21_398693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 3].length) (baseStart_398693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398693 prefixEnd_398693 := by exact prefixLift 398693
  have htrace : WordTrace (prefixWord ++ tailWord_398693) baseStart_398693 baseEnd_398693 := by
    simpa [prefixWord, tailWord_398693, baseEnd_398693] using wordTrace_append hprefix tailTrace_398693
  have hstable : (prefixWord ++ tailWord_398693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398693).length < 2 ^ (prefixWord ++ tailWord_398693).sum := by decide
  have hdescent : baseEnd_398693 < baseStart_398693 := by decide
  rcases family_descends (prefixWord ++ tailWord_398693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398752 : List Nat := [2, 1, 1, 4, 1, 2, 4, 1, 5]
def baseStart_398752 : Nat := 118140960795 + 398752 * 2 ^ 59
def prefixEnd_398752 : Nat := 4983230072969 + 3 ^ 40 * 398752 * 2
def baseEnd_398752 : Nat := 91000639085212939851635

theorem tailTrace_398752 : CollatzResearch.WordTrace tailWord_398752 prefixEnd_398752 91000639085212939851635 := by
  unfold tailWord_398752
  simp only [CollatzResearch.WordTrace]
  refine ⟨7271840125698540132439255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9695786834264720176585673 7271840125698540132439255)
  ·
    refine ⟨10907760188547810198658883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7271840125698540132439255 10907760188547810198658883)
    ·
      refine ⟨16361640282821715297988325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10907760188547810198658883 16361640282821715297988325)
      ·
        refine ⟨3067807553029071618372811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16361640282821715297988325 3067807553029071618372811)
        ·
          refine ⟨4601711329543607427559217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3067807553029071618372811 4601711329543607427559217)
          ·
            refine ⟨3451283497157705570669413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4601711329543607427559217 3451283497157705570669413)
            ·
              refine ⟨647115655717069794500515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3451283497157705570669413 647115655717069794500515)
              ·
                refine ⟨970673483575604691750773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 647115655717069794500515 970673483575604691750773)
                ·
                  refine ⟨91000639085212939851635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 970673483575604691750773 91000639085212939851635)
                  ·
                    rfl

theorem cell21_398752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 5].length) (baseStart_398752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398752 prefixEnd_398752 := by exact prefixLift 398752
  have htrace : WordTrace (prefixWord ++ tailWord_398752) baseStart_398752 baseEnd_398752 := by
    simpa [prefixWord, tailWord_398752, baseEnd_398752] using wordTrace_append hprefix tailTrace_398752
  have hstable : (prefixWord ++ tailWord_398752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398752).length < 2 ^ (prefixWord ++ tailWord_398752).sum := by decide
  have hdescent : baseEnd_398752 < baseStart_398752 := by decide
  rcases family_descends (prefixWord ++ tailWord_398752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398854 : List Nat := [6, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_398854 : Nat := 118140960795 + 398854 * 2 ^ 59
def prefixEnd_398854 : Nat := 4983230072969 + 3 ^ 40 * 398854 * 2
def baseEnd_398854 : Nat := 91023916874883429151427

theorem tailTrace_398854 : CollatzResearch.WordTrace tailWord_398854 prefixEnd_398854 91023916874883429151427 := by
  unfold tailWord_398854
  simp only [CollatzResearch.WordTrace]
  refine ⟨454606265532110990159113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9698266998018367790061077 454606265532110990159113)
  ·
    refine ⟨340954699149083242619335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 454606265532110990159113 340954699149083242619335)
    ·
      refine ⟨511432048723624863929003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 340954699149083242619335 511432048723624863929003)
      ·
        refine ⟨767148073085437295893505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 511432048723624863929003 767148073085437295893505)
        ·
          refine ⟨575361054814077971920129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 767148073085437295893505 575361054814077971920129)
          ·
            refine ⟨431520791110558478940097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 575361054814077971920129 431520791110558478940097)
            ·
              refine ⟨323640593332918859205073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431520791110558478940097 323640593332918859205073)
              ·
                refine ⟨242730444999689144403805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 323640593332918859205073 242730444999689144403805)
                ·
                  refine ⟨91023916874883429151427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242730444999689144403805 91023916874883429151427)
                  ·
                    rfl

theorem cell21_398854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_398854 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398854 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398854 prefixEnd_398854 := by exact prefixLift 398854
  have htrace : WordTrace (prefixWord ++ tailWord_398854) baseStart_398854 baseEnd_398854 := by
    simpa [prefixWord, tailWord_398854, baseEnd_398854] using wordTrace_append hprefix tailTrace_398854
  have hstable : (prefixWord ++ tailWord_398854).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398854).length < 2 ^ (prefixWord ++ tailWord_398854).sum := by decide
  have hdescent : baseEnd_398854 < baseStart_398854 := by decide
  rcases family_descends (prefixWord ++ tailWord_398854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398862 : List Nat := [4, 1, 1, 2, 4, 1, 1, 4, 3]
def baseStart_398862 : Nat := 118140960795 + 398862 * 2 ^ 59
def prefixEnd_398862 : Nat := 4983230072969 + 3 ^ 40 * 398862 * 2
def baseEnd_398862 : Nat := 91025742583877193018077

theorem tailTrace_398862 : CollatzResearch.WordTrace tailWord_398862 prefixEnd_398862 91025742583877193018077 := by
  unfold tailWord_398862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1818461535124821131422855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9698461520665712700921893 1818461535124821131422855)
  ·
    refine ⟨2727692302687231697134283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1818461535124821131422855 2727692302687231697134283)
    ·
      refine ⟨4091538454030847545701425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2727692302687231697134283 4091538454030847545701425)
      ·
        refine ⟨3068653840523135659276069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4091538454030847545701425 3068653840523135659276069)
        ·
          refine ⟨575372595098087936114263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3068653840523135659276069 575372595098087936114263)
          ·
            refine ⟨863058892647131904171395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 575372595098087936114263 863058892647131904171395)
            ·
              refine ⟨1294588338970697856257093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 863058892647131904171395 1294588338970697856257093)
              ·
                refine ⟨242735313557005848048205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1294588338970697856257093 242735313557005848048205)
                ·
                  refine ⟨91025742583877193018077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 242735313557005848048205 91025742583877193018077)
                  ·
                    rfl

theorem cell21_398862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_398862 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398862 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398862 prefixEnd_398862 := by exact prefixLift 398862
  have htrace : WordTrace (prefixWord ++ tailWord_398862) baseStart_398862 baseEnd_398862 := by
    simpa [prefixWord, tailWord_398862, baseEnd_398862] using wordTrace_append hprefix tailTrace_398862
  have hstable : (prefixWord ++ tailWord_398862).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398862).length < 2 ^ (prefixWord ++ tailWord_398862).sum := by decide
  have hdescent : baseEnd_398862 < baseStart_398862 := by decide
  rcases family_descends (prefixWord ++ tailWord_398862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398890 : List Nat := [3, 1, 4, 1, 1, 1, 5, 5]
def baseStart_398890 : Nat := 118140960795 + 398890 * 2 ^ 59
def prefixEnd_398890 : Nat := 4983230072969 + 3 ^ 40 * 398890 * 2
def baseEnd_398890 : Nat := 30344044188451788850451

theorem tailTrace_398890 : CollatzResearch.WordTrace tailWord_398890 prefixEnd_398890 30344044188451788850451 := by
  unfold tailWord_398890
  simp only [CollatzResearch.WordTrace]
  refine ⟨3637178381224282458350531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9699142349931419888934749 3637178381224282458350531)
  ·
    refine ⟨5455767571836423687525797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3637178381224282458350531 5455767571836423687525797)
    ·
      refine ⟨1022956419719329441411087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5455767571836423687525797 1022956419719329441411087)
      ·
        refine ⟨1534434629578994162116631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1022956419719329441411087 1534434629578994162116631)
        ·
          refine ⟨2301651944368491243174947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1534434629578994162116631 2301651944368491243174947)
          ·
            refine ⟨3452477916552736864762421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2301651944368491243174947 3452477916552736864762421)
            ·
              refine ⟨323669804676819081071477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3452477916552736864762421 323669804676819081071477)
              ·
                refine ⟨30344044188451788850451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 323669804676819081071477 30344044188451788850451)
                ·
                  rfl

theorem cell21_398890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 5, 5].length) (baseStart_398890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398890 prefixEnd_398890 := by exact prefixLift 398890
  have htrace : WordTrace (prefixWord ++ tailWord_398890) baseStart_398890 baseEnd_398890 := by
    simpa [prefixWord, tailWord_398890, baseEnd_398890] using wordTrace_append hprefix tailTrace_398890
  have hstable : (prefixWord ++ tailWord_398890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398890).length < 2 ^ (prefixWord ++ tailWord_398890).sum := by decide
  have hdescent : baseEnd_398890 < baseStart_398890 := by decide
  rcases family_descends (prefixWord ++ tailWord_398890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_398941 : List Nat := [1, 4, 4, 2, 2, 1, 2, 5]
def baseStart_398941 : Nat := 118140960795 + 398941 * 2 ^ 59
def prefixEnd_398941 : Nat := 4983230072969 + 3 ^ 40 * 398941 * 2
def baseEnd_398941 : Nat := 30347923820063537067083

theorem tailTrace_398941 : CollatzResearch.WordTrace tailWord_398941 prefixEnd_398941 30347923820063537067083 := by
  unfold tailWord_398941
  simp only [CollatzResearch.WordTrace]
  refine ⟨14550573647712365543508677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9700382431808243695672451 14550573647712365543508677)
  ·
    refine ⟨2728232558946068539407877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14550573647712365543508677 2728232558946068539407877)
    ·
      refine ⟨511543604802387851138977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2728232558946068539407877 511543604802387851138977)
      ·
        refine ⟨383657703601790888354233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 511543604802387851138977 383657703601790888354233)
        ·
          refine ⟨287743277701343166265675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 383657703601790888354233 287743277701343166265675)
          ·
            refine ⟨431614916552014749398513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 287743277701343166265675 431614916552014749398513)
            ·
              refine ⟨323711187414011062048885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 431614916552014749398513 323711187414011062048885)
              ·
                refine ⟨30347923820063537067083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 323711187414011062048885 30347923820063537067083)
                ·
                  rfl

theorem cell21_398941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 2, 5].length) (baseStart_398941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_398941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_398941 prefixEnd_398941 := by exact prefixLift 398941
  have htrace : WordTrace (prefixWord ++ tailWord_398941) baseStart_398941 baseEnd_398941 := by
    simpa [prefixWord, tailWord_398941, baseEnd_398941] using wordTrace_append hprefix tailTrace_398941
  have hstable : (prefixWord ++ tailWord_398941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_398941).length < 2 ^ (prefixWord ++ tailWord_398941).sum := by decide
  have hdescent : baseEnd_398941 < baseStart_398941 := by decide
  rcases family_descends (prefixWord ++ tailWord_398941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
