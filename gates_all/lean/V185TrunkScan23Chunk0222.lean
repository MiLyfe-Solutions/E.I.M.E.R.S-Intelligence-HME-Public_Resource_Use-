import V185TrunkScan23Chunk0221

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1313351 : List Nat := [1, 1, 4, 1, 4, 2, 3, 1, 1, 2, 3]
def baseStart_1313351 : Nat := 118140960795 + 1313351 * 2 ^ 59
def prefixEnd_1313351 : Nat := 4983230072969 + 3 ^ 40 * 1313351 * 2
def baseEnd_1313351 : Nat := 674380331063196241872515

theorem tailTrace_1313351 : CollatzResearch.WordTrace tailWord_1313351 prefixEnd_1313351 674380331063196241872515 := by
  unfold tailWord_1313351
  simp only [CollatzResearch.WordTrace]
  refine ⟨47901846264961104338275907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31934564176640736225517271 47901846264961104338275907)
  ·
    refine ⟨71852769397441656507413861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47901846264961104338275907 71852769397441656507413861)
    ·
      refine ⟨13472394262020310595140099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71852769397441656507413861 13472394262020310595140099)
      ·
        refine ⟨20208591393030465892710149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13472394262020310595140099 20208591393030465892710149)
        ·
          refine ⟨3789110886193212354883153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20208591393030465892710149 3789110886193212354883153)
          ·
            refine ⟨2841833164644909266162365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3789110886193212354883153 2841833164644909266162365)
            ·
              refine ⟨1065687436741840974810887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2841833164644909266162365 1065687436741840974810887)
              ·
                refine ⟨1598531155112761462216331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1065687436741840974810887 1598531155112761462216331)
                ·
                  refine ⟨2397796732669142193324497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1598531155112761462216331 2397796732669142193324497)
                  ·
                    refine ⟨1798347549501856644993373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2397796732669142193324497 1798347549501856644993373)
                    ·
                      refine ⟨674380331063196241872515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1798347549501856644993373 674380331063196241872515)
                      ·
                        rfl

theorem cell23_1313351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 1, 2, 3].length) (baseStart_1313351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313351 prefixEnd_1313351 := by exact prefixLift 1313351
  have htrace : WordTrace (prefixWord ++ tailWord_1313351) baseStart_1313351 baseEnd_1313351 := by
    simpa [prefixWord, tailWord_1313351, baseEnd_1313351] using wordTrace_append hprefix tailTrace_1313351
  have hstable : (prefixWord ++ tailWord_1313351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313351).length < 2 ^ (prefixWord ++ tailWord_1313351).sum := by decide
  have hdescent : baseEnd_1313351 < baseStart_1313351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313404 : List Nat := [2, 2, 2, 1, 1, 2, 4, 2, 1, 4, 2]
def baseStart_1313404 : Nat := 118140960795 + 1313404 * 2 ^ 59
def prefixEnd_1313404 : Nat := 4983230072969 + 3 ^ 40 * 1313404 * 2
def baseEnd_1313404 : Nat := 674407545537884534509771

theorem tailTrace_1313404 : CollatzResearch.WordTrace tailWord_1313404 prefixEnd_1313404 674407545537884534509771 := by
  unfold tailWord_1313404
  simp only [CollatzResearch.WordTrace]
  refine ⟨23951889666884547194977633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31935852889179396259970177 23951889666884547194977633)
  ·
    refine ⟨17963917250163410396233225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23951889666884547194977633 17963917250163410396233225)
    ·
      refine ⟨13472937937622557797174919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17963917250163410396233225 13472937937622557797174919)
      ·
        refine ⟨20209406906433836695762379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13472937937622557797174919 20209406906433836695762379)
        ·
          refine ⟨30314110359650755043643569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20209406906433836695762379 30314110359650755043643569)
          ·
            refine ⟨22735582769738066282732677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30314110359650755043643569 22735582769738066282732677)
            ·
              refine ⟨4262921769325887428012377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22735582769738066282732677 4262921769325887428012377)
              ·
                refine ⟨3197191326994415571009283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4262921769325887428012377 3197191326994415571009283)
                ·
                  refine ⟨4795786990491623356513925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3197191326994415571009283 4795786990491623356513925)
                  ·
                    refine ⟨899210060717179379346361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4795786990491623356513925 899210060717179379346361)
                    ·
                      refine ⟨674407545537884534509771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 899210060717179379346361 674407545537884534509771)
                      ·
                        rfl

theorem cell23_1313404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 4, 2, 1, 4, 2].length) (baseStart_1313404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313404 prefixEnd_1313404 := by exact prefixLift 1313404
  have htrace : WordTrace (prefixWord ++ tailWord_1313404) baseStart_1313404 baseEnd_1313404 := by
    simpa [prefixWord, tailWord_1313404, baseEnd_1313404] using wordTrace_append hprefix tailTrace_1313404
  have hstable : (prefixWord ++ tailWord_1313404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313404).length < 2 ^ (prefixWord ++ tailWord_1313404).sum := by decide
  have hdescent : baseEnd_1313404 < baseStart_1313404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313408 : List Nat := [2, 1, 1, 2, 1, 7, 2, 1, 1, 3, 2]
def baseStart_1313408 : Nat := 118140960795 + 1313408 * 2 ^ 59
def prefixEnd_1313408 : Nat := 4983230072969 + 3 ^ 40 * 1313408 * 2
def baseEnd_1313408 : Nat := 674409599460502518859753

theorem tailTrace_1313408 : CollatzResearch.WordTrace tailWord_1313408 prefixEnd_1313408 674409599460502518859753 := by
  unfold tailWord_1313408
  simp only [CollatzResearch.WordTrace]
  refine ⟨23951962612877301536550439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31935950150503068715400585 23951962612877301536550439)
  ·
    refine ⟨35927943919315952304825659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23951962612877301536550439 35927943919315952304825659)
    ·
      refine ⟨53891915878973928457238489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35927943919315952304825659 53891915878973928457238489)
      ·
        refine ⟨40418936909230446342928867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53891915878973928457238489 40418936909230446342928867)
        ·
          refine ⟨60628405363845669514393301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40418936909230446342928867 60628405363845669514393301)
          ·
            refine ⟨1420978250715132879243593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 60628405363845669514393301 1420978250715132879243593)
            ·
              refine ⟨1065733688036349659432695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1420978250715132879243593 1065733688036349659432695)
              ·
                refine ⟨1598600532054524489149043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1065733688036349659432695 1598600532054524489149043)
                ·
                  refine ⟨2397900798081786733723565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1598600532054524489149043 2397900798081786733723565)
                  ·
                    refine ⟨899212799280670025146337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2397900798081786733723565 899212799280670025146337)
                    ·
                      refine ⟨674409599460502518859753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 899212799280670025146337 674409599460502518859753)
                      ·
                        rfl

theorem cell23_1313408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 1, 3, 2].length) (baseStart_1313408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313408 prefixEnd_1313408 := by exact prefixLift 1313408
  have htrace : WordTrace (prefixWord ++ tailWord_1313408) baseStart_1313408 baseEnd_1313408 := by
    simpa [prefixWord, tailWord_1313408, baseEnd_1313408] using wordTrace_append hprefix tailTrace_1313408
  have hstable : (prefixWord ++ tailWord_1313408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313408).length < 2 ^ (prefixWord ++ tailWord_1313408).sum := by decide
  have hdescent : baseEnd_1313408 < baseStart_1313408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313420 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 9]
def baseStart_1313420 : Nat := 118140960795 + 1313420 * 2 ^ 59
def prefixEnd_1313420 : Nat := 4983230072969 + 3 ^ 40 * 1313420 * 2
def baseEnd_1313420 : Nat := 674415761228356471909697

theorem tailTrace_1313420 : CollatzResearch.WordTrace tailWord_1313420 prefixEnd_1313420 674415761228356471909697 := by
  unfold tailWord_1313420
  simp only [CollatzResearch.WordTrace]
  refine ⟨23952181450855564561268857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31936241934474086081691809 23952181450855564561268857)
  ·
    refine ⟨17964136088141673420951643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23952181450855564561268857 17964136088141673420951643)
    ·
      refine ⟨26946204132212510131427465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17964136088141673420951643 26946204132212510131427465)
      ·
        refine ⟨20209653099159382598570599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26946204132212510131427465 20209653099159382598570599)
        ·
          refine ⟨30314479648739073897855899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20209653099159382598570599 30314479648739073897855899)
          ·
            refine ⟨45471719473108610846783849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30314479648739073897855899 45471719473108610846783849)
            ·
              refine ⟨34103789604831458135087887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45471719473108610846783849 34103789604831458135087887)
              ·
                refine ⟨51155684407247187202631831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34103789604831458135087887 51155684407247187202631831)
                ·
                  refine ⟨76733526610870780803947747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51155684407247187202631831 76733526610870780803947747)
                  ·
                    refine ⟨115100289916306171205921621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 76733526610870780803947747 115100289916306171205921621)
                    ·
                      refine ⟨674415761228356471909697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 115100289916306171205921621 674415761228356471909697)
                      ·
                        rfl

theorem cell23_1313420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_1313420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313420 prefixEnd_1313420 := by exact prefixLift 1313420
  have htrace : WordTrace (prefixWord ++ tailWord_1313420) baseStart_1313420 baseEnd_1313420 := by
    simpa [prefixWord, tailWord_1313420, baseEnd_1313420] using wordTrace_append hprefix tailTrace_1313420
  have hstable : (prefixWord ++ tailWord_1313420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313420).length < 2 ^ (prefixWord ++ tailWord_1313420).sum := by decide
  have hdescent : baseEnd_1313420 < baseStart_1313420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313461 : List Nat := [1, 3, 3, 3, 1, 1, 3, 3, 5]
def baseStart_1313461 : Nat := 118140960795 + 1313461 * 2 ^ 59
def prefixEnd_1313461 : Nat := 4983230072969 + 3 ^ 40 * 1313461 * 2
def baseEnd_1313461 : Nat := 74937423770576756833001

theorem tailTrace_1313461 : CollatzResearch.WordTrace tailWord_1313461 prefixEnd_1313461 74937423770576756833001 := by
  unfold tailWord_1313461
  simp only [CollatzResearch.WordTrace]
  refine ⟨47905858294562593124780237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31937238863041728749853491 47905858294562593124780237)
  ·
    refine ⟨17964696860460972421792589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47905858294562593124780237 17964696860460972421792589)
    ·
      refine ⟨6736761322672864658172221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17964696860460972421792589 6736761322672864658172221)
      ·
        refine ⟨2526285496002324246814583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6736761322672864658172221 2526285496002324246814583)
        ·
          refine ⟨3789428244003486370221875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2526285496002324246814583 3789428244003486370221875)
          ·
            refine ⟨5684142366005229555332813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3789428244003486370221875 5684142366005229555332813)
            ·
              refine ⟨2131553387251961083249805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5684142366005229555332813 2131553387251961083249805)
              ·
                refine ⟨799332520219485406218677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2131553387251961083249805 799332520219485406218677)
                ·
                  refine ⟨74937423770576756833001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 799332520219485406218677 74937423770576756833001)
                  ·
                    rfl

theorem cell23_1313461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 5].length) (baseStart_1313461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313461 prefixEnd_1313461 := by exact prefixLift 1313461
  have htrace : WordTrace (prefixWord ++ tailWord_1313461) baseStart_1313461 baseEnd_1313461 := by
    simpa [prefixWord, tailWord_1313461, baseEnd_1313461] using wordTrace_append hprefix tailTrace_1313461
  have hstable : (prefixWord ++ tailWord_1313461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313461).length < 2 ^ (prefixWord ++ tailWord_1313461).sum := by decide
  have hdescent : baseEnd_1313461 < baseStart_1313461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313484 : List Nat := [2, 2, 1, 5, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1313484 : Nat := 118140960795 + 1313484 * 2 ^ 59
def prefixEnd_1313484 : Nat := 4983230072969 + 3 ^ 40 * 1313484 * 2
def baseEnd_1313484 : Nat := 674448623990244221509403

theorem tailTrace_1313484 : CollatzResearch.WordTrace tailWord_1313484 prefixEnd_1313484 674448623990244221509403 := by
  unfold tailWord_1313484
  simp only [CollatzResearch.WordTrace]
  refine ⟨23953348586739634026433753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31937798115652845368578337 23953348586739634026433753)
  ·
    refine ⟨17965011440054725519825315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23953348586739634026433753 17965011440054725519825315)
    ·
      refine ⟨26947517160082088279737973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17965011440054725519825315 26947517160082088279737973)
      ·
        refine ⟨2526329733757695776225435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 26947517160082088279737973 2526329733757695776225435)
        ·
          refine ⟨3789494600636543664338153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2526329733757695776225435 3789494600636543664338153)
          ·
            refine ⟨2842120950477407748253615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3789494600636543664338153 2842120950477407748253615)
            ·
              refine ⟨4263181425716111622380423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2842120950477407748253615 4263181425716111622380423)
              ·
                refine ⟨6394772138574167433570635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4263181425716111622380423 6394772138574167433570635)
                ·
                  refine ⟨9592158207861251150355953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6394772138574167433570635 9592158207861251150355953)
                  ·
                    refine ⟨7194118655895938362766965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9592158207861251150355953 7194118655895938362766965)
                    ·
                      refine ⟨674448623990244221509403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7194118655895938362766965 674448623990244221509403)
                      ·
                        rfl

theorem cell23_1313484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1313484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313484 prefixEnd_1313484 := by exact prefixLift 1313484
  have htrace : WordTrace (prefixWord ++ tailWord_1313484) baseStart_1313484 baseEnd_1313484 := by
    simpa [prefixWord, tailWord_1313484, baseEnd_1313484] using wordTrace_append hprefix tailTrace_1313484
  have hstable : (prefixWord ++ tailWord_1313484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313484).length < 2 ^ (prefixWord ++ tailWord_1313484).sum := by decide
  have hdescent : baseEnd_1313484 < baseStart_1313484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313521 : List Nat := [1, 2, 2, 2, 2, 2, 2, 5, 1, 4]
def baseStart_1313521 : Nat := 118140960795 + 1313521 * 2 ^ 59
def prefixEnd_1313521 : Nat := 4983230072969 + 3 ^ 40 * 1313521 * 2
def baseEnd_1313521 : Nat := 224822540924820192248911

theorem tailTrace_1313521 : CollatzResearch.WordTrace tailWord_1313521 prefixEnd_1313521 224822540924820192248911 := by
  unfold tailWord_1313521
  simp only [CollatzResearch.WordTrace]
  refine ⟨47908046674345223371964417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31938697782896815581309611 47908046674345223371964417)
  ·
    refine ⟨35931035005758917528973313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47908046674345223371964417 35931035005758917528973313)
    ·
      refine ⟨26948276254319188146729985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35931035005758917528973313 26948276254319188146729985)
      ·
        refine ⟨20211207190739391110047489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26948276254319188146729985 20211207190739391110047489)
        ·
          refine ⟨15158405393054543332535617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20211207190739391110047489 15158405393054543332535617)
          ·
            refine ⟨11368804044790907499401713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15158405393054543332535617 11368804044790907499401713)
            ·
              refine ⟨8526603033593180624551285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11368804044790907499401713 8526603033593180624551285)
              ·
                refine ⟨799369034399360683551683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8526603033593180624551285 799369034399360683551683)
                ·
                  refine ⟨1199053551599041025327525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 799369034399360683551683 1199053551599041025327525)
                  ·
                    refine ⟨224822540924820192248911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1199053551599041025327525 224822540924820192248911)
                    ·
                      rfl

theorem cell23_1313521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 5, 1, 4].length) (baseStart_1313521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313521 prefixEnd_1313521 := by exact prefixLift 1313521
  have htrace : WordTrace (prefixWord ++ tailWord_1313521) baseStart_1313521 baseEnd_1313521 := by
    simpa [prefixWord, tailWord_1313521, baseEnd_1313521] using wordTrace_append hprefix tailTrace_1313521
  have hstable : (prefixWord ++ tailWord_1313521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313521).length < 2 ^ (prefixWord ++ tailWord_1313521).sum := by decide
  have hdescent : baseEnd_1313521 < baseStart_1313521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313537 : List Nat := [1, 2, 4, 1, 1, 1, 1, 3, 1, 2, 6]
def baseStart_1313537 : Nat := 118140960795 + 1313537 * 2 ^ 59
def prefixEnd_1313537 : Nat := 4983230072969 + 3 ^ 40 * 1313537 * 2
def baseEnd_1313537 : Nat := 674475838464932514146659

theorem tailTrace_1313537 : CollatzResearch.WordTrace tailWord_1313537 prefixEnd_1313537 674475838464932514146659 := by
  unfold tailWord_1313537
  simp only [CollatzResearch.WordTrace]
  refine ⟨47908630242287258104546865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31939086828191505403031243 47908630242287258104546865)
  ·
    refine ⟨35931472681715443578410149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47908630242287258104546865 35931472681715443578410149)
    ·
      refine ⟨6737151127821645670951903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35931472681715443578410149 6737151127821645670951903)
      ·
        refine ⟨10105726691732468506427855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6737151127821645670951903 10105726691732468506427855)
        ·
          refine ⟨15158590037598702759641783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10105726691732468506427855 15158590037598702759641783)
          ·
            refine ⟨22737885056398054139462675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15158590037598702759641783 22737885056398054139462675)
            ·
              refine ⟨34106827584597081209194013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22737885056398054139462675 34106827584597081209194013)
              ·
                refine ⟨12790060344223905453447755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34106827584597081209194013 12790060344223905453447755)
                ·
                  refine ⟨19185090516335858180171633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12790060344223905453447755 19185090516335858180171633)
                  ·
                    refine ⟨14388817887251893635128725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19185090516335858180171633 14388817887251893635128725)
                    ·
                      refine ⟨674475838464932514146659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14388817887251893635128725 674475838464932514146659)
                      ·
                        rfl

theorem cell23_1313537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 3, 1, 2, 6].length) (baseStart_1313537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313537 prefixEnd_1313537 := by exact prefixLift 1313537
  have htrace : WordTrace (prefixWord ++ tailWord_1313537) baseStart_1313537 baseEnd_1313537 := by
    simpa [prefixWord, tailWord_1313537, baseEnd_1313537] using wordTrace_append hprefix tailTrace_1313537
  have hstable : (prefixWord ++ tailWord_1313537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313537).length < 2 ^ (prefixWord ++ tailWord_1313537).sum := by decide
  have hdescent : baseEnd_1313537 < baseStart_1313537 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313557 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 2, 1, 7]
def baseStart_1313557 : Nat := 118140960795 + 1313557 * 2 ^ 59
def prefixEnd_1313557 : Nat := 4983230072969 + 3 ^ 40 * 1313557 * 2
def baseEnd_1313557 : Nat := 674486108078022435896567

theorem tailTrace_1313557 : CollatzResearch.WordTrace tailWord_1313557 prefixEnd_1313557 674486108078022435896567 := by
  unfold tailWord_1313557
  simp only [CollatzResearch.WordTrace]
  refine ⟨47909359702214801520274925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31939573134809867680183283 47909359702214801520274925)
  ·
    refine ⟨17966009888330550570103097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47909359702214801520274925 17966009888330550570103097)
    ·
      refine ⟨13474507416247912927577323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17966009888330550570103097 13474507416247912927577323)
      ·
        refine ⟨20211761124371869391365985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13474507416247912927577323 20211761124371869391365985)
        ·
          refine ⟨15158820843278902043524489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20211761124371869391365985 15158820843278902043524489)
          ·
            refine ⟨11369115632459176532643367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15158820843278902043524489 11369115632459176532643367)
            ·
              refine ⟨17053673448688764798965051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11369115632459176532643367 17053673448688764798965051)
              ·
                refine ⟨25580510173033147198447577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17053673448688764798965051 25580510173033147198447577)
                ·
                  refine ⟨19185382629774860398835683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25580510173033147198447577 19185382629774860398835683)
                  ·
                    refine ⟨28778073944662290598253525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19185382629774860398835683 28778073944662290598253525)
                    ·
                      refine ⟨674486108078022435896567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28778073944662290598253525 674486108078022435896567)
                      ·
                        rfl

theorem cell23_1313557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_1313557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313557 prefixEnd_1313557 := by exact prefixLift 1313557
  have htrace : WordTrace (prefixWord ++ tailWord_1313557) baseStart_1313557 baseEnd_1313557 := by
    simpa [prefixWord, tailWord_1313557, baseEnd_1313557] using wordTrace_append hprefix tailTrace_1313557
  have hstable : (prefixWord ++ tailWord_1313557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313557).length < 2 ^ (prefixWord ++ tailWord_1313557).sum := by decide
  have hdescent : baseEnd_1313557 < baseStart_1313557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313564 : List Nat := [2, 2, 3, 1, 1, 3, 2, 1, 3, 5]
def baseStart_1313564 : Nat := 118140960795 + 1313564 * 2 ^ 59
def prefixEnd_1313564 : Nat := 4983230072969 + 3 ^ 40 * 1313564 * 2
def baseEnd_1313564 : Nat := 224829900814201302836345

theorem tailTrace_1313564 : CollatzResearch.WordTrace tailWord_1313564 prefixEnd_1313564 224829900814201302836345 := by
  unfold tailWord_1313564
  simp only [CollatzResearch.WordTrace]
  refine ⟨23954807506594720857889873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31939743342126294477186497 23954807506594720857889873)
  ·
    refine ⟨17966105629946040643417405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23954807506594720857889873 17966105629946040643417405)
    ·
      refine ⟨6737289611229765241281527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17966105629946040643417405 6737289611229765241281527)
      ·
        refine ⟨10105934416844647861922291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6737289611229765241281527 10105934416844647861922291)
        ·
          refine ⟨15158901625266971792883437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10105934416844647861922291 15158901625266971792883437)
          ·
            refine ⟨5684588109475114422331289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15158901625266971792883437 5684588109475114422331289)
            ·
              refine ⟨4263441082106335816748467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5684588109475114422331289 4263441082106335816748467)
              ·
                refine ⟨6395161623159503725122701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4263441082106335816748467 6395161623159503725122701)
                ·
                  refine ⟨2398185608684813896921013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6395161623159503725122701 2398185608684813896921013)
                  ·
                    refine ⟨224829900814201302836345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2398185608684813896921013 224829900814201302836345)
                    ·
                      rfl

theorem cell23_1313564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_1313564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313564 prefixEnd_1313564 := by exact prefixLift 1313564
  have htrace : WordTrace (prefixWord ++ tailWord_1313564) baseStart_1313564 baseEnd_1313564 := by
    simpa [prefixWord, tailWord_1313564, baseEnd_1313564] using wordTrace_append hprefix tailTrace_1313564
  have hstable : (prefixWord ++ tailWord_1313564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313564).length < 2 ^ (prefixWord ++ tailWord_1313564).sum := by decide
  have hdescent : baseEnd_1313564 < baseStart_1313564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313565 : List Nat := [1, 4, 2, 4, 1, 2, 1, 1, 2, 2, 3]
def baseStart_1313565 : Nat := 118140960795 + 1313565 * 2 ^ 59
def prefixEnd_1313565 : Nat := 4983230072969 + 3 ^ 40 * 1313565 * 2
def baseEnd_1313565 : Nat := 674490215923258404596531

theorem tailTrace_1313565 : CollatzResearch.WordTrace tailWord_1313565 prefixEnd_1313565 674490215923258404596531 := by
  unfold tailWord_1313565
  simp only [CollatzResearch.WordTrace]
  refine ⟨47909651486185818886566149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31939767657457212591044099 47909651486185818886566149)
  ·
    refine ⟨8983059653659841041231153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47909651486185818886566149 8983059653659841041231153)
    ·
      refine ⟨6737294740244880780923365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8983059653659841041231153 6737294740244880780923365)
      ·
        refine ⟨1263242763795915146423131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6737294740244880780923365 1263242763795915146423131)
        ·
          refine ⟨1894864145693872719634697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1263242763795915146423131 1894864145693872719634697)
          ·
            refine ⟨1421148109270404539726023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1894864145693872719634697 1421148109270404539726023)
            ·
              refine ⟨2131722163905606809589035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1421148109270404539726023 2131722163905606809589035)
              ·
                refine ⟨3197583245858410214383553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2131722163905606809589035 3197583245858410214383553)
                ·
                  refine ⟨2398187434393807660787665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3197583245858410214383553 2398187434393807660787665)
                  ·
                    refine ⟨1798640575795355745590749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2398187434393807660787665 1798640575795355745590749)
                    ·
                      refine ⟨674490215923258404596531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1798640575795355745590749 674490215923258404596531)
                      ·
                        rfl

theorem cell23_1313565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_1313565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313565 prefixEnd_1313565 := by exact prefixLift 1313565
  have htrace : WordTrace (prefixWord ++ tailWord_1313565) baseStart_1313565 baseEnd_1313565 := by
    simpa [prefixWord, tailWord_1313565, baseEnd_1313565] using wordTrace_append hprefix tailTrace_1313565
  have hstable : (prefixWord ++ tailWord_1313565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313565).length < 2 ^ (prefixWord ++ tailWord_1313565).sum := by decide
  have hdescent : baseEnd_1313565 < baseStart_1313565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313584 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 1, 8, 2]
def baseStart_1313584 : Nat := 118140960795 + 1313584 * 2 ^ 59
def prefixEnd_1313584 : Nat := 4983230072969 + 3 ^ 40 * 1313584 * 2
def baseEnd_1313584 : Nat := 674499972055693830258943

theorem tailTrace_1313584 : CollatzResearch.WordTrace tailWord_1313584 prefixEnd_1313584 674499972055693830258943 := by
  unfold tailWord_1313584
  simp only [CollatzResearch.WordTrace]
  refine ⟨23955172236558492565753903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31940229648744656754338537 23955172236558492565753903)
  ·
    refine ⟨35932758354837738848630855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23955172236558492565753903 35932758354837738848630855)
    ·
      refine ⟨53899137532256608272946283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35932758354837738848630855 53899137532256608272946283)
      ·
        refine ⟨80848706298384912409419425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53899137532256608272946283 80848706298384912409419425)
        ·
          refine ⟨60636529723788684307064569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80848706298384912409419425 60636529723788684307064569)
          ·
            refine ⟨45477397292841513230298427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60636529723788684307064569 45477397292841513230298427)
            ·
              refine ⟨68216095939262269845447641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45477397292841513230298427 68216095939262269845447641)
              ·
                refine ⟨51162071954446702384085731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68216095939262269845447641 51162071954446702384085731)
                ·
                  refine ⟨76743107931670053576128597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51162071954446702384085731 76743107931670053576128597)
                  ·
                    refine ⟨899333296074258440345257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 76743107931670053576128597 899333296074258440345257)
                    ·
                      refine ⟨674499972055693830258943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 899333296074258440345257 674499972055693830258943)
                      ·
                        rfl

theorem cell23_1313584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 1, 8, 2].length) (baseStart_1313584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313584 prefixEnd_1313584 := by exact prefixLift 1313584
  have htrace : WordTrace (prefixWord ++ tailWord_1313584) baseStart_1313584 baseEnd_1313584 := by
    simpa [prefixWord, tailWord_1313584, baseEnd_1313584] using wordTrace_append hprefix tailTrace_1313584
  have hstable : (prefixWord ++ tailWord_1313584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313584).length < 2 ^ (prefixWord ++ tailWord_1313584).sum := by decide
  have hdescent : baseEnd_1313584 < baseStart_1313584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313607 : List Nat := [1, 1, 4, 1, 2, 1, 1, 12]
def baseStart_1313607 : Nat := 118140960795 + 1313607 * 2 ^ 59
def prefixEnd_1313607 : Nat := 4983230072969 + 3 ^ 40 * 1313607 * 2
def baseEnd_1313607 : Nat := 24981917855953601491531

theorem tailTrace_1313607 : CollatzResearch.WordTrace tailWord_1313607 prefixEnd_1313607 24981917855953601491531 := by
  unfold tailWord_1313607
  simp only [CollatzResearch.WordTrace]
  refine ⟨47911183352033660059595075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31940788901355773373063383 47911183352033660059595075)
  ·
    refine ⟨71866775028050490089392613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47911183352033660059595075 71866775028050490089392613)
    ·
      refine ⟨13475020317759466891761115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71866775028050490089392613 13475020317759466891761115)
      ·
        refine ⟨20212530476639200337641673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13475020317759466891761115 20212530476639200337641673)
        ·
          refine ⟨15159397857479400253231255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20212530476639200337641673 15159397857479400253231255)
          ·
            refine ⟨22739096786219100379846883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15159397857479400253231255 22739096786219100379846883)
            ·
              refine ⟨34108645179328650569770325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22739096786219100379846883 34108645179328650569770325)
              ·
                refine ⟨24981917855953601491531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 34108645179328650569770325 24981917855953601491531)
                ·
                  rfl

theorem cell23_1313607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 12].length) (baseStart_1313607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313607 prefixEnd_1313607 := by exact prefixLift 1313607
  have htrace : WordTrace (prefixWord ++ tailWord_1313607) baseStart_1313607 baseEnd_1313607 := by
    simpa [prefixWord, tailWord_1313607, baseEnd_1313607] using wordTrace_append hprefix tailTrace_1313607
  have hstable : (prefixWord ++ tailWord_1313607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313607).length < 2 ^ (prefixWord ++ tailWord_1313607).sum := by decide
  have hdescent : baseEnd_1313607 < baseStart_1313607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313618 : List Nat := [3, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2]
def baseStart_1313618 : Nat := 118140960795 + 1313618 * 2 ^ 59
def prefixEnd_1313618 : Nat := 4983230072969 + 3 ^ 40 * 1313618 * 2
def baseEnd_1313618 : Nat := 674517430397946697233787

theorem tailTrace_1313618 : CollatzResearch.WordTrace tailWord_1313618 prefixEnd_1313618 674517430397946697233787 := by
  unfold tailWord_1313618
  simp only [CollatzResearch.WordTrace]
  refine ⟨11977896138748452234561377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31941056369995872625497005 11977896138748452234561377)
  ·
    refine ⟨8983422104061339175921033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11977896138748452234561377 8983422104061339175921033)
    ·
      refine ⟨6737566578046004381940775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8983422104061339175921033 6737566578046004381940775)
      ·
        refine ⟨10106349867069006572911163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6737566578046004381940775 10106349867069006572911163)
        ·
          refine ⟨15159524800603509859366745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10106349867069006572911163 15159524800603509859366745)
          ·
            refine ⟨11369643600452632394525059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15159524800603509859366745 11369643600452632394525059)
            ·
              refine ⟨17054465400678948591787589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11369643600452632394525059 17054465400678948591787589)
              ·
                refine ⟨3197712262627302860960173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17054465400678948591787589 3197712262627302860960173)
                ·
                  refine ⟨1199142098485238572860065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3197712262627302860960173 1199142098485238572860065)
                  ·
                    refine ⟨899356573863928929645049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1199142098485238572860065 899356573863928929645049)
                    ·
                      refine ⟨674517430397946697233787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 899356573863928929645049 674517430397946697233787)
                      ·
                        rfl

theorem cell23_1313618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_1313618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313618 prefixEnd_1313618 := by exact prefixLift 1313618
  have htrace : WordTrace (prefixWord ++ tailWord_1313618) baseStart_1313618 baseEnd_1313618 := by
    simpa [prefixWord, tailWord_1313618, baseEnd_1313618] using wordTrace_append hprefix tailTrace_1313618
  have hstable : (prefixWord ++ tailWord_1313618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313618).length < 2 ^ (prefixWord ++ tailWord_1313618).sum := by decide
  have hdescent : baseEnd_1313618 < baseStart_1313618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313651 : List Nat := [1, 1, 1, 2, 2, 1, 6, 1, 4, 1, 3]
def baseStart_1313651 : Nat := 118140960795 + 1313651 * 2 ^ 59
def prefixEnd_1313651 : Nat := 4983230072969 + 3 ^ 40 * 1313651 * 2
def baseEnd_1313651 : Nat := 674534375259545068121135

theorem tailTrace_1313651 : CollatzResearch.WordTrace tailWord_1313651 prefixEnd_1313651 674534375259545068121135 := by
  unfold tailWord_1313651
  simp only [CollatzResearch.WordTrace]
  refine ⟨47912788163874255574196807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31941858775916170382797871 47912788163874255574196807)
  ·
    refine ⟨71869182245811383361295211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47912788163874255574196807 71869182245811383361295211)
    ·
      refine ⟨107803773368717075041942817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71869182245811383361295211 107803773368717075041942817)
      ·
        refine ⟨80852830026537806281457113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107803773368717075041942817 80852830026537806281457113)
        ·
          refine ⟨60639622519903354711092835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80852830026537806281457113 60639622519903354711092835)
          ·
            refine ⟨90959433779855032066639253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60639622519903354711092835 90959433779855032066639253)
            ·
              refine ⟨4263723458430704628123715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 90959433779855032066639253 4263723458430704628123715)
              ·
                refine ⟨6395585187646056942185573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4263723458430704628123715 6395585187646056942185573)
                ·
                  refine ⟨1199172222683635676659795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6395585187646056942185573 1199172222683635676659795)
                  ·
                    refine ⟨1798758334025453514989693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1199172222683635676659795 1798758334025453514989693)
                    ·
                      refine ⟨674534375259545068121135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1798758334025453514989693 674534375259545068121135)
                      ·
                        rfl

theorem cell23_1313651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 1, 4, 1, 3].length) (baseStart_1313651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313651 prefixEnd_1313651 := by exact prefixLift 1313651
  have htrace : WordTrace (prefixWord ++ tailWord_1313651) baseStart_1313651 baseEnd_1313651 := by
    simpa [prefixWord, tailWord_1313651, baseEnd_1313651] using wordTrace_append hprefix tailTrace_1313651
  have hstable : (prefixWord ++ tailWord_1313651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313651).length < 2 ^ (prefixWord ++ tailWord_1313651).sum := by decide
  have hdescent : baseEnd_1313651 < baseStart_1313651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313721 : List Nat := [1, 2, 1, 4, 2, 3, 1, 1, 2, 2, 4]
def baseStart_1313721 : Nat := 118140960795 + 1313721 * 2 ^ 59
def prefixEnd_1313721 : Nat := 4983230072969 + 3 ^ 40 * 1313721 * 2
def baseEnd_1313721 : Nat := 674570318905359794245813

theorem tailTrace_1313721 : CollatzResearch.WordTrace tailWord_1313721 prefixEnd_1313721 674570318905359794245813 := by
  unfold tailWord_1313721
  simp only [CollatzResearch.WordTrace]
  refine ⟨47915341273620657529245017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31943560849080438352830011 47915341273620657529245017)
  ·
    refine ⟨35936505955215493146933763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47915341273620657529245017 35936505955215493146933763)
    ·
      refine ⟨53904758932823239720400645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35936505955215493146933763 53904758932823239720400645)
      ·
        refine ⟨10107142299904357447575121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53904758932823239720400645 10107142299904357447575121)
        ·
          refine ⟨7580356724928268085681341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10107142299904357447575121 7580356724928268085681341)
          ·
            refine ⟨2842633771848100532130503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7580356724928268085681341 2842633771848100532130503)
            ·
              refine ⟨4263950657772150798195755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2842633771848100532130503 4263950657772150798195755)
              ·
                refine ⟨6395925986658226197293633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4263950657772150798195755 6395925986658226197293633)
                ·
                  refine ⟨4796944489993669647970225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6395925986658226197293633 4796944489993669647970225)
                  ·
                    refine ⟨3597708367495252235977669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4796944489993669647970225 3597708367495252235977669)
                    ·
                      refine ⟨674570318905359794245813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3597708367495252235977669 674570318905359794245813)
                      ·
                        rfl

theorem cell23_1313721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 3, 1, 1, 2, 2, 4].length) (baseStart_1313721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313721 prefixEnd_1313721 := by exact prefixLift 1313721
  have htrace : WordTrace (prefixWord ++ tailWord_1313721) baseStart_1313721 baseEnd_1313721 := by
    simpa [prefixWord, tailWord_1313721, baseEnd_1313721] using wordTrace_append hprefix tailTrace_1313721
  have hstable : (prefixWord ++ tailWord_1313721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313721).length < 2 ^ (prefixWord ++ tailWord_1313721).sum := by decide
  have hdescent : baseEnd_1313721 < baseStart_1313721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313725 : List Nat := [1, 4, 1, 2, 4, 1, 2, 1, 1, 4, 2]
def baseStart_1313725 : Nat := 118140960795 + 1313725 * 2 ^ 59
def prefixEnd_1313725 : Nat := 4983230072969 + 3 ^ 40 * 1313725 * 2
def baseEnd_1313725 : Nat := 674572372827977778595795

theorem tailTrace_1313725 : CollatzResearch.WordTrace tailWord_1313725 prefixEnd_1313725 674572372827977778595795 := by
  unfold tailWord_1313725
  simp only [CollatzResearch.WordTrace]
  refine ⟨47915487165606166212390629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31943658110404110808260419 47915487165606166212390629)
  ·
    refine ⟨8984153843551156164823243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47915487165606166212390629 8984153843551156164823243)
    ·
      refine ⟨13476230765326734247234865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8984153843551156164823243 13476230765326734247234865)
      ·
        refine ⟨10107173073995050685426149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13476230765326734247234865 10107173073995050685426149)
        ·
          refine ⟨1895094951374072003517403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10107173073995050685426149 1895094951374072003517403)
          ·
            refine ⟨2842642427061108005276105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1895094951374072003517403 2842642427061108005276105)
            ·
              refine ⟨2131981820295831003957079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2842642427061108005276105 2131981820295831003957079)
              ·
                refine ⟨3197972730443746505935619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2131981820295831003957079 3197972730443746505935619)
                ·
                  refine ⟨4796959095665619758903429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3197972730443746505935619 4796959095665619758903429)
                  ·
                    refine ⟨899429830437303704794393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4796959095665619758903429 899429830437303704794393)
                    ·
                      refine ⟨674572372827977778595795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 899429830437303704794393 674572372827977778595795)
                      ·
                        rfl

theorem cell23_1313725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_1313725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313725 prefixEnd_1313725 := by exact prefixLift 1313725
  have htrace : WordTrace (prefixWord ++ tailWord_1313725) baseStart_1313725 baseEnd_1313725 := by
    simpa [prefixWord, tailWord_1313725, baseEnd_1313725] using wordTrace_append hprefix tailTrace_1313725
  have hstable : (prefixWord ++ tailWord_1313725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313725).length < 2 ^ (prefixWord ++ tailWord_1313725).sum := by decide
  have hdescent : baseEnd_1313725 < baseStart_1313725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313748 : List Nat := [2, 4, 1, 2, 1, 2, 1, 5, 5]
def baseStart_1313748 : Nat := 118140960795 + 1313748 * 2 ^ 59
def prefixEnd_1313748 : Nat := 4983230072969 + 3 ^ 40 * 1313748 * 2
def baseEnd_1313748 : Nat := 74953798098114576512021

theorem tailTrace_1313748 : CollatzResearch.WordTrace tailWord_1313748 prefixEnd_1313748 74953798098114576512021 := by
  unfold tailWord_1313748
  simp only [CollatzResearch.WordTrace]
  refine ⟨23958163022261420570238949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31944217363015227426985265 23958163022261420570238949)
  ·
    refine ⟨4492155566674016356919803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23958163022261420570238949 4492155566674016356919803)
    ·
      refine ⟨6738233350011024535379705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4492155566674016356919803 6738233350011024535379705)
      ·
        refine ⟨5053675012508268401534779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6738233350011024535379705 5053675012508268401534779)
        ·
          refine ⟨7580512518762402602302169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5053675012508268401534779 7580512518762402602302169)
          ·
            refine ⟨5685384389071801951726627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7580512518762402602302169 5685384389071801951726627)
            ·
              refine ⟨8528076583607702927589941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5685384389071801951726627 8528076583607702927589941)
              ·
                refine ⟨799507179713222149461557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8528076583607702927589941 799507179713222149461557)
                ·
                  refine ⟨74953798098114576512021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 799507179713222149461557 74953798098114576512021)
                  ·
                    rfl

theorem cell23_1313748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_1313748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313748 prefixEnd_1313748 := by exact prefixLift 1313748
  have htrace : WordTrace (prefixWord ++ tailWord_1313748) baseStart_1313748 baseEnd_1313748 := by
    simpa [prefixWord, tailWord_1313748, baseEnd_1313748] using wordTrace_append hprefix tailTrace_1313748
  have hstable : (prefixWord ++ tailWord_1313748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313748).length < 2 ^ (prefixWord ++ tailWord_1313748).sum := by decide
  have hdescent : baseEnd_1313748 < baseStart_1313748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313751 : List Nat := [1, 1, 3, 2, 1, 1, 2, 2, 1, 7, 2]
def baseStart_1313751 : Nat := 118140960795 + 1313751 * 2 ^ 59
def prefixEnd_1313751 : Nat := 4983230072969 + 3 ^ 40 * 1313751 * 2
def baseEnd_1313751 : Nat := 674585723324994676870675

theorem tailTrace_1313751 : CollatzResearch.WordTrace tailWord_1313751 prefixEnd_1313751 674585723324994676870675 := by
  unfold tailWord_1313751
  simp only [CollatzResearch.WordTrace]
  refine ⟨47916435463511972652837107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31944290309007981768558071 47916435463511972652837107)
  ·
    refine ⟨71874653195267958979255661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47916435463511972652837107 71874653195267958979255661)
    ·
      refine ⟨26952994948225484617220873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71874653195267958979255661 26952994948225484617220873)
      ·
        refine ⟨20214746211169113462915655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26952994948225484617220873 20214746211169113462915655)
        ·
          refine ⟨30322119316753670194373483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20214746211169113462915655 30322119316753670194373483)
          ·
            refine ⟨45483178975130505291560225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30322119316753670194373483 45483178975130505291560225)
            ·
              refine ⟨34112384231347878968670169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45483178975130505291560225 34112384231347878968670169)
              ·
                refine ⟨25584288173510909226502627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34112384231347878968670169 25584288173510909226502627)
                ·
                  refine ⟨38376432260266363839753941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25584288173510909226502627 38376432260266363839753941)
                  ·
                    refine ⟨899447631099992902494233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38376432260266363839753941 899447631099992902494233)
                    ·
                      refine ⟨674585723324994676870675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 899447631099992902494233 674585723324994676870675)
                      ·
                        rfl

theorem cell23_1313751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 2, 1, 7, 2].length) (baseStart_1313751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313751 prefixEnd_1313751 := by exact prefixLift 1313751
  have htrace : WordTrace (prefixWord ++ tailWord_1313751) baseStart_1313751 baseEnd_1313751 := by
    simpa [prefixWord, tailWord_1313751, baseEnd_1313751] using wordTrace_append hprefix tailTrace_1313751
  have hstable : (prefixWord ++ tailWord_1313751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313751).length < 2 ^ (prefixWord ++ tailWord_1313751).sum := by decide
  have hdescent : baseEnd_1313751 < baseStart_1313751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313759 : List Nat := [1, 1, 2, 3, 6, 1, 1, 2, 2, 2, 2]
def baseStart_1313759 : Nat := 118140960795 + 1313759 * 2 ^ 59
def prefixEnd_1313759 : Nat := 4983230072969 + 3 ^ 40 * 1313759 * 2
def baseEnd_1313759 : Nat := 674589831170230645570639

theorem tailTrace_1313759 : CollatzResearch.WordTrace tailWord_1313759 prefixEnd_1313759 674589831170230645570639 := by
  unfold tailWord_1313759
  simp only [CollatzResearch.WordTrace]
  refine ⟨47916727247482990019128331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31944484831655326679418887 47916727247482990019128331)
  ·
    refine ⟨71875090871224485028692497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47916727247482990019128331 71875090871224485028692497)
    ·
      refine ⟨53906318153418363771519373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71875090871224485028692497 53906318153418363771519373)
      ·
        refine ⟨20214869307531886414319765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53906318153418363771519373 20214869307531886414319765)
        ·
          refine ⟨947571998790557175671239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 20214869307531886414319765 947571998790557175671239)
          ·
            refine ⟨1421357998185835763506859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 947571998790557175671239 1421357998185835763506859)
            ·
              refine ⟨2132036997278753645260289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1421357998185835763506859 2132036997278753645260289)
              ·
                refine ⟨1599027747959065233945217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2132036997278753645260289 1599027747959065233945217)
                ·
                  refine ⟨1199270810969298925458913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1599027747959065233945217 1199270810969298925458913)
                  ·
                    refine ⟨899453108226974194094185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1199270810969298925458913 899453108226974194094185)
                    ·
                      refine ⟨674589831170230645570639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 899453108226974194094185 674589831170230645570639)
                      ·
                        rfl

theorem cell23_1313759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 2, 2, 2].length) (baseStart_1313759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313759 prefixEnd_1313759 := by exact prefixLift 1313759
  have htrace : WordTrace (prefixWord ++ tailWord_1313759) baseStart_1313759 baseEnd_1313759 := by
    simpa [prefixWord, tailWord_1313759, baseEnd_1313759] using wordTrace_append hprefix tailTrace_1313759
  have hstable : (prefixWord ++ tailWord_1313759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313759).length < 2 ^ (prefixWord ++ tailWord_1313759).sum := by decide
  have hdescent : baseEnd_1313759 < baseStart_1313759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313801 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 6, 2, 3]
def baseStart_1313801 : Nat := 118140960795 + 1313801 * 2 ^ 59
def prefixEnd_1313801 : Nat := 4983230072969 + 3 ^ 40 * 1313801 * 2
def baseEnd_1313801 : Nat := 674611397357719481245445

theorem tailTrace_1313801 : CollatzResearch.WordTrace tailWord_1313801 prefixEnd_1313801 674611397357719481245445 := by
  unfold tailWord_1313801
  simp only [CollatzResearch.WordTrace]
  refine ⟨47918259113330831192157257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31945506075553887461438171 47918259113330831192157257)
  ·
    refine ⟨35938694334998123394117943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47918259113330831192157257 35938694334998123394117943)
    ·
      refine ⟨53908041502497185091176915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35938694334998123394117943 53908041502497185091176915)
      ·
        refine ⟨80862062253745777636765373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53908041502497185091176915 80862062253745777636765373)
        ·
          refine ⟨30323273345154666613787015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80862062253745777636765373 30323273345154666613787015)
          ·
            refine ⟨45484910017731999920680523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30323273345154666613787015 45484910017731999920680523)
            ·
              refine ⟨68227365026597999881020785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45484910017731999920680523 68227365026597999881020785)
              ·
                refine ⟨51170523769948499910765589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68227365026597999881020785 51170523769948499910765589)
                ·
                  refine ⟨2398618301716335933317137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51170523769948499910765589 2398618301716335933317137)
                  ·
                    refine ⟨1798963726287251949987853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2398618301716335933317137 1798963726287251949987853)
                    ·
                      refine ⟨674611397357719481245445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1798963726287251949987853 674611397357719481245445)
                      ·
                        rfl

theorem cell23_1313801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 6, 2, 3].length) (baseStart_1313801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313801 prefixEnd_1313801 := by exact prefixLift 1313801
  have htrace : WordTrace (prefixWord ++ tailWord_1313801) baseStart_1313801 baseEnd_1313801 := by
    simpa [prefixWord, tailWord_1313801, baseEnd_1313801] using wordTrace_append hprefix tailTrace_1313801
  have hstable : (prefixWord ++ tailWord_1313801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313801).length < 2 ^ (prefixWord ++ tailWord_1313801).sum := by decide
  have hdescent : baseEnd_1313801 < baseStart_1313801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313818 : List Nat := [3, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3]
def baseStart_1313818 : Nat := 118140960795 + 1313818 * 2 ^ 59
def prefixEnd_1313818 : Nat := 4983230072969 + 3 ^ 40 * 1313818 * 2
def baseEnd_1313818 : Nat := 674620126528845914732867

theorem tailTrace_1313818 : CollatzResearch.WordTrace tailWord_1313818 prefixEnd_1313818 674620126528845914732867 := by
  unfold tailWord_1313818
  simp only [CollatzResearch.WordTrace]
  refine ⟨11979719788567310773881527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31945919436179495397017405 11979719788567310773881527)
  ·
    refine ⟨17969579682850966160822291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11979719788567310773881527 17969579682850966160822291)
    ·
      refine ⟨26954369524276449241233437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17969579682850966160822291 26954369524276449241233437)
      ·
        refine ⟨10107888571603668465462539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26954369524276449241233437 10107888571603668465462539)
        ·
          refine ⟨15161832857405502698193809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10107888571603668465462539 15161832857405502698193809)
          ·
            refine ⟨11371374643054127023645357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15161832857405502698193809 11371374643054127023645357)
            ·
              refine ⟨4264265491145297633867009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11371374643054127023645357 4264265491145297633867009)
              ·
                refine ⟨3198199118358973225400257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4264265491145297633867009 3198199118358973225400257)
                ·
                  refine ⟨2398649338769229919050193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3198199118358973225400257 2398649338769229919050193)
                  ·
                    refine ⟨1798987004076922439287645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2398649338769229919050193 1798987004076922439287645)
                    ·
                      refine ⟨674620126528845914732867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1798987004076922439287645 674620126528845914732867)
                      ·
                        rfl

theorem cell23_1313818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 2, 2, 3].length) (baseStart_1313818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313818 prefixEnd_1313818 := by exact prefixLift 1313818
  have htrace : WordTrace (prefixWord ++ tailWord_1313818) baseStart_1313818 baseEnd_1313818 := by
    simpa [prefixWord, tailWord_1313818, baseEnd_1313818] using wordTrace_append hprefix tailTrace_1313818
  have hstable : (prefixWord ++ tailWord_1313818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313818).length < 2 ^ (prefixWord ++ tailWord_1313818).sum := by decide
  have hdescent : baseEnd_1313818 < baseStart_1313818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313825 : List Nat := [1, 2, 3, 2, 3, 3, 1, 1, 3, 4]
def baseStart_1313825 : Nat := 118140960795 + 1313825 * 2 ^ 59
def prefixEnd_1313825 : Nat := 4983230072969 + 3 ^ 40 * 1313825 * 2
def baseEnd_1313825 : Nat := 224874573631142462448445

theorem tailTrace_1313825 : CollatzResearch.WordTrace tailWord_1313825 prefixEnd_1313825 224874573631142462448445 := by
  unfold tailWord_1313825
  simp only [CollatzResearch.WordTrace]
  refine ⟨47919134465243883291030929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31946089643495922194020619 47919134465243883291030929)
  ·
    refine ⟨35939350848932912468273197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47919134465243883291030929 35939350848932912468273197)
    ·
      refine ⟨13477256568349842175602449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35939350848932912468273197 13477256568349842175602449)
      ·
        refine ⟨10107942426262381631701837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13477256568349842175602449 10107942426262381631701837)
        ·
          refine ⟨3790478409848393111888189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10107942426262381631701837 3790478409848393111888189)
          ·
            refine ⟨1421429403693147416958071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3790478409848393111888189 1421429403693147416958071)
            ·
              refine ⟨2132144105539721125437107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1421429403693147416958071 2132144105539721125437107)
              ·
                refine ⟨3198216158309581688155661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2132144105539721125437107 3198216158309581688155661)
                ·
                  refine ⟨1199331059366093133058373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3198216158309581688155661 1199331059366093133058373)
                  ·
                    refine ⟨224874573631142462448445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1199331059366093133058373 224874573631142462448445)
                    ·
                      rfl

theorem cell23_1313825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_1313825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313825 prefixEnd_1313825 := by exact prefixLift 1313825
  have htrace : WordTrace (prefixWord ++ tailWord_1313825) baseStart_1313825 baseEnd_1313825 := by
    simpa [prefixWord, tailWord_1313825, baseEnd_1313825] using wordTrace_append hprefix tailTrace_1313825
  have hstable : (prefixWord ++ tailWord_1313825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313825).length < 2 ^ (prefixWord ++ tailWord_1313825).sum := by decide
  have hdescent : baseEnd_1313825 < baseStart_1313825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313838 : List Nat := [4, 1, 3, 1, 1, 1, 3, 3, 6]
def baseStart_1313838 : Nat := 118140960795 + 1313838 * 2 ^ 59
def prefixEnd_1313838 : Nat := 4983230072969 + 3 ^ 40 * 1313838 * 2
def baseEnd_1313838 : Nat := 74958932904659537386975

theorem tailTrace_1313838 : CollatzResearch.WordTrace tailWord_1313838 prefixEnd_1313838 74958932904659537386975 := by
  unfold tailWord_1313838
  simp only [CollatzResearch.WordTrace]
  refine ⟨5989951076774598313906771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31946405742797857674169445 5989951076774598313906771)
  ·
    refine ⟨8984926615161897470860157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5989951076774598313906771 8984926615161897470860157)
    ·
      refine ⟨3369347480685711551572559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8984926615161897470860157 3369347480685711551572559)
      ·
        refine ⟨5054021221028567327358839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3369347480685711551572559 5054021221028567327358839)
        ·
          refine ⟨7581031831542850991038259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5054021221028567327358839 7581031831542850991038259)
          ·
            refine ⟨11371547747314276486557389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7581031831542850991038259 11371547747314276486557389)
            ·
              refine ⟨4264330405242853682459021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11371547747314276486557389 4264330405242853682459021)
              ·
                refine ⟨1599123901966070130922133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4264330405242853682459021 1599123901966070130922133)
                ·
                  refine ⟨74958932904659537386975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1599123901966070130922133 74958932904659537386975)
                  ·
                    rfl

theorem cell23_1313838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_1313838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313838 prefixEnd_1313838 := by exact prefixLift 1313838
  have htrace : WordTrace (prefixWord ++ tailWord_1313838) baseStart_1313838 baseEnd_1313838 := by
    simpa [prefixWord, tailWord_1313838, baseEnd_1313838] using wordTrace_append hprefix tailTrace_1313838
  have hstable : (prefixWord ++ tailWord_1313838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313838).length < 2 ^ (prefixWord ++ tailWord_1313838).sum := by decide
  have hdescent : baseEnd_1313838 < baseStart_1313838 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313871 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 4]
def baseStart_1313871 : Nat := 118140960795 + 1313871 * 2 ^ 59
def prefixEnd_1313871 : Nat := 4983230072969 + 3 ^ 40 * 1313871 * 2
def baseEnd_1313871 : Nat := 674647341003534207370123

theorem tailTrace_1313871 : CollatzResearch.WordTrace tailWord_1313871 prefixEnd_1313871 674647341003534207370123 := by
  unfold tailWord_1313871
  simp only [CollatzResearch.WordTrace]
  refine ⟨47920812223077233147205467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31947208148718155431470311 47920812223077233147205467)
  ·
    refine ⟨71881218334615849720808201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47920812223077233147205467 71881218334615849720808201)
    ·
      refine ⟨53910913750961887290606151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71881218334615849720808201 53910913750961887290606151)
      ·
        refine ⟨80866370626442830935909227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53910913750961887290606151 80866370626442830935909227)
        ·
          refine ⟨121299555939664246403863841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80866370626442830935909227 121299555939664246403863841)
          ·
            refine ⟨90974666954748184802897881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121299555939664246403863841 90974666954748184802897881)
            ·
              refine ⟨68231000216061138602173411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90974666954748184802897881 68231000216061138602173411)
              ·
                refine ⟨102346500324091707903260117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68231000216061138602173411 102346500324091707903260117)
                ·
                  refine ⟨2398746101345899403982659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 102346500324091707903260117 2398746101345899403982659)
                  ·
                    refine ⟨3598119152018849105973989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2398746101345899403982659 3598119152018849105973989)
                    ·
                      refine ⟨674647341003534207370123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3598119152018849105973989 674647341003534207370123)
                      ·
                        rfl

theorem cell23_1313871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 4].length) (baseStart_1313871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313871 prefixEnd_1313871 := by exact prefixLift 1313871
  have htrace : WordTrace (prefixWord ++ tailWord_1313871) baseStart_1313871 baseEnd_1313871 := by
    simpa [prefixWord, tailWord_1313871, baseEnd_1313871] using wordTrace_append hprefix tailTrace_1313871
  have hstable : (prefixWord ++ tailWord_1313871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313871).length < 2 ^ (prefixWord ++ tailWord_1313871).sum := by decide
  have hdescent : baseEnd_1313871 < baseStart_1313871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313891 : List Nat := [1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 5]
def baseStart_1313891 : Nat := 118140960795 + 1313891 * 2 ^ 59
def prefixEnd_1313891 : Nat := 4983230072969 + 3 ^ 40 * 1313891 * 2
def baseEnd_1313891 : Nat := 674657610616624129120031

theorem tailTrace_1313891 : CollatzResearch.WordTrace tailWord_1313891 prefixEnd_1313891 674657610616624129120031 := by
  unfold tailWord_1313891
  simp only [CollatzResearch.WordTrace]
  refine ⟨47921541683004776562933527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31947694455336517708622351 47921541683004776562933527)
  ·
    refine ⟨71882312524507164844400291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47921541683004776562933527 71882312524507164844400291)
    ·
      refine ⟨107823468786760747266600437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71882312524507164844400291 107823468786760747266600437)
      ·
        refine ⟨10108450198758820056243791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107823468786760747266600437 10108450198758820056243791)
        ·
          refine ⟨15162675298138230084365687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10108450198758820056243791 15162675298138230084365687)
          ·
            refine ⟨22744012947207345126548531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15162675298138230084365687 22744012947207345126548531)
            ·
              refine ⟨34116019420811017689822797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22744012947207345126548531 34116019420811017689822797)
              ·
                refine ⟨12793507282804131633683549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34116019420811017689822797 12793507282804131633683549)
                ·
                  refine ⟨4797565231051549362631331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12793507282804131633683549 4797565231051549362631331)
                  ·
                    refine ⟨7196347846577324043946997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4797565231051549362631331 7196347846577324043946997)
                    ·
                      refine ⟨674657610616624129120031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7196347846577324043946997 674657610616624129120031)
                      ·
                        rfl

theorem cell23_1313891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_1313891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313891 prefixEnd_1313891 := by exact prefixLift 1313891
  have htrace : WordTrace (prefixWord ++ tailWord_1313891) baseStart_1313891 baseEnd_1313891 := by
    simpa [prefixWord, tailWord_1313891, baseEnd_1313891] using wordTrace_append hprefix tailTrace_1313891
  have hstable : (prefixWord ++ tailWord_1313891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313891).length < 2 ^ (prefixWord ++ tailWord_1313891).sum := by decide
  have hdescent : baseEnd_1313891 < baseStart_1313891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313898 : List Nat := [3, 1, 3, 2, 2, 1, 1, 3, 1, 6]
def baseStart_1313898 : Nat := 118140960795 + 1313898 * 2 ^ 59
def prefixEnd_1313898 : Nat := 4983230072969 + 3 ^ 40 * 1313898 * 2
def baseEnd_1313898 : Nat := 224887068327068533910833

theorem tailTrace_1313898 : CollatzResearch.WordTrace tailWord_1313898 prefixEnd_1313898 224887068327068533910833 := by
  unfold tailWord_1313898
  simp only [CollatzResearch.WordTrace]
  refine ⟨11980449248494854189609587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31947864662652944505625565 11980449248494854189609587)
  ·
    refine ⟨17970673872742281284414381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11980449248494854189609587 17970673872742281284414381)
    ·
      refine ⟨6739002702278355481655393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17970673872742281284414381 6739002702278355481655393)
      ·
        refine ⟨5054252026708766611241545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6739002702278355481655393 5054252026708766611241545)
        ·
          refine ⟨3790689020031574958431159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5054252026708766611241545 3790689020031574958431159)
          ·
            refine ⟨5686033530047362437646739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3790689020031574958431159 5686033530047362437646739)
            ·
              refine ⟨8529050295071043656470109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5686033530047362437646739 8529050295071043656470109)
              ·
                refine ⟨3198393860651641371176291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8529050295071043656470109 3198393860651641371176291)
                ·
                  refine ⟨4797590790977462056764437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3198393860651641371176291 4797590790977462056764437)
                  ·
                    refine ⟨224887068327068533910833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4797590790977462056764437 224887068327068533910833)
                    ·
                      rfl

theorem cell23_1313898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 3, 1, 6].length) (baseStart_1313898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313898 prefixEnd_1313898 := by exact prefixLift 1313898
  have htrace : WordTrace (prefixWord ++ tailWord_1313898) baseStart_1313898 baseEnd_1313898 := by
    simpa [prefixWord, tailWord_1313898, baseEnd_1313898] using wordTrace_append hprefix tailTrace_1313898
  have hstable : (prefixWord ++ tailWord_1313898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313898).length < 2 ^ (prefixWord ++ tailWord_1313898).sum := by decide
  have hdescent : baseEnd_1313898 < baseStart_1313898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313928 : List Nat := [2, 1, 3, 4, 2, 1, 10]
def baseStart_1313928 : Nat := 118140960795 + 1313928 * 2 ^ 59
def prefixEnd_1313928 : Nat := 4983230072969 + 3 ^ 40 * 1313928 * 2
def baseEnd_1313928 : Nat := 8329340856800499806881

theorem tailTrace_1313928 : CollatzResearch.WordTrace tailWord_1313928 prefixEnd_1313928 8329340856800499806881 := by
  unfold tailWord_1313928
  simp only [CollatzResearch.WordTrace]
  refine ⟨23961445591935365941015219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31948594122580487921353625 23961445591935365941015219)
  ·
    refine ⟨35942168387903048911522829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23961445591935365941015219 35942168387903048911522829)
    ·
      refine ⟨13478313145463643341821061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35942168387903048911522829 13478313145463643341821061)
      ·
        refine ⟨2527183714774433126591449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13478313145463643341821061 2527183714774433126591449)
        ·
          refine ⟨1895387786080824844943587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2527183714774433126591449 1895387786080824844943587)
          ·
            refine ⟨2843081679121237267415381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1895387786080824844943587 2843081679121237267415381)
            ·
              refine ⟨8329340856800499806881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2843081679121237267415381 8329340856800499806881)
              ·
                rfl

theorem cell23_1313928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 10].length) (baseStart_1313928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313928 prefixEnd_1313928 := by exact prefixLift 1313928
  have htrace : WordTrace (prefixWord ++ tailWord_1313928) baseStart_1313928 baseEnd_1313928 := by
    simpa [prefixWord, tailWord_1313928, baseEnd_1313928] using wordTrace_append hprefix tailTrace_1313928
  have hstable : (prefixWord ++ tailWord_1313928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313928).length < 2 ^ (prefixWord ++ tailWord_1313928).sum := by decide
  have hdescent : baseEnd_1313928 < baseStart_1313928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313941 : List Nat := [1, 3, 2, 1, 1, 1, 2, 3, 2, 7]
def baseStart_1313941 : Nat := 118140960795 + 1313941 * 2 ^ 59
def prefixEnd_1313941 : Nat := 4983230072969 + 3 ^ 40 * 1313941 * 2
def baseEnd_1313941 : Nat := 224894428216449644498267

theorem tailTrace_1313941 : CollatzResearch.WordTrace tailWord_1313941 prefixEnd_1313941 224894428216449644498267 := by
  unfold tailWord_1313941
  simp only [CollatzResearch.WordTrace]
  refine ⟨47923365332823635102253677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31948910221882423401502451 47923365332823635102253677)
  ·
    refine ⟨17971261999808863163345129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47923365332823635102253677 17971261999808863163345129)
    ·
      refine ⟨13478446499856647372508847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17971261999808863163345129 13478446499856647372508847)
      ·
        refine ⟨20217669749784971058763271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13478446499856647372508847 20217669749784971058763271)
        ·
          refine ⟨30326504624677456588144907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20217669749784971058763271 30326504624677456588144907)
          ·
            refine ⟨45489756937016184882217361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30326504624677456588144907 45489756937016184882217361)
            ·
              refine ⟨34117317702762138661663021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45489756937016184882217361 34117317702762138661663021)
              ·
                refine ⟨12793994138535801998123633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34117317702762138661663021 12793994138535801998123633)
                ·
                  refine ⟨9595495603901851498592725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12793994138535801998123633 9595495603901851498592725)
                  ·
                    refine ⟨224894428216449644498267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9595495603901851498592725 224894428216449644498267)
                    ·
                      rfl

theorem cell23_1313941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_1313941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313941 prefixEnd_1313941 := by exact prefixLift 1313941
  have htrace : WordTrace (prefixWord ++ tailWord_1313941) baseStart_1313941 baseEnd_1313941 := by
    simpa [prefixWord, tailWord_1313941, baseEnd_1313941] using wordTrace_append hprefix tailTrace_1313941
  have hstable : (prefixWord ++ tailWord_1313941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313941).length < 2 ^ (prefixWord ++ tailWord_1313941).sum := by decide
  have hdescent : baseEnd_1313941 < baseStart_1313941 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313955 : List Nat := [1, 1, 1, 4, 1, 1, 1, 7, 2, 1, 3]
def baseStart_1313955 : Nat := 118140960795 + 1313955 * 2 ^ 59
def prefixEnd_1313955 : Nat := 4983230072969 + 3 ^ 40 * 1313955 * 2
def baseEnd_1313955 : Nat := 674690473378511878719737

theorem tailTrace_1313955 : CollatzResearch.WordTrace tailWord_1313955 prefixEnd_1313955 674690473378511878719737 := by
  unfold tailWord_1313955
  simp only [CollatzResearch.WordTrace]
  refine ⟨47923875954772915493263319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31949250636515276995508879 47923875954772915493263319)
  ·
    refine ⟨71885813932159373239894979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47923875954772915493263319 71885813932159373239894979)
    ·
      refine ⟨107828720898239059859842469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71885813932159373239894979 107828720898239059859842469)
      ·
        refine ⟨20217885168419823723720463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107828720898239059859842469 20217885168419823723720463)
        ·
          refine ⟨30326827752629735585580695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20217885168419823723720463 30326827752629735585580695)
          ·
            refine ⟨45490241628944603378371043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30326827752629735585580695 45490241628944603378371043)
            ·
              refine ⟨68235362443416905067556565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45490241628944603378371043 68235362443416905067556565)
              ·
                refine ⟨1599266307267583712520857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 68235362443416905067556565 1599266307267583712520857)
                ·
                  refine ⟨1199449730450687784390643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1599266307267583712520857 1199449730450687784390643)
                  ·
                    refine ⟨1799174595676031676585965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1199449730450687784390643 1799174595676031676585965)
                    ·
                      refine ⟨674690473378511878719737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1799174595676031676585965 674690473378511878719737)
                      ·
                        rfl

theorem cell23_1313955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 7, 2, 1, 3].length) (baseStart_1313955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313955 prefixEnd_1313955 := by exact prefixLift 1313955
  have htrace : WordTrace (prefixWord ++ tailWord_1313955) baseStart_1313955 baseEnd_1313955 := by
    simpa [prefixWord, tailWord_1313955, baseEnd_1313955] using wordTrace_append hprefix tailTrace_1313955
  have hstable : (prefixWord ++ tailWord_1313955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313955).length < 2 ^ (prefixWord ++ tailWord_1313955).sum := by decide
  have hdescent : baseEnd_1313955 < baseStart_1313955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313962 : List Nat := [3, 1, 5, 1, 1, 3, 2, 7]
def baseStart_1313962 : Nat := 118140960795 + 1313962 * 2 ^ 59
def prefixEnd_1313962 : Nat := 4983230072969 + 3 ^ 40 * 1313962 * 2
def baseEnd_1313962 : Nat := 24988669175670124123415

theorem tailTrace_1313962 : CollatzResearch.WordTrace tailWord_1313962 prefixEnd_1313962 24988669175670124123415 := by
  unfold tailWord_1313962
  simp only [CollatzResearch.WordTrace]
  refine ⟨11981032816436888922192035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31949420843831703792512093 11981032816436888922192035)
  ·
    refine ⟨17971549224655333383288053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11981032816436888922192035 17971549224655333383288053)
    ·
      refine ⟨1684832739811437504683255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17971549224655333383288053 1684832739811437504683255)
      ·
        refine ⟨2527249109717156257024883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1684832739811437504683255 2527249109717156257024883)
        ·
          refine ⟨3790873664575734385537325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2527249109717156257024883 3790873664575734385537325)
          ·
            refine ⟨1421577624215900394576497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3790873664575734385537325 1421577624215900394576497)
            ·
              refine ⟨1066183218161925295932373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1421577624215900394576497 1066183218161925295932373)
              ·
                refine ⟨24988669175670124123415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1066183218161925295932373 24988669175670124123415)
                ·
                  rfl

theorem cell23_1313962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 3, 2, 7].length) (baseStart_1313962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313962 prefixEnd_1313962 := by exact prefixLift 1313962
  have htrace : WordTrace (prefixWord ++ tailWord_1313962) baseStart_1313962 baseEnd_1313962 := by
    simpa [prefixWord, tailWord_1313962, baseEnd_1313962] using wordTrace_append hprefix tailTrace_1313962
  have hstable : (prefixWord ++ tailWord_1313962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313962).length < 2 ^ (prefixWord ++ tailWord_1313962).sum := by decide
  have hdescent : baseEnd_1313962 < baseStart_1313962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313971 : List Nat := [1, 1, 1, 2, 3, 2, 2, 2, 1, 8]
def baseStart_1313971 : Nat := 118140960795 + 1313971 * 2 ^ 59
def prefixEnd_1313971 : Nat := 4983230072969 + 3 ^ 40 * 1313971 * 2
def baseEnd_1313971 : Nat := 224899563022994605373221

theorem tailTrace_1313971 : CollatzResearch.WordTrace tailWord_1313971 prefixEnd_1313971 224899563022994605373221 := by
  unfold tailWord_1313971
  simp only [CollatzResearch.WordTrace]
  refine ⟨47924459522714950225845767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31949639681809966817230511 47924459522714950225845767)
  ·
    refine ⟨71886689284072425338768651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47924459522714950225845767 71886689284072425338768651)
    ·
      refine ⟨107830033926108638008152977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71886689284072425338768651 107830033926108638008152977)
      ·
        refine ⟨80872525444581478506114733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107830033926108638008152977 80872525444581478506114733)
        ·
          refine ⟨30327197041718054439793025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80872525444581478506114733 30327197041718054439793025)
          ·
            refine ⟨22745397781288540829844769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30327197041718054439793025 22745397781288540829844769)
            ·
              refine ⟨17059048335966405622383577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22745397781288540829844769 17059048335966405622383577)
              ·
                refine ⟨12794286251974804216787683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17059048335966405622383577 12794286251974804216787683)
                ·
                  refine ⟨19191429377962206325181525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12794286251974804216787683 19191429377962206325181525)
                  ·
                    refine ⟨224899563022994605373221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19191429377962206325181525 224899563022994605373221)
                    ·
                      rfl

theorem cell23_1313971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 2, 1, 8].length) (baseStart_1313971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313971 prefixEnd_1313971 := by exact prefixLift 1313971
  have htrace : WordTrace (prefixWord ++ tailWord_1313971) baseStart_1313971 baseEnd_1313971 := by
    simpa [prefixWord, tailWord_1313971, baseEnd_1313971] using wordTrace_append hprefix tailTrace_1313971
  have hstable : (prefixWord ++ tailWord_1313971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313971).length < 2 ^ (prefixWord ++ tailWord_1313971).sum := by decide
  have hdescent : baseEnd_1313971 < baseStart_1313971 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1313990 : List Nat := [6, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2]
def baseStart_1313990 : Nat := 118140960795 + 1313990 * 2 ^ 59
def prefixEnd_1313990 : Nat := 4983230072969 + 3 ^ 40 * 1313990 * 2
def baseEnd_1313990 : Nat := 674708445201419241782077

theorem tailTrace_1313990 : CollatzResearch.WordTrace tailWord_1313990 prefixEnd_1313990 674708445201419241782077 := by
  unfold tailWord_1313990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1497661015926441139712107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 31950101673097410980524949 1497661015926441139712107)
  ·
    refine ⟨2246491523889661709568161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1497661015926441139712107 2246491523889661709568161)
    ·
      refine ⟨1684868642917246282176121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2246491523889661709568161 1684868642917246282176121)
      ·
        refine ⟨1263651482187934711632091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1684868642917246282176121 1263651482187934711632091)
        ·
          refine ⟨1895477223281902067448137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1263651482187934711632091 1895477223281902067448137)
          ·
            refine ⟨1421607917461426550586103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1895477223281902067448137 1421607917461426550586103)
            ·
              refine ⟨2132411876192139825879155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1421607917461426550586103 2132411876192139825879155)
              ·
                refine ⟨3198617814288209738818733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2132411876192139825879155 3198617814288209738818733)
                ·
                  refine ⟨1199481680358078652057025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3198617814288209738818733 1199481680358078652057025)
                  ·
                    refine ⟨899611260268558989042769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1199481680358078652057025 899611260268558989042769)
                    ·
                      refine ⟨674708445201419241782077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 899611260268558989042769 674708445201419241782077)
                      ·
                        rfl

theorem cell23_1313990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_1313990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1313990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1313990 prefixEnd_1313990 := by exact prefixLift 1313990
  have htrace : WordTrace (prefixWord ++ tailWord_1313990) baseStart_1313990 baseEnd_1313990 := by
    simpa [prefixWord, tailWord_1313990, baseEnd_1313990] using wordTrace_append hprefix tailTrace_1313990
  have hstable : (prefixWord ++ tailWord_1313990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1313990).length < 2 ^ (prefixWord ++ tailWord_1313990).sum := by decide
  have hdescent : baseEnd_1313990 < baseStart_1313990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1313990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314006 : List Nat := [5, 2, 1, 2, 2, 1, 1, 3, 2, 1, 3]
def baseStart_1314006 : Nat := 118140960795 + 1314006 * 2 ^ 59
def prefixEnd_1314006 : Nat := 4983230072969 + 3 ^ 40 * 1314006 * 2
def baseEnd_1314006 : Nat := 674716660891891179182003

theorem tailTrace_1314006 : CollatzResearch.WordTrace tailWord_1314006 prefixEnd_1314006 674716660891891179182003 := by
  unfold tailWord_1314006
  simp only [CollatzResearch.WordTrace]
  refine ⟨2995358504849259450210617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31950490718392100802246581 2995358504849259450210617)
  ·
    refine ⟨2246518878636944587657963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2995358504849259450210617 2246518878636944587657963)
    ·
      refine ⟨3369778317955416881486945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2246518878636944587657963 3369778317955416881486945)
      ·
        refine ⟨2527333738466562661115209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3369778317955416881486945 2527333738466562661115209)
        ·
          refine ⟨1895500303849921995836407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2527333738466562661115209 1895500303849921995836407)
          ·
            refine ⟨2843250455774882993754611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1895500303849921995836407 2843250455774882993754611)
            ·
              refine ⟨4264875683662324490631917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2843250455774882993754611 4264875683662324490631917)
              ·
                refine ⟨1599328381373371683986969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4264875683662324490631917 1599328381373371683986969)
                ·
                  refine ⟨1199496286030028762990227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1599328381373371683986969 1199496286030028762990227)
                  ·
                    refine ⟨1799244429045043144485341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1199496286030028762990227 1799244429045043144485341)
                    ·
                      refine ⟨674716660891891179182003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1799244429045043144485341 674716660891891179182003)
                      ·
                        rfl

theorem cell23_1314006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_1314006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314006 prefixEnd_1314006 := by exact prefixLift 1314006
  have htrace : WordTrace (prefixWord ++ tailWord_1314006) baseStart_1314006 baseEnd_1314006 := by
    simpa [prefixWord, tailWord_1314006, baseEnd_1314006] using wordTrace_append hprefix tailTrace_1314006
  have hstable : (prefixWord ++ tailWord_1314006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314006).length < 2 ^ (prefixWord ++ tailWord_1314006).sum := by decide
  have hdescent : baseEnd_1314006 < baseStart_1314006 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314011 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 7]
def baseStart_1314011 : Nat := 118140960795 + 1314011 * 2 ^ 59
def prefixEnd_1314011 : Nat := 4983230072969 + 3 ^ 40 * 1314011 * 2
def baseEnd_1314011 : Nat := 674719228295163659619479

theorem tailTrace_1314011 : CollatzResearch.WordTrace tailWord_1314011 prefixEnd_1314011 674719228295163659619479 := by
  unfold tailWord_1314011
  simp only [CollatzResearch.WordTrace]
  refine ⟨47925918442570037057301887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31950612295046691371534591 47925918442570037057301887)
  ·
    refine ⟨71888877663855055585952831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47925918442570037057301887 71888877663855055585952831)
    ·
      refine ⟨107833316495782583378929247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71888877663855055585952831 107833316495782583378929247)
      ·
        refine ⟨161749974743673875068393871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107833316495782583378929247 161749974743673875068393871)
        ·
          refine ⟨242624962115510812602590807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161749974743673875068393871 242624962115510812602590807)
          ·
            refine ⟨363937443173266218903886211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242624962115510812602590807 363937443173266218903886211)
            ·
              refine ⟨545906164759899328355829317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 363937443173266218903886211 545906164759899328355829317)
              ·
                refine ⟨102357405892481124066717997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 545906164759899328355829317 102357405892481124066717997)
                ·
                  refine ⟨38384027209680421525019249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102357405892481124066717997 38384027209680421525019249)
                  ·
                    refine ⟨28788020407260316143764437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 38384027209680421525019249 28788020407260316143764437)
                    ·
                      refine ⟨674719228295163659619479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28788020407260316143764437 674719228295163659619479)
                      ·
                        rfl

theorem cell23_1314011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 2, 7].length) (baseStart_1314011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314011 prefixEnd_1314011 := by exact prefixLift 1314011
  have htrace : WordTrace (prefixWord ++ tailWord_1314011) baseStart_1314011 baseEnd_1314011 := by
    simpa [prefixWord, tailWord_1314011, baseEnd_1314011] using wordTrace_append hprefix tailTrace_1314011
  have hstable : (prefixWord ++ tailWord_1314011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314011).length < 2 ^ (prefixWord ++ tailWord_1314011).sum := by decide
  have hdescent : baseEnd_1314011 < baseStart_1314011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314046 : List Nat := [4, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2]
def baseStart_1314046 : Nat := 118140960795 + 1314046 * 2 ^ 59
def prefixEnd_1314046 : Nat := 4983230072969 + 3 ^ 40 * 1314046 * 2
def baseEnd_1314046 : Nat := 674737200118071022681819

theorem tailTrace_1314046 : CollatzResearch.WordTrace tailWord_1314046 prefixEnd_1314046 674737200118071022681819 := by
  unfold tailWord_1314046
  simp only [CollatzResearch.WordTrace]
  refine ⟨5990899374680404754353249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31951463331628825356550661 5990899374680404754353249)
  ·
    refine ⟨4493174531010303565764937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5990899374680404754353249 4493174531010303565764937)
    ·
      refine ⟨3369880898257727674323703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4493174531010303565764937 3369880898257727674323703)
      ·
        refine ⟨5054821347386591511485555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3369880898257727674323703 5054821347386591511485555)
        ·
          refine ⟨7582232021079887267228333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5054821347386591511485555 7582232021079887267228333)
          ·
            refine ⟨2843337007904957725210625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7582232021079887267228333 2843337007904957725210625)
            ·
              refine ⟨2132502755928718293907969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2843337007904957725210625 2132502755928718293907969)
              ·
                refine ⟨1599377066946538720430977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2132502755928718293907969 1599377066946538720430977)
                ·
                  refine ⟨1199532800209904040323233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1599377066946538720430977 1199532800209904040323233)
                  ·
                    refine ⟨899649600157428030242425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1199532800209904040323233 899649600157428030242425)
                    ·
                      refine ⟨674737200118071022681819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 899649600157428030242425 674737200118071022681819)
                      ·
                        rfl

theorem cell23_1314046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_1314046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314046 prefixEnd_1314046 := by exact prefixLift 1314046
  have htrace : WordTrace (prefixWord ++ tailWord_1314046) baseStart_1314046 baseEnd_1314046 := by
    simpa [prefixWord, tailWord_1314046, baseEnd_1314046] using wordTrace_append hprefix tailTrace_1314046
  have hstable : (prefixWord ++ tailWord_1314046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314046).length < 2 ^ (prefixWord ++ tailWord_1314046).sum := by decide
  have hdescent : baseEnd_1314046 < baseStart_1314046 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314052 : List Nat := [2, 3, 2, 2, 2, 2, 1, 4, 5]
def baseStart_1314052 : Nat := 118140960795 + 1314052 * 2 ^ 59
def prefixEnd_1314052 : Nat := 4983230072969 + 3 ^ 40 * 1314052 * 2
def baseEnd_1314052 : Nat := 74971142333555333245199

theorem tailTrace_1314052 : CollatzResearch.WordTrace tailWord_1314052 prefixEnd_1314052 74971142333555333245199 := by
  unfold tailWord_1314052
  simp only [CollatzResearch.WordTrace]
  refine ⟨23963706917710750529772205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31951609223614334039696273 23963706917710750529772205)
  ·
    refine ⟨8986390094141531448664577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23963706917710750529772205 8986390094141531448664577)
    ·
      refine ⟨6739792570606148586498433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8986390094141531448664577 6739792570606148586498433)
      ·
        refine ⟨5054844427954611439873825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6739792570606148586498433 5054844427954611439873825)
        ·
          refine ⟨3791133320965958579905369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5054844427954611439873825 3791133320965958579905369)
          ·
            refine ⟨2843349990724468934929027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3791133320965958579905369 2843349990724468934929027)
            ·
              refine ⟨4265024986086703402393541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2843349990724468934929027 4265024986086703402393541)
              ·
                refine ⟨799692184891256887948789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4265024986086703402393541 799692184891256887948789)
                ·
                  refine ⟨74971142333555333245199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 799692184891256887948789 74971142333555333245199)
                  ·
                    rfl

theorem cell23_1314052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_1314052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314052 prefixEnd_1314052 := by exact prefixLift 1314052
  have htrace : WordTrace (prefixWord ++ tailWord_1314052) baseStart_1314052 baseEnd_1314052 := by
    simpa [prefixWord, tailWord_1314052, baseEnd_1314052] using wordTrace_append hprefix tailTrace_1314052
  have hstable : (prefixWord ++ tailWord_1314052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314052).length < 2 ^ (prefixWord ++ tailWord_1314052).sum := by decide
  have hdescent : baseEnd_1314052 < baseStart_1314052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314085 : List Nat := [1, 3, 1, 2, 4, 2, 1, 1, 1, 3, 4]
def baseStart_1314085 : Nat := 118140960795 + 1314085 * 2 ^ 59
def prefixEnd_1314085 : Nat := 4983230072969 + 3 ^ 40 * 1314085 * 2
def baseEnd_1314085 : Nat := 674757225863596370094139

theorem tailTrace_1314085 : CollatzResearch.WordTrace tailWord_1314085 prefixEnd_1314085 674757225863596370094139 := by
  unfold tailWord_1314085
  simp only [CollatzResearch.WordTrace]
  refine ⟨47928617444301947695495709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31952411629534631796997139 47928617444301947695495709)
  ·
    refine ⟨17973231541613230385810891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47928617444301947695495709 17973231541613230385810891)
    ·
      refine ⟨26959847312419845578716337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17973231541613230385810891 26959847312419845578716337)
      ·
        refine ⟨20219885484314884184037253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26959847312419845578716337 20219885484314884184037253)
        ·
          refine ⟨3791228528309040784506985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20219885484314884184037253 3791228528309040784506985)
          ·
            refine ⟨2843421396231780588380239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3791228528309040784506985 2843421396231780588380239)
            ·
              refine ⟨4265132094347670882570359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2843421396231780588380239 4265132094347670882570359)
              ·
                refine ⟨6397698141521506323855539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4265132094347670882570359 6397698141521506323855539)
                ·
                  refine ⟨9596547212282259485783309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6397698141521506323855539 9596547212282259485783309)
                  ·
                    refine ⟨3598705204605847307168741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9596547212282259485783309 3598705204605847307168741)
                    ·
                      refine ⟨674757225863596370094139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3598705204605847307168741 674757225863596370094139)
                      ·
                        rfl

theorem cell23_1314085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 1, 1, 1, 3, 4].length) (baseStart_1314085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314085 prefixEnd_1314085 := by exact prefixLift 1314085
  have htrace : WordTrace (prefixWord ++ tailWord_1314085) baseStart_1314085 baseEnd_1314085 := by
    simpa [prefixWord, tailWord_1314085, baseEnd_1314085] using wordTrace_append hprefix tailTrace_1314085
  have hstable : (prefixWord ++ tailWord_1314085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314085).length < 2 ^ (prefixWord ++ tailWord_1314085).sum := by decide
  have hdescent : baseEnd_1314085 < baseStart_1314085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314112 : List Nat := [2, 1, 1, 2, 2, 1, 3, 6, 1, 4]
def baseStart_1314112 : Nat := 118140960795 + 1314112 * 2 ^ 59
def prefixEnd_1314112 : Nat := 4983230072969 + 3 ^ 40 * 1314112 * 2
def baseEnd_1314112 : Nat := 224923696613755921485505

theorem tailTrace_1314112 : CollatzResearch.WordTrace tailWord_1314112 prefixEnd_1314112 224923696613755921485505 := by
  unfold tailWord_1314112
  simp only [CollatzResearch.WordTrace]
  refine ⟨23964801107602065653364295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31953068143469420871152393 23964801107602065653364295)
  ·
    refine ⟨35947201661403098480046443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23964801107602065653364295 35947201661403098480046443)
    ·
      refine ⟨53920802492104647720069665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35947201661403098480046443 53920802492104647720069665)
      ·
        refine ⟨40440601869078485790052249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53920802492104647720069665 40440601869078485790052249)
        ·
          refine ⟨30330451401808864342539187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40440601869078485790052249 30330451401808864342539187)
          ·
            refine ⟨45495677102713296513808781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30330451401808864342539187 45495677102713296513808781)
            ·
              refine ⟨17060878913517486192678293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45495677102713296513808781 17060878913517486192678293)
              ·
                refine ⟨799728699071132165281795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17060878913517486192678293 799728699071132165281795)
                ·
                  refine ⟨1199593048606698247922693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 799728699071132165281795 1199593048606698247922693)
                  ·
                    refine ⟨224923696613755921485505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1199593048606698247922693 224923696613755921485505)
                    ·
                      rfl

theorem cell23_1314112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 6, 1, 4].length) (baseStart_1314112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314112 prefixEnd_1314112 := by exact prefixLift 1314112
  have htrace : WordTrace (prefixWord ++ tailWord_1314112) baseStart_1314112 baseEnd_1314112 := by
    simpa [prefixWord, tailWord_1314112, baseEnd_1314112] using wordTrace_append hprefix tailTrace_1314112
  have hstable : (prefixWord ++ tailWord_1314112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314112).length < 2 ^ (prefixWord ++ tailWord_1314112).sum := by decide
  have hdescent : baseEnd_1314112 < baseStart_1314112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314128 : List Nat := [2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 6]
def baseStart_1314128 : Nat := 118140960795 + 1314128 * 2 ^ 59
def prefixEnd_1314128 : Nat := 4983230072969 + 3 ^ 40 * 1314128 * 2
def baseEnd_1314128 : Nat := 674779305531739701856441

theorem tailTrace_1314128 : CollatzResearch.WordTrace tailWord_1314128 prefixEnd_1314128 674779305531739701856441 := by
  unfold tailWord_1314128
  simp only [CollatzResearch.WordTrace]
  refine ⟨23965092891573083019655519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31953457188764110692874025 23965092891573083019655519)
  ·
    refine ⟨35947639337359624529483279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23965092891573083019655519 35947639337359624529483279)
    ·
      refine ⟨53921459006039436794224919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35947639337359624529483279 53921459006039436794224919)
      ·
        refine ⟨80882188509059155191337379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53921459006039436794224919 80882188509059155191337379)
        ·
          refine ⟨121323282763588732787006069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80882188509059155191337379 121323282763588732787006069)
          ·
            refine ⟨11374057759086443698781819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 121323282763588732787006069 11374057759086443698781819)
            ·
              refine ⟨17061086638629665548172729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11374057759086443698781819 17061086638629665548172729)
              ·
                refine ⟨12795814978972249161129547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17061086638629665548172729 12795814978972249161129547)
                ·
                  refine ⟨19193722468458373741694321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12795814978972249161129547 19193722468458373741694321)
                  ·
                    refine ⟨14395291851343780306270741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19193722468458373741694321 14395291851343780306270741)
                    ·
                      refine ⟨674779305531739701856441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14395291851343780306270741 674779305531739701856441)
                      ·
                        rfl

theorem cell23_1314128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 2, 1, 2, 6].length) (baseStart_1314128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314128 prefixEnd_1314128 := by exact prefixLift 1314128
  have htrace : WordTrace (prefixWord ++ tailWord_1314128) baseStart_1314128 baseEnd_1314128 := by
    simpa [prefixWord, tailWord_1314128, baseEnd_1314128] using wordTrace_append hprefix tailTrace_1314128
  have hstable : (prefixWord ++ tailWord_1314128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314128).length < 2 ^ (prefixWord ++ tailWord_1314128).sum := by decide
  have hdescent : baseEnd_1314128 < baseStart_1314128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314169 : List Nat := [1, 2, 1, 3, 2, 1, 2, 6, 1, 1, 3]
def baseStart_1314169 : Nat := 118140960795 + 1314169 * 2 ^ 59
def prefixEnd_1314169 : Nat := 4983230072969 + 3 ^ 40 * 1314169 * 2
def baseEnd_1314169 : Nat := 674800358238574041443753

theorem tailTrace_1314169 : CollatzResearch.WordTrace tailWord_1314169 prefixEnd_1314169 674800358238574041443753 := by
  unfold tailWord_1314169
  simp only [CollatzResearch.WordTrace]
  refine ⟨47931681175997630041553561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31954454117331753361035707 47931681175997630041553561)
  ·
    refine ⟨35948760881998222531165171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47931681175997630041553561 35948760881998222531165171)
    ·
      refine ⟨53923141322997333796747757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35948760881998222531165171 53923141322997333796747757)
      ·
        refine ⟨20221177996124000173780409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 53923141322997333796747757 20221177996124000173780409)
        ·
          refine ⟨15165883497093000130335307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20221177996124000173780409 15165883497093000130335307)
          ·
            refine ⟨22748825245639500195502961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15165883497093000130335307 22748825245639500195502961)
            ·
              refine ⟨17061618934229625146627221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22748825245639500195502961 17061618934229625146627221)
              ·
                refine ⟨799763387542013678748151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 17061618934229625146627221 799763387542013678748151)
                ·
                  refine ⟨1199645081313020518122227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 799763387542013678748151 1199645081313020518122227)
                  ·
                    refine ⟨1799467621969530777183341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1199645081313020518122227 1799467621969530777183341)
                    ·
                      refine ⟨674800358238574041443753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1799467621969530777183341 674800358238574041443753)
                      ·
                        rfl

theorem cell23_1314169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 1, 1, 3].length) (baseStart_1314169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314169 prefixEnd_1314169 := by exact prefixLift 1314169
  have htrace : WordTrace (prefixWord ++ tailWord_1314169) baseStart_1314169 baseEnd_1314169 := by
    simpa [prefixWord, tailWord_1314169, baseEnd_1314169] using wordTrace_append hprefix tailTrace_1314169
  have hstable : (prefixWord ++ tailWord_1314169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314169).length < 2 ^ (prefixWord ++ tailWord_1314169).sum := by decide
  have hdescent : baseEnd_1314169 < baseStart_1314169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314196 : List Nat := [2, 4, 2, 1, 2, 2, 2, 1, 2, 3, 2]
def baseStart_1314196 : Nat := 118140960795 + 1314196 * 2 ^ 59
def prefixEnd_1314196 : Nat := 4983230072969 + 3 ^ 40 * 1314196 * 2
def baseEnd_1314196 : Nat := 674814222216245435806129

theorem tailTrace_1314196 : CollatzResearch.WordTrace tailWord_1314196 prefixEnd_1314196 674814222216245435806129 := by
  unfold tailWord_1314196
  simp only [CollatzResearch.WordTrace]
  refine ⟨23966332973449906826393221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31955110631266542435190961 23966332973449906826393221)
  ·
    refine ⟨4493687432521857529948729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23966332973449906826393221 4493687432521857529948729)
    ·
      refine ⟨3370265574391393147461547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4493687432521857529948729 3370265574391393147461547)
      ·
        refine ⟨5055398361587089721192321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3370265574391393147461547 5055398361587089721192321)
        ·
          refine ⟨3791548771190317290894241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5055398361587089721192321 3791548771190317290894241)
          ·
            refine ⟨2843661578392737968170681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3791548771190317290894241 2843661578392737968170681)
            ·
              refine ⟨2132746183794553476128011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2843661578392737968170681 2132746183794553476128011)
              ·
                refine ⟨3199119275691830214192017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2132746183794553476128011 3199119275691830214192017)
                ·
                  refine ⟨2399339456768872660644013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3199119275691830214192017 2399339456768872660644013)
                  ·
                    refine ⟨899752296288327247741505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2399339456768872660644013 899752296288327247741505)
                    ·
                      refine ⟨674814222216245435806129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 899752296288327247741505 674814222216245435806129)
                      ·
                        rfl

theorem cell23_1314196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 2, 2, 1, 2, 3, 2].length) (baseStart_1314196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314196 prefixEnd_1314196 := by exact prefixLift 1314196
  have htrace : WordTrace (prefixWord ++ tailWord_1314196) baseStart_1314196 baseEnd_1314196 := by
    simpa [prefixWord, tailWord_1314196, baseEnd_1314196] using wordTrace_append hprefix tailTrace_1314196
  have hstable : (prefixWord ++ tailWord_1314196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314196).length < 2 ^ (prefixWord ++ tailWord_1314196).sum := by decide
  have hdescent : baseEnd_1314196 < baseStart_1314196 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314260 : List Nat := [2, 4, 1, 2, 3, 1, 2, 3, 1, 2, 2]
def baseStart_1314260 : Nat := 118140960795 + 1314260 * 2 ^ 59
def prefixEnd_1314260 : Nat := 4983230072969 + 3 ^ 40 * 1314260 * 2
def baseEnd_1314260 : Nat := 674847084978133185405835

theorem tailTrace_1314260 : CollatzResearch.WordTrace tailWord_1314260 prefixEnd_1314260 674847084978133185405835 := by
  unfold tailWord_1314260
  simp only [CollatzResearch.WordTrace]
  refine ⟨23967500109333976291558117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31956666812445301722077489 23967500109333976291558117)
  ·
    refine ⟨4493906270500120554667147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23967500109333976291558117 4493906270500120554667147)
    ·
      refine ⟨6740859405750180832000721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4493906270500120554667147 6740859405750180832000721)
      ·
        refine ⟨5055644554312635624000541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6740859405750180832000721 5055644554312635624000541)
        ·
          refine ⟨1895866707867238359000203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5055644554312635624000541 1895866707867238359000203)
          ·
            refine ⟨2843800061800857538500305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1895866707867238359000203 2843800061800857538500305)
            ·
              refine ⟨2132850046350643153875229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2843800061800857538500305 2132850046350643153875229)
              ·
                refine ⟨799818767381491182703211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2132850046350643153875229 799818767381491182703211)
                ·
                  refine ⟨1199728151072236774054817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 799818767381491182703211 1199728151072236774054817)
                  ·
                    refine ⟨899796113304177580541113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1199728151072236774054817 899796113304177580541113)
                    ·
                      refine ⟨674847084978133185405835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 899796113304177580541113 674847084978133185405835)
                      ·
                        rfl

theorem cell23_1314260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_1314260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314260 prefixEnd_1314260 := by exact prefixLift 1314260
  have htrace : WordTrace (prefixWord ++ tailWord_1314260) baseStart_1314260 baseEnd_1314260 := by
    simpa [prefixWord, tailWord_1314260, baseEnd_1314260] using wordTrace_append hprefix tailTrace_1314260
  have hstable : (prefixWord ++ tailWord_1314260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314260).length < 2 ^ (prefixWord ++ tailWord_1314260).sum := by decide
  have hdescent : baseEnd_1314260 < baseStart_1314260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314295 : List Nat := [1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 4]
def baseStart_1314295 : Nat := 118140960795 + 1314295 * 2 ^ 59
def prefixEnd_1314295 : Nat := 4983230072969 + 3 ^ 40 * 1314295 * 2
def baseEnd_1314295 : Nat := 674865056801040548468173

theorem tailTrace_1314295 : CollatzResearch.WordTrace tailWord_1314295 prefixEnd_1314295 674865056801040548468173 := by
  unfold tailWord_1314295
  simp only [CollatzResearch.WordTrace]
  refine ⟨47936276773541153560640339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31957517849027435707093559 47936276773541153560640339)
  ·
    refine ⟨71904415160311730340960509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47936276773541153560640339 71904415160311730340960509)
    ·
      refine ⟨26964155685116898877860191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71904415160311730340960509 26964155685116898877860191)
      ·
        refine ⟨40446233527675348316790287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26964155685116898877860191 40446233527675348316790287)
        ·
          refine ⟨60669350291513022475185431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40446233527675348316790287 60669350291513022475185431)
          ·
            refine ⟨91004025437269533712778147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60669350291513022475185431 91004025437269533712778147)
            ·
              refine ⟨136506038155904300569167221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91004025437269533712778147 136506038155904300569167221)
              ·
                refine ⟨12797441077116028178359427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 136506038155904300569167221 12797441077116028178359427)
                ·
                  refine ⟨19196161615674042267539141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12797441077116028178359427 19196161615674042267539141)
                  ·
                    refine ⟨3599280302938882925163589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19196161615674042267539141 3599280302938882925163589)
                    ·
                      refine ⟨674865056801040548468173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3599280302938882925163589 674865056801040548468173)
                      ·
                        rfl

theorem cell23_1314295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 5, 1, 4, 4].length) (baseStart_1314295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314295 prefixEnd_1314295 := by exact prefixLift 1314295
  have htrace : WordTrace (prefixWord ++ tailWord_1314295) baseStart_1314295 baseEnd_1314295 := by
    simpa [prefixWord, tailWord_1314295, baseEnd_1314295] using wordTrace_append hprefix tailTrace_1314295
  have hstable : (prefixWord ++ tailWord_1314295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314295).length < 2 ^ (prefixWord ++ tailWord_1314295).sum := by decide
  have hdescent : baseEnd_1314295 < baseStart_1314295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314339 : List Nat := [1, 1, 1, 4, 5, 2, 1, 1, 7]
def baseStart_1314339 : Nat := 118140960795 + 1314339 * 2 ^ 59
def prefixEnd_1314339 : Nat := 4983230072969 + 3 ^ 40 * 1314339 * 2
def baseEnd_1314339 : Nat := 74987516661093152924219

theorem tailTrace_1314339 : CollatzResearch.WordTrace tailWord_1314339 prefixEnd_1314339 74987516661093152924219 := by
  unfold tailWord_1314339
  simp only [CollatzResearch.WordTrace]
  refine ⟨47937881585381749075242071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31958587723587832716828047 47937881585381749075242071)
  ·
    refine ⟨71906822378072623612863107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47937881585381749075242071 71906822378072623612863107)
    ·
      refine ⟨107860233567108935419294661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71906822378072623612863107 107860233567108935419294661)
      ·
        refine ⟨20223793793832925391117749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107860233567108935419294661 20223793793832925391117749)
        ·
          refine ⟨1895980668171836755417289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20223793793832925391117749 1895980668171836755417289)
          ·
            refine ⟨1421985501128877566562967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1895980668171836755417289 1421985501128877566562967)
            ·
              refine ⟨2132978251693316349844451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1421985501128877566562967 2132978251693316349844451)
              ·
                refine ⟨3199467377539974524766677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2132978251693316349844451 3199467377539974524766677)
                ·
                  refine ⟨74987516661093152924219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3199467377539974524766677 74987516661093152924219)
                  ·
                    rfl

theorem cell23_1314339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 7].length) (baseStart_1314339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314339 prefixEnd_1314339 := by exact prefixLift 1314339
  have htrace : WordTrace (prefixWord ++ tailWord_1314339) baseStart_1314339 baseEnd_1314339 := by
    simpa [prefixWord, tailWord_1314339, baseEnd_1314339] using wordTrace_append hprefix tailTrace_1314339
  have hstable : (prefixWord ++ tailWord_1314339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314339).length < 2 ^ (prefixWord ++ tailWord_1314339).sum := by decide
  have hdescent : baseEnd_1314339 < baseStart_1314339 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314350 : List Nat := [4, 1, 3, 1, 2, 1, 4, 1, 2, 2, 2]
def baseStart_1314350 : Nat := 118140960795 + 1314350 * 2 ^ 59
def prefixEnd_1314350 : Nat := 4983230072969 + 3 ^ 40 * 1314350 * 2
def baseEnd_1314350 : Nat := 674893298237037833280421

theorem tailTrace_1314350 : CollatzResearch.WordTrace tailWord_1314350 prefixEnd_1314350 674893298237037833280421 := by
  unfold tailWord_1314350
  simp only [CollatzResearch.WordTrace]
  refine ⟨5992285348542737244236563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31958855192227931969261669 5992285348542737244236563)
  ·
    refine ⟨8988428022814105866354845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5992285348542737244236563 8988428022814105866354845)
    ·
      refine ⟨3370660508555289699883067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8988428022814105866354845 3370660508555289699883067)
      ·
        refine ⟨5055990762832934549824601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3370660508555289699883067 5055990762832934549824601)
        ·
          refine ⟨3791993072124700912368451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5055990762832934549824601 3791993072124700912368451)
          ·
            refine ⟨5687989608187051368552677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3791993072124700912368451 5687989608187051368552677)
            ·
              refine ⟨1066498051535072131603627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5687989608187051368552677 1066498051535072131603627)
              ·
                refine ⟨1599747077302608197405441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066498051535072131603627 1599747077302608197405441)
                ·
                  refine ⟨1199810307976956148054081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1599747077302608197405441 1199810307976956148054081)
                  ·
                    refine ⟨899857730982717111040561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1199810307976956148054081 899857730982717111040561)
                    ·
                      refine ⟨674893298237037833280421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 899857730982717111040561 674893298237037833280421)
                      ·
                        rfl

theorem cell23_1314350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_1314350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314350 prefixEnd_1314350 := by exact prefixLift 1314350
  have htrace : WordTrace (prefixWord ++ tailWord_1314350) baseStart_1314350 baseEnd_1314350 := by
    simpa [prefixWord, tailWord_1314350, baseEnd_1314350] using wordTrace_append hprefix tailTrace_1314350
  have hstable : (prefixWord ++ tailWord_1314350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314350).length < 2 ^ (prefixWord ++ tailWord_1314350).sum := by decide
  have hdescent : baseEnd_1314350 < baseStart_1314350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314369 : List Nat := [1, 2, 5, 1, 1, 1, 4, 1, 2, 5]
def baseStart_1314369 : Nat := 118140960795 + 1314369 * 2 ^ 59
def prefixEnd_1314369 : Nat := 4983230072969 + 3 ^ 40 * 1314369 * 2
def baseEnd_1314369 : Nat := 224967684789824419647611

theorem tailTrace_1314369 : CollatzResearch.WordTrace tailWord_1314369 prefixEnd_1314369 224967684789824419647611 := by
  unfold tailWord_1314369
  simp only [CollatzResearch.WordTrace]
  refine ⟨47938975775273064198834161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31959317183515376132556107 47938975775273064198834161)
  ·
    refine ⟨35954231831454798149125621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47938975775273064198834161 35954231831454798149125621)
    ·
      refine ⟨3370709234198887326480527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35954231831454798149125621 3370709234198887326480527)
      ·
        refine ⟨5056063851298330989720791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3370709234198887326480527 5056063851298330989720791)
        ·
          refine ⟨7584095776947496484581187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5056063851298330989720791 7584095776947496484581187)
          ·
            refine ⟨11376143665421244726871781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7584095776947496484581187 11376143665421244726871781)
            ·
              refine ⟨2133026937266483386288459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11376143665421244726871781 2133026937266483386288459)
              ·
                refine ⟨3199540405899725079432689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2133026937266483386288459 3199540405899725079432689)
                ·
                  refine ⟨2399655304424793809574517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3199540405899725079432689 2399655304424793809574517)
                  ·
                    refine ⟨224967684789824419647611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2399655304424793809574517 224967684789824419647611)
                    ·
                      rfl

theorem cell23_1314369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_1314369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314369 prefixEnd_1314369 := by exact prefixLift 1314369
  have htrace : WordTrace (prefixWord ++ tailWord_1314369) baseStart_1314369 baseEnd_1314369 := by
    simpa [prefixWord, tailWord_1314369, baseEnd_1314369] using wordTrace_append hprefix tailTrace_1314369
  have hstable : (prefixWord ++ tailWord_1314369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314369).length < 2 ^ (prefixWord ++ tailWord_1314369).sum := by decide
  have hdescent : baseEnd_1314369 < baseStart_1314369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314389 : List Nat := [1, 3, 2, 2, 1, 1, 1, 4, 2, 4, 2]
def baseStart_1314389 : Nat := 118140960795 + 1314389 * 2 ^ 59
def prefixEnd_1314389 : Nat := 4983230072969 + 3 ^ 40 * 1314389 * 2
def baseEnd_1314389 : Nat := 674913323982563180692741

theorem tailTrace_1314389 : CollatzResearch.WordTrace tailWord_1314389 prefixEnd_1314389 674913323982563180692741 := by
  unfold tailWord_1314389
  simp only [CollatzResearch.WordTrace]
  refine ⟨47939705235200607614562221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31959803490133738409708147 47939705235200607614562221)
  ·
    refine ⟨17977389463200227855460833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47939705235200607614562221 17977389463200227855460833)
    ·
      refine ⟨13483042097400170891595625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17977389463200227855460833 13483042097400170891595625)
      ·
        refine ⟨10112281573050128168696719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13483042097400170891595625 10112281573050128168696719)
        ·
          refine ⟨15168422359575192253045079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10112281573050128168696719 15168422359575192253045079)
          ·
            refine ⟨22752633539362788379567619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15168422359575192253045079 22752633539362788379567619)
            ·
              refine ⟨34128950309044182569351429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22752633539362788379567619 34128950309044182569351429)
              ·
                refine ⟨6399178182945784231753393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34128950309044182569351429 6399178182945784231753393)
                ·
                  refine ⟨4799383637209338173815045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6399178182945784231753393 4799383637209338173815045)
                  ·
                    refine ⟨899884431976750907590321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4799383637209338173815045 899884431976750907590321)
                    ·
                      refine ⟨674913323982563180692741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 899884431976750907590321 674913323982563180692741)
                      ·
                        rfl

theorem cell23_1314389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_1314389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314389 prefixEnd_1314389 := by exact prefixLift 1314389
  have htrace : WordTrace (prefixWord ++ tailWord_1314389) baseStart_1314389 baseEnd_1314389 := by
    simpa [prefixWord, tailWord_1314389, baseEnd_1314389] using wordTrace_append hprefix tailTrace_1314389
  have hstable : (prefixWord ++ tailWord_1314389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314389).length < 2 ^ (prefixWord ++ tailWord_1314389).sum := by decide
  have hdescent : baseEnd_1314389 < baseStart_1314389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314390 : List Nat := [5, 2, 2, 2, 1, 1, 1, 4, 5]
def baseStart_1314390 : Nat := 118140960795 + 1314390 * 2 ^ 59
def prefixEnd_1314390 : Nat := 4983230072969 + 3 ^ 40 * 1314390 * 2
def baseEnd_1314390 : Nat := 74990426384801964086693

theorem tailTrace_1314390 : CollatzResearch.WordTrace tailWord_1314390 prefixEnd_1314390 74990426384801964086693 := by
  unfold tailWord_1314390
  simp only [CollatzResearch.WordTrace]
  refine ⟨2996233856762311549084289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31959827805464656523565749 2996233856762311549084289)
  ·
    refine ⟨2247175392571733661813217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2996233856762311549084289 2247175392571733661813217)
    ·
      refine ⟨1685381544428800246359913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2247175392571733661813217 1685381544428800246359913)
      ·
        refine ⟨1264036158321600184769935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1685381544428800246359913 1264036158321600184769935)
        ·
          refine ⟨1896054237482400277154903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1264036158321600184769935 1896054237482400277154903)
          ·
            refine ⟨2844081356223600415732355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1896054237482400277154903 2844081356223600415732355)
            ·
              refine ⟨4266122034335400623598533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2844081356223600415732355 4266122034335400623598533)
              ·
                refine ⟨799897881437887616924725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4266122034335400623598533 799897881437887616924725)
                ·
                  refine ⟨74990426384801964086693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 799897881437887616924725 74990426384801964086693)
                  ·
                    rfl

theorem cell23_1314390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_1314390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314390 prefixEnd_1314390 := by exact prefixLift 1314390
  have htrace : WordTrace (prefixWord ++ tailWord_1314390) baseStart_1314390 baseEnd_1314390 := by
    simpa [prefixWord, tailWord_1314390, baseEnd_1314390] using wordTrace_append hprefix tailTrace_1314390
  have hstable : (prefixWord ++ tailWord_1314390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314390).length < 2 ^ (prefixWord ++ tailWord_1314390).sum := by decide
  have hdescent : baseEnd_1314390 < baseStart_1314390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314392 : List Nat := [2, 1, 2, 2, 1, 2, 1, 2, 3, 4, 3]
def baseStart_1314392 : Nat := 118140960795 + 1314392 * 2 ^ 59
def prefixEnd_1314392 : Nat := 4983230072969 + 3 ^ 40 * 1314392 * 2
def baseEnd_1314392 : Nat := 674914864424526668955227

theorem tailTrace_1314392 : CollatzResearch.WordTrace tailWord_1314392 prefixEnd_1314392 674914864424526668955227 := by
  unfold tailWord_1314392
  simp only [CollatzResearch.WordTrace]
  refine ⟨23969907327094869563460715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31959876436126492751280953 23969907327094869563460715)
  ·
    refine ⟨35954860990642304345191073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23969907327094869563460715 35954860990642304345191073)
    ·
      refine ⟨26966145742981728258893305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35954860990642304345191073 26966145742981728258893305)
      ·
        refine ⟨20224609307236296194169979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26966145742981728258893305 20224609307236296194169979)
        ·
          refine ⟨30336913960854444291254969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20224609307236296194169979 30336913960854444291254969)
          ·
            refine ⟨22752685470640833218441227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30336913960854444291254969 22752685470640833218441227)
            ·
              refine ⟨34129028205961249827661841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22752685470640833218441227 34129028205961249827661841)
              ·
                refine ⟨25596771154470937370746381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34129028205961249827661841 25596771154470937370746381)
                ·
                  refine ⟨9598789182926601514029893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 25596771154470937370746381 9598789182926601514029893)
                  ·
                    refine ⟨1799772971798737783880605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9598789182926601514029893 1799772971798737783880605)
                    ·
                      refine ⟨674914864424526668955227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1799772971798737783880605 674914864424526668955227)
                      ·
                        rfl

theorem cell23_1314392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 2, 3, 4, 3].length) (baseStart_1314392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314392 prefixEnd_1314392 := by exact prefixLift 1314392
  have htrace : WordTrace (prefixWord ++ tailWord_1314392) baseStart_1314392 baseEnd_1314392 := by
    simpa [prefixWord, tailWord_1314392, baseEnd_1314392] using wordTrace_append hprefix tailTrace_1314392
  have hstable : (prefixWord ++ tailWord_1314392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314392).length < 2 ^ (prefixWord ++ tailWord_1314392).sum := by decide
  have hdescent : baseEnd_1314392 < baseStart_1314392 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314433 : List Nat := [1, 2, 4, 2, 1, 3, 2, 3, 1, 4]
def baseStart_1314433 : Nat := 118140960795 + 1314433 * 2 ^ 59
def prefixEnd_1314433 : Nat := 4983230072969 + 3 ^ 40 * 1314433 * 2
def baseEnd_1314433 : Nat := 224978639043787002847513

theorem tailTrace_1314433 : CollatzResearch.WordTrace tailWord_1314433 prefixEnd_1314433 224978639043787002847513 := by
  unfold tailWord_1314433
  simp only [CollatzResearch.WordTrace]
  refine ⟨47941310047041203129163953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31960873364694135419442635 47941310047041203129163953)
  ·
    refine ⟨35955982535280902346872965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47941310047041203129163953 35955982535280902346872965)
    ·
      refine ⟨6741746725365169190038681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35955982535280902346872965 6741746725365169190038681)
      ·
        refine ⟨5056310044023876892529011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6741746725365169190038681 5056310044023876892529011)
        ·
          refine ⟨7584465066035815338793517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5056310044023876892529011 7584465066035815338793517)
          ·
            refine ⟨2844174399763430752047569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7584465066035815338793517 2844174399763430752047569)
            ·
              refine ⟨2133130799822573064035677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2844174399763430752047569 2133130799822573064035677)
              ·
                refine ⟨799924049933464899013379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2133130799822573064035677 799924049933464899013379)
                ·
                  refine ⟨1199886074900197348520069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 799924049933464899013379 1199886074900197348520069)
                  ·
                    refine ⟨224978639043787002847513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1199886074900197348520069 224978639043787002847513)
                    ·
                      rfl

theorem cell23_1314433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 3, 2, 3, 1, 4].length) (baseStart_1314433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314433 prefixEnd_1314433 := by exact prefixLift 1314433
  have htrace : WordTrace (prefixWord ++ tailWord_1314433) baseStart_1314433 baseEnd_1314433 := by
    simpa [prefixWord, tailWord_1314433, baseEnd_1314433] using wordTrace_append hprefix tailTrace_1314433
  have hstable : (prefixWord ++ tailWord_1314433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314433).length < 2 ^ (prefixWord ++ tailWord_1314433).sum := by decide
  have hdescent : baseEnd_1314433 < baseStart_1314433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314446 : List Nat := [4, 1, 1, 3, 1, 4, 1, 2, 6]
def baseStart_1314446 : Nat := 118140960795 + 1314446 * 2 ^ 59
def prefixEnd_1314446 : Nat := 4983230072969 + 3 ^ 40 * 1314446 * 2
def baseEnd_1314446 : Nat := 74993621375541050853331

theorem tailTrace_1314446 : CollatzResearch.WordTrace tailWord_1314446 prefixEnd_1314446 74993621375541050853331 := by
  unfold tailWord_1314446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5992723024499263293673399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31961189463996070899591461 5992723024499263293673399)
  ·
    refine ⟨8989084536748894940510099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5992723024499263293673399 8989084536748894940510099)
    ·
      refine ⟨13483626805123342410765149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8989084536748894940510099 13483626805123342410765149)
      ·
        refine ⟨5056360051921253404036931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13483626805123342410765149 5056360051921253404036931)
        ·
          refine ⟨7584540077881880106055397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5056360051921253404036931 7584540077881880106055397)
          ·
            refine ⟨1422101264602852519885387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7584540077881880106055397 1422101264602852519885387)
            ·
              refine ⟨2133151896904278779828081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1422101264602852519885387 2133151896904278779828081)
              ·
                refine ⟨1599863922678209084871061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2133151896904278779828081 1599863922678209084871061)
                ·
                  refine ⟨74993621375541050853331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1599863922678209084871061 74993621375541050853331)
                  ·
                    rfl

theorem cell23_1314446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_1314446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314446 prefixEnd_1314446 := by exact prefixLift 1314446
  have htrace : WordTrace (prefixWord ++ tailWord_1314446) baseStart_1314446 baseEnd_1314446 := by
    simpa [prefixWord, tailWord_1314446, baseEnd_1314446] using wordTrace_append hprefix tailTrace_1314446
  have hstable : (prefixWord ++ tailWord_1314446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314446).length < 2 ^ (prefixWord ++ tailWord_1314446).sum := by decide
  have hdescent : baseEnd_1314446 < baseStart_1314446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314456 : List Nat := [2, 1, 2, 4, 1, 2, 1, 3, 3, 1, 3]
def baseStart_1314456 : Nat := 118140960795 + 1314456 * 2 ^ 59
def prefixEnd_1314456 : Nat := 4983230072969 + 3 ^ 40 * 1314456 * 2
def baseEnd_1314456 : Nat := 674947727186414418554933

theorem tailTrace_1314456 : CollatzResearch.WordTrace tailWord_1314456 prefixEnd_1314456 674947727186414418554933 := by
  unfold tailWord_1314456
  simp only [CollatzResearch.WordTrace]
  refine ⟨23971074462978939028625611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31961432617305252038167481 23971074462978939028625611)
  ·
    refine ⟨35956611694468408542938417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23971074462978939028625611 35956611694468408542938417)
    ·
      refine ⟨26967458770851306407203813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35956611694468408542938417 26967458770851306407203813)
      ·
        refine ⟨5056398519534619951350715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26967458770851306407203813 5056398519534619951350715)
        ·
          refine ⟨7584597779301929927026073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5056398519534619951350715 7584597779301929927026073)
          ·
            refine ⟨5688448334476447445269555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7584597779301929927026073 5688448334476447445269555)
            ·
              refine ⟨8532672501714671167904333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5688448334476447445269555 8532672501714671167904333)
              ·
                refine ⟨3199752188143001687964125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8532672501714671167904333 3199752188143001687964125)
                ·
                  refine ⟨1199907070553625632986547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3199752188143001687964125 1199907070553625632986547)
                  ·
                    refine ⟨1799860605830438449479821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1199907070553625632986547 1799860605830438449479821)
                    ·
                      refine ⟨674947727186414418554933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1799860605830438449479821 674947727186414418554933)
                      ·
                        rfl

theorem cell23_1314456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_1314456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314456 prefixEnd_1314456 := by exact prefixLift 1314456
  have htrace : WordTrace (prefixWord ++ tailWord_1314456) baseStart_1314456 baseEnd_1314456 := by
    simpa [prefixWord, tailWord_1314456, baseEnd_1314456] using wordTrace_append hprefix tailTrace_1314456
  have hstable : (prefixWord ++ tailWord_1314456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314456).length < 2 ^ (prefixWord ++ tailWord_1314456).sum := by decide
  have hdescent : baseEnd_1314456 < baseStart_1314456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314463 : List Nat := [1, 1, 2, 7, 1, 1, 3, 1, 6]
def baseStart_1314463 : Nat := 118140960795 + 1314463 * 2 ^ 59
def prefixEnd_1314463 : Nat := 4983230072969 + 3 ^ 40 * 1314463 * 2
def baseEnd_1314463 : Nat := 74994591283443987907489

theorem tailTrace_1314463 : CollatzResearch.WordTrace tailWord_1314463 prefixEnd_1314463 74994591283443987907489 := by
  unfold tailWord_1314463
  simp only [CollatzResearch.WordTrace]
  refine ⟨47942404236932518252756043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31961602824621678835170695 47942404236932518252756043)
  ·
    refine ⟨71913606355398777379134065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47942404236932518252756043 71913606355398777379134065)
    ·
      refine ⟨53935204766549083034350549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71913606355398777379134065 53935204766549083034350549)
      ·
        refine ⟨1264106361715994133617591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 53935204766549083034350549 1264106361715994133617591)
        ·
          refine ⟨1896159542573991200426387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1264106361715994133617591 1896159542573991200426387)
          ·
            refine ⟨2844239313860986800639581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1896159542573991200426387 2844239313860986800639581)
            ·
              refine ⟨1066589742697870050239843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2844239313860986800639581 1066589742697870050239843)
              ·
                refine ⟨1599884614046805075359765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066589742697870050239843 1599884614046805075359765)
                ·
                  refine ⟨74994591283443987907489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1599884614046805075359765 74994591283443987907489)
                  ·
                    rfl

theorem cell23_1314463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 6].length) (baseStart_1314463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314463 prefixEnd_1314463 := by exact prefixLift 1314463
  have htrace : WordTrace (prefixWord ++ tailWord_1314463) baseStart_1314463 baseEnd_1314463 := by
    simpa [prefixWord, tailWord_1314463, baseEnd_1314463] using wordTrace_append hprefix tailTrace_1314463
  have hstable : (prefixWord ++ tailWord_1314463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314463).length < 2 ^ (prefixWord ++ tailWord_1314463).sum := by decide
  have hdescent : baseEnd_1314463 < baseStart_1314463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314479 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 2, 6, 2]
def baseStart_1314479 : Nat := 118140960795 + 1314479 * 2 ^ 59
def prefixEnd_1314479 : Nat := 4983230072969 + 3 ^ 40 * 1314479 * 2
def baseEnd_1314479 : Nat := 674959537241467828567327

theorem tailTrace_1314479 : CollatzResearch.WordTrace tailWord_1314479 prefixEnd_1314479 674959537241467828567327 := by
  unfold tailWord_1314479
  simp only [CollatzResearch.WordTrace]
  refine ⟨47942987804874552985338491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31961991869916368656892327 47942987804874552985338491)
  ·
    refine ⟨71914481707311829478007737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47942987804874552985338491 71914481707311829478007737)
    ·
      refine ⟨53935861280483872108505803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71914481707311829478007737 53935861280483872108505803)
      ·
        refine ⟨80903791920725808162758705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53935861280483872108505803 80903791920725808162758705)
        ·
          refine ⟨60677843940544356122069029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80903791920725808162758705 60677843940544356122069029)
          ·
            refine ⟨11377095738852066772887943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 60677843940544356122069029 11377095738852066772887943)
            ·
              refine ⟨17065643608278100159331915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11377095738852066772887943 17065643608278100159331915)
              ·
                refine ⟨25598465412417150238997873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17065643608278100159331915 25598465412417150238997873)
                ·
                  refine ⟨19198849059312862679248405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25598465412417150238997873 19198849059312862679248405)
                  ·
                    refine ⟨899946049655290438089769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19198849059312862679248405 899946049655290438089769)
                    ·
                      refine ⟨674959537241467828567327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 899946049655290438089769 674959537241467828567327)
                      ·
                        rfl

theorem cell23_1314479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 2, 6, 2].length) (baseStart_1314479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314479 prefixEnd_1314479 := by exact prefixLift 1314479
  have htrace : WordTrace (prefixWord ++ tailWord_1314479) baseStart_1314479 baseEnd_1314479 := by
    simpa [prefixWord, tailWord_1314479, baseEnd_1314479] using wordTrace_append hprefix tailTrace_1314479
  have hstable : (prefixWord ++ tailWord_1314479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314479).length < 2 ^ (prefixWord ++ tailWord_1314479).sum := by decide
  have hdescent : baseEnd_1314479 < baseStart_1314479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314489 : List Nat := [1, 2, 1, 4, 1, 1, 3, 2, 4, 4]
def baseStart_1314489 : Nat := 118140960795 + 1314489 * 2 ^ 59
def prefixEnd_1314489 : Nat := 4983230072969 + 3 ^ 40 * 1314489 * 2
def baseEnd_1314489 : Nat := 224988224016004263147427

theorem tailTrace_1314489 : CollatzResearch.WordTrace tailWord_1314489 prefixEnd_1314489 224988224016004263147427 := by
  unfold tailWord_1314489
  simp only [CollatzResearch.WordTrace]
  refine ⟨47943352534838324693202521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31962235023225549795468347 47943352534838324693202521)
  ·
    refine ⟨35957514401128743519901891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47943352534838324693202521 35957514401128743519901891)
    ·
      refine ⟨53936271601693115279852837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35957514401128743519901891 53936271601693115279852837)
      ·
        refine ⟨10113050925317459114972407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53936271601693115279852837 10113050925317459114972407)
        ·
          refine ⟨15169576387976188672458611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10113050925317459114972407 15169576387976188672458611)
          ·
            refine ⟨22754364581964283008687917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15169576387976188672458611 22754364581964283008687917)
            ·
              refine ⟨8532886718236606128257969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22754364581964283008687917 8532886718236606128257969)
              ·
                refine ⟨6399665038677454596193477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8532886718236606128257969 6399665038677454596193477)
                ·
                  refine ⟨1199937194752022736786277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6399665038677454596193477 1199937194752022736786277)
                  ·
                    refine ⟨224988224016004263147427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1199937194752022736786277 224988224016004263147427)
                    ·
                      rfl

theorem cell23_1314489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 3, 2, 4, 4].length) (baseStart_1314489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314489 prefixEnd_1314489 := by exact prefixLift 1314489
  have htrace : WordTrace (prefixWord ++ tailWord_1314489) baseStart_1314489 baseEnd_1314489 := by
    simpa [prefixWord, tailWord_1314489, baseEnd_1314489] using wordTrace_append hprefix tailTrace_1314489
  have hstable : (prefixWord ++ tailWord_1314489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314489).length < 2 ^ (prefixWord ++ tailWord_1314489).sum := by decide
  have hdescent : baseEnd_1314489 < baseStart_1314489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314490 : List Nat := [3, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3]
def baseStart_1314490 : Nat := 118140960795 + 1314490 * 2 ^ 59
def prefixEnd_1314490 : Nat := 4983230072969 + 3 ^ 40 * 1314490 * 2
def baseEnd_1314490 : Nat := 674965185528667285529777

theorem tailTrace_1314490 : CollatzResearch.WordTrace tailWord_1314490 prefixEnd_1314490 674965185528667285529777 := by
  unfold tailWord_1314490
  simp only [CollatzResearch.WordTrace]
  refine ⟨11985847251958675465997231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31962259338556467909325949 11985847251958675465997231)
  ·
    refine ⟨17978770877938013198995847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11985847251958675465997231 17978770877938013198995847)
    ·
      refine ⟨26968156316907019798493771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17978770877938013198995847 26968156316907019798493771)
      ·
        refine ⟨40452234475360529697740657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26968156316907019798493771 40452234475360529697740657)
        ·
          refine ⟨30339175856520397273305493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40452234475360529697740657 30339175856520397273305493)
          ·
            refine ⟨1422148868274393622186195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30339175856520397273305493 1422148868274393622186195)
            ·
              refine ⟨2133223302411590433279293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1422148868274393622186195 2133223302411590433279293)
              ·
                refine ⟨799958738404346412479735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2133223302411590433279293 799958738404346412479735)
                ·
                  refine ⟨1199938107606519618719603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 799958738404346412479735 1199938107606519618719603)
                  ·
                    refine ⟨1799907161409779428079405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1199938107606519618719603 1799907161409779428079405)
                    ·
                      refine ⟨674965185528667285529777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1799907161409779428079405 674965185528667285529777)
                      ·
                        rfl

theorem cell23_1314490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 1, 1, 3].length) (baseStart_1314490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314490 prefixEnd_1314490 := by exact prefixLift 1314490
  have htrace : WordTrace (prefixWord ++ tailWord_1314490) baseStart_1314490 baseEnd_1314490 := by
    simpa [prefixWord, tailWord_1314490, baseEnd_1314490] using wordTrace_append hprefix tailTrace_1314490
  have hstable : (prefixWord ++ tailWord_1314490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314490).length < 2 ^ (prefixWord ++ tailWord_1314490).sum := by decide
  have hdescent : baseEnd_1314490 < baseStart_1314490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314513 : List Nat := [1, 2, 2, 1, 2, 4, 3, 1, 3, 2, 2]
def baseStart_1314513 : Nat := 118140960795 + 1314513 * 2 ^ 59
def prefixEnd_1314513 : Nat := 4983230072969 + 3 ^ 40 * 1314513 * 2
def baseEnd_1314513 : Nat := 674976995583720695542171

theorem tailTrace_1314513 : CollatzResearch.WordTrace tailWord_1314513 prefixEnd_1314513 674976995583720695542171 := by
  unfold tailWord_1314513
  simp only [CollatzResearch.WordTrace]
  refine ⟨47944227886751376792076193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31962818591167584528050795 47944227886751376792076193)
  ·
    refine ⟨35958170915063532594057145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47944227886751376792076193 35958170915063532594057145)
    ·
      refine ⟨26968628186297649445542859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35958170915063532594057145 26968628186297649445542859)
      ·
        refine ⟨40452942279446474168314289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26968628186297649445542859 40452942279446474168314289)
        ·
          refine ⟨30339706709584855626235717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40452942279446474168314289 30339706709584855626235717)
          ·
            refine ⟨5688695008047160429919197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30339706709584855626235717 5688695008047160429919197)
            ·
              refine ⟨2133260628017685161219699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5688695008047160429919197 2133260628017685161219699)
              ·
                refine ⟨3199890942026527741829549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2133260628017685161219699 3199890942026527741829549)
                ·
                  refine ⟨1199959103259947903186081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3199890942026527741829549 1199959103259947903186081)
                  ·
                    refine ⟨899969327444960927389561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1199959103259947903186081 899969327444960927389561)
                    ·
                      refine ⟨674976995583720695542171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 899969327444960927389561 674976995583720695542171)
                      ·
                        rfl

theorem cell23_1314513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 4, 3, 1, 3, 2, 2].length) (baseStart_1314513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314513 prefixEnd_1314513 := by exact prefixLift 1314513
  have htrace : WordTrace (prefixWord ++ tailWord_1314513) baseStart_1314513 baseEnd_1314513 := by
    simpa [prefixWord, tailWord_1314513, baseEnd_1314513] using wordTrace_append hprefix tailTrace_1314513
  have hstable : (prefixWord ++ tailWord_1314513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314513).length < 2 ^ (prefixWord ++ tailWord_1314513).sum := by decide
  have hdescent : baseEnd_1314513 < baseStart_1314513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314516 : List Nat := [2, 4, 1, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_1314516 : Nat := 118140960795 + 1314516 * 2 ^ 59
def prefixEnd_1314516 : Nat := 4983230072969 + 3 ^ 40 * 1314516 * 2
def baseEnd_1314516 : Nat := 674978536025684183804657

theorem tailTrace_1314516 : CollatzResearch.WordTrace tailWord_1314516 prefixEnd_1314516 674978536025684183804657 := by
  unfold tailWord_1314516
  simp only [CollatzResearch.WordTrace]
  refine ⟨23972168652870254152217701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31962891537160338869623601 23972168652870254152217701)
  ·
    refine ⟨4494781622413172653540819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23972168652870254152217701 4494781622413172653540819)
    ·
      refine ⟨6742172433619758980311229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4494781622413172653540819 6742172433619758980311229)
      ·
        refine ⟨2528314662607409617616711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6742172433619758980311229 2528314662607409617616711)
        ·
          refine ⟨3792471993911114426425067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2528314662607409617616711 3792471993911114426425067)
          ·
            refine ⟨5688707990866671639637601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3792471993911114426425067 5688707990866671639637601)
            ·
              refine ⟨4266530993150003729728201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5688707990866671639637601 4266530993150003729728201)
              ·
                refine ⟨3199898244862502797296151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4266530993150003729728201 3199898244862502797296151)
                ·
                  refine ⟨4799847367293754195944227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3199898244862502797296151 4799847367293754195944227)
                  ·
                    refine ⟨7199771050940631293916341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4799847367293754195944227 7199771050940631293916341)
                    ·
                      refine ⟨674978536025684183804657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7199771050940631293916341 674978536025684183804657)
                      ·
                        rfl

theorem cell23_1314516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_1314516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314516 prefixEnd_1314516 := by exact prefixLift 1314516
  have htrace : WordTrace (prefixWord ++ tailWord_1314516) baseStart_1314516 baseEnd_1314516 := by
    simpa [prefixWord, tailWord_1314516, baseEnd_1314516] using wordTrace_append hprefix tailTrace_1314516
  have hstable : (prefixWord ++ tailWord_1314516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314516).length < 2 ^ (prefixWord ++ tailWord_1314516).sum := by decide
  have hdescent : baseEnd_1314516 < baseStart_1314516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314546 : List Nat := [3, 2, 1, 3, 1, 1, 3, 2, 1, 3, 3]
def baseStart_1314546 : Nat := 118140960795 + 1314546 * 2 ^ 59
def prefixEnd_1314546 : Nat := 4983230072969 + 3 ^ 40 * 1314546 * 2
def baseEnd_1314546 : Nat := 674993940445319066429519

theorem tailTrace_1314546 : CollatzResearch.WordTrace tailWord_1314546 prefixEnd_1314546 674993940445319066429519 := by
  unfold tailWord_1314546
  simp only [CollatzResearch.WordTrace]
  refine ⟨11986357873907955857006873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31963620997087882285351661 11986357873907955857006873)
  ·
    refine ⟨8989768405430966892755155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11986357873907955857006873 8989768405430966892755155)
    ·
      refine ⟨13484652608146450339132733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8989768405430966892755155 13484652608146450339132733)
      ·
        refine ⟨5056744728054918877174775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13484652608146450339132733 5056744728054918877174775)
        ·
          refine ⟨7585117092082378315762163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5056744728054918877174775 7585117092082378315762163)
          ·
            refine ⟨11377675638123567473643245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7585117092082378315762163 11377675638123567473643245)
            ·
              refine ⟨4266628364296337802616217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11377675638123567473643245 4266628364296337802616217)
              ·
                refine ⟨3199971273222253351962163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4266628364296337802616217 3199971273222253351962163)
                ·
                  refine ⟨4799956909833380027943245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3199971273222253351962163 4799956909833380027943245)
                  ·
                    refine ⟨1799983841187517510478717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4799956909833380027943245 1799983841187517510478717)
                    ·
                      refine ⟨674993940445319066429519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1799983841187517510478717 674993940445319066429519)
                      ·
                        rfl

theorem cell23_1314546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_1314546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314546 prefixEnd_1314546 := by exact prefixLift 1314546
  have htrace : WordTrace (prefixWord ++ tailWord_1314546) baseStart_1314546 baseEnd_1314546 := by
    simpa [prefixWord, tailWord_1314546, baseEnd_1314546] using wordTrace_append hprefix tailTrace_1314546
  have hstable : (prefixWord ++ tailWord_1314546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314546).length < 2 ^ (prefixWord ++ tailWord_1314546).sum := by decide
  have hdescent : baseEnd_1314546 < baseStart_1314546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314550 : List Nat := [5, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3]
def baseStart_1314550 : Nat := 118140960795 + 1314550 * 2 ^ 59
def prefixEnd_1314550 : Nat := 4983230072969 + 3 ^ 40 * 1314550 * 2
def baseEnd_1314550 : Nat := 674995994367937050779501

theorem tailTrace_1314550 : CollatzResearch.WordTrace tailWord_1314550 prefixEnd_1314550 674995994367937050779501 := by
  unfold tailWord_1314550
  simp only [CollatzResearch.WordTrace]
  refine ⟨2996598586726083256948319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31963718258411554740782069 2996598586726083256948319)
  ·
    refine ⟨4494897880089124885422479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2996598586726083256948319 4494897880089124885422479)
    ·
      refine ⟨6742346820133687328133719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4494897880089124885422479 6742346820133687328133719)
      ·
        refine ⟨10113520230200530992200579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6742346820133687328133719 10113520230200530992200579)
        ·
          refine ⟨15170280345300796488300869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10113520230200530992200579 15170280345300796488300869)
          ·
            refine ⟨2844427564743899341556413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15170280345300796488300869 2844427564743899341556413)
            ·
              refine ⟨1066660336778962253083655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2844427564743899341556413 1066660336778962253083655)
              ·
                refine ⟨1599990505168443379625483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066660336778962253083655 1599990505168443379625483)
                ·
                  refine ⟨2399985757752665069438225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1599990505168443379625483 2399985757752665069438225)
                  ·
                    refine ⟨1799989318314498802078669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2399985757752665069438225 1799989318314498802078669)
                    ·
                      refine ⟨674995994367937050779501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1799989318314498802078669 674995994367937050779501)
                      ·
                        rfl

theorem cell23_1314550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_1314550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314550 prefixEnd_1314550 := by exact prefixLift 1314550
  have htrace : WordTrace (prefixWord ++ tailWord_1314550) baseStart_1314550 baseEnd_1314550 := by
    simpa [prefixWord, tailWord_1314550, baseEnd_1314550] using wordTrace_append hprefix tailTrace_1314550
  have hstable : (prefixWord ++ tailWord_1314550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314550).length < 2 ^ (prefixWord ++ tailWord_1314550).sum := by decide
  have hdescent : baseEnd_1314550 < baseStart_1314550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314564 : List Nat := [2, 3, 2, 2, 1, 4, 2, 2, 1, 2, 2]
def baseStart_1314564 : Nat := 118140960795 + 1314564 * 2 ^ 59
def prefixEnd_1314564 : Nat := 4983230072969 + 3 ^ 40 * 1314564 * 2
def baseEnd_1314564 : Nat := 675003183097099996004437

theorem tailTrace_1314564 : CollatzResearch.WordTrace tailWord_1314564 prefixEnd_1314564 675003183097099996004437 := by
  unfold tailWord_1314564
  simp only [CollatzResearch.WordTrace]
  refine ⟨23973044004783306251091373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31964058673044408334788497 23973044004783306251091373)
  ·
    refine ⟨8989891501793739844159265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23973044004783306251091373 8989891501793739844159265)
    ·
      refine ⟨6742418626345304883119449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8989891501793739844159265 6742418626345304883119449)
      ·
        refine ⟨5056813969758978662339587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6742418626345304883119449 5056813969758978662339587)
        ·
          refine ⟨7585220954638467993509381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5056813969758978662339587 7585220954638467993509381)
          ·
            refine ⟨1422228928994712748783009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7585220954638467993509381 1422228928994712748783009)
            ·
              refine ⟨1066671696746034561587257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1422228928994712748783009 1066671696746034561587257)
              ·
                refine ⟨800003772559525921190443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1066671696746034561587257 800003772559525921190443)
                ·
                  refine ⟨1200005658839288881785665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 800003772559525921190443 1200005658839288881785665)
                  ·
                    refine ⟨900004244129466661339249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1200005658839288881785665 900004244129466661339249)
                    ·
                      refine ⟨675003183097099996004437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 900004244129466661339249 675003183097099996004437)
                      ·
                        rfl

theorem cell23_1314564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 2, 1, 2, 2].length) (baseStart_1314564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314564 prefixEnd_1314564 := by exact prefixLift 1314564
  have htrace : WordTrace (prefixWord ++ tailWord_1314564) baseStart_1314564 baseEnd_1314564 := by
    simpa [prefixWord, tailWord_1314564, baseEnd_1314564] using wordTrace_append hprefix tailTrace_1314564
  have hstable : (prefixWord ++ tailWord_1314564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314564).length < 2 ^ (prefixWord ++ tailWord_1314564).sum := by decide
  have hdescent : baseEnd_1314564 < baseStart_1314564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314620 : List Nat := [2, 2, 2, 2, 1, 1, 5, 2, 2, 2, 2]
def baseStart_1314620 : Nat := 118140960795 + 1314620 * 2 ^ 59
def prefixEnd_1314620 : Nat := 4983230072969 + 3 ^ 40 * 1314620 * 2
def baseEnd_1314620 : Nat := 675031938013751776904179

theorem tailTrace_1314620 : CollatzResearch.WordTrace tailWord_1314620 prefixEnd_1314620 675031938013751776904179 := by
  unfold tailWord_1314620
  simp only [CollatzResearch.WordTrace]
  refine ⟨23974065248681867033110657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31965420331575822710814209 23974065248681867033110657)
  ·
    refine ⟨17980548936511400274832993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23974065248681867033110657 17980548936511400274832993)
    ·
      refine ⟨13485411702383550206124745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17980548936511400274832993 13485411702383550206124745)
      ·
        refine ⟨10114058776787662654593559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13485411702383550206124745 10114058776787662654593559)
        ·
          refine ⟨15171088165181493981890339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10114058776787662654593559 15171088165181493981890339)
          ·
            refine ⟨22756632247772240972835509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15171088165181493981890339 22756632247772240972835509)
            ·
              refine ⟨2133434273228647591203329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22756632247772240972835509 2133434273228647591203329)
              ·
                refine ⟨1600075704921485693402497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2133434273228647591203329 1600075704921485693402497)
                ·
                  refine ⟨1200056778691114270051873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1600075704921485693402497 1200056778691114270051873)
                  ·
                    refine ⟨900042584018335702538905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1200056778691114270051873 900042584018335702538905)
                    ·
                      refine ⟨675031938013751776904179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 900042584018335702538905 675031938013751776904179)
                      ·
                        rfl

theorem cell23_1314620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 2, 2, 2].length) (baseStart_1314620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314620 prefixEnd_1314620 := by exact prefixLift 1314620
  have htrace : WordTrace (prefixWord ++ tailWord_1314620) baseStart_1314620 baseEnd_1314620 := by
    simpa [prefixWord, tailWord_1314620, baseEnd_1314620] using wordTrace_append hprefix tailTrace_1314620
  have hstable : (prefixWord ++ tailWord_1314620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314620).length < 2 ^ (prefixWord ++ tailWord_1314620).sum := by decide
  have hdescent : baseEnd_1314620 < baseStart_1314620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314637 : List Nat := [1, 6, 1, 2, 1, 3, 1, 1, 1, 4, 2]
def baseStart_1314637 : Nat := 118140960795 + 1314637 * 2 ^ 59
def prefixEnd_1314637 : Nat := 4983230072969 + 3 ^ 40 * 1314637 * 2
def baseEnd_1314637 : Nat := 675040667184878210391601

theorem tailTrace_1314637 : CollatzResearch.WordTrace tailWord_1314637 prefixEnd_1314637 675040667184878210391601 := by
  unfold tailWord_1314637
  simp only [CollatzResearch.WordTrace]
  refine ⟨47948750538302145969590165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31965833692201430646393443 47948750538302145969590165)
  ·
    refine ⟨2247597681482913092324539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 47948750538302145969590165 2247597681482913092324539)
    ·
      refine ⟨3371396522224369638486809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2247597681482913092324539 3371396522224369638486809)
      ·
        refine ⟨2528547391668277228865107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3371396522224369638486809 2528547391668277228865107)
        ·
          refine ⟨3792821087502415843297661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2528547391668277228865107 3792821087502415843297661)
          ·
            refine ⟨1422307907813405941236623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3792821087502415843297661 1422307907813405941236623)
            ·
              refine ⟨2133461861720108911854935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1422307907813405941236623 2133461861720108911854935)
              ·
                refine ⟨3200192792580163367782403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2133461861720108911854935 3200192792580163367782403)
                ·
                  refine ⟨4800289188870245051673605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3200192792580163367782403 4800289188870245051673605)
                  ·
                    refine ⟨900054222913170947188801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4800289188870245051673605 900054222913170947188801)
                    ·
                      refine ⟨675040667184878210391601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 900054222913170947188801 675040667184878210391601)
                      ·
                        rfl

theorem cell23_1314637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 3, 1, 1, 1, 4, 2].length) (baseStart_1314637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314637 prefixEnd_1314637 := by exact prefixLift 1314637
  have htrace : WordTrace (prefixWord ++ tailWord_1314637) baseStart_1314637 baseEnd_1314637 := by
    simpa [prefixWord, tailWord_1314637, baseEnd_1314637] using wordTrace_append hprefix tailTrace_1314637
  have hstable : (prefixWord ++ tailWord_1314637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314637).length < 2 ^ (prefixWord ++ tailWord_1314637).sum := by decide
  have hdescent : baseEnd_1314637 < baseStart_1314637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314660 : List Nat := [2, 3, 1, 1, 5, 2, 1, 3, 5]
def baseStart_1314660 : Nat := 118140960795 + 1314660 * 2 ^ 59
def prefixEnd_1314660 : Nat := 4983230072969 + 3 ^ 40 * 1314660 * 2
def baseEnd_1314660 : Nat := 75005830804436846711555

theorem tailTrace_1314660 : CollatzResearch.WordTrace tailWord_1314660 prefixEnd_1314660 75005830804436846711555 := by
  unfold tailWord_1314660
  simp only [CollatzResearch.WordTrace]
  refine ⟨23974794708609410448838717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31966392944812547265118289 23974794708609410448838717)
  ·
    refine ⟨8990548015728528918314519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23974794708609410448838717 8990548015728528918314519)
    ·
      refine ⟨13485822023592793377471779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8990548015728528918314519 13485822023592793377471779)
      ·
        refine ⟨20228733035389190066207669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13485822023592793377471779 20228733035389190066207669)
        ·
          refine ⟨1896443722067736568706969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20228733035389190066207669 1896443722067736568706969)
          ·
            refine ⟨1422332791550802426530227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1896443722067736568706969 1422332791550802426530227)
            ·
              refine ⟨2133499187326203639795341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1422332791550802426530227 2133499187326203639795341)
              ·
                refine ⟨800062195247326364923253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2133499187326203639795341 800062195247326364923253)
                ·
                  refine ⟨75005830804436846711555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 800062195247326364923253 75005830804436846711555)
                  ·
                    rfl

theorem cell23_1314660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_1314660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314660 prefixEnd_1314660 := by exact prefixLift 1314660
  have htrace : WordTrace (prefixWord ++ tailWord_1314660) baseStart_1314660 baseEnd_1314660 := by
    simpa [prefixWord, tailWord_1314660, baseEnd_1314660] using wordTrace_append hprefix tailTrace_1314660
  have hstable : (prefixWord ++ tailWord_1314660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314660).length < 2 ^ (prefixWord ++ tailWord_1314660).sum := by decide
  have hdescent : baseEnd_1314660 < baseStart_1314660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314737 : List Nat := [1, 2, 2, 4, 2, 1, 4, 2, 1, 4]
def baseStart_1314737 : Nat := 118140960795 + 1314737 * 2 ^ 59
def prefixEnd_1314737 : Nat := 4983230072969 + 3 ^ 40 * 1314737 * 2
def baseEnd_1314737 : Nat := 225030671750109273047047

theorem tailTrace_1314737 : CollatzResearch.WordTrace tailWord_1314737 prefixEnd_1314737 225030671750109273047047 := by
  unfold tailWord_1314737
  simp only [CollatzResearch.WordTrace]
  refine ⟨47952397837939863048230465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31968265225293242032153643 47952397837939863048230465)
  ·
    refine ⟨35964298378454897286172849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47952397837939863048230465 35964298378454897286172849)
    ·
      refine ⟨26973223783841172964629637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35964298378454897286172849 26973223783841172964629637)
      ·
        refine ⟨5057479459470219930868057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26973223783841172964629637 5057479459470219930868057)
        ·
          refine ⟨3793109594602664948151043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5057479459470219930868057 3793109594602664948151043)
          ·
            refine ⟨5689664391903997422226565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3793109594602664948151043 5689664391903997422226565)
            ·
              refine ⟨1066812073481999516667481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5689664391903997422226565 1066812073481999516667481)
              ·
                refine ⟨800109055111499637500611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1066812073481999516667481 800109055111499637500611)
                ·
                  refine ⟨1200163582667249456250917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 800109055111499637500611 1200163582667249456250917)
                  ·
                    refine ⟨225030671750109273047047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1200163582667249456250917 225030671750109273047047)
                    ·
                      rfl

theorem cell23_1314737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 1, 4, 2, 1, 4].length) (baseStart_1314737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314737 prefixEnd_1314737 := by exact prefixLift 1314737
  have htrace : WordTrace (prefixWord ++ tailWord_1314737) baseStart_1314737 baseEnd_1314737 := by
    simpa [prefixWord, tailWord_1314737, baseEnd_1314737] using wordTrace_append hprefix tailTrace_1314737
  have hstable : (prefixWord ++ tailWord_1314737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314737).length < 2 ^ (prefixWord ++ tailWord_1314737).sum := by decide
  have hdescent : baseEnd_1314737 < baseStart_1314737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314743 : List Nat := [1, 1, 3, 1, 3, 1, 1, 5, 3, 1, 3]
def baseStart_1314743 : Nat := 118140960795 + 1314743 * 2 ^ 59
def prefixEnd_1314743 : Nat := 4983230072969 + 3 ^ 40 * 1314743 * 2
def baseEnd_1314743 : Nat := 675095096134254795666113

theorem tailTrace_1314743 : CollatzResearch.WordTrace tailWord_1314743 prefixEnd_1314743 675095096134254795666113 := by
  unfold tailWord_1314743
  simp only [CollatzResearch.WordTrace]
  refine ⟨47952616675918126072948883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31968411117278750715299255 47952616675918126072948883)
  ·
    refine ⟨71928925013877189109423325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47952616675918126072948883 71928925013877189109423325)
    ·
      refine ⟨26973346880203945916033747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 71928925013877189109423325 26973346880203945916033747)
      ·
        refine ⟨40460020320305918874050621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26973346880203945916033747 40460020320305918874050621)
        ·
          refine ⟨15172507620114719577768983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40460020320305918874050621 15172507620114719577768983)
          ·
            refine ⟨22758761430172079366653475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15172507620114719577768983 22758761430172079366653475)
            ·
              refine ⟨34138142145258119049980213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22758761430172079366653475 34138142145258119049980213)
              ·
                refine ⟨3200450826117948660935645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34138142145258119049980213 3200450826117948660935645)
                ·
                  refine ⟨1200169059794230747850867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3200450826117948660935645 1200169059794230747850867)
                  ·
                    refine ⟨1800253589691346121776301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1200169059794230747850867 1800253589691346121776301)
                    ·
                      refine ⟨675095096134254795666113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1800253589691346121776301 675095096134254795666113)
                      ·
                        rfl

theorem cell23_1314743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 5, 3, 1, 3].length) (baseStart_1314743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314743 prefixEnd_1314743 := by exact prefixLift 1314743
  have htrace : WordTrace (prefixWord ++ tailWord_1314743) baseStart_1314743 baseEnd_1314743 := by
    simpa [prefixWord, tailWord_1314743, baseEnd_1314743] using wordTrace_append hprefix tailTrace_1314743
  have hstable : (prefixWord ++ tailWord_1314743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314743).length < 2 ^ (prefixWord ++ tailWord_1314743).sum := by decide
  have hdescent : baseEnd_1314743 < baseStart_1314743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314760 : List Nat := [2, 1, 3, 1, 4, 2, 1, 2, 3, 1, 3]
def baseStart_1314760 : Nat := 118140960795 + 1314760 * 2 ^ 59
def prefixEnd_1314760 : Nat := 4983230072969 + 3 ^ 40 * 1314760 * 2
def baseEnd_1314760 : Nat := 675103825305381229153535

theorem tailTrace_1314760 : CollatzResearch.WordTrace tailWord_1314760 prefixEnd_1314760 675103825305381229153535 := by
  unfold tailWord_1314760
  simp only [CollatzResearch.WordTrace]
  refine ⟨23976618358428268988158867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31968824477904358650878489 23976618358428268988158867)
  ·
    refine ⟨35964927537642403482238301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23976618358428268988158867 35964927537642403482238301)
    ·
      refine ⟨13486847826615901305839363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35964927537642403482238301 13486847826615901305839363)
      ·
        refine ⟨20230271739923851958759045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13486847826615901305839363 20230271739923851958759045)
        ·
          refine ⟨3793175951235722242267321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20230271739923851958759045 3793175951235722242267321)
          ·
            refine ⟨2844881963426791681700491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3793175951235722242267321 2844881963426791681700491)
            ·
              refine ⟨4267322945140187522550737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2844881963426791681700491 4267322945140187522550737)
              ·
                refine ⟨3200492208855140641913053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4267322945140187522550737 3200492208855140641913053)
                ·
                  refine ⟨1200184578320677740717395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3200492208855140641913053 1200184578320677740717395)
                  ·
                    refine ⟨1800276867481016611076093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1200184578320677740717395 1800276867481016611076093)
                    ·
                      refine ⟨675103825305381229153535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1800276867481016611076093 675103825305381229153535)
                      ·
                        rfl

theorem cell23_1314760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_1314760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314760 prefixEnd_1314760 := by exact prefixLift 1314760
  have htrace : WordTrace (prefixWord ++ tailWord_1314760) baseStart_1314760 baseEnd_1314760 := by
    simpa [prefixWord, tailWord_1314760, baseEnd_1314760] using wordTrace_append hprefix tailTrace_1314760
  have hstable : (prefixWord ++ tailWord_1314760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314760).length < 2 ^ (prefixWord ++ tailWord_1314760).sum := by decide
  have hdescent : baseEnd_1314760 < baseStart_1314760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314776 : List Nat := [2, 1, 2, 2, 2, 2, 1, 4, 1, 6]
def baseStart_1314776 : Nat := 118140960795 + 1314776 * 2 ^ 59
def prefixEnd_1314776 : Nat := 4983230072969 + 3 ^ 40 * 1314776 * 2
def baseEnd_1314776 : Nat := 225037346998617722184487

theorem tailTrace_1314776 : CollatzResearch.WordTrace tailWord_1314776 prefixEnd_1314776 225037346998617722184487 := by
  unfold tailWord_1314776
  simp only [CollatzResearch.WordTrace]
  refine ⟨23976910142399286354450091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31969213523199048472600121 23976910142399286354450091)
  ·
    refine ⟨35965365213598929531675137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23976910142399286354450091 35965365213598929531675137)
    ·
      refine ⟨26974023910199197148756353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35965365213598929531675137 26974023910199197148756353)
      ·
        refine ⟨20230517932649397861567265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26974023910199197148756353 20230517932649397861567265)
        ·
          refine ⟨15172888449487048396175449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20230517932649397861567265 15172888449487048396175449)
          ·
            refine ⟨11379666337115286297131587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15172888449487048396175449 11379666337115286297131587)
            ·
              refine ⟨17069499505672929445697381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11379666337115286297131587 17069499505672929445697381)
              ·
                refine ⟨3200531157313674271068259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17069499505672929445697381 3200531157313674271068259)
                ·
                  refine ⟨4800796735970511406602389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3200531157313674271068259 4800796735970511406602389)
                  ·
                    refine ⟨225037346998617722184487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4800796735970511406602389 225037346998617722184487)
                    ·
                      rfl

theorem cell23_1314776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 4, 1, 6].length) (baseStart_1314776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314776 prefixEnd_1314776 := by exact prefixLift 1314776
  have htrace : WordTrace (prefixWord ++ tailWord_1314776) baseStart_1314776 baseEnd_1314776 := by
    simpa [prefixWord, tailWord_1314776, baseEnd_1314776] using wordTrace_append hprefix tailTrace_1314776
  have hstable : (prefixWord ++ tailWord_1314776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314776).length < 2 ^ (prefixWord ++ tailWord_1314776).sum := by decide
  have hdescent : baseEnd_1314776 < baseStart_1314776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314796 : List Nat := [2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 4]
def baseStart_1314796 : Nat := 118140960795 + 1314796 * 2 ^ 59
def prefixEnd_1314796 : Nat := 4983230072969 + 3 ^ 40 * 1314796 * 2
def baseEnd_1314796 : Nat := 675122310608943088303369

theorem tailTrace_1314796 : CollatzResearch.WordTrace tailWord_1314796 prefixEnd_1314796 675122310608943088303369 := by
  unfold tailWord_1314796
  simp only [CollatzResearch.WordTrace]
  refine ⟨23977274872363058062314121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31969699829817410749752161 23977274872363058062314121)
  ·
    refine ⟨17982956154272293546735591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23977274872363058062314121 17982956154272293546735591)
    ·
      refine ⟨26974434231408440320103387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17982956154272293546735591 26974434231408440320103387)
      ·
        refine ⟨40461651347112660480155081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26974434231408440320103387 40461651347112660480155081)
        ·
          refine ⟨30346238510334495360116311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40461651347112660480155081 30346238510334495360116311)
          ·
            refine ⟨45519357765501743040174467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30346238510334495360116311 45519357765501743040174467)
            ·
              refine ⟨68279036648252614560261701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45519357765501743040174467 68279036648252614560261701)
              ·
                refine ⟨12802319371547365230049069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68279036648252614560261701 12802319371547365230049069)
                ·
                  refine ⟨4800869764330261961268401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12802319371547365230049069 4800869764330261961268401)
                  ·
                    refine ⟨3600652323247696470951301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4800869764330261961268401 3600652323247696470951301)
                    ·
                      refine ⟨675122310608943088303369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3600652323247696470951301 675122310608943088303369)
                      ·
                        rfl

theorem cell23_1314796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_1314796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314796 prefixEnd_1314796 := by exact prefixLift 1314796
  have htrace : WordTrace (prefixWord ++ tailWord_1314796) baseStart_1314796 baseEnd_1314796 := by
    simpa [prefixWord, tailWord_1314796, baseEnd_1314796] using wordTrace_append hprefix tailTrace_1314796
  have hstable : (prefixWord ++ tailWord_1314796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314796).length < 2 ^ (prefixWord ++ tailWord_1314796).sum := by decide
  have hdescent : baseEnd_1314796 < baseStart_1314796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314800 : List Nat := [2, 1, 1, 1, 3, 2, 3, 3, 3, 2, 2]
def baseStart_1314800 : Nat := 118140960795 + 1314800 * 2 ^ 59
def prefixEnd_1314800 : Nat := 4983230072969 + 3 ^ 40 * 1314800 * 2
def baseEnd_1314800 : Nat := 675124364531561072653351

theorem tailTrace_1314800 : CollatzResearch.WordTrace tailWord_1314800 prefixEnd_1314800 675124364531561072653351 := by
  unfold tailWord_1314800
  simp only [CollatzResearch.WordTrace]
  refine ⟨23977347818355812403886927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31969797091141083205182569 23977347818355812403886927)
  ·
    refine ⟨35966021727533718605830391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23977347818355812403886927 35966021727533718605830391)
    ·
      refine ⟨53949032591300577908745587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35966021727533718605830391 53949032591300577908745587)
      ·
        refine ⟨80923548886950866863118381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53949032591300577908745587 80923548886950866863118381)
        ·
          refine ⟨30346330832606575073669393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80923548886950866863118381 30346330832606575073669393)
          ·
            refine ⟨22759748124454931305252045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30346330832606575073669393 22759748124454931305252045)
            ·
              refine ⟨8534905546670599239469517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22759748124454931305252045 8534905546670599239469517)
              ·
                refine ⟨3200589580001474714801069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8534905546670599239469517 3200589580001474714801069)
                ·
                  refine ⟨1200221092500553018050401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3200589580001474714801069 1200221092500553018050401)
                  ·
                    refine ⟨900165819375414763537801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1200221092500553018050401 900165819375414763537801)
                    ·
                      refine ⟨675124364531561072653351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 900165819375414763537801 675124364531561072653351)
                      ·
                        rfl

theorem cell23_1314800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 3, 2, 2].length) (baseStart_1314800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314800 prefixEnd_1314800 := by exact prefixLift 1314800
  have htrace : WordTrace (prefixWord ++ tailWord_1314800) baseStart_1314800 baseEnd_1314800 := by
    simpa [prefixWord, tailWord_1314800, baseEnd_1314800] using wordTrace_append hprefix tailTrace_1314800
  have hstable : (prefixWord ++ tailWord_1314800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314800).length < 2 ^ (prefixWord ++ tailWord_1314800).sum := by decide
  have hdescent : baseEnd_1314800 < baseStart_1314800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314813 : List Nat := [1, 4, 1, 1, 1, 2, 5, 1, 1, 2, 4]
def baseStart_1314813 : Nat := 118140960795 + 1314813 * 2 ^ 59
def prefixEnd_1314813 : Nat := 4983230072969 + 3 ^ 40 * 1314813 * 2
def baseEnd_1314813 : Nat := 675131039780069521790791

theorem tailTrace_1314813 : CollatzResearch.WordTrace tailWord_1314813 prefixEnd_1314813 675131039780069521790791 := by
  unfold tailWord_1314813
  simp only [CollatzResearch.WordTrace]
  refine ⟨47955169785664528027997093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31970113190443018685331395 47955169785664528027997093)
  ·
    refine ⟨8991594334812099005249455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47955169785664528027997093 8991594334812099005249455)
    ·
      refine ⟨13487391502218148507874183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8991594334812099005249455 13487391502218148507874183)
      ·
        refine ⟨20231087253327222761811275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13487391502218148507874183 20231087253327222761811275)
        ·
          refine ⟨30346630879990834142716913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20231087253327222761811275 30346630879990834142716913)
          ·
            refine ⟨22759973159993125607037685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30346630879990834142716913 22759973159993125607037685)
            ·
              refine ⟨2133747483749355525659783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22759973159993125607037685 2133747483749355525659783)
              ·
                refine ⟨3200621225624033288489675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2133747483749355525659783 3200621225624033288489675)
                ·
                  refine ⟨4800931838436049932734513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3200621225624033288489675 4800931838436049932734513)
                  ·
                    refine ⟨3600698878827037449550885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4800931838436049932734513 3600698878827037449550885)
                    ·
                      refine ⟨675131039780069521790791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3600698878827037449550885 675131039780069521790791)
                      ·
                        rfl

theorem cell23_1314813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 5, 1, 1, 2, 4].length) (baseStart_1314813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314813 prefixEnd_1314813 := by exact prefixLift 1314813
  have htrace : WordTrace (prefixWord ++ tailWord_1314813) baseStart_1314813 baseEnd_1314813 := by
    simpa [prefixWord, tailWord_1314813, baseEnd_1314813] using wordTrace_append hprefix tailTrace_1314813
  have hstable : (prefixWord ++ tailWord_1314813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314813).length < 2 ^ (prefixWord ++ tailWord_1314813).sum := by decide
  have hdescent : baseEnd_1314813 < baseStart_1314813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314823 : List Nat := [1, 1, 4, 3, 1, 2, 4, 7]
def baseStart_1314823 : Nat := 118140960795 + 1314823 * 2 ^ 59
def prefixEnd_1314823 : Nat := 4983230072969 + 3 ^ 40 * 1314823 * 2
def baseEnd_1314823 : Nat := 25005043503207943802435

theorem tailTrace_1314823 : CollatzResearch.WordTrace tailWord_1314823 prefixEnd_1314823 25005043503207943802435 := by
  unfold tailWord_1314823
  simp only [CollatzResearch.WordTrace]
  refine ⟨47955534515628299735861123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31970356343752199823907415 47955534515628299735861123)
  ·
    refine ⟨71933301773442449603791685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47955534515628299735861123 71933301773442449603791685)
    ·
      refine ⟨13487494082520459300710941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71933301773442449603791685 13487494082520459300710941)
      ·
        refine ⟨5057810280945172237766603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13487494082520459300710941 5057810280945172237766603)
        ·
          refine ⟨7586715421417758356649905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5057810280945172237766603 7586715421417758356649905)
          ·
            refine ⟨5690036566063318767487429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7586715421417758356649905 5690036566063318767487429)
            ·
              refine ⟨1066881856136872268903893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5690036566063318767487429 1066881856136872268903893)
              ·
                refine ⟨25005043503207943802435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1066881856136872268903893 25005043503207943802435)
                ·
                  rfl

theorem cell23_1314823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 4, 7].length) (baseStart_1314823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314823 prefixEnd_1314823 := by exact prefixLift 1314823
  have htrace : WordTrace (prefixWord ++ tailWord_1314823) baseStart_1314823 baseEnd_1314823 := by
    simpa [prefixWord, tailWord_1314823, baseEnd_1314823] using wordTrace_append hprefix tailTrace_1314823
  have hstable : (prefixWord ++ tailWord_1314823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314823).length < 2 ^ (prefixWord ++ tailWord_1314823).sum := by decide
  have hdescent : baseEnd_1314823 < baseStart_1314823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314850 : List Nat := [3, 3, 1, 1, 1, 2, 1, 3, 4, 1, 3]
def baseStart_1314850 : Nat := 118140960795 + 1314850 * 2 ^ 59
def prefixEnd_1314850 : Nat := 4983230072969 + 3 ^ 40 * 1314850 * 2
def baseEnd_1314850 : Nat := 675150038564285877028121

theorem tailTrace_1314850 : CollatzResearch.WordTrace tailWord_1314850 prefixEnd_1314850 675150038564285877028121 := by
  unfold tailWord_1314850
  simp only [CollatzResearch.WordTrace]
  refine ⟨11989129821632620836773501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31971012857686988898062669 11989129821632620836773501)
  ·
    refine ⟨4495923683112232813790063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11989129821632620836773501 4495923683112232813790063)
    ·
      refine ⟨6743885524668349220685095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4495923683112232813790063 6743885524668349220685095)
      ·
        refine ⟨10115828287002523831027643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6743885524668349220685095 10115828287002523831027643)
        ·
          refine ⟨15173742430503785746541465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10115828287002523831027643 15173742430503785746541465)
          ·
            refine ⟨11380306822877839309906099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15173742430503785746541465 11380306822877839309906099)
            ·
              refine ⟨17070460234316758964859149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11380306822877839309906099 17070460234316758964859149)
              ·
                refine ⟨6401422587868784611822181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17070460234316758964859149 6401422587868784611822181)
                ·
                  refine ⟨1200266735225397114716659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6401422587868784611822181 1200266735225397114716659)
                  ·
                    refine ⟨1800400102838095672074989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1200266735225397114716659 1800400102838095672074989)
                    ·
                      refine ⟨675150038564285877028121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1800400102838095672074989 675150038564285877028121)
                      ·
                        rfl

theorem cell23_1314850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 4, 1, 3].length) (baseStart_1314850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314850 prefixEnd_1314850 := by exact prefixLift 1314850
  have htrace : WordTrace (prefixWord ++ tailWord_1314850) baseStart_1314850 baseEnd_1314850 := by
    simpa [prefixWord, tailWord_1314850, baseEnd_1314850] using wordTrace_append hprefix tailTrace_1314850
  have hstable : (prefixWord ++ tailWord_1314850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314850).length < 2 ^ (prefixWord ++ tailWord_1314850).sum := by decide
  have hdescent : baseEnd_1314850 < baseStart_1314850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314867 : List Nat := [1, 1, 1, 2, 4, 1, 6, 1, 2, 1, 3]
def baseStart_1314867 : Nat := 118140960795 + 1314867 * 2 ^ 59
def prefixEnd_1314867 : Nat := 4983230072969 + 3 ^ 40 * 1314867 * 2
def baseEnd_1314867 : Nat := 675158767735412310515543

theorem tailTrace_1314867 : CollatzResearch.WordTrace tailWord_1314867 prefixEnd_1314867 675158767735412310515543 := by
  unfold tailWord_1314867
  simp only [CollatzResearch.WordTrace]
  refine ⟨47957139327468895250462855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31971426218312596833641903 47957139327468895250462855)
  ·
    refine ⟨71935708991203342875694283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47957139327468895250462855 71935708991203342875694283)
    ·
      refine ⟨107903563486805014313541425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71935708991203342875694283 107903563486805014313541425)
      ·
        refine ⟨80927672615103760735156069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107903563486805014313541425 80927672615103760735156069)
        ·
          refine ⟨15173938615331955137841763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 80927672615103760735156069 15173938615331955137841763)
          ·
            refine ⟨22760907922997932706762645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15173938615331955137841763 22760907922997932706762645)
            ·
              refine ⟨1066917558890528095629499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 22760907922997932706762645 1066917558890528095629499)
              ·
                refine ⟨1600376338335792143444249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066917558890528095629499 1600376338335792143444249)
                ·
                  refine ⟨1200282253751844107583187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1600376338335792143444249 1200282253751844107583187)
                  ·
                    refine ⟨1800423380627766161374781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1200282253751844107583187 1800423380627766161374781)
                    ·
                      refine ⟨675158767735412310515543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1800423380627766161374781 675158767735412310515543)
                      ·
                        rfl

theorem cell23_1314867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 6, 1, 2, 1, 3].length) (baseStart_1314867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314867 prefixEnd_1314867 := by exact prefixLift 1314867
  have htrace : WordTrace (prefixWord ++ tailWord_1314867) baseStart_1314867 baseEnd_1314867 := by
    simpa [prefixWord, tailWord_1314867, baseEnd_1314867] using wordTrace_append hprefix tailTrace_1314867
  have hstable : (prefixWord ++ tailWord_1314867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314867).length < 2 ^ (prefixWord ++ tailWord_1314867).sum := by decide
  have hdescent : baseEnd_1314867 < baseStart_1314867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314894 : List Nat := [4, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2]
def baseStart_1314894 : Nat := 118140960795 + 1314894 * 2 ^ 59
def prefixEnd_1314894 : Nat := 4983230072969 + 3 ^ 40 * 1314894 * 2
def baseEnd_1314894 : Nat := 675172631713083704877919

theorem tailTrace_1314894 : CollatzResearch.WordTrace tailWord_1314894 prefixEnd_1314894 675172631713083704877919 := by
  unfold tailWord_1314894
  simp only [CollatzResearch.WordTrace]
  refine ⟨5994765512296384857711967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31972082732247385907797157 5994765512296384857711967)
  ·
    refine ⟨8992148268444577286567951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5994765512296384857711967 8992148268444577286567951)
    ·
      refine ⟨13488222402666865929851927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8992148268444577286567951 13488222402666865929851927)
      ·
        refine ⟨20232333604000298894777891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13488222402666865929851927 20232333604000298894777891)
        ·
          refine ⟨30348500406000448342166837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20232333604000298894777891 30348500406000448342166837)
          ·
            refine ⟨2845171913062542032078141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30348500406000448342166837 2845171913062542032078141)
            ·
              refine ⟨1066939467398453262029303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2845171913062542032078141 1066939467398453262029303)
              ·
                refine ⟨1600409201097679893043955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1066939467398453262029303 1600409201097679893043955)
                ·
                  refine ⟨2400613801646519839565933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1600409201097679893043955 2400613801646519839565933)
                  ·
                    refine ⟨900230175617444939837225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2400613801646519839565933 900230175617444939837225)
                    ·
                      refine ⟨675172631713083704877919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 900230175617444939837225 675172631713083704877919)
                      ·
                        rfl

theorem cell23_1314894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 3, 1, 1, 3, 2].length) (baseStart_1314894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314894 prefixEnd_1314894 := by exact prefixLift 1314894
  have htrace : WordTrace (prefixWord ++ tailWord_1314894) baseStart_1314894 baseEnd_1314894 := by
    simpa [prefixWord, tailWord_1314894, baseEnd_1314894] using wordTrace_append hprefix tailTrace_1314894
  have hstable : (prefixWord ++ tailWord_1314894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314894).length < 2 ^ (prefixWord ++ tailWord_1314894).sum := by decide
  have hdescent : baseEnd_1314894 < baseStart_1314894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314958 : List Nat := [4, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2]
def baseStart_1314958 : Nat := 118140960795 + 1314958 * 2 ^ 59
def prefixEnd_1314958 : Nat := 4983230072969 + 3 ^ 40 * 1314958 * 2
def baseEnd_1314958 : Nat := 675205494474971454477625

theorem tailTrace_1314958 : CollatzResearch.WordTrace tailWord_1314958 prefixEnd_1314958 675205494474971454477625 := by
  unfold tailWord_1314958
  simp only [CollatzResearch.WordTrace]
  refine ⟨5995057296267402224003191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31973638913426145194683685 5995057296267402224003191)
  ·
    refine ⟨8992585944401103336004787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5995057296267402224003191 8992585944401103336004787)
    ·
      refine ⟨13488878916601655004007181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8992585944401103336004787 13488878916601655004007181)
      ·
        refine ⟨5058329593725620626502693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13488878916601655004007181 5058329593725620626502693)
        ·
          refine ⟨948436798823553867469255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5058329593725620626502693 948436798823553867469255)
          ·
            refine ⟨1422655198235330801203883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948436798823553867469255 1422655198235330801203883)
            ·
              refine ⟨2133982797352996201805825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1422655198235330801203883 2133982797352996201805825)
              ·
                refine ⟨1600487098014747151354369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2133982797352996201805825 1600487098014747151354369)
                ·
                  refine ⟨1200365323511060363515777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1600487098014747151354369 1200365323511060363515777)
                  ·
                    refine ⟨900273992633295272636833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1200365323511060363515777 900273992633295272636833)
                    ·
                      refine ⟨675205494474971454477625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 900273992633295272636833 675205494474971454477625)
                      ·
                        rfl

theorem cell23_1314958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_1314958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314958 prefixEnd_1314958 := by exact prefixLift 1314958
  have htrace : WordTrace (prefixWord ++ tailWord_1314958) baseStart_1314958 baseEnd_1314958 := by
    simpa [prefixWord, tailWord_1314958, baseEnd_1314958] using wordTrace_append hprefix tailTrace_1314958
  have hstable : (prefixWord ++ tailWord_1314958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314958).length < 2 ^ (prefixWord ++ tailWord_1314958).sum := by decide
  have hdescent : baseEnd_1314958 < baseStart_1314958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1314963 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 4]
def baseStart_1314963 : Nat := 118140960795 + 1314963 * 2 ^ 59
def prefixEnd_1314963 : Nat := 4983230072969 + 3 ^ 40 * 1314963 * 2
def baseEnd_1314963 : Nat := 675208061878243934915101

theorem tailTrace_1314963 : CollatzResearch.WordTrace tailWord_1314963 prefixEnd_1314963 675208061878243934915101 := by
  unfold tailWord_1314963
  simp only [CollatzResearch.WordTrace]
  refine ⟨47960640735121103645957543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31973760490080735763971695 47960640735121103645957543)
  ·
    refine ⟨71940961102681655468936315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47960640735121103645957543 71940961102681655468936315)
    ·
      refine ⟨107911441654022483203404473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71940961102681655468936315 107911441654022483203404473)
      ·
        refine ⟨80933581240516862402553355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107911441654022483203404473 80933581240516862402553355)
        ·
          refine ⟨121400371860775293603830033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80933581240516862402553355 121400371860775293603830033)
          ·
            refine ⟨91050278895581470202872525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121400371860775293603830033 91050278895581470202872525)
            ·
              refine ⟨34143854585843051326077197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91050278895581470202872525 34143854585843051326077197)
              ·
                refine ⟨12803945469691144247278949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34143854585843051326077197 12803945469691144247278949)
                ·
                  refine ⟨2400739775567089546364803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12803945469691144247278949 2400739775567089546364803)
                  ·
                    refine ⟨3601109663350634319547205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2400739775567089546364803 3601109663350634319547205)
                    ·
                      refine ⟨675208061878243934915101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3601109663350634319547205 675208061878243934915101)
                      ·
                        rfl

theorem cell23_1314963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 4, 1, 4].length) (baseStart_1314963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1314963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1314963 prefixEnd_1314963 := by exact prefixLift 1314963
  have htrace : WordTrace (prefixWord ++ tailWord_1314963) baseStart_1314963 baseEnd_1314963 := by
    simpa [prefixWord, tailWord_1314963, baseEnd_1314963] using wordTrace_append hprefix tailTrace_1314963
  have hstable : (prefixWord ++ tailWord_1314963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1314963).length < 2 ^ (prefixWord ++ tailWord_1314963).sum := by decide
  have hdescent : baseEnd_1314963 < baseStart_1314963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1314963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315000 : List Nat := [2, 1, 2, 1, 2, 1, 4, 3, 2, 2, 3]
def baseStart_1315000 : Nat := 118140960795 + 1315000 * 2 ^ 59
def prefixEnd_1315000 : Nat := 4983230072969 + 3 ^ 40 * 1315000 * 2
def baseEnd_1315000 : Nat := 675227060662460290152431

theorem tailTrace_1315000 : CollatzResearch.WordTrace tailWord_1315000 prefixEnd_1315000 675227060662460290152431 := by
  unfold tailWord_1315000
  simp only [CollatzResearch.WordTrace]
  refine ⟨23980995117993529482527227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31974660157324705976702969 23980995117993529482527227)
  ·
    refine ⟨35971492676990294223790841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23980995117993529482527227 35971492676990294223790841)
    ·
      refine ⟨26978619507742720667843131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35971492676990294223790841 26978619507742720667843131)
      ·
        refine ⟨40467929261614081001764697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26978619507742720667843131 40467929261614081001764697)
        ·
          refine ⟨30350946946210560751323523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40467929261614081001764697 30350946946210560751323523)
          ·
            refine ⟨45526420419315841126985285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30350946946210560751323523 45526420419315841126985285)
            ·
              refine ⟨8536203828621720211309741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45526420419315841126985285 8536203828621720211309741)
              ·
                refine ⟨3201076435733145079241153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8536203828621720211309741 3201076435733145079241153)
                ·
                  refine ⟨2400807326799858809430865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3201076435733145079241153 2400807326799858809430865)
                  ·
                    refine ⟨1800605495099894107073149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2400807326799858809430865 1800605495099894107073149)
                    ·
                      refine ⟨675227060662460290152431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1800605495099894107073149 675227060662460290152431)
                      ·
                        rfl

theorem cell23_1315000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 4, 3, 2, 2, 3].length) (baseStart_1315000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315000 prefixEnd_1315000 := by exact prefixLift 1315000
  have htrace : WordTrace (prefixWord ++ tailWord_1315000) baseStart_1315000 baseEnd_1315000 := by
    simpa [prefixWord, tailWord_1315000, baseEnd_1315000] using wordTrace_append hprefix tailTrace_1315000
  have hstable : (prefixWord ++ tailWord_1315000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315000).length < 2 ^ (prefixWord ++ tailWord_1315000).sum := by decide
  have hdescent : baseEnd_1315000 < baseStart_1315000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315037 : List Nat := [1, 4, 3, 2, 1, 2, 1, 3, 6]
def baseStart_1315037 : Nat := 118140960795 + 1315037 * 2 ^ 59
def prefixEnd_1315037 : Nat := 4983230072969 + 3 ^ 40 * 1315037 * 2
def baseEnd_1315037 : Nat := 75027339938519627265529

theorem tailTrace_1315037 : CollatzResearch.WordTrace tailWord_1315037 prefixEnd_1315037 75027339938519627265529 := by
  unfold tailWord_1315037
  simp only [CollatzResearch.WordTrace]
  refine ⟨47963339736853014284151365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31975559824568676189434243 47963339736853014284151365)
  ·
    refine ⟨8993126200659940178278381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47963339736853014284151365 8993126200659940178278381)
    ·
      refine ⟨3372422325247477566854393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8993126200659940178278381 3372422325247477566854393)
      ·
        refine ⟨2529316743935608175140795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3372422325247477566854393 2529316743935608175140795)
        ·
          refine ⟨3793975115903412262711193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2529316743935608175140795 3793975115903412262711193)
          ·
            refine ⟨2845481336927559197033395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3793975115903412262711193 2845481336927559197033395)
            ·
              refine ⟨4268222005391338795550093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2845481336927559197033395 4268222005391338795550093)
              ·
                refine ⟨1600583252021752048331285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4268222005391338795550093 1600583252021752048331285)
                ·
                  refine ⟨75027339938519627265529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1600583252021752048331285 75027339938519627265529)
                  ·
                    rfl

theorem cell23_1315037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 6].length) (baseStart_1315037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315037 prefixEnd_1315037 := by exact prefixLift 1315037
  have htrace : WordTrace (prefixWord ++ tailWord_1315037) baseStart_1315037 baseEnd_1315037 := by
    simpa [prefixWord, tailWord_1315037, baseEnd_1315037] using wordTrace_append hprefix tailTrace_1315037
  have hstable : (prefixWord ++ tailWord_1315037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315037).length < 2 ^ (prefixWord ++ tailWord_1315037).sum := by decide
  have hdescent : baseEnd_1315037 < baseStart_1315037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315050 : List Nat := [3, 1, 3, 1, 1, 2, 3, 1, 3, 5]
def baseStart_1315050 : Nat := 118140960795 + 1315050 * 2 ^ 59
def prefixEnd_1315050 : Nat := 4983230072969 + 3 ^ 40 * 1315050 * 2
def baseEnd_1315050 : Nat := 225084244898395031509067

theorem tailTrace_1315050 : CollatzResearch.WordTrace tailWord_1315050 prefixEnd_1315050 225084244898395031509067 := by
  unfold tailWord_1315050
  simp only [CollatzResearch.WordTrace]
  refine ⟨11990953471451479376093651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31975875923870611669583069 11990953471451479376093651)
  ·
    refine ⟨17986430207177219064140477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11990953471451479376093651 17986430207177219064140477)
    ·
      refine ⟨6744911327691457149052679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17986430207177219064140477 6744911327691457149052679)
      ·
        refine ⟨10117366991537185723579019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6744911327691457149052679 10117366991537185723579019)
        ·
          refine ⟨15176050487305778585368529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10117366991537185723579019 15176050487305778585368529)
          ·
            refine ⟨11382037865479333939026397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15176050487305778585368529 11382037865479333939026397)
            ·
              refine ⟨4268264199554750227134899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11382037865479333939026397 4268264199554750227134899)
              ·
                refine ⟨6402396299332125340702349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4268264199554750227134899 6402396299332125340702349)
                ·
                  refine ⟨2400898612249547002763381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6402396299332125340702349 2400898612249547002763381)
                  ·
                    refine ⟨225084244898395031509067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2400898612249547002763381 225084244898395031509067)
                    ·
                      rfl

theorem cell23_1315050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_1315050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315050 prefixEnd_1315050 := by exact prefixLift 1315050
  have htrace : WordTrace (prefixWord ++ tailWord_1315050) baseStart_1315050 baseEnd_1315050 := by
    simpa [prefixWord, tailWord_1315050, baseEnd_1315050] using wordTrace_append hprefix tailTrace_1315050
  have hstable : (prefixWord ++ tailWord_1315050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315050).length < 2 ^ (prefixWord ++ tailWord_1315050).sum := by decide
  have hdescent : baseEnd_1315050 < baseStart_1315050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315057 : List Nat := [1, 2, 2, 2, 2, 1, 3, 3, 2, 3, 2]
def baseStart_1315057 : Nat := 118140960795 + 1315057 * 2 ^ 59
def prefixEnd_1315057 : Nat := 4983230072969 + 3 ^ 40 * 1315057 * 2
def baseEnd_1315057 : Nat := 675256329059766567139669

theorem tailTrace_1315057 : CollatzResearch.WordTrace tailWord_1315057 prefixEnd_1315057 675256329059766567139669 := by
  unfold tailWord_1315057
  simp only [CollatzResearch.WordTrace]
  refine ⟨47964069196780557699879425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31976046131187038466586283 47964069196780557699879425)
  ·
    refine ⟨35973051897585418274909569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47964069196780557699879425 35973051897585418274909569)
    ·
      refine ⟨26979788923189063706182177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35973051897585418274909569 26979788923189063706182177)
      ·
        refine ⟨20234841692391797779636633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26979788923189063706182177 20234841692391797779636633)
        ·
          refine ⟨15176131269293848334727475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20234841692391797779636633 15176131269293848334727475)
          ·
            refine ⟨22764196903940772502091213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15176131269293848334727475 22764196903940772502091213)
            ·
              refine ⟨8536573838977789688284205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22764196903940772502091213 8536573838977789688284205)
              ·
                refine ⟨3201215189616671133106577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8536573838977789688284205 3201215189616671133106577)
                ·
                  refine ⟨2400911392212503349829933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3201215189616671133106577 2400911392212503349829933)
                  ·
                    refine ⟨900341772079688756186225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2400911392212503349829933 900341772079688756186225)
                    ·
                      refine ⟨675256329059766567139669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 900341772079688756186225 675256329059766567139669)
                      ·
                        rfl

theorem cell23_1315057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 3, 2, 3, 2].length) (baseStart_1315057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315057 prefixEnd_1315057 := by exact prefixLift 1315057
  have htrace : WordTrace (prefixWord ++ tailWord_1315057) baseStart_1315057 baseEnd_1315057 := by
    simpa [prefixWord, tailWord_1315057, baseEnd_1315057] using wordTrace_append hprefix tailTrace_1315057
  have hstable : (prefixWord ++ tailWord_1315057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315057).length < 2 ^ (prefixWord ++ tailWord_1315057).sum := by decide
  have hdescent : baseEnd_1315057 < baseStart_1315057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315081 : List Nat := [1, 2, 1, 1, 3, 4, 4, 2, 1, 1, 3]
def baseStart_1315081 : Nat := 118140960795 + 1315081 * 2 ^ 59
def prefixEnd_1315081 : Nat := 4983230072969 + 3 ^ 40 * 1315081 * 2
def baseEnd_1315081 : Nat := 675268652595474473239559

theorem tailTrace_1315081 : CollatzResearch.WordTrace tailWord_1315081 prefixEnd_1315081 675268652595474473239559 := by
  unfold tailWord_1315081
  simp only [CollatzResearch.WordTrace]
  refine ⟨47964944548693609798753097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31976629699129073199168731 47964944548693609798753097)
  ·
    refine ⟨35973708411520207349064823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47964944548693609798753097 35973708411520207349064823)
    ·
      refine ⟨53960562617280311023597235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35973708411520207349064823 53960562617280311023597235)
      ·
        refine ⟨80940843925920466535395853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53960562617280311023597235 80940843925920466535395853)
        ·
          refine ⟨30352816472220174950773445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 80940843925920466535395853 30352816472220174950773445)
          ·
            refine ⟨5691153088541282803270021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30352816472220174950773445 5691153088541282803270021)
            ·
              refine ⟨1067091204101490525613129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5691153088541282803270021 1067091204101490525613129)
              ·
                refine ⟨800318403076117894209847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1067091204101490525613129 800318403076117894209847)
                ·
                  refine ⟨1200477604614176841314771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 800318403076117894209847 1200477604614176841314771)
                  ·
                    refine ⟨1800716406921265261972157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1200477604614176841314771 1800716406921265261972157)
                    ·
                      refine ⟨675268652595474473239559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1800716406921265261972157 675268652595474473239559)
                      ·
                        rfl

theorem cell23_1315081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 1, 1, 3].length) (baseStart_1315081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315081 prefixEnd_1315081 := by exact prefixLift 1315081
  have htrace : WordTrace (prefixWord ++ tailWord_1315081) baseStart_1315081 baseEnd_1315081 := by
    simpa [prefixWord, tailWord_1315081, baseEnd_1315081] using wordTrace_append hprefix tailTrace_1315081
  have hstable : (prefixWord ++ tailWord_1315081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315081).length < 2 ^ (prefixWord ++ tailWord_1315081).sum := by decide
  have hdescent : baseEnd_1315081 < baseStart_1315081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315087 : List Nat := [1, 1, 2, 1, 1, 1, 3, 2, 7, 2, 2]
def baseStart_1315087 : Nat := 118140960795 + 1315087 * 2 ^ 59
def prefixEnd_1315087 : Nat := 4983230072969 + 3 ^ 40 * 1315087 * 2
def baseEnd_1315087 : Nat := 675271733479401449764531

theorem tailTrace_1315087 : CollatzResearch.WordTrace tailWord_1315087 prefixEnd_1315087 675271733479401449764531 := by
  unfold tailWord_1315087
  simp only [CollatzResearch.WordTrace]
  refine ⟨47965163386671872823471515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31976775591114581882314343 47965163386671872823471515)
  ·
    refine ⟨71947745080007809235207273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47965163386671872823471515 71947745080007809235207273)
    ·
      refine ⟨53960808810005856926405455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71947745080007809235207273 53960808810005856926405455)
      ·
        refine ⟨80941213215008785389608183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53960808810005856926405455 80941213215008785389608183)
        ·
          refine ⟨121411819822513178084412275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80941213215008785389608183 121411819822513178084412275)
          ·
            refine ⟨182117729733769767126618413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121411819822513178084412275 182117729733769767126618413)
            ·
              refine ⟨68294148650163662672481905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182117729733769767126618413 68294148650163662672481905)
              ·
                refine ⟨51220611487622747004361429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68294148650163662672481905 51220611487622747004361429)
                ·
                  refine ⟨1200483081741158132914721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 51220611487622747004361429 1200483081741158132914721)
                  ·
                    refine ⟨900362311305868599686041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1200483081741158132914721 900362311305868599686041)
                    ·
                      refine ⟨675271733479401449764531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 900362311305868599686041 675271733479401449764531)
                      ·
                        rfl

theorem cell23_1315087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 2, 7, 2, 2].length) (baseStart_1315087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315087 prefixEnd_1315087 := by exact prefixLift 1315087
  have htrace : WordTrace (prefixWord ++ tailWord_1315087) baseStart_1315087 baseEnd_1315087 := by
    simpa [prefixWord, tailWord_1315087, baseEnd_1315087] using wordTrace_append hprefix tailTrace_1315087
  have hstable : (prefixWord ++ tailWord_1315087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315087).length < 2 ^ (prefixWord ++ tailWord_1315087).sum := by decide
  have hdescent : baseEnd_1315087 < baseStart_1315087 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315104 : List Nat := [2, 1, 1, 5, 2, 1, 1, 1, 5, 2, 2]
def baseStart_1315104 : Nat := 118140960795 + 1315104 * 2 ^ 59
def prefixEnd_1315104 : Nat := 4983230072969 + 3 ^ 40 * 1315104 * 2
def baseEnd_1315104 : Nat := 675280462650527883251953

theorem tailTrace_1315104 : CollatzResearch.WordTrace tailWord_1315104 prefixEnd_1315104 675280462650527883251953 := by
  unfold tailWord_1315104
  simp only [CollatzResearch.WordTrace]
  refine ⟨23982891713805142363420183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31977188951740189817893577 23982891713805142363420183)
  ·
    refine ⟨35974337570707713545130275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23982891713805142363420183 35974337570707713545130275)
    ·
      refine ⟨53961506356061570317695413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35974337570707713545130275 53961506356061570317695413)
      ·
        refine ⟨5058891220880772217283945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 53961506356061570317695413 5058891220880772217283945)
        ·
          refine ⟨3794168415660579162962959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5058891220880772217283945 3794168415660579162962959)
          ·
            refine ⟨5691252623490868744444439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3794168415660579162962959 5691252623490868744444439)
            ·
              refine ⟨8536878935236303116666659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5691252623490868744444439 8536878935236303116666659)
              ·
                refine ⟨12805318402854454674999989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8536878935236303116666659 12805318402854454674999989)
                ·
                  refine ⟨1200498600267605125781249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12805318402854454674999989 1200498600267605125781249)
                  ·
                    refine ⟨900373950200703844335937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1200498600267605125781249 900373950200703844335937)
                    ·
                      refine ⟨675280462650527883251953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 900373950200703844335937 675280462650527883251953)
                      ·
                        rfl

theorem cell23_1315104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_1315104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315104 prefixEnd_1315104 := by exact prefixLift 1315104
  have htrace : WordTrace (prefixWord ++ tailWord_1315104) baseStart_1315104 baseEnd_1315104 := by
    simpa [prefixWord, tailWord_1315104, baseEnd_1315104] using wordTrace_append hprefix tailTrace_1315104
  have hstable : (prefixWord ++ tailWord_1315104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315104).length < 2 ^ (prefixWord ++ tailWord_1315104).sum := by decide
  have hdescent : baseEnd_1315104 < baseStart_1315104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315107 : List Nat := [1, 1, 1, 4, 2, 2, 2, 4, 1, 2, 3]
def baseStart_1315107 : Nat := 118140960795 + 1315107 * 2 ^ 59
def prefixEnd_1315107 : Nat := 4983230072969 + 3 ^ 40 * 1315107 * 2
def baseEnd_1315107 : Nat := 675282003092491371514439

theorem tailTrace_1315107 : CollatzResearch.WordTrace tailWord_1315107 prefixEnd_1315107 675282003092491371514439 := by
  unfold tailWord_1315107
  simp only [CollatzResearch.WordTrace]
  refine ⟨47965892846599416239199575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31977261897732944159466383 47965892846599416239199575)
  ·
    refine ⟨71948839269899124358799363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47965892846599416239199575 71948839269899124358799363)
    ·
      refine ⟨107923258904848686538199045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71948839269899124358799363 107923258904848686538199045)
      ·
        refine ⟨20235611044659128725912321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107923258904848686538199045 20235611044659128725912321)
        ·
          refine ⟨15176708283494346544434241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20235611044659128725912321 15176708283494346544434241)
          ·
            refine ⟨11382531212620759908325681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15176708283494346544434241 11382531212620759908325681)
            ·
              refine ⟨8536898409465569931244261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11382531212620759908325681 8536898409465569931244261)
              ·
                refine ⟨1600668451774794362108299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8536898409465569931244261 1600668451774794362108299)
                ·
                  refine ⟨2401002677662191543162449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1600668451774794362108299 2401002677662191543162449)
                  ·
                    refine ⟨1800752008246643657371837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2401002677662191543162449 1800752008246643657371837)
                    ·
                      refine ⟨675282003092491371514439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1800752008246643657371837 675282003092491371514439)
                      ·
                        rfl

theorem cell23_1315107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 4, 1, 2, 3].length) (baseStart_1315107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315107 prefixEnd_1315107 := by exact prefixLift 1315107
  have htrace : WordTrace (prefixWord ++ tailWord_1315107) baseStart_1315107 baseEnd_1315107 := by
    simpa [prefixWord, tailWord_1315107, baseEnd_1315107] using wordTrace_append hprefix tailTrace_1315107
  have hstable : (prefixWord ++ tailWord_1315107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315107).length < 2 ^ (prefixWord ++ tailWord_1315107).sum := by decide
  have hdescent : baseEnd_1315107 < baseStart_1315107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315118 : List Nat := [4, 1, 3, 3, 1, 2, 2, 1, 1, 5]
def baseStart_1315118 : Nat := 118140960795 + 1315118 * 2 ^ 59
def prefixEnd_1315118 : Nat := 4983230072969 + 3 ^ 40 * 1315118 * 2
def baseEnd_1315118 : Nat := 225095883793230276158963

theorem tailTrace_1315118 : CollatzResearch.WordTrace tailWord_1315118 prefixEnd_1315118 225095883793230276158963 := by
  unfold tailWord_1315118
  simp only [CollatzResearch.WordTrace]
  refine ⟨5995786756194945639731251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31977529366373043411900005 5995786756194945639731251)
  ·
    refine ⟨8993680134292418459596877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5995786756194945639731251 8993680134292418459596877)
    ·
      refine ⟨3372630050359656922348829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8993680134292418459596877 3372630050359656922348829)
      ·
        refine ⟨1264736268884871345880811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3372630050359656922348829 1264736268884871345880811)
        ·
          refine ⟨1897104403327307018821217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1264736268884871345880811 1897104403327307018821217)
          ·
            refine ⟨1422828302495480264115913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1897104403327307018821217 1422828302495480264115913)
            ·
              refine ⟨1067121226871610198086935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1422828302495480264115913 1067121226871610198086935)
              ·
                refine ⟨1600681840307415297130403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1067121226871610198086935 1600681840307415297130403)
                ·
                  refine ⟨2401022760461122945695605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1600681840307415297130403 2401022760461122945695605)
                  ·
                    refine ⟨225095883793230276158963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2401022760461122945695605 225095883793230276158963)
                    ·
                      rfl

theorem cell23_1315118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_1315118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315118 prefixEnd_1315118 := by exact prefixLift 1315118
  have htrace : WordTrace (prefixWord ++ tailWord_1315118) baseStart_1315118 baseEnd_1315118 := by
    simpa [prefixWord, tailWord_1315118, baseEnd_1315118] using wordTrace_append hprefix tailTrace_1315118
  have hstable : (prefixWord ++ tailWord_1315118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315118).length < 2 ^ (prefixWord ++ tailWord_1315118).sum := by decide
  have hdescent : baseEnd_1315118 < baseStart_1315118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315120 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3]
def baseStart_1315120 : Nat := 118140960795 + 1315120 * 2 ^ 59
def prefixEnd_1315120 : Nat := 4983230072969 + 3 ^ 40 * 1315120 * 2
def baseEnd_1315120 : Nat := 675288678340999820651879

theorem tailTrace_1315120 : CollatzResearch.WordTrace tailWord_1315120 prefixEnd_1315120 675288678340999820651879 := by
  unfold tailWord_1315120
  simp only [CollatzResearch.WordTrace]
  refine ⟨23983183497776159729711407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31977577997034879639615209 23983183497776159729711407)
  ·
    refine ⟨35974775246664239594567111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23983183497776159729711407 35974775246664239594567111)
    ·
      refine ⟨53962162869996359391850667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35974775246664239594567111 53962162869996359391850667)
      ·
        refine ⟨80943244304994539087776001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53962162869996359391850667 80943244304994539087776001)
        ·
          refine ⟨60707433228745904315832001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80943244304994539087776001 60707433228745904315832001)
          ·
            refine ⟨45530574921559428236874001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60707433228745904315832001 45530574921559428236874001)
            ·
              refine ⟨34147931191169571177655501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45530574921559428236874001 34147931191169571177655501)
              ·
                refine ⟨12805474196688589191620813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34147931191169571177655501 12805474196688589191620813)
                ·
                  refine ⟨4802052823758220946857805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12805474196688589191620813 4802052823758220946857805)
                  ·
                    refine ⟨1800769808909332855071677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4802052823758220946857805 1800769808909332855071677)
                    ·
                      refine ⟨675288678340999820651879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1800769808909332855071677 675288678340999820651879)
                      ·
                        rfl

theorem cell23_1315120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3].length) (baseStart_1315120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315120 prefixEnd_1315120 := by exact prefixLift 1315120
  have htrace : WordTrace (prefixWord ++ tailWord_1315120) baseStart_1315120 baseEnd_1315120 := by
    simpa [prefixWord, tailWord_1315120, baseEnd_1315120] using wordTrace_append hprefix tailTrace_1315120
  have hstable : (prefixWord ++ tailWord_1315120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315120).length < 2 ^ (prefixWord ++ tailWord_1315120).sum := by decide
  have hdescent : baseEnd_1315120 < baseStart_1315120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315121 : List Nat := [1, 2, 2, 3, 4, 2, 2, 1, 1, 1, 4]
def baseStart_1315121 : Nat := 118140960795 + 1315121 * 2 ^ 59
def prefixEnd_1315121 : Nat := 4983230072969 + 3 ^ 40 * 1315121 * 2
def baseEnd_1315121 : Nat := 675289191821654316739375

theorem tailTrace_1315121 : CollatzResearch.WordTrace tailWord_1315121 prefixEnd_1315121 675289191821654316739375 := by
  unfold tailWord_1315121
  simp only [CollatzResearch.WordTrace]
  refine ⟨47966403468548696630209217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31977602312365797753472811 47966403468548696630209217)
  ·
    refine ⟨35974802601411522472656913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47966403468548696630209217 35974802601411522472656913)
    ·
      refine ⟨26981101951058641854492685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35974802601411522472656913 26981101951058641854492685)
      ·
        refine ⟨10117913231646990695434757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26981101951058641854492685 10117913231646990695434757)
        ·
          refine ⟨1897108730933810755394017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10117913231646990695434757 1897108730933810755394017)
          ·
            refine ⟨1422831548200358066545513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1897108730933810755394017 1422831548200358066545513)
            ·
              refine ⟨1067123661150268549909135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1422831548200358066545513 1067123661150268549909135)
              ·
                refine ⟨1600685491725402824863703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1067123661150268549909135 1600685491725402824863703)
                ·
                  refine ⟨2401028237588104237295555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1600685491725402824863703 2401028237588104237295555)
                  ·
                    refine ⟨3601542356382156355943333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2401028237588104237295555 3601542356382156355943333)
                    ·
                      refine ⟨675289191821654316739375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3601542356382156355943333 675289191821654316739375)
                      ·
                        rfl

theorem cell23_1315121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 2, 2, 1, 1, 1, 4].length) (baseStart_1315121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315121 prefixEnd_1315121 := by exact prefixLift 1315121
  have htrace : WordTrace (prefixWord ++ tailWord_1315121) baseStart_1315121 baseEnd_1315121 := by
    simpa [prefixWord, tailWord_1315121, baseEnd_1315121] using wordTrace_append hprefix tailTrace_1315121
  have hstable : (prefixWord ++ tailWord_1315121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315121).length < 2 ^ (prefixWord ++ tailWord_1315121).sum := by decide
  have hdescent : baseEnd_1315121 < baseStart_1315121 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315147 : List Nat := [1, 1, 1, 1, 3, 1, 1, 6, 3, 3, 2]
def baseStart_1315147 : Nat := 118140960795 + 1315147 * 2 ^ 59
def prefixEnd_1315147 : Nat := 4983230072969 + 3 ^ 40 * 1315147 * 2
def baseEnd_1315147 : Nat := 675302542318671215014255

theorem tailTrace_1315147 : CollatzResearch.WordTrace tailWord_1315147 prefixEnd_1315147 675302542318671215014255 := by
  unfold tailWord_1315147
  simp only [CollatzResearch.WordTrace]
  refine ⟨47967351766454503070655695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31978234510969668713770463 47967351766454503070655695)
  ·
    refine ⟨71951027649681754605983543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47967351766454503070655695 71951027649681754605983543)
    ·
      refine ⟨107926541474522631908975315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71951027649681754605983543 107926541474522631908975315)
      ·
        refine ⟨161889812211783947863462973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107926541474522631908975315 161889812211783947863462973)
        ·
          refine ⟨60708679579418980448798615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161889812211783947863462973 60708679579418980448798615)
          ·
            refine ⟨91063019369128470673197923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60708679579418980448798615 91063019369128470673197923)
            ·
              refine ⟨136594529053692706009796885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91063019369128470673197923 136594529053692706009796885)
              ·
                refine ⟨6402868549391845594209229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 136594529053692706009796885 6402868549391845594209229)
                ·
                  refine ⟨2401075706021942097828461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6402868549391845594209229 2401075706021942097828461)
                  ·
                    refine ⟨900403389758228286685673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2401075706021942097828461 900403389758228286685673)
                    ·
                      refine ⟨675302542318671215014255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 900403389758228286685673 675302542318671215014255)
                      ·
                        rfl

theorem cell23_1315147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 6, 3, 3, 2].length) (baseStart_1315147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315147 prefixEnd_1315147 := by exact prefixLift 1315147
  have htrace : WordTrace (prefixWord ++ tailWord_1315147) baseStart_1315147 baseEnd_1315147 := by
    simpa [prefixWord, tailWord_1315147, baseEnd_1315147] using wordTrace_append hprefix tailTrace_1315147
  have hstable : (prefixWord ++ tailWord_1315147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315147).length < 2 ^ (prefixWord ++ tailWord_1315147).sum := by decide
  have hdescent : baseEnd_1315147 < baseStart_1315147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315154 : List Nat := [3, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3]
def baseStart_1315154 : Nat := 118140960795 + 1315154 * 2 ^ 59
def prefixEnd_1315154 : Nat := 4983230072969 + 3 ^ 40 * 1315154 * 2
def baseEnd_1315154 : Nat := 675306136683252687626723

theorem tailTrace_1315154 : CollatzResearch.WordTrace tailWord_1315154 prefixEnd_1315154 675306136683252687626723 := by
  unfold tailWord_1315154
  simp only [CollatzResearch.WordTrace]
  refine ⟨11991901769357285816540129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31978404718286095510773677 11991901769357285816540129)
  ·
    refine ⟨8993926327017964362405097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11991901769357285816540129 8993926327017964362405097)
    ·
      refine ⟨6745444745263473271803823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8993926327017964362405097 6745444745263473271803823)
      ·
        refine ⟨10118167117895209907705735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6745444745263473271803823 10118167117895209907705735)
        ·
          refine ⟨15177250676842814861558603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10118167117895209907705735 15177250676842814861558603)
          ·
            refine ⟨22765876015264222292337905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15177250676842814861558603 22765876015264222292337905)
            ·
              refine ⟨17074407011448166719253429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22765876015264222292337905 17074407011448166719253429)
              ·
                refine ⟨1600725657323265629930009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17074407011448166719253429 1600725657323265629930009)
                ·
                  refine ⟨1200544242992449222447507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1600725657323265629930009 1200544242992449222447507)
                  ·
                    refine ⟨1800816364488673833671261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1200544242992449222447507 1800816364488673833671261)
                    ·
                      refine ⟨675306136683252687626723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1800816364488673833671261 675306136683252687626723)
                      ·
                        rfl

theorem cell23_1315154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3].length) (baseStart_1315154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315154 prefixEnd_1315154 := by exact prefixLift 1315154
  have htrace : WordTrace (prefixWord ++ tailWord_1315154) baseStart_1315154 baseEnd_1315154 := by
    simpa [prefixWord, tailWord_1315154, baseEnd_1315154] using wordTrace_append hprefix tailTrace_1315154
  have hstable : (prefixWord ++ tailWord_1315154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315154).length < 2 ^ (prefixWord ++ tailWord_1315154).sum := by decide
  have hdescent : baseEnd_1315154 < baseStart_1315154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315166 : List Nat := [4, 4, 2, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_1315166 : Nat := 118140960795 + 1315166 * 2 ^ 59
def prefixEnd_1315166 : Nat := 4983230072969 + 3 ^ 40 * 1315166 * 2
def baseEnd_1315166 : Nat := 675312298451106640676669

theorem tailTrace_1315166 : CollatzResearch.WordTrace tailWord_1315166 prefixEnd_1315166 675312298451106640676669 := by
  unfold tailWord_1315166
  simp only [CollatzResearch.WordTrace]
  refine ⟨5996005594173208664449669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31978696502257112877064901 5996005594173208664449669)
  ·
    refine ⟨1124251048907476624584313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5996005594173208664449669 1124251048907476624584313)
    ·
      refine ⟨843188286680607468438235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1124251048907476624584313 843188286680607468438235)
      ·
        refine ⟨1264782430020911202657353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 843188286680607468438235 1264782430020911202657353)
        ·
          refine ⟨948586822515683401993015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1264782430020911202657353 948586822515683401993015)
          ·
            refine ⟨1422880233773525102989523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 948586822515683401993015 1422880233773525102989523)
            ·
              refine ⟨2134320350660287654484285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1422880233773525102989523 2134320350660287654484285)
              ·
                refine ⟨800370131497607870431607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2134320350660287654484285 800370131497607870431607)
                ·
                  refine ⟨1200555197246411805647411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 800370131497607870431607 1200555197246411805647411)
                  ·
                    refine ⟨1800832795869617708471117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1200555197246411805647411 1800832795869617708471117)
                    ·
                      refine ⟨675312298451106640676669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1800832795869617708471117 675312298451106640676669)
                      ·
                        rfl

theorem cell23_1315166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_1315166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315166 prefixEnd_1315166 := by exact prefixLift 1315166
  have htrace : WordTrace (prefixWord ++ tailWord_1315166) baseStart_1315166 baseEnd_1315166 := by
    simpa [prefixWord, tailWord_1315166, baseEnd_1315166] using wordTrace_append hprefix tailTrace_1315166
  have hstable : (prefixWord ++ tailWord_1315166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315166).length < 2 ^ (prefixWord ++ tailWord_1315166).sum := by decide
  have hdescent : baseEnd_1315166 < baseStart_1315166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315177 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 3, 4, 2]
def baseStart_1315177 : Nat := 118140960795 + 1315177 * 2 ^ 59
def prefixEnd_1315177 : Nat := 4983230072969 + 3 ^ 40 * 1315177 * 2
def baseEnd_1315177 : Nat := 675317946738306097639117

theorem tailTrace_1315177 : CollatzResearch.WordTrace tailWord_1315177 prefixEnd_1315177 675317946738306097639117 := by
  unfold tailWord_1315177
  simp only [CollatzResearch.WordTrace]
  refine ⟨47968445956345818194247785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31978963970897212129498523 47968445956345818194247785)
  ·
    refine ⟨35976334467259363645685839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47968445956345818194247785 35976334467259363645685839)
    ·
      refine ⟨53964501700889045468528759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35976334467259363645685839 53964501700889045468528759)
      ·
        refine ⟨80946752551333568202793139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53964501700889045468528759 80946752551333568202793139)
        ·
          refine ⟨121420128827000352304189709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80946752551333568202793139 121420128827000352304189709)
          ·
            refine ⟨45532548310125132114071141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121420128827000352304189709 45532548310125132114071141)
            ·
              refine ⟨8537352808148462271388339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45532548310125132114071141 8537352808148462271388339)
              ·
                refine ⟨12806029212222693407082509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8537352808148462271388339 12806029212222693407082509)
                ·
                  refine ⟨4802260954583510027655941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12806029212222693407082509 4802260954583510027655941)
                  ·
                    refine ⟨900423928984408130185489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4802260954583510027655941 900423928984408130185489)
                    ·
                      refine ⟨675317946738306097639117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 900423928984408130185489 675317946738306097639117)
                      ·
                        rfl

theorem cell23_1315177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 3, 4, 2].length) (baseStart_1315177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315177 prefixEnd_1315177 := by exact prefixLift 1315177
  have htrace : WordTrace (prefixWord ++ tailWord_1315177) baseStart_1315177 baseEnd_1315177 := by
    simpa [prefixWord, tailWord_1315177, baseEnd_1315177] using wordTrace_append hprefix tailTrace_1315177
  have hstable : (prefixWord ++ tailWord_1315177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315177).length < 2 ^ (prefixWord ++ tailWord_1315177).sum := by decide
  have hdescent : baseEnd_1315177 < baseStart_1315177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315211 : List Nat := [1, 1, 1, 1, 4, 5, 1, 3, 2, 2, 2]
def baseStart_1315211 : Nat := 118140960795 + 1315211 * 2 ^ 59
def prefixEnd_1315211 : Nat := 4983230072969 + 3 ^ 40 * 1315211 * 2
def baseEnd_1315211 : Nat := 675335405080558964613961

theorem tailTrace_1315211 : CollatzResearch.WordTrace tailWord_1315211 prefixEnd_1315211 675335405080558964613961 := by
  unfold tailWord_1315211
  simp only [CollatzResearch.WordTrace]
  refine ⟨47969686038222642000985487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31979790692148428000656991 47969686038222642000985487)
  ·
    refine ⟨71954529057333963001478231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47969686038222642000985487 71954529057333963001478231)
    ·
      refine ⟨107931793586000944502217347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71954529057333963001478231 107931793586000944502217347)
      ·
        refine ⟨161897690379001416753326021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107931793586000944502217347 161897690379001416753326021)
        ·
          refine ⟨30355816946062765641248629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 161897690379001416753326021 30355816946062765641248629)
          ·
            refine ⟨2845857838693384278867059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30355816946062765641248629 2845857838693384278867059)
            ·
              refine ⟨4268786758040076418300589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2845857838693384278867059 4268786758040076418300589)
              ·
                refine ⟨1600795034265028656862721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4268786758040076418300589 1600795034265028656862721)
                ·
                  refine ⟨1200596275698771492647041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1600795034265028656862721 1200596275698771492647041)
                  ·
                    refine ⟨900447206774078619485281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1200596275698771492647041 900447206774078619485281)
                    ·
                      refine ⟨675335405080558964613961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 900447206774078619485281 675335405080558964613961)
                      ·
                        rfl

theorem cell23_1315211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 2, 2, 2].length) (baseStart_1315211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315211 prefixEnd_1315211 := by exact prefixLift 1315211
  have htrace : WordTrace (prefixWord ++ tailWord_1315211) baseStart_1315211 baseEnd_1315211 := by
    simpa [prefixWord, tailWord_1315211, baseEnd_1315211] using wordTrace_append hprefix tailTrace_1315211
  have hstable : (prefixWord ++ tailWord_1315211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315211).length < 2 ^ (prefixWord ++ tailWord_1315211).sum := by decide
  have hdescent : baseEnd_1315211 < baseStart_1315211 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315234 : List Nat := [3, 3, 1, 2, 1, 1, 2, 5, 5]
def baseStart_1315234 : Nat := 118140960795 + 1315234 * 2 ^ 59
def prefixEnd_1315234 : Nat := 4983230072969 + 3 ^ 40 * 1315234 * 2
def baseEnd_1315234 : Nat := 75038579459512486069595

theorem tailTrace_1315234 : CollatzResearch.WordTrace tailWord_1315234 prefixEnd_1315234 75038579459512486069595 := by
  unfold tailWord_1315234
  simp only [CollatzResearch.WordTrace]
  refine ⟨11992631229284829232268189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31980349944759544619381837 11992631229284829232268189)
  ·
    refine ⟨4497236710981810962100571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11992631229284829232268189 4497236710981810962100571)
    ·
      refine ⟨6745855066472716443150857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4497236710981810962100571 6745855066472716443150857)
      ·
        refine ⟨5059391299854537332363143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6745855066472716443150857 5059391299854537332363143)
        ·
          refine ⟨7589086949781805998544715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5059391299854537332363143 7589086949781805998544715)
          ·
            refine ⟨11383630424672708997817073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7589086949781805998544715 11383630424672708997817073)
            ·
              refine ⟨8537722818504531748362805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11383630424672708997817073 8537722818504531748362805)
              ·
                refine ⟨800411514234799851409013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8537722818504531748362805 800411514234799851409013)
                ·
                  refine ⟨75038579459512486069595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 800411514234799851409013 75038579459512486069595)
                  ·
                    rfl

theorem cell23_1315234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_1315234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315234 prefixEnd_1315234 := by exact prefixLift 1315234
  have htrace : WordTrace (prefixWord ++ tailWord_1315234) baseStart_1315234 baseEnd_1315234 := by
    simpa [prefixWord, tailWord_1315234, baseEnd_1315234] using wordTrace_append hprefix tailTrace_1315234
  have hstable : (prefixWord ++ tailWord_1315234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315234).length < 2 ^ (prefixWord ++ tailWord_1315234).sum := by decide
  have hdescent : baseEnd_1315234 < baseStart_1315234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315245 : List Nat := [1, 5, 2, 2, 2, 1, 2, 2, 2, 2, 2]
def baseStart_1315245 : Nat := 118140960795 + 1315245 * 2 ^ 59
def prefixEnd_1315245 : Nat := 4983230072969 + 3 ^ 40 * 1315245 * 2
def baseEnd_1315245 : Nat := 675352863422811831588805

theorem tailTrace_1315245 : CollatzResearch.WordTrace tailWord_1315245 prefixEnd_1315245 675352863422811831588805 := by
  unfold tailWord_1315245
  simp only [CollatzResearch.WordTrace]
  refine ⟨47970926120099465807723189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31980617413399643871815459 47970926120099465807723189)
  ·
    refine ⟨4497274323759324919474049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 47970926120099465807723189 4497274323759324919474049)
    ·
      refine ⟨3372955742819493689605537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4497274323759324919474049 3372955742819493689605537)
      ·
        refine ⟨2529716807114620267204153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3372955742819493689605537 2529716807114620267204153)
        ·
          refine ⟨1897287605335965200403115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2529716807114620267204153 1897287605335965200403115)
          ·
            refine ⟨2845931408003947800604673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1897287605335965200403115 2845931408003947800604673)
            ·
              refine ⟨2134448556002960850453505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2845931408003947800604673 2134448556002960850453505)
              ·
                refine ⟨1600836417002220637840129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2134448556002960850453505 1600836417002220637840129)
                ·
                  refine ⟨1200627312751665478380097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1600836417002220637840129 1200627312751665478380097)
                  ·
                    refine ⟨900470484563749108785073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1200627312751665478380097 900470484563749108785073)
                    ·
                      refine ⟨675352863422811831588805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 900470484563749108785073 675352863422811831588805)
                      ·
                        rfl

theorem cell23_1315245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_1315245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315245 prefixEnd_1315245 := by exact prefixLift 1315245
  have htrace : WordTrace (prefixWord ++ tailWord_1315245) baseStart_1315245 baseEnd_1315245 := by
    simpa [prefixWord, tailWord_1315245, baseEnd_1315245] using wordTrace_append hprefix tailTrace_1315245
  have hstable : (prefixWord ++ tailWord_1315245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315245).length < 2 ^ (prefixWord ++ tailWord_1315245).sum := by decide
  have hdescent : baseEnd_1315245 < baseStart_1315245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315257 : List Nat := [1, 2, 1, 4, 3, 1, 2, 1, 1, 2, 5]
def baseStart_1315257 : Nat := 118140960795 + 1315257 * 2 ^ 59
def prefixEnd_1315257 : Nat := 4983230072969 + 3 ^ 40 * 1315257 * 2
def baseEnd_1315257 : Nat := 675359025190665784638749

theorem tailTrace_1315257 : CollatzResearch.WordTrace tailWord_1315257 prefixEnd_1315257 675359025190665784638749 := by
  unfold tailWord_1315257
  simp only [CollatzResearch.WordTrace]
  refine ⟨47971363796055991857160025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31980909197370661238106683 47971363796055991857160025)
  ·
    refine ⟨35978522847041993892870019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47971363796055991857160025 35978522847041993892870019)
    ·
      refine ⟨53967784270562990839305029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35978522847041993892870019 53967784270562990839305029)
      ·
        refine ⟨10118959550730560782369693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 53967784270562990839305029 10118959550730560782369693)
        ·
          refine ⟨3794609831523960293388635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10118959550730560782369693 3794609831523960293388635)
          ·
            refine ⟨5691914747285940440082953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3794609831523960293388635 5691914747285940440082953)
            ·
              refine ⟨4268936060464455330062215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5691914747285940440082953 4268936060464455330062215)
              ·
                refine ⟨6403404090696682995093323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4268936060464455330062215 6403404090696682995093323)
                ·
                  refine ⟨9605106136045024492639985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6403404090696682995093323 9605106136045024492639985)
                  ·
                    refine ⟨7203829602033768369479989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9605106136045024492639985 7203829602033768369479989)
                    ·
                      refine ⟨675359025190665784638749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7203829602033768369479989 675359025190665784638749)
                      ·
                        rfl

theorem cell23_1315257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 1, 1, 2, 5].length) (baseStart_1315257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315257 prefixEnd_1315257 := by exact prefixLift 1315257
  have htrace : WordTrace (prefixWord ++ tailWord_1315257) baseStart_1315257 baseEnd_1315257 := by
    simpa [prefixWord, tailWord_1315257, baseEnd_1315257] using wordTrace_append hprefix tailTrace_1315257
  have hstable : (prefixWord ++ tailWord_1315257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315257).length < 2 ^ (prefixWord ++ tailWord_1315257).sum := by decide
  have hdescent : baseEnd_1315257 < baseStart_1315257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315280 : List Nat := [2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 6]
def baseStart_1315280 : Nat := 118140960795 + 1315280 * 2 ^ 59
def prefixEnd_1315280 : Nat := 4983230072969 + 3 ^ 40 * 1315280 * 2
def baseEnd_1315280 : Nat := 675370835245719194651143

theorem tailTrace_1315280 : CollatzResearch.WordTrace tailWord_1315280 prefixEnd_1315280 675370835245719194651143 := by
  unfold tailWord_1315280
  simp only [CollatzResearch.WordTrace]
  refine ⟨23986101337486333392623647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31981468449981777856831529 23986101337486333392623647)
  ·
    refine ⟨35979152006229500088935471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23986101337486333392623647 35979152006229500088935471)
    ·
      refine ⟨53968728009344250133403207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35979152006229500088935471 53968728009344250133403207)
      ·
        refine ⟨80953092014016375200104811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53968728009344250133403207 80953092014016375200104811)
        ·
          refine ⟨121429638021024562800157217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80953092014016375200104811 121429638021024562800157217)
          ·
            refine ⟨91072228515768422100117913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121429638021024562800157217 91072228515768422100117913)
            ·
              refine ⟨68304171386826316575088435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91072228515768422100117913 68304171386826316575088435)
              ·
                refine ⟨102456257080239474862632653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68304171386826316575088435 102456257080239474862632653)
                ·
                  refine ⟨38421096405089803073487245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102456257080239474862632653 38421096405089803073487245)
                  ·
                    refine ⟨14407911151908676152557717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 38421096405089803073487245 14407911151908676152557717)
                    ·
                      refine ⟨675370835245719194651143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14407911151908676152557717 675370835245719194651143)
                      ·
                        rfl

theorem cell23_1315280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 1, 3, 3, 6].length) (baseStart_1315280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315280 prefixEnd_1315280 := by exact prefixLift 1315280
  have htrace : WordTrace (prefixWord ++ tailWord_1315280) baseStart_1315280 baseEnd_1315280 := by
    simpa [prefixWord, tailWord_1315280, baseEnd_1315280] using wordTrace_append hprefix tailTrace_1315280
  have hstable : (prefixWord ++ tailWord_1315280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315280).length < 2 ^ (prefixWord ++ tailWord_1315280).sum := by decide
  have hdescent : baseEnd_1315280 < baseStart_1315280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315284 : List Nat := [2, 4, 1, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_1315284 : Nat := 118140960795 + 1315284 * 2 ^ 59
def prefixEnd_1315284 : Nat := 4983230072969 + 3 ^ 40 * 1315284 * 2
def baseEnd_1315284 : Nat := 675372889168337179001125

theorem tailTrace_1315284 : CollatzResearch.WordTrace tailWord_1315284 prefixEnd_1315284 675372889168337179001125 := by
  unfold tailWord_1315284
  simp only [CollatzResearch.WordTrace]
  refine ⟨23986174283479087734196453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31981565711305450312261937 23986174283479087734196453)
  ·
    refine ⟨4497407678152328950161835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 23986174283479087734196453 4497407678152328950161835)
    ·
      refine ⟨6746111517228493425242753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4497407678152328950161835 6746111517228493425242753)
      ·
        refine ⟨5059583637921370068932065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6746111517228493425242753 5059583637921370068932065)
        ·
          refine ⟨3794687728441027551699049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5059583637921370068932065 3794687728441027551699049)
          ·
            refine ⟨2846015796330770663774287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3794687728441027551699049 2846015796330770663774287)
            ·
              refine ⟨4269023694496155995661431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2846015796330770663774287 4269023694496155995661431)
              ·
                refine ⟨6403535541744233993492147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4269023694496155995661431 6403535541744233993492147)
                ·
                  refine ⟨9605303312616350990238221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6403535541744233993492147 9605303312616350990238221)
                  ·
                    refine ⟨3601988742231131621339333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9605303312616350990238221 3601988742231131621339333)
                    ·
                      refine ⟨675372889168337179001125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3601988742231131621339333 675372889168337179001125)
                      ·
                        rfl

theorem cell23_1315284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_1315284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315284 prefixEnd_1315284 := by exact prefixLift 1315284
  have htrace : WordTrace (prefixWord ++ tailWord_1315284) baseStart_1315284 baseEnd_1315284 := by
    simpa [prefixWord, tailWord_1315284, baseEnd_1315284] using wordTrace_append hprefix tailTrace_1315284
  have hstable : (prefixWord ++ tailWord_1315284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315284).length < 2 ^ (prefixWord ++ tailWord_1315284).sum := by decide
  have hdescent : baseEnd_1315284 < baseStart_1315284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315341 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 8]
def baseStart_1315341 : Nat := 118140960795 + 1315341 * 2 ^ 59
def prefixEnd_1315341 : Nat := 4983230072969 + 3 ^ 40 * 1315341 * 2
def baseEnd_1315341 : Nat := 75044684173960383998707

theorem tailTrace_1315341 : CollatzResearch.WordTrace tailWord_1315341 prefixEnd_1315341 75044684173960383998707 := by
  unfold tailWord_1315341
  simp only [CollatzResearch.WordTrace]
  refine ⟨47974427527751674203217877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31982951685167782802145251 47974427527751674203217877)
  ·
    refine ⟨1124400645181679864137919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 47974427527751674203217877 1124400645181679864137919)
    ·
      refine ⟨1686600967772519796206879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1124400645181679864137919 1686600967772519796206879)
      ·
        refine ⟨2529901451658779694310319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1686600967772519796206879 2529901451658779694310319)
        ·
          refine ⟨3794852177488169541465479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2529901451658779694310319 3794852177488169541465479)
          ·
            refine ⟨5692278266232254312198219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3794852177488169541465479 5692278266232254312198219)
            ·
              refine ⟨8538417399348381468297329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5692278266232254312198219 8538417399348381468297329)
              ·
                refine ⟨6403813049511286101222997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8538417399348381468297329 6403813049511286101222997)
                ·
                  refine ⟨75044684173960383998707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6403813049511286101222997 75044684173960383998707)
                  ·
                    rfl

theorem cell23_1315341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_1315341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315341 prefixEnd_1315341 := by exact prefixLift 1315341
  have htrace : WordTrace (prefixWord ++ tailWord_1315341) baseStart_1315341 baseEnd_1315341 := by
    simpa [prefixWord, tailWord_1315341, baseEnd_1315341] using wordTrace_append hprefix tailTrace_1315341
  have hstable : (prefixWord ++ tailWord_1315341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315341).length < 2 ^ (prefixWord ++ tailWord_1315341).sum := by decide
  have hdescent : baseEnd_1315341 < baseStart_1315341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315354 : List Nat := [3, 1, 1, 3, 1, 1, 4, 3, 1, 5]
def baseStart_1315354 : Nat := 118140960795 + 1315354 * 2 ^ 59
def prefixEnd_1315354 : Nat := 4983230072969 + 3 ^ 40 * 1315354 * 2
def baseEnd_1315354 : Nat := 225136277604717301708601

theorem tailTrace_1315354 : CollatzResearch.WordTrace tailWord_1315354 prefixEnd_1315354 225136277604717301708601 := by
  unfold tailWord_1315354
  simp only [CollatzResearch.WordTrace]
  refine ⟨11993725419176144355860279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31983267784469718282294077 11993725419176144355860279)
  ·
    refine ⟨17990588128764216533790419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11993725419176144355860279 17990588128764216533790419)
    ·
      refine ⟨26985882193146324800685629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17990588128764216533790419 26985882193146324800685629)
      ·
        refine ⟨10119705822429871800257111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26985882193146324800685629 10119705822429871800257111)
        ·
          refine ⟨15179558733644807700385667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10119705822429871800257111 15179558733644807700385667)
          ·
            refine ⟨22769338100467211550578501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15179558733644807700385667 22769338100467211550578501)
            ·
              refine ⟨4269250893837602165733469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22769338100467211550578501 4269250893837602165733469)
              ·
                refine ⟨1600969085189100812150051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4269250893837602165733469 1600969085189100812150051)
                ·
                  refine ⟨2401453627783651218225077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1600969085189100812150051 2401453627783651218225077)
                  ·
                    refine ⟨225136277604717301708601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2401453627783651218225077 225136277604717301708601)
                    ·
                      rfl

theorem cell23_1315354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 4, 3, 1, 5].length) (baseStart_1315354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315354 prefixEnd_1315354 := by exact prefixLift 1315354
  have htrace : WordTrace (prefixWord ++ tailWord_1315354) baseStart_1315354 baseEnd_1315354 := by
    simpa [prefixWord, tailWord_1315354, baseEnd_1315354] using wordTrace_append hprefix tailTrace_1315354
  have hstable : (prefixWord ++ tailWord_1315354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315354).length < 2 ^ (prefixWord ++ tailWord_1315354).sum := by decide
  have hdescent : baseEnd_1315354 < baseStart_1315354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315361 : List Nat := [1, 2, 3, 2, 2, 1, 3, 2, 2, 3, 2]
def baseStart_1315361 : Nat := 118140960795 + 1315361 * 2 ^ 59
def prefixEnd_1315361 : Nat := 4983230072969 + 3 ^ 40 * 1315361 * 2
def baseEnd_1315361 : Nat := 675412427178733377738271

theorem tailTrace_1315361 : CollatzResearch.WordTrace tailWord_1315361 prefixEnd_1315361 675412427178733377738271 := by
  unfold tailWord_1315361
  simp only [CollatzResearch.WordTrace]
  refine ⟨47975156987679217618945937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31983437991786145079297291 47975156987679217618945937)
  ·
    refine ⟨35981367740759413214209453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47975156987679217618945937 35981367740759413214209453)
    ·
      refine ⟨13493012902784779955328545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35981367740759413214209453 13493012902784779955328545)
      ·
        refine ⟨10119759677088584966496409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13493012902784779955328545 10119759677088584966496409)
        ·
          refine ⟨7589819757816438724872307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10119759677088584966496409 7589819757816438724872307)
          ·
            refine ⟨11384729636724658087308461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7589819757816438724872307 11384729636724658087308461)
            ·
              refine ⟨4269273613771746782740673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11384729636724658087308461 4269273613771746782740673)
              ·
                refine ⟨3201955210328810087055505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4269273613771746782740673 3201955210328810087055505)
                ·
                  refine ⟨2401466407746607565291629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3201955210328810087055505 2401466407746607565291629)
                  ·
                    refine ⟨900549902904977836984361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2401466407746607565291629 900549902904977836984361)
                    ·
                      refine ⟨675412427178733377738271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 900549902904977836984361 675412427178733377738271)
                      ·
                        rfl

theorem cell23_1315361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_1315361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315361 prefixEnd_1315361 := by exact prefixLift 1315361
  have htrace : WordTrace (prefixWord ++ tailWord_1315361) baseStart_1315361 baseEnd_1315361 := by
    simpa [prefixWord, tailWord_1315361, baseEnd_1315361] using wordTrace_append hprefix tailTrace_1315361
  have hstable : (prefixWord ++ tailWord_1315361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315361).length < 2 ^ (prefixWord ++ tailWord_1315361).sum := by decide
  have hdescent : baseEnd_1315361 < baseStart_1315361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315368 : List Nat := [2, 1, 5, 2, 1, 1, 3, 1, 3, 1, 3]
def baseStart_1315368 : Nat := 118140960795 + 1315368 * 2 ^ 59
def prefixEnd_1315368 : Nat := 4983230072969 + 3 ^ 40 * 1315368 * 2
def baseEnd_1315368 : Nat := 675416021543314850350739

theorem tailTrace_1315368 : CollatzResearch.WordTrace tailWord_1315368 prefixEnd_1315368 675416021543314850350739 := by
  unfold tailWord_1315368
  simp only [CollatzResearch.WordTrace]
  refine ⟨23987706149326928907225379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31983608199102571876300505 23987706149326928907225379)
  ·
    refine ⟨35981559223990393360838069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23987706149326928907225379 35981559223990393360838069)
    ·
      refine ⟨3373271177249099377578569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 35981559223990393360838069 3373271177249099377578569)
      ·
        refine ⟨2529953382936824533183927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3373271177249099377578569 2529953382936824533183927)
        ·
          refine ⟨3794930074405236799775891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2529953382936824533183927 3794930074405236799775891)
          ·
            refine ⟨5692395111607855199663837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3794930074405236799775891 5692395111607855199663837)
            ·
              refine ⟨2134648166852945699873939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5692395111607855199663837 2134648166852945699873939)
              ·
                refine ⟨3201972250279418549810909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2134648166852945699873939 3201972250279418549810909)
                ·
                  refine ⟨1200739593854781956179091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3201972250279418549810909 1200739593854781956179091)
                  ·
                    refine ⟨1801109390782172934268637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1200739593854781956179091 1801109390782172934268637)
                    ·
                      refine ⟨675416021543314850350739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1801109390782172934268637 675416021543314850350739)
                      ·
                        rfl

theorem cell23_1315368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_1315368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315368 prefixEnd_1315368 := by exact prefixLift 1315368
  have htrace : WordTrace (prefixWord ++ tailWord_1315368) baseStart_1315368 baseEnd_1315368 := by
    simpa [prefixWord, tailWord_1315368, baseEnd_1315368] using wordTrace_append hprefix tailTrace_1315368
  have hstable : (prefixWord ++ tailWord_1315368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315368).length < 2 ^ (prefixWord ++ tailWord_1315368).sum := by decide
  have hdescent : baseEnd_1315368 < baseStart_1315368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315391 : List Nat := [1, 1, 2, 2, 3, 2, 2, 1, 5, 2, 2]
def baseStart_1315391 : Nat := 118140960795 + 1315391 * 2 ^ 59
def prefixEnd_1315391 : Nat := 4983230072969 + 3 ^ 40 * 1315391 * 2
def baseEnd_1315391 : Nat := 675427831598368260363133

theorem tailTrace_1315391 : CollatzResearch.WordTrace tailWord_1315391 prefixEnd_1315391 675427831598368260363133 := by
  unfold tailWord_1315391
  simp only [CollatzResearch.WordTrace]
  refine ⟨47976251177570532742538027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31984167451713688495025351 47976251177570532742538027)
  ·
    refine ⟨71964376766355799113807041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47976251177570532742538027 71964376766355799113807041)
    ·
      refine ⟨53973282574766849335355281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71964376766355799113807041 53973282574766849335355281)
      ·
        refine ⟨40479961931075137001516461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53973282574766849335355281 40479961931075137001516461)
        ·
          refine ⟨15179985724153176375568673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40479961931075137001516461 15179985724153176375568673)
          ·
            refine ⟨11384989293114882281676505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15179985724153176375568673 11384989293114882281676505)
            ·
              refine ⟨8538741969836161711257379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11384989293114882281676505 8538741969836161711257379)
              ·
                refine ⟨12808112954754242566886069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8538741969836161711257379 12808112954754242566886069)
                ·
                  refine ⟨1200760589508210240645569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12808112954754242566886069 1200760589508210240645569)
                  ·
                    refine ⟨900570442131157680484177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1200760589508210240645569 900570442131157680484177)
                    ·
                      refine ⟨675427831598368260363133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 900570442131157680484177 675427831598368260363133)
                      ·
                        rfl

theorem cell23_1315391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 5, 2, 2].length) (baseStart_1315391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315391 prefixEnd_1315391 := by exact prefixLift 1315391
  have htrace : WordTrace (prefixWord ++ tailWord_1315391) baseStart_1315391 baseEnd_1315391 := by
    simpa [prefixWord, tailWord_1315391, baseEnd_1315391] using wordTrace_append hprefix tailTrace_1315391
  have hstable : (prefixWord ++ tailWord_1315391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315391).length < 2 ^ (prefixWord ++ tailWord_1315391).sum := by decide
  have hdescent : baseEnd_1315391 < baseStart_1315391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315397 : List Nat := [1, 3, 1, 1, 1, 5, 2, 9]
def baseStart_1315397 : Nat := 118140960795 + 1315397 * 2 ^ 59
def prefixEnd_1315397 : Nat := 4983230072969 + 3 ^ 40 * 1315397 * 2
def baseEnd_1315397 : Nat := 25015959721566490255115

theorem tailTrace_1315397 : CollatzResearch.WordTrace tailWord_1315397 prefixEnd_1315397 25015959721566490255115 := by
  unfold tailWord_1315397
  simp only [CollatzResearch.WordTrace]
  refine ⟨47976470015548795767256445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31984313343699197178170963 47976470015548795767256445)
  ·
    refine ⟨17991176255830798412721167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47976470015548795767256445 17991176255830798412721167)
    ·
      refine ⟨26986764383746197619081751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17991176255830798412721167 26986764383746197619081751)
      ·
        refine ⟨40480146575619296428622627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 26986764383746197619081751 40480146575619296428622627)
        ·
          refine ⟨60720219863428944642933941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40480146575619296428622627 60720219863428944642933941)
          ·
            refine ⟨5692520612196463560275057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60720219863428944642933941 5692520612196463560275057)
            ·
              refine ⟨4269390459147347670206293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5692520612196463560275057 4269390459147347670206293)
              ·
                refine ⟨25015959721566490255115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4269390459147347670206293 25015959721566490255115)
                ·
                  rfl

theorem cell23_1315397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 9].length) (baseStart_1315397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315397 prefixEnd_1315397 := by exact prefixLift 1315397
  have htrace : WordTrace (prefixWord ++ tailWord_1315397) baseStart_1315397 baseEnd_1315397 := by
    simpa [prefixWord, tailWord_1315397, baseEnd_1315397] using wordTrace_append hprefix tailTrace_1315397
  have hstable : (prefixWord ++ tailWord_1315397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315397).length < 2 ^ (prefixWord ++ tailWord_1315397).sum := by decide
  have hdescent : baseEnd_1315397 < baseStart_1315397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315404 : List Nat := [2, 2, 1, 3, 1, 2, 3, 2, 1, 2, 4]
def baseStart_1315404 : Nat := 118140960795 + 1315404 * 2 ^ 59
def prefixEnd_1315404 : Nat := 4983230072969 + 3 ^ 40 * 1315404 * 2
def baseEnd_1315404 : Nat := 675434506846876709500573

theorem tailTrace_1315404 : CollatzResearch.WordTrace tailWord_1315404 prefixEnd_1315404 675434506846876709500573 := by
  unfold tailWord_1315404
  simp only [CollatzResearch.WordTrace]
  refine ⟨23988362663261717981380633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31984483551015623975174177 23988362663261717981380633)
  ·
    refine ⟨17991271997446288486035475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23988362663261717981380633 17991271997446288486035475)
    ·
      refine ⟨26986907996169432729053213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17991271997446288486035475 26986907996169432729053213)
      ·
        refine ⟨10120090498563537273394955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 26986907996169432729053213 10120090498563537273394955)
        ·
          refine ⟨15180135747845305910092433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10120090498563537273394955 15180135747845305910092433)
          ·
            refine ⟨11385101810883979432569325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15180135747845305910092433 11385101810883979432569325)
            ·
              refine ⟨4269413179081492287213497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11385101810883979432569325 4269413179081492287213497)
              ·
                refine ⟨3202059884311119215410123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4269413179081492287213497 3202059884311119215410123)
                ·
                  refine ⟨4803089826466678823115185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3202059884311119215410123 4803089826466678823115185)
                  ·
                    refine ⟨3602317369850009117336389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4803089826466678823115185 3602317369850009117336389)
                    ·
                      refine ⟨675434506846876709500573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3602317369850009117336389 675434506846876709500573)
                      ·
                        rfl

theorem cell23_1315404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 3, 2, 1, 2, 4].length) (baseStart_1315404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315404 prefixEnd_1315404 := by exact prefixLift 1315404
  have htrace : WordTrace (prefixWord ++ tailWord_1315404) baseStart_1315404 baseEnd_1315404 := by
    simpa [prefixWord, tailWord_1315404, baseEnd_1315404] using wordTrace_append hprefix tailTrace_1315404
  have hstable : (prefixWord ++ tailWord_1315404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315404).length < 2 ^ (prefixWord ++ tailWord_1315404).sum := by decide
  have hdescent : baseEnd_1315404 < baseStart_1315404 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315414 : List Nat := [5, 2, 2, 14]
def baseStart_1315414 : Nat := 118140960795 + 1315414 * 2 ^ 59
def prefixEnd_1315414 : Nat := 4983230072969 + 3 ^ 40 * 1315414 * 2
def baseEnd_1315414 : Nat := 308843000298775340821

theorem tailTrace_1315414 : CollatzResearch.WordTrace tailWord_1315414 prefixEnd_1315414 308843000298775340821 := by
  unfold tailWord_1315414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2998568128530450479414081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 31984726704324805113750197 2998568128530450479414081)
  ·
    refine ⟨2248926096397837859560561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2998568128530450479414081 2248926096397837859560561)
    ·
      refine ⟨1686694572298378394670421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2248926096397837859560561 1686694572298378394670421)
      ·
        refine ⟨308843000298775340821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 14 1686694572298378394670421 308843000298775340821)
        ·
          rfl

theorem cell23_1315414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 14].length) (baseStart_1315414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315414 prefixEnd_1315414 := by exact prefixLift 1315414
  have htrace : WordTrace (prefixWord ++ tailWord_1315414) baseStart_1315414 baseEnd_1315414 := by
    simpa [prefixWord, tailWord_1315414, baseEnd_1315414] using wordTrace_append hprefix tailTrace_1315414
  have hstable : (prefixWord ++ tailWord_1315414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315414).length < 2 ^ (prefixWord ++ tailWord_1315414).sum := by decide
  have hdescent : baseEnd_1315414 < baseStart_1315414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315425 : List Nat := [1, 2, 3, 1, 1, 5, 1, 4, 1, 2, 2]
def baseStart_1315425 : Nat := 118140960795 + 1315425 * 2 ^ 59
def prefixEnd_1315425 : Nat := 4983230072969 + 3 ^ 40 * 1315425 * 2
def baseEnd_1315425 : Nat := 675445289940621127337977

theorem tailTrace_1315425 : CollatzResearch.WordTrace tailWord_1315425 prefixEnd_1315425 675445289940621127337977 := by
  unfold tailWord_1315425
  simp only [CollatzResearch.WordTrace]
  refine ⟨47977491259447356549275729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31984994172964904366183819 47977491259447356549275729)
  ·
    refine ⟨35983118444585517411956797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47977491259447356549275729 35983118444585517411956797)
    ·
      refine ⟨13493669416719569029483799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35983118444585517411956797 13493669416719569029483799)
      ·
        refine ⟨20240504125079353544225699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13493669416719569029483799 20240504125079353544225699)
        ·
          refine ⟨30360756187619030316338549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20240504125079353544225699 30360756187619030316338549)
          ·
            refine ⟨2846320892589284092156739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30360756187619030316338549 2846320892589284092156739)
            ·
              refine ⟨4269481338883926138235109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2846320892589284092156739 4269481338883926138235109)
              ·
                refine ⟨800527751040736150919083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4269481338883926138235109 800527751040736150919083)
                ·
                  refine ⟨1200791626561104226378625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 800527751040736150919083 1200791626561104226378625)
                  ·
                    refine ⟨900593719920828169783969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1200791626561104226378625 900593719920828169783969)
                    ·
                      refine ⟨675445289940621127337977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 900593719920828169783969 675445289940621127337977)
                      ·
                        rfl

theorem cell23_1315425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 4, 1, 2, 2].length) (baseStart_1315425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315425 prefixEnd_1315425 := by exact prefixLift 1315425
  have htrace : WordTrace (prefixWord ++ tailWord_1315425) baseStart_1315425 baseEnd_1315425 := by
    simpa [prefixWord, tailWord_1315425, baseEnd_1315425] using wordTrace_append hprefix tailTrace_1315425
  have hstable : (prefixWord ++ tailWord_1315425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315425).length < 2 ^ (prefixWord ++ tailWord_1315425).sum := by decide
  have hdescent : baseEnd_1315425 < baseStart_1315425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315427 : List Nat := [1, 1, 1, 5, 1, 2, 1, 1, 1, 9]
def baseStart_1315427 : Nat := 118140960795 + 1315427 * 2 ^ 59
def prefixEnd_1315427 : Nat := 4983230072969 + 3 ^ 40 * 1315427 * 2
def baseEnd_1315427 : Nat := 225148772300643373170989

theorem tailTrace_1315427 : CollatzResearch.WordTrace tailWord_1315427 prefixEnd_1315427 225148772300643373170989 := by
  unfold tailWord_1315427
  simp only [CollatzResearch.WordTrace]
  refine ⟨47977564205440110890848535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31985042803626740593899023 47977564205440110890848535)
  ·
    refine ⟨71966346308160166336272803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47977564205440110890848535 71966346308160166336272803)
    ·
      refine ⟨107949519462240249504409205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71966346308160166336272803 107949519462240249504409205)
      ·
        refine ⟨10120267449585023391038363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 107949519462240249504409205 10120267449585023391038363)
        ·
          refine ⟨15180401174377535086557545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10120267449585023391038363 15180401174377535086557545)
          ·
            refine ⟨11385300880783151314918159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15180401174377535086557545 11385300880783151314918159)
            ·
              refine ⟨17077951321174726972377239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11385300880783151314918159 17077951321174726972377239)
              ·
                refine ⟨25616926981762090458565859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17077951321174726972377239 25616926981762090458565859)
                ·
                  refine ⟨38425390472643135687848789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25616926981762090458565859 38425390472643135687848789)
                  ·
                    refine ⟨225148772300643373170989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 38425390472643135687848789 225148772300643373170989)
                    ·
                      rfl

theorem cell23_1315427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 1, 1, 9].length) (baseStart_1315427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315427 prefixEnd_1315427 := by exact prefixLift 1315427
  have htrace : WordTrace (prefixWord ++ tailWord_1315427) baseStart_1315427 baseEnd_1315427 := by
    simpa [prefixWord, tailWord_1315427, baseEnd_1315427] using wordTrace_append hprefix tailTrace_1315427
  have hstable : (prefixWord ++ tailWord_1315427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315427).length < 2 ^ (prefixWord ++ tailWord_1315427).sum := by decide
  have hdescent : baseEnd_1315427 < baseStart_1315427 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315502 : List Nat := [4, 1, 4, 1, 1, 2, 2, 2, 1, 3, 2]
def baseStart_1315502 : Nat := 118140960795 + 1315502 * 2 ^ 59
def prefixEnd_1315502 : Nat := 4983230072969 + 3 ^ 40 * 1315502 * 2
def baseEnd_1315502 : Nat := 675484827951017326075123

theorem tailTrace_1315502 : CollatzResearch.WordTrace tailWord_1315502 prefixEnd_1315502 675484827951017326075123 := by
  unfold tailWord_1315502
  simp only [CollatzResearch.WordTrace]
  refine ⟨5997537460021049837478595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 31986866453445599133219173 5997537460021049837478595)
  ·
    refine ⟨8996306190031574756217893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5997537460021049837478595 8996306190031574756217893)
    ·
      refine ⟨1686807410630920266790855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8996306190031574756217893 1686807410630920266790855)
      ·
        refine ⟨2530211115946380400186283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1686807410630920266790855 2530211115946380400186283)
        ·
          refine ⟨3795316673919570600279425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2530211115946380400186283 3795316673919570600279425)
          ·
            refine ⟨2846487505439677950209569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3795316673919570600279425 2846487505439677950209569)
            ·
              refine ⟨2134865629079758462657177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2846487505439677950209569 2134865629079758462657177)
              ·
                refine ⟨1601149221809818846992883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2134865629079758462657177 1601149221809818846992883)
                ·
                  refine ⟨2401723832714728270489325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1601149221809818846992883 2401723832714728270489325)
                  ·
                    refine ⟨900646437268023101433497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2401723832714728270489325 900646437268023101433497)
                    ·
                      refine ⟨675484827951017326075123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 900646437268023101433497 675484827951017326075123)
                      ·
                        rfl

theorem cell23_1315502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_1315502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315502 prefixEnd_1315502 := by exact prefixLift 1315502
  have htrace : WordTrace (prefixWord ++ tailWord_1315502) baseStart_1315502 baseEnd_1315502 := by
    simpa [prefixWord, tailWord_1315502, baseEnd_1315502] using wordTrace_append hprefix tailTrace_1315502
  have hstable : (prefixWord ++ tailWord_1315502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315502).length < 2 ^ (prefixWord ++ tailWord_1315502).sum := by decide
  have hdescent : baseEnd_1315502 < baseStart_1315502 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315538 : List Nat := [3, 2, 2, 2, 3, 2, 1, 1, 7]
def baseStart_1315538 : Nat := 118140960795 + 1315538 * 2 ^ 59
def prefixEnd_1315538 : Nat := 4983230072969 + 3 ^ 40 * 1315538 * 2
def baseEnd_1315538 : Nat := 75055923694953242802773

theorem tailTrace_1315538 : CollatzResearch.WordTrace tailWord_1315538 prefixEnd_1315538 75055923694953242802773 := by
  unfold tailWord_1315538
  simp only [CollatzResearch.WordTrace]
  refine ⟨11995403177009494212034817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31987741805358651232092845 11995403177009494212034817)
  ·
    refine ⟨8996552382757120659026113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11995403177009494212034817 8996552382757120659026113)
    ·
      refine ⟨6747414287067840494269585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8996552382757120659026113 6747414287067840494269585)
      ·
        refine ⟨5060560715300880370702189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6747414287067840494269585 5060560715300880370702189)
        ·
          refine ⟨1897710268237830139013321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5060560715300880370702189 1897710268237830139013321)
          ·
            refine ⟨1423282701178372604259991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1897710268237830139013321 1423282701178372604259991)
            ·
              refine ⟨2134924051767558906389987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1423282701178372604259991 2134924051767558906389987)
              ·
                refine ⟨3202386077651338359584981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2134924051767558906389987 3202386077651338359584981)
                ·
                  refine ⟨75055923694953242802773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3202386077651338359584981 75055923694953242802773)
                  ·
                    rfl

theorem cell23_1315538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 7].length) (baseStart_1315538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315538 prefixEnd_1315538 := by exact prefixLift 1315538
  have htrace : WordTrace (prefixWord ++ tailWord_1315538) baseStart_1315538 baseEnd_1315538 := by
    simpa [prefixWord, tailWord_1315538, baseEnd_1315538] using wordTrace_append hprefix tailTrace_1315538
  have hstable : (prefixWord ++ tailWord_1315538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315538).length < 2 ^ (prefixWord ++ tailWord_1315538).sum := by decide
  have hdescent : baseEnd_1315538 < baseStart_1315538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315544 : List Nat := [2, 1, 2, 2, 3, 2, 1, 1, 1, 1, 7]
def baseStart_1315544 : Nat := 118140960795 + 1315544 * 2 ^ 59
def prefixEnd_1315544 : Nat := 4983230072969 + 3 ^ 40 * 1315544 * 2
def baseEnd_1315544 : Nat := 675506394138506161749929

theorem tailTrace_1315544 : CollatzResearch.WordTrace tailWord_1315544 prefixEnd_1315544 675506394138506161749929 := by
  unfold tailWord_1315544
  simp only [CollatzResearch.WordTrace]
  refine ⟨23990915773008119936428843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31987887697344159915238457 23990915773008119936428843)
  ·
    refine ⟨35986373659512179904643265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23990915773008119936428843 35986373659512179904643265)
    ·
      refine ⟨26989780244634134928482449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35986373659512179904643265 26989780244634134928482449)
      ·
        refine ⟨20242335183475601196361837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26989780244634134928482449 20242335183475601196361837)
        ·
          refine ⟨7590875693803350448635689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20242335183475601196361837 7590875693803350448635689)
          ·
            refine ⟨5693156770352512836476767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7590875693803350448635689 5693156770352512836476767)
            ·
              refine ⟨8539735155528769254715151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5693156770352512836476767 8539735155528769254715151)
              ·
                refine ⟨12809602733293153882072727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8539735155528769254715151 12809602733293153882072727)
                ·
                  refine ⟨19214404099939730823109091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12809602733293153882072727 19214404099939730823109091)
                  ·
                    refine ⟨28821606149909596234663637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19214404099939730823109091 28821606149909596234663637)
                    ·
                      refine ⟨675506394138506161749929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28821606149909596234663637 675506394138506161749929)
                      ·
                        rfl

theorem cell23_1315544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 1, 1, 1, 7].length) (baseStart_1315544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315544 prefixEnd_1315544 := by exact prefixLift 1315544
  have htrace : WordTrace (prefixWord ++ tailWord_1315544) baseStart_1315544 baseEnd_1315544 := by
    simpa [prefixWord, tailWord_1315544, baseEnd_1315544] using wordTrace_append hprefix tailTrace_1315544
  have hstable : (prefixWord ++ tailWord_1315544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315544).length < 2 ^ (prefixWord ++ tailWord_1315544).sum := by decide
  have hdescent : baseEnd_1315544 < baseStart_1315544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315571 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 4, 4, 2]
def baseStart_1315571 : Nat := 118140960795 + 1315571 * 2 ^ 59
def prefixEnd_1315571 : Nat := 4983230072969 + 3 ^ 40 * 1315571 * 2
def baseEnd_1315571 : Nat := 675520258116177556112305

theorem tailTrace_1315571 : CollatzResearch.WordTrace tailWord_1315571 prefixEnd_1315571 675520258116177556112305 := by
  unfold tailWord_1315571
  simp only [CollatzResearch.WordTrace]
  refine ⟨47982816316918423484090567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31988544211278948989393711 47982816316918423484090567)
  ·
    refine ⟨71974224475377635226135851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47982816316918423484090567 71974224475377635226135851)
    ·
      refine ⟨107961336713066452839203777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71974224475377635226135851 107961336713066452839203777)
      ·
        refine ⟨80971002534799839629402833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 107961336713066452839203777 80971002534799839629402833)
        ·
          refine ⟨60728251901099879722052125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 80971002534799839629402833 60728251901099879722052125)
          ·
            refine ⟨22773094462912454895769547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60728251901099879722052125 22773094462912454895769547)
            ·
              refine ⟨34159641694368682343654321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22773094462912454895769547 34159641694368682343654321)
              ·
                refine ⟨25619731270776511757740741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34159641694368682343654321 25619731270776511757740741)
                ·
                  refine ⟨4803699613270595954576389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25619731270776511757740741 4803699613270595954576389)
                  ·
                    refine ⟨900693677488236741483073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4803699613270595954576389 900693677488236741483073)
                    ·
                      refine ⟨675520258116177556112305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 900693677488236741483073 675520258116177556112305)
                      ·
                        rfl

theorem cell23_1315571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 4, 4, 2].length) (baseStart_1315571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315571 prefixEnd_1315571 := by exact prefixLift 1315571
  have htrace : WordTrace (prefixWord ++ tailWord_1315571) baseStart_1315571 baseEnd_1315571 := by
    simpa [prefixWord, tailWord_1315571, baseEnd_1315571] using wordTrace_append hprefix tailTrace_1315571
  have hstable : (prefixWord ++ tailWord_1315571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315571).length < 2 ^ (prefixWord ++ tailWord_1315571).sum := by decide
  have hdescent : baseEnd_1315571 < baseStart_1315571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315588 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 2, 4, 2]
def baseStart_1315588 : Nat := 118140960795 + 1315588 * 2 ^ 59
def prefixEnd_1315588 : Nat := 4983230072969 + 3 ^ 40 * 1315588 * 2
def baseEnd_1315588 : Nat := 675528987287303989599727

theorem tailTrace_1315588 : CollatzResearch.WordTrace tailWord_1315588 prefixEnd_1315588 675528987287303989599727 := by
  unfold tailWord_1315588
  simp only [CollatzResearch.WordTrace]
  refine ⟨23991718178928417693729709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31988957571904556924972945 23991718178928417693729709)
  ·
    refine ⟨8996894317098156635148641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 23991718178928417693729709 8996894317098156635148641)
    ·
      refine ⟨6747670737823617476361481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8996894317098156635148641 6747670737823617476361481)
      ·
        refine ⟨5060753053367713107271111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6747670737823617476361481 5060753053367713107271111)
        ·
          refine ⟨7591129580051569660906667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5060753053367713107271111 7591129580051569660906667)
          ·
            refine ⟨11386694370077354491360001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7591129580051569660906667 11386694370077354491360001)
            ·
              refine ⟨8540020777558015868520001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11386694370077354491360001 8540020777558015868520001)
              ·
                refine ⟨6405015583168511901390001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8540020777558015868520001 6405015583168511901390001)
                ·
                  refine ⟨4803761687376383926042501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6405015583168511901390001 4803761687376383926042501)
                  ·
                    refine ⟨900705316383071986132969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4803761687376383926042501 900705316383071986132969)
                    ·
                      refine ⟨675528987287303989599727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 900705316383071986132969 675528987287303989599727)
                      ·
                        rfl

theorem cell23_1315588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 2, 4, 2].length) (baseStart_1315588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315588 prefixEnd_1315588 := by exact prefixLift 1315588
  have htrace : WordTrace (prefixWord ++ tailWord_1315588) baseStart_1315588 baseEnd_1315588 := by
    simpa [prefixWord, tailWord_1315588, baseEnd_1315588] using wordTrace_append hprefix tailTrace_1315588
  have hstable : (prefixWord ++ tailWord_1315588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315588).length < 2 ^ (prefixWord ++ tailWord_1315588).sum := by decide
  have hdescent : baseEnd_1315588 < baseStart_1315588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315645 : List Nat := [1, 4, 1, 4, 2, 2, 1, 2, 6]
def baseStart_1315645 : Nat := 118140960795 + 1315645 * 2 ^ 59
def prefixEnd_1315645 : Nat := 4983230072969 + 3 ^ 40 * 1315645 * 2
def baseEnd_1315645 : Nat := 75062028409401140731885

theorem tailTrace_1315645 : CollatzResearch.WordTrace tailWord_1315645 prefixEnd_1315645 75062028409401140731885 := by
  unfold tailWord_1315645
  simp only [CollatzResearch.WordTrace]
  refine ⟨47985515318650334122284389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31990343545766889414856259 47985515318650334122284389)
  ·
    refine ⟨8997284122246937647928323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47985515318650334122284389 8997284122246937647928323)
    ·
      refine ⟨13495926183370406471892485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8997284122246937647928323 13495926183370406471892485)
      ·
        refine ⟨2530486159381951213479841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13495926183370406471892485 2530486159381951213479841)
        ·
          refine ⟨1897864619536463410109881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2530486159381951213479841 1897864619536463410109881)
          ·
            refine ⟨1423398464652347557582411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1897864619536463410109881 1423398464652347557582411)
            ·
              refine ⟨2135097696978521336373617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1423398464652347557582411 2135097696978521336373617)
              ·
                refine ⟨1601323272733891002280213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2135097696978521336373617 1601323272733891002280213)
                ·
                  refine ⟨75062028409401140731885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1601323272733891002280213 75062028409401140731885)
                  ·
                    rfl

theorem cell23_1315645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 6].length) (baseStart_1315645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315645 prefixEnd_1315645 := by exact prefixLift 1315645
  have htrace : WordTrace (prefixWord ++ tailWord_1315645) baseStart_1315645 baseEnd_1315645 := by
    simpa [prefixWord, tailWord_1315645, baseEnd_1315645] using wordTrace_append hprefix tailTrace_1315645
  have hstable : (prefixWord ++ tailWord_1315645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315645).length < 2 ^ (prefixWord ++ tailWord_1315645).sum := by decide
  have hdescent : baseEnd_1315645 < baseStart_1315645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315648 : List Nat := [2, 1, 1, 2, 2, 1, 1, 6, 2, 3, 2]
def baseStart_1315648 : Nat := 118140960795 + 1315648 * 2 ^ 59
def prefixEnd_1315648 : Nat := 4983230072969 + 3 ^ 40 * 1315648 * 2
def baseEnd_1315648 : Nat := 675559796126573754849451

theorem tailTrace_1315648 : CollatzResearch.WordTrace tailWord_1315648 prefixEnd_1315648 675559796126573754849451 := by
  unfold tailWord_1315648
  simp only [CollatzResearch.WordTrace]
  refine ⟨23992812368819732817321799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31990416491759643756429065 23992812368819732817321799)
  ·
    refine ⟨35989218553229599225982699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23992812368819732817321799 35989218553229599225982699)
    ·
      refine ⟨53983827829844398838974049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35989218553229599225982699 53983827829844398838974049)
      ·
        refine ⟨40487870872383299129230537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 53983827829844398838974049 40487870872383299129230537)
        ·
          refine ⟨30365903154287474346922903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40487870872383299129230537 30365903154287474346922903)
          ·
            refine ⟨45548854731431211520384355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30365903154287474346922903 45548854731431211520384355)
            ·
              refine ⟨68323282097146817280576533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45548854731431211520384355 68323282097146817280576533)
              ·
                refine ⟨3202653848303757060027025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 68323282097146817280576533 3202653848303757060027025)
                ·
                  refine ⟨2401990386227817795020269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3202653848303757060027025 2401990386227817795020269)
                  ·
                    refine ⟨900746394835431673132601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2401990386227817795020269 900746394835431673132601)
                    ·
                      refine ⟨675559796126573754849451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 900746394835431673132601 675559796126573754849451)
                      ·
                        rfl

theorem cell23_1315648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 6, 2, 3, 2].length) (baseStart_1315648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315648 prefixEnd_1315648 := by exact prefixLift 1315648
  have htrace : WordTrace (prefixWord ++ tailWord_1315648) baseStart_1315648 baseEnd_1315648 := by
    simpa [prefixWord, tailWord_1315648, baseEnd_1315648] using wordTrace_append hprefix tailTrace_1315648
  have hstable : (prefixWord ++ tailWord_1315648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315648).length < 2 ^ (prefixWord ++ tailWord_1315648).sum := by decide
  have hdescent : baseEnd_1315648 < baseStart_1315648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315688 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 4, 4]
def baseStart_1315688 : Nat := 118140960795 + 1315688 * 2 ^ 59
def prefixEnd_1315688 : Nat := 4983230072969 + 3 ^ 40 * 1315688 * 2
def baseEnd_1315688 : Nat := 225193445117584532783089

theorem tailTrace_1315688 : CollatzResearch.WordTrace tailWord_1315688 prefixEnd_1315688 225193445117584532783089 := by
  unfold tailWord_1315688
  simp only [CollatzResearch.WordTrace]
  refine ⟨23993541828747276233049859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31991389104996368310733145 23993541828747276233049859)
  ·
    refine ⟨35990312743120914349574789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23993541828747276233049859 35990312743120914349574789)
    ·
      refine ⟨6748183639335171440545273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35990312743120914349574789 6748183639335171440545273)
      ·
        refine ⟨5061137729501378580408955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6748183639335171440545273 5061137729501378580408955)
        ·
          refine ⟨7591706594252067870613433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5061137729501378580408955 7591706594252067870613433)
          ·
            refine ⟨5693779945689050902960075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7591706594252067870613433 5693779945689050902960075)
            ·
              refine ⟨8540669918533576354440113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5693779945689050902960075 8540669918533576354440113)
              ·
                refine ⟨6405502438900182265830085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8540669918533576354440113 6405502438900182265830085)
                ·
                  refine ⟨1201031707293784174843141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6405502438900182265830085 1201031707293784174843141)
                  ·
                    refine ⟨225193445117584532783089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1201031707293784174843141 225193445117584532783089)
                    ·
                      rfl

theorem cell23_1315688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 4, 4].length) (baseStart_1315688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315688 prefixEnd_1315688 := by exact prefixLift 1315688
  have htrace : WordTrace (prefixWord ++ tailWord_1315688) baseStart_1315688 baseEnd_1315688 := by
    simpa [prefixWord, tailWord_1315688, baseEnd_1315688] using wordTrace_append hprefix tailTrace_1315688
  have hstable : (prefixWord ++ tailWord_1315688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315688).length < 2 ^ (prefixWord ++ tailWord_1315688).sum := by decide
  have hdescent : baseEnd_1315688 < baseStart_1315688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315691 : List Nat := [1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 4]
def baseStart_1315691 : Nat := 118140960795 + 1315691 * 2 ^ 59
def prefixEnd_1315691 : Nat := 4983230072969 + 3 ^ 40 * 1315691 * 2
def baseEnd_1315691 : Nat := 675581875794717086611753

theorem tailTrace_1315691 : CollatzResearch.WordTrace tailWord_1315691 prefixEnd_1315691 675581875794717086611753 := by
  unfold tailWord_1315691
  simp only [CollatzResearch.WordTrace]
  refine ⟨47987193076483683978458927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31991462050989122652305951 47987193076483683978458927)
  ·
    refine ⟨71980789614725525967688391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47987193076483683978458927 71980789614725525967688391)
    ·
      refine ⟨107971184422088288951532587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71980789614725525967688391 107971184422088288951532587)
      ·
        refine ⟨161956776633132433427298881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107971184422088288951532587 161956776633132433427298881)
        ·
          refine ⟨121467582474849325070474161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161956776633132433427298881 121467582474849325070474161)
          ·
            refine ⟨91100686856136993802855621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121467582474849325070474161 91100686856136993802855621)
            ·
              refine ⟨17081378785525686338035429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91100686856136993802855621 17081378785525686338035429)
              ·
                refine ⟨3202758522286066188381643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17081378785525686338035429 3202758522286066188381643)
                ·
                  refine ⟨4804137783429099282572465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3202758522286066188381643 4804137783429099282572465)
                  ·
                    refine ⟨3603103337571824461929349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4804137783429099282572465 3603103337571824461929349)
                    ·
                      refine ⟨675581875794717086611753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3603103337571824461929349 675581875794717086611753)
                      ·
                        rfl

theorem cell23_1315691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 4, 1, 2, 4].length) (baseStart_1315691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315691 prefixEnd_1315691 := by exact prefixLift 1315691
  have htrace : WordTrace (prefixWord ++ tailWord_1315691) baseStart_1315691 baseEnd_1315691 := by
    simpa [prefixWord, tailWord_1315691, baseEnd_1315691] using wordTrace_append hprefix tailTrace_1315691
  have hstable : (prefixWord ++ tailWord_1315691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315691).length < 2 ^ (prefixWord ++ tailWord_1315691).sum := by decide
  have hdescent : baseEnd_1315691 < baseStart_1315691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315701 : List Nat := [1, 3, 4, 1, 1, 2, 11]
def baseStart_1315701 : Nat := 118140960795 + 1315701 * 2 ^ 59
def prefixEnd_1315701 : Nat := 4983230072969 + 3 ^ 40 * 1315701 * 2
def baseEnd_1315701 : Nat := 8340580377793358610947

theorem tailTrace_1315701 : CollatzResearch.WordTrace tailWord_1315701 prefixEnd_1315701 8340580377793358610947 := by
  unfold tailWord_1315701
  simp only [CollatzResearch.WordTrace]
  refine ⟨47987557806447455686322957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31991705204298303790881971 47987557806447455686322957)
  ·
    refine ⟨17995334177417795882371109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 47987557806447455686322957 17995334177417795882371109)
    ·
      refine ⟨3374125158265836727944583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17995334177417795882371109 3374125158265836727944583)
      ·
        refine ⟨5061187737398755091916875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3374125158265836727944583 5061187737398755091916875)
        ·
          refine ⟨7591781606098132637875313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5061187737398755091916875 7591781606098132637875313)
          ·
            refine ⟨5693836204573599478406485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7591781606098132637875313 5693836204573599478406485)
            ·
              refine ⟨8340580377793358610947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5693836204573599478406485 8340580377793358610947)
              ·
                rfl

theorem cell23_1315701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 11].length) (baseStart_1315701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315701 prefixEnd_1315701 := by exact prefixLift 1315701
  have htrace : WordTrace (prefixWord ++ tailWord_1315701) baseStart_1315701 baseEnd_1315701 := by
    simpa [prefixWord, tailWord_1315701, baseEnd_1315701] using wordTrace_append hprefix tailTrace_1315701
  have hstable : (prefixWord ++ tailWord_1315701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315701).length < 2 ^ (prefixWord ++ tailWord_1315701).sum := by decide
  have hdescent : baseEnd_1315701 < baseStart_1315701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315722 : List Nat := [3, 1, 2, 4, 1, 1, 4, 1, 2, 4]
def baseStart_1315722 : Nat := 118140960795 + 1315722 * 2 ^ 59
def prefixEnd_1315722 : Nat := 4983230072969 + 3 ^ 40 * 1315722 * 2
def baseEnd_1315722 : Nat := 225199264565002155108037

theorem tailTrace_1315722 : CollatzResearch.WordTrace tailWord_1315722 prefixEnd_1315722 225199264565002155108037 := by
  unfold tailWord_1315722
  simp only [CollatzResearch.WordTrace]
  refine ⟨11997080934842844068209355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 31992215826247584181891613 11997080934842844068209355)
  ·
    refine ⟨17995621402264266102314033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11997080934842844068209355 17995621402264266102314033)
    ·
      refine ⟨13496716051698199576735525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17995621402264266102314033 13496716051698199576735525)
      ·
        refine ⟨2530634259693412420637911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13496716051698199576735525 2530634259693412420637911)
        ·
          refine ⟨3795951389540118630956867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2530634259693412420637911 3795951389540118630956867)
          ·
            refine ⟨5693927084310177946435301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3795951389540118630956867 5693927084310177946435301)
            ·
              refine ⟨1067611328308158364956619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5693927084310177946435301 1067611328308158364956619)
              ·
                refine ⟨1601416992462237547434929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1067611328308158364956619 1601416992462237547434929)
                ·
                  refine ⟨1201062744346678160576197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1601416992462237547434929 1201062744346678160576197)
                  ·
                    refine ⟨225199264565002155108037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1201062744346678160576197 225199264565002155108037)
                    ·
                      rfl

theorem cell23_1315722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_1315722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315722 prefixEnd_1315722 := by exact prefixLift 1315722
  have htrace : WordTrace (prefixWord ++ tailWord_1315722) baseStart_1315722 baseEnd_1315722 := by
    simpa [prefixWord, tailWord_1315722, baseEnd_1315722] using wordTrace_append hprefix tailTrace_1315722
  have hstable : (prefixWord ++ tailWord_1315722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315722).length < 2 ^ (prefixWord ++ tailWord_1315722).sum := by decide
  have hdescent : baseEnd_1315722 < baseStart_1315722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315745 : List Nat := [1, 2, 3, 4, 1, 2, 1, 2, 1, 3, 3]
def baseStart_1315745 : Nat := 118140960795 + 1315745 * 2 ^ 59
def prefixEnd_1315745 : Nat := 4983230072969 + 3 ^ 40 * 1315745 * 2
def baseEnd_1315745 : Nat := 675609603750059875336505

theorem tailTrace_1315745 : CollatzResearch.WordTrace tailWord_1315745 prefixEnd_1315745 675609603750059875336505 := by
  unfold tailWord_1315745
  simp only [CollatzResearch.WordTrace]
  refine ⟨47989162618288051200924689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31992775078858700800616459 47989162618288051200924689)
  ·
    refine ⟨35991871963716038400693517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47989162618288051200924689 35991871963716038400693517)
    ·
      refine ⟨13496951986393514400260069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 35991871963716038400693517 13496951986393514400260069)
      ·
        refine ⟨2530678497448783950048763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13496951986393514400260069 2530678497448783950048763)
        ·
          refine ⟨3796017746173175925073145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2530678497448783950048763 3796017746173175925073145)
          ·
            refine ⟨2847013309629881943804859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3796017746173175925073145 2847013309629881943804859)
            ·
              refine ⟨4270519964444822915707289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2847013309629881943804859 4270519964444822915707289)
              ·
                refine ⟨3202889973333617186780467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4270519964444822915707289 3202889973333617186780467)
                ·
                  refine ⟨4804334960000425780170701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3202889973333617186780467 4804334960000425780170701)
                  ·
                    refine ⟨1801625610000159667564013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4804334960000425780170701 1801625610000159667564013)
                    ·
                      refine ⟨675609603750059875336505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1801625610000159667564013 675609603750059875336505)
                      ·
                        rfl

theorem cell23_1315745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_1315745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315745 prefixEnd_1315745 := by exact prefixLift 1315745
  have htrace : WordTrace (prefixWord ++ tailWord_1315745) baseStart_1315745 baseEnd_1315745 := by
    simpa [prefixWord, tailWord_1315745, baseEnd_1315745] using wordTrace_append hprefix tailTrace_1315745
  have hstable : (prefixWord ++ tailWord_1315745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315745).length < 2 ^ (prefixWord ++ tailWord_1315745).sum := by decide
  have hdescent : baseEnd_1315745 < baseStart_1315745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315788 : List Nat := [2, 2, 1, 4, 1, 1, 1, 2, 2, 4, 3]
def baseStart_1315788 : Nat := 118140960795 + 1315788 * 2 ^ 59
def prefixEnd_1315788 : Nat := 4983230072969 + 3 ^ 40 * 1315788 * 2
def baseEnd_1315788 : Nat := 675631683418203207098807

theorem tailTrace_1315788 : CollatzResearch.WordTrace tailWord_1315788 prefixEnd_1315788 675631683418203207098807 := by
  unfold tailWord_1315788
  simp only [CollatzResearch.WordTrace]
  refine ⟨23995365478566134772370009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31993820638088179696493345 23995365478566134772370009)
  ·
    refine ⟨17996524108924601079277507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 23995365478566134772370009 17996524108924601079277507)
    ·
      refine ⟨26994786163386901618916261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17996524108924601079277507 26994786163386901618916261)
      ·
        refine ⟨5061522405635044053546799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26994786163386901618916261 5061522405635044053546799)
        ·
          refine ⟨7592283608452566080320199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5061522405635044053546799 7592283608452566080320199)
          ·
            refine ⟨11388425412678849120480299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7592283608452566080320199 11388425412678849120480299)
            ·
              refine ⟨17082638119018273680720449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11388425412678849120480299 17082638119018273680720449)
              ·
                refine ⟨12811978589263705260540337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17082638119018273680720449 12811978589263705260540337)
                ·
                  refine ⟨9608983941947778945405253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12811978589263705260540337 9608983941947778945405253)
                  ·
                    refine ⟨1801684489115208552263485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9608983941947778945405253 1801684489115208552263485)
                    ·
                      refine ⟨675631683418203207098807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1801684489115208552263485 675631683418203207098807)
                      ·
                        rfl

theorem cell23_1315788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 2, 4, 3].length) (baseStart_1315788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315788 prefixEnd_1315788 := by exact prefixLift 1315788
  have htrace : WordTrace (prefixWord ++ tailWord_1315788) baseStart_1315788 baseEnd_1315788 := by
    simpa [prefixWord, tailWord_1315788, baseEnd_1315788] using wordTrace_append hprefix tailTrace_1315788
  have hstable : (prefixWord ++ tailWord_1315788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315788).length < 2 ^ (prefixWord ++ tailWord_1315788).sum := by decide
  have hdescent : baseEnd_1315788 < baseStart_1315788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315791 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 9]
def baseStart_1315791 : Nat := 118140960795 + 1315791 * 2 ^ 59
def prefixEnd_1315791 : Nat := 4983230072969 + 3 ^ 40 * 1315791 * 2
def baseEnd_1315791 : Nat := 75070358206685188373477

theorem tailTrace_1315791 : CollatzResearch.WordTrace tailWord_1315791 prefixEnd_1315791 75070358206685188373477 := by
  unfold tailWord_1315791
  simp only [CollatzResearch.WordTrace]
  refine ⟨47990840376121401057099227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31993893584080934038066151 47990840376121401057099227)
  ·
    refine ⟨71986260564182101585648841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47990840376121401057099227 71986260564182101585648841)
    ·
      refine ⟨53989695423136576189236631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 71986260564182101585648841 53989695423136576189236631)
      ·
        refine ⟨80984543134704864283854947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53989695423136576189236631 80984543134704864283854947)
        ·
          refine ⟨121476814702057296425782421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80984543134704864283854947 121476814702057296425782421)
          ·
            refine ⟨5694225689158935769958551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 121476814702057296425782421 5694225689158935769958551)
            ·
              refine ⟨8541338533738403654937827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5694225689158935769958551 8541338533738403654937827)
              ·
                refine ⟨12812007800607605482406741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8541338533738403654937827 12812007800607605482406741)
                ·
                  refine ⟨75070358206685188373477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12812007800607605482406741 75070358206685188373477)
                  ·
                    rfl

theorem cell23_1315791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 9].length) (baseStart_1315791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315791 prefixEnd_1315791 := by exact prefixLift 1315791
  have htrace : WordTrace (prefixWord ++ tailWord_1315791) baseStart_1315791 baseEnd_1315791 := by
    simpa [prefixWord, tailWord_1315791, baseEnd_1315791] using wordTrace_append hprefix tailTrace_1315791
  have hstable : (prefixWord ++ tailWord_1315791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315791).length < 2 ^ (prefixWord ++ tailWord_1315791).sum := by decide
  have hdescent : baseEnd_1315791 < baseStart_1315791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315825 : List Nat := [1, 2, 2, 2, 4, 1, 2, 4, 5]
def baseStart_1315825 : Nat := 118140960795 + 1315825 * 2 ^ 59
def prefixEnd_1315825 : Nat := 4983230072969 + 3 ^ 40 * 1315825 * 2
def baseEnd_1315825 : Nat := 75072298022491062481793

theorem tailTrace_1315825 : CollatzResearch.WordTrace tailWord_1315825 prefixEnd_1315825 75072298022491062481793 := by
  unfold tailWord_1315825
  simp only [CollatzResearch.WordTrace]
  refine ⟨47992080457998224863836929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31994720305332149909224619 47992080457998224863836929)
  ·
    refine ⟨35994060343498668647877697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47992080457998224863836929 35994060343498668647877697)
    ·
      refine ⟨26995545257624001485908273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35994060343498668647877697 26995545257624001485908273)
      ·
        refine ⟨20246658943218001114431205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 26995545257624001485908273 20246658943218001114431205)
        ·
          refine ⟨3796248551853375208955851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20246658943218001114431205 3796248551853375208955851)
          ·
            refine ⟨5694372827780062813433777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3796248551853375208955851 5694372827780062813433777)
            ·
              refine ⟨4270779620835047110075333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5694372827780062813433777 4270779620835047110075333)
              ·
                refine ⟨800771178906571333139125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4270779620835047110075333 800771178906571333139125)
                ·
                  refine ⟨75072298022491062481793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 800771178906571333139125 75072298022491062481793)
                  ·
                    rfl

theorem cell23_1315825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 5].length) (baseStart_1315825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315825 prefixEnd_1315825 := by exact prefixLift 1315825
  have htrace : WordTrace (prefixWord ++ tailWord_1315825) baseStart_1315825 baseEnd_1315825 := by
    simpa [prefixWord, tailWord_1315825, baseEnd_1315825] using wordTrace_append hprefix tailTrace_1315825
  have hstable : (prefixWord ++ tailWord_1315825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315825).length < 2 ^ (prefixWord ++ tailWord_1315825).sum := by decide
  have hdescent : baseEnd_1315825 < baseStart_1315825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315872 : List Nat := [2, 1, 1, 7, 1, 1, 1, 2, 2, 5]
def baseStart_1315872 : Nat := 118140960795 + 1315872 * 2 ^ 59
def prefixEnd_1315872 : Nat := 4983230072969 + 3 ^ 40 * 1315872 * 2
def baseEnd_1315872 : Nat := 225224938597726959482807

theorem tailTrace_1315872 : CollatzResearch.WordTrace tailWord_1315872 prefixEnd_1315872 225224938597726959482807 := by
  unfold tailWord_1315872
  simp only [CollatzResearch.WordTrace]
  refine ⟨23996897344413975945398935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31995863125885301260531913 23996897344413975945398935)
  ·
    refine ⟨35995346016620963918098403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23996897344413975945398935 35995346016620963918098403)
    ·
      refine ⟨53993019024931445877147605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 35995346016620963918098403 53993019024931445877147605)
      ·
        refine ⟨1265461383396830762745647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 53993019024931445877147605 1265461383396830762745647)
        ·
          refine ⟨1898192075095246144118471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1265461383396830762745647 1898192075095246144118471)
          ·
            refine ⟨2847288112642869216177707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1898192075095246144118471 2847288112642869216177707)
            ·
              refine ⟨4270932168964303824266561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2847288112642869216177707 4270932168964303824266561)
              ·
                refine ⟨3203199126723227868199921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4270932168964303824266561 3203199126723227868199921)
                ·
                  refine ⟨2402399345042420901149941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3203199126723227868199921 2402399345042420901149941)
                  ·
                    refine ⟨225224938597726959482807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2402399345042420901149941 225224938597726959482807)
                    ·
                      rfl

theorem cell23_1315872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 2, 2, 5].length) (baseStart_1315872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315872 prefixEnd_1315872 := by exact prefixLift 1315872
  have htrace : WordTrace (prefixWord ++ tailWord_1315872) baseStart_1315872 baseEnd_1315872 := by
    simpa [prefixWord, tailWord_1315872, baseEnd_1315872] using wordTrace_append hprefix tailTrace_1315872
  have hstable : (prefixWord ++ tailWord_1315872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315872).length < 2 ^ (prefixWord ++ tailWord_1315872).sum := by decide
  have hdescent : baseEnd_1315872 < baseStart_1315872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315875 : List Nat := [1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 4]
def baseStart_1315875 : Nat := 118140960795 + 1315875 * 2 ^ 59
def prefixEnd_1315875 : Nat := 4983230072969 + 3 ^ 40 * 1315875 * 2
def baseEnd_1315875 : Nat := 675676356235144366710907

theorem tailTrace_1315875 : CollatzResearch.WordTrace tailWord_1315875 prefixEnd_1315875 675676356235144366710907 := by
  unfold tailWord_1315875
  simp only [CollatzResearch.WordTrace]
  refine ⟨47993904107817083403157079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31995936071878055602104719 47993904107817083403157079)
  ·
    refine ⟨71990856161725625104735619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47993904107817083403157079 71990856161725625104735619)
    ·
      refine ⟨107986284242588437657103429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71990856161725625104735619 107986284242588437657103429)
      ·
        refine ⟨20247428295485332060706893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 107986284242588437657103429 20247428295485332060706893)
        ·
          refine ⟨7592785610806999522765085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20247428295485332060706893 7592785610806999522765085)
          ·
            refine ⟨2847294604052624821036907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7592785610806999522765085 2847294604052624821036907)
            ·
              refine ⟨4270941906078937231555361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2847294604052624821036907 4270941906078937231555361)
              ·
                refine ⟨3203206429559202923666521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4270941906078937231555361 3203206429559202923666521)
                ·
                  refine ⟨2402404822169402192749891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3203206429559202923666521 2402404822169402192749891)
                  ·
                    refine ⟨3603607233254103289124837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2402404822169402192749891 3603607233254103289124837)
                    ·
                      refine ⟨675676356235144366710907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3603607233254103289124837 675676356235144366710907)
                      ·
                        rfl

theorem cell23_1315875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_1315875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315875 prefixEnd_1315875 := by exact prefixLift 1315875
  have htrace : WordTrace (prefixWord ++ tailWord_1315875) baseStart_1315875 baseEnd_1315875 := by
    simpa [prefixWord, tailWord_1315875, baseEnd_1315875] using wordTrace_append hprefix tailTrace_1315875
  have hstable : (prefixWord ++ tailWord_1315875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315875).length < 2 ^ (prefixWord ++ tailWord_1315875).sum := by decide
  have hdescent : baseEnd_1315875 < baseStart_1315875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315965 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 3, 1, 4]
def baseStart_1315965 : Nat := 118140960795 + 1315965 * 2 ^ 59
def prefixEnd_1315965 : Nat := 4983230072969 + 3 ^ 40 * 1315965 * 2
def baseEnd_1315965 : Nat := 675722569494049014585493

theorem tailTrace_1315965 : CollatzResearch.WordTrace tailWord_1315965 prefixEnd_1315965 675722569494049014585493 := by
  unfold tailWord_1315965
  simp only [CollatzResearch.WordTrace]
  refine ⟨47997186677491028773933349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31998124451660685849288899 47997186677491028773933349)
  ·
    refine ⟨8999472502029567895112503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 47997186677491028773933349 8999472502029567895112503)
    ·
      refine ⟨13499208753044351842668755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8999472502029567895112503 13499208753044351842668755)
      ·
        refine ⟨20248813129566527764003133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13499208753044351842668755 20248813129566527764003133)
        ·
          refine ⟨7593304923587447911501175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20248813129566527764003133 7593304923587447911501175)
          ·
            refine ⟨11389957385381171867251763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7593304923587447911501175 11389957385381171867251763)
            ·
              refine ⟨17084936078071757800877645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11389957385381171867251763 17084936078071757800877645)
              ·
                refine ⟨6406851029276909175329117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17084936078071757800877645 6406851029276909175329117)
                ·
                  refine ⟨2402569135978840940748419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6406851029276909175329117 2402569135978840940748419)
                  ·
                    refine ⟨3603853703968261411122629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2402569135978840940748419 3603853703968261411122629)
                    ·
                      refine ⟨675722569494049014585493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3603853703968261411122629 675722569494049014585493)
                      ·
                        rfl

theorem cell23_1315965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 3, 1, 4].length) (baseStart_1315965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315965 prefixEnd_1315965 := by exact prefixLift 1315965
  have htrace : WordTrace (prefixWord ++ tailWord_1315965) baseStart_1315965 baseEnd_1315965 := by
    simpa [prefixWord, tailWord_1315965, baseEnd_1315965] using wordTrace_append hprefix tailTrace_1315965
  have hstable : (prefixWord ++ tailWord_1315965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315965).length < 2 ^ (prefixWord ++ tailWord_1315965).sum := by decide
  have hdescent : baseEnd_1315965 < baseStart_1315965 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315969 : List Nat := [1, 2, 4, 2, 2, 1, 3, 1, 2, 3, 2]
def baseStart_1315969 : Nat := 118140960795 + 1315969 * 2 ^ 59
def prefixEnd_1315969 : Nat := 4983230072969 + 3 ^ 40 * 1315969 * 2
def baseEnd_1315969 : Nat := 675724623416666998935475

theorem tailTrace_1315969 : CollatzResearch.WordTrace tailWord_1315969 prefixEnd_1315969 675724623416666998935475 := by
  unfold tailWord_1315969
  simp only [CollatzResearch.WordTrace]
  refine ⟨47997332569476537457078961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31998221712984358304719307 47997332569476537457078961)
  ·
    refine ⟨35997999427107403092809221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 47997332569476537457078961 35997999427107403092809221)
    ·
      refine ⟨6749624892582638079901729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 35997999427107403092809221 6749624892582638079901729)
      ·
        refine ⟨5062218669436978559926297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6749624892582638079901729 5062218669436978559926297)
        ·
          refine ⟨3796664002077733919944723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5062218669436978559926297 3796664002077733919944723)
          ·
            refine ⟨5694996003116600879917085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3796664002077733919944723 5694996003116600879917085)
            ·
              refine ⟨2135623501168725329968907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5694996003116600879917085 2135623501168725329968907)
              ·
                refine ⟨3203435251753087994953361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2135623501168725329968907 3203435251753087994953361)
                ·
                  refine ⟨2402576438814815996215021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3203435251753087994953361 2402576438814815996215021)
                  ·
                    refine ⟨900966164555555998580633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2402576438814815996215021 900966164555555998580633)
                    ·
                      refine ⟨675724623416666998935475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 900966164555555998580633 675724623416666998935475)
                      ·
                        rfl

theorem cell23_1315969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_1315969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315969 prefixEnd_1315969 := by exact prefixLift 1315969
  have htrace : WordTrace (prefixWord ++ tailWord_1315969) baseStart_1315969 baseEnd_1315969 := by
    simpa [prefixWord, tailWord_1315969, baseEnd_1315969] using wordTrace_append hprefix tailTrace_1315969
  have hstable : (prefixWord ++ tailWord_1315969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315969).length < 2 ^ (prefixWord ++ tailWord_1315969).sum := by decide
  have hdescent : baseEnd_1315969 < baseStart_1315969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315975 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 4, 4]
def baseStart_1315975 : Nat := 118140960795 + 1315975 * 2 ^ 59
def prefixEnd_1315975 : Nat := 4983230072969 + 3 ^ 40 * 1315975 * 2
def baseEnd_1315975 : Nat := 225242568100197991820149

theorem tailTrace_1315975 : CollatzResearch.WordTrace tailWord_1315975 prefixEnd_1315975 225242568100197991820149 := by
  unfold tailWord_1315975
  simp only [CollatzResearch.WordTrace]
  refine ⟨47997551407454800481797379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 31998367604969866987864919 47997551407454800481797379)
  ·
    refine ⟨71996327111182200722696069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 47997551407454800481797379 71996327111182200722696069)
    ·
      refine ⟨13499311333346662635505513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 71996327111182200722696069 13499311333346662635505513)
      ·
        refine ⟨10124483500009996976629135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13499311333346662635505513 10124483500009996976629135)
        ·
          refine ⟨15186725250014995464943703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10124483500009996976629135 15186725250014995464943703)
          ·
            refine ⟨22780087875022493197415555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15186725250014995464943703 22780087875022493197415555)
            ·
              refine ⟨34170131812533739796123333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22780087875022493197415555 34170131812533739796123333)
              ·
                refine ⟨6406899714850076211773125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34170131812533739796123333 6406899714850076211773125)
                ·
                  refine ⟨1201293696534389289707461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6406899714850076211773125 1201293696534389289707461)
                  ·
                    refine ⟨225242568100197991820149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1201293696534389289707461 225242568100197991820149)
                    ·
                      rfl

theorem cell23_1315975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 4, 4].length) (baseStart_1315975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315975 prefixEnd_1315975 := by exact prefixLift 1315975
  have htrace : WordTrace (prefixWord ++ tailWord_1315975) baseStart_1315975 baseEnd_1315975 := by
    simpa [prefixWord, tailWord_1315975, baseEnd_1315975] using wordTrace_append hprefix tailTrace_1315975
  have hstable : (prefixWord ++ tailWord_1315975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315975).length < 2 ^ (prefixWord ++ tailWord_1315975).sum := by decide
  have hdescent : baseEnd_1315975 < baseStart_1315975 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1315992 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 4, 4]
def baseStart_1315992 : Nat := 118140960795 + 1315992 * 2 ^ 59
def prefixEnd_1315992 : Nat := 4983230072969 + 3 ^ 40 * 1315992 * 2
def baseEnd_1315992 : Nat := 225245477823906802982623

theorem tailTrace_1315992 : CollatzResearch.WordTrace tailWord_1315992 prefixEnd_1315992 225245477823906802982623 := by
  unfold tailWord_1315992
  simp only [CollatzResearch.WordTrace]
  refine ⟨23999085724196606192583115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 31998780965595474923444153 23999085724196606192583115)
  ·
    refine ⟨35998628586294909288874673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 23999085724196606192583115 35998628586294909288874673)
    ·
      refine ⟨26998971439721181966656005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 35998628586294909288874673 26998971439721181966656005)
      ·
        refine ⟨5062307144947721618748001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 26998971439721181966656005 5062307144947721618748001)
        ·
          refine ⟨3796730358710791214061001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5062307144947721618748001 3796730358710791214061001)
          ·
            refine ⟨2847547769033093410545751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3796730358710791214061001 2847547769033093410545751)
            ·
              refine ⟨4271321653549640115818627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2847547769033093410545751 4271321653549640115818627)
              ·
                refine ⟨6406982480324460173727941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4271321653549640115818627 6406982480324460173727941)
                ·
                  refine ⟨1201309215060836282573989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6406982480324460173727941 1201309215060836282573989)
                  ·
                    refine ⟨225245477823906802982623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1201309215060836282573989 225245477823906802982623)
                    ·
                      rfl

theorem cell23_1315992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 4, 4].length) (baseStart_1315992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1315992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1315992 prefixEnd_1315992 := by exact prefixLift 1315992
  have htrace : WordTrace (prefixWord ++ tailWord_1315992) baseStart_1315992 baseEnd_1315992 := by
    simpa [prefixWord, tailWord_1315992, baseEnd_1315992] using wordTrace_append hprefix tailTrace_1315992
  have hstable : (prefixWord ++ tailWord_1315992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1315992).length < 2 ^ (prefixWord ++ tailWord_1315992).sum := by decide
  have hdescent : baseEnd_1315992 < baseStart_1315992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1315992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316075 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 5]
def baseStart_1316075 : Nat := 118140960795 + 1316075 * 2 ^ 59
def prefixEnd_1316075 : Nat := 4983230072969 + 3 ^ 40 * 1316075 * 2
def baseEnd_1316075 : Nat := 675779052366043584209987

theorem tailTrace_1316075 : CollatzResearch.WordTrace tailWord_1316075 prefixEnd_1316075 675779052366043584209987 := by
  unfold tailWord_1316075
  simp only [CollatzResearch.WordTrace]
  refine ⟨48001198707092517560437679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32000799138061678373625119 48001198707092517560437679)
  ·
    refine ⟨72001798060638776340656519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48001198707092517560437679 72001798060638776340656519)
    ·
      refine ⟨108002697090958164510984779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72001798060638776340656519 108002697090958164510984779)
      ·
        refine ⟨162004045636437246766477169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108002697090958164510984779 162004045636437246766477169)
        ·
          refine ⟨121503034227327935074857877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162004045636437246766477169 121503034227327935074857877)
          ·
            refine ⟨5695454729405996956633963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 121503034227327935074857877 5695454729405996956633963)
            ·
              refine ⟨8543182094108995434950945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5695454729405996956633963 8543182094108995434950945)
              ·
                refine ⟨6407386570581746576213209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8543182094108995434950945 6407386570581746576213209)
                ·
                  refine ⟨4805539927936309932159907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6407386570581746576213209 4805539927936309932159907)
                  ·
                    refine ⟨7208309891904464898239861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4805539927936309932159907 7208309891904464898239861)
                    ·
                      refine ⟨675779052366043584209987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7208309891904464898239861 675779052366043584209987)
                      ·
                        rfl

theorem cell23_1316075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 2, 1, 5].length) (baseStart_1316075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316075 prefixEnd_1316075 := by exact prefixLift 1316075
  have htrace : WordTrace (prefixWord ++ tailWord_1316075) baseStart_1316075 baseEnd_1316075 := by
    simpa [prefixWord, tailWord_1316075, baseEnd_1316075] using wordTrace_append hprefix tailTrace_1316075
  have hstable : (prefixWord ++ tailWord_1316075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316075).length < 2 ^ (prefixWord ++ tailWord_1316075).sum := by decide
  have hdescent : baseEnd_1316075 < baseStart_1316075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316076 : List Nat := [2, 2, 1, 1, 2, 6, 1, 2, 1, 3, 2]
def baseStart_1316076 : Nat := 118140960795 + 1316076 * 2 ^ 59
def prefixEnd_1316076 : Nat := 4983230072969 + 3 ^ 40 * 1316076 * 2
def baseEnd_1316076 : Nat := 675779565846698080297483

theorem tailTrace_1316076 : CollatzResearch.WordTrace tailWord_1316076 prefixEnd_1316076 675779565846698080297483 := by
  unfold tailWord_1316076
  simp only [CollatzResearch.WordTrace]
  refine ⟨24000617590044447365612041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32000823453392596487482721 24000617590044447365612041)
  ·
    refine ⟨18000463192533335524209031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24000617590044447365612041 18000463192533335524209031)
    ·
      refine ⟨27000694788800003286313547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18000463192533335524209031 27000694788800003286313547)
      ·
        refine ⟨40501042183200004929470321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27000694788800003286313547 40501042183200004929470321)
        ·
          refine ⟨30375781637400003697102741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40501042183200004929470321 30375781637400003697102741)
          ·
            refine ⟨1423864764253125173301691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 30375781637400003697102741 1423864764253125173301691)
            ·
              refine ⟨2135797146379687759952537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1423864764253125173301691 2135797146379687759952537)
              ·
                refine ⟨1601847859784765819964403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2135797146379687759952537 1601847859784765819964403)
                ·
                  refine ⟨2402771789677148729946605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1601847859784765819964403 2402771789677148729946605)
                  ·
                    refine ⟨901039421128930773729977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2402771789677148729946605 901039421128930773729977)
                    ·
                      refine ⟨675779565846698080297483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 901039421128930773729977 675779565846698080297483)
                      ·
                        rfl

theorem cell23_1316076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 3, 2].length) (baseStart_1316076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316076 prefixEnd_1316076 := by exact prefixLift 1316076
  have htrace : WordTrace (prefixWord ++ tailWord_1316076) baseStart_1316076 baseEnd_1316076 := by
    simpa [prefixWord, tailWord_1316076, baseEnd_1316076] using wordTrace_append hprefix tailTrace_1316076
  have hstable : (prefixWord ++ tailWord_1316076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316076).length < 2 ^ (prefixWord ++ tailWord_1316076).sum := by decide
  have hdescent : baseEnd_1316076 < baseStart_1316076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316122 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3]
def baseStart_1316122 : Nat := 118140960795 + 1316122 * 2 ^ 59
def prefixEnd_1316122 : Nat := 4983230072969 + 3 ^ 40 * 1316122 * 2
def baseEnd_1316122 : Nat := 675803185956804900322271

theorem tailTrace_1316122 : CollatzResearch.WordTrace tailWord_1316122 prefixEnd_1316122 675803185956804900322271 := by
  unfold tailWord_1316122
  simp only [CollatzResearch.WordTrace]
  refine ⟨12000728234480561146849655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32001941958614829724932413 12000728234480561146849655)
  ·
    refine ⟨18001092351720841720274483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12000728234480561146849655 18001092351720841720274483)
    ·
      refine ⟨27001638527581262580411725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18001092351720841720274483 27001638527581262580411725)
      ·
        refine ⟨10125614447842973467654397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27001638527581262580411725 10125614447842973467654397)
        ·
          refine ⟨3797105417941115050370399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10125614447842973467654397 3797105417941115050370399)
          ·
            refine ⟨5695658126911672575555599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3797105417941115050370399 5695658126911672575555599)
            ·
              refine ⟨8543487190367508863333399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5695658126911672575555599 8543487190367508863333399)
              ·
                refine ⟨12815230785551263295000099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8543487190367508863333399 12815230785551263295000099)
                ·
                  refine ⟨19222846178326894942500149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12815230785551263295000099 19222846178326894942500149)
                  ·
                    refine ⟨1802141829218146400859389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 19222846178326894942500149 1802141829218146400859389)
                    ·
                      refine ⟨675803185956804900322271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1802141829218146400859389 675803185956804900322271)
                      ·
                        rfl

theorem cell23_1316122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_1316122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316122 prefixEnd_1316122 := by exact prefixLift 1316122
  have htrace : WordTrace (prefixWord ++ tailWord_1316122) baseStart_1316122 baseEnd_1316122 := by
    simpa [prefixWord, tailWord_1316122, baseEnd_1316122] using wordTrace_append hprefix tailTrace_1316122
  have hstable : (prefixWord ++ tailWord_1316122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316122).length < 2 ^ (prefixWord ++ tailWord_1316122).sum := by decide
  have hdescent : baseEnd_1316122 < baseStart_1316122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316157 : List Nat := [1, 4, 1, 5, 2, 1, 1, 2, 2, 2, 2]
def baseStart_1316157 : Nat := 118140960795 + 1316157 * 2 ^ 59
def prefixEnd_1316157 : Nat := 4983230072969 + 3 ^ 40 * 1316157 * 2
def baseEnd_1316157 : Nat := 675821157779712263384611

theorem tailTrace_1316157 : CollatzResearch.WordTrace tailWord_1316157 prefixEnd_1316157 675821157779712263384611 := by
  unfold tailWord_1316157
  simp only [CollatzResearch.WordTrace]
  refine ⟨48004189492795445564922725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32002792995196963709948483 48004189492795445564922725)
  ·
    refine ⟨9000785529899146043423011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48004189492795445564922725 9000785529899146043423011)
    ·
      refine ⟨13501178294848719065134517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9000785529899146043423011 13501178294848719065134517)
      ·
        refine ⟨1265735465142067412356361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 13501178294848719065134517 1265735465142067412356361)
        ·
          refine ⟨949301598856550559267271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1265735465142067412356361 949301598856550559267271)
          ·
            refine ⟨1423952398284825838900907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 949301598856550559267271 1423952398284825838900907)
            ·
              refine ⟨2135928597427238758351361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1423952398284825838900907 2135928597427238758351361)
              ·
                refine ⟨1601946448070429068763521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2135928597427238758351361 1601946448070429068763521)
                ·
                  refine ⟨1201459836052821801572641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1601946448070429068763521 1201459836052821801572641)
                  ·
                    refine ⟨901094877039616351179481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1201459836052821801572641 901094877039616351179481)
                    ·
                      refine ⟨675821157779712263384611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 901094877039616351179481 675821157779712263384611)
                      ·
                        rfl

theorem cell23_1316157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_1316157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316157 prefixEnd_1316157 := by exact prefixLift 1316157
  have htrace : WordTrace (prefixWord ++ tailWord_1316157) baseStart_1316157 baseEnd_1316157 := by
    simpa [prefixWord, tailWord_1316157, baseEnd_1316157] using wordTrace_append hprefix tailTrace_1316157
  have hstable : (prefixWord ++ tailWord_1316157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316157).length < 2 ^ (prefixWord ++ tailWord_1316157).sum := by decide
  have hdescent : baseEnd_1316157 < baseStart_1316157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316165 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 2, 3, 5]
def baseStart_1316165 : Nat := 118140960795 + 1316165 * 2 ^ 59
def prefixEnd_1316165 : Nat := 4983230072969 + 3 ^ 40 * 1316165 * 2
def baseEnd_1316165 : Nat := 675825265624948232084573

theorem tailTrace_1316165 : CollatzResearch.WordTrace tailWord_1316165 prefixEnd_1316165 675825265624948232084573 := by
  unfold tailWord_1316165
  simp only [CollatzResearch.WordTrace]
  refine ⟨48004481276766462931213949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32002987517844308620809299 48004481276766462931213949)
  ·
    refine ⟨18001680478787423599205231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48004481276766462931213949 18001680478787423599205231)
    ·
      refine ⟨27002520718181135398807847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18001680478787423599205231 27002520718181135398807847)
      ·
        refine ⟨40503781077271703098211771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27002520718181135398807847 40503781077271703098211771)
        ·
          refine ⟨60755671615907554647317657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40503781077271703098211771 60755671615907554647317657)
          ·
            refine ⟨45566753711930665985488243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60755671615907554647317657 45566753711930665985488243)
            ·
              refine ⟨68350130567895998978232365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45566753711930665985488243 68350130567895998978232365)
              ·
                refine ⟨25631298962960999616837137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 68350130567895998978232365 25631298962960999616837137)
                ·
                  refine ⟨19223474222220749712627853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25631298962960999616837137 19223474222220749712627853)
                  ·
                    refine ⟨7208802833332781142235445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19223474222220749712627853 7208802833332781142235445)
                    ·
                      refine ⟨675825265624948232084573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7208802833332781142235445 675825265624948232084573)
                      ·
                        rfl

theorem cell23_1316165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_1316165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316165 prefixEnd_1316165 := by exact prefixLift 1316165
  have htrace : WordTrace (prefixWord ++ tailWord_1316165) baseStart_1316165 baseEnd_1316165 := by
    simpa [prefixWord, tailWord_1316165, baseEnd_1316165] using wordTrace_append hprefix tailTrace_1316165
  have hstable : (prefixWord ++ tailWord_1316165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316165).length < 2 ^ (prefixWord ++ tailWord_1316165).sum := by decide
  have hdescent : baseEnd_1316165 < baseStart_1316165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316249 : List Nat := [1, 2, 1, 2, 1, 5, 3, 2, 1, 5]
def baseStart_1316249 : Nat := 118140960795 + 1316249 * 2 ^ 59
def prefixEnd_1316249 : Nat := 4983230072969 + 3 ^ 40 * 1316249 * 2
def baseEnd_1316249 : Nat := 225289465999975301144729

theorem tailTrace_1316249 : CollatzResearch.WordTrace tailWord_1316249 prefixEnd_1316249 225289465999975301144729 := by
  unfold tailWord_1316249
  simp only [CollatzResearch.WordTrace]
  refine ⟨48007545008462145277271801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32005030005641430184847867 48007545008462145277271801)
  ·
    refine ⟨36005658756346608957953851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48007545008462145277271801 36005658756346608957953851)
    ·
      refine ⟨54008488134519913436930777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36005658756346608957953851 54008488134519913436930777)
      ·
        refine ⟨40506366100889935077698083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54008488134519913436930777 40506366100889935077698083)
        ·
          refine ⟨60759549151334902616547125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40506366100889935077698083 60759549151334902616547125)
          ·
            refine ⟨5696207732937647120301293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60759549151334902616547125 5696207732937647120301293)
            ·
              refine ⟨2136077899851617670112985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5696207732937647120301293 2136077899851617670112985)
              ·
                refine ⟨1602058424888713252584739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2136077899851617670112985 1602058424888713252584739)
                ·
                  refine ⟨2403087637333069878877109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1602058424888713252584739 2403087637333069878877109)
                  ·
                    refine ⟨225289465999975301144729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2403087637333069878877109 225289465999975301144729)
                    ·
                      rfl

theorem cell23_1316249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 1, 5].length) (baseStart_1316249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316249 prefixEnd_1316249 := by exact prefixLift 1316249
  have htrace : WordTrace (prefixWord ++ tailWord_1316249) baseStart_1316249 baseEnd_1316249 := by
    simpa [prefixWord, tailWord_1316249, baseEnd_1316249] using wordTrace_append hprefix tailTrace_1316249
  have hstable : (prefixWord ++ tailWord_1316249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316249).length < 2 ^ (prefixWord ++ tailWord_1316249).sum := by decide
  have hdescent : baseEnd_1316249 < baseStart_1316249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316256 : List Nat := [2, 1, 1, 4, 1, 2, 4, 1, 2, 3, 2]
def baseStart_1316256 : Nat := 118140960795 + 1316256 * 2 ^ 59
def prefixEnd_1316256 : Nat := 4983230072969 + 3 ^ 40 * 1316256 * 2
def baseEnd_1316256 : Nat := 675871992364507376046655

theorem tailTrace_1316256 : CollatzResearch.WordTrace tailWord_1316256 prefixEnd_1316256 675871992364507376046655 := by
  unfold tailWord_1316256
  simp only [CollatzResearch.WordTrace]
  refine ⟨24003900159718392736388311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32005200212957856981851081 24003900159718392736388311)
  ·
    refine ⟨36005850239577589104582467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24003900159718392736388311 36005850239577589104582467)
    ·
      refine ⟨54008775359366383656873701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36005850239577589104582467 54008775359366383656873701)
      ·
        refine ⟨10126645379881196935663819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54008775359366383656873701 10126645379881196935663819)
        ·
          refine ⟨15189968069821795403495729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10126645379881196935663819 15189968069821795403495729)
          ·
            refine ⟨11392476052366346552621797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15189968069821795403495729 11392476052366346552621797)
            ·
              refine ⟨2136089259818689978616587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11392476052366346552621797 2136089259818689978616587)
              ·
                refine ⟨3204133889728034967924881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2136089259818689978616587 3204133889728034967924881)
                ·
                  refine ⟨2403100417296026225943661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3204133889728034967924881 2403100417296026225943661)
                  ·
                    refine ⟨901162656486009834728873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2403100417296026225943661 901162656486009834728873)
                    ·
                      refine ⟨675871992364507376046655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 901162656486009834728873 675871992364507376046655)
                      ·
                        rfl

theorem cell23_1316256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_1316256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316256 prefixEnd_1316256 := by exact prefixLift 1316256
  have htrace : WordTrace (prefixWord ++ tailWord_1316256) baseStart_1316256 baseEnd_1316256 := by
    simpa [prefixWord, tailWord_1316256, baseEnd_1316256] using wordTrace_append hprefix tailTrace_1316256
  have hstable : (prefixWord ++ tailWord_1316256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316256).length < 2 ^ (prefixWord ++ tailWord_1316256).sum := by decide
  have hdescent : baseEnd_1316256 < baseStart_1316256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316263 : List Nat := [1, 1, 6, 1, 1, 1, 2, 5, 1, 1, 3]
def baseStart_1316263 : Nat := 118140960795 + 1316263 * 2 ^ 59
def prefixEnd_1316263 : Nat := 4983230072969 + 3 ^ 40 * 1316263 * 2
def baseEnd_1316263 : Nat := 675875586729088848659123

theorem tailTrace_1316263 : CollatzResearch.WordTrace tailWord_1316263 prefixEnd_1316263 675875586729088848659123 := by
  unfold tailWord_1316263
  simp only [CollatzResearch.WordTrace]
  refine ⟨48008055630411425668281443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32005370420274283778854295 48008055630411425668281443)
  ·
    refine ⟨72012083445617138502422165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48008055630411425668281443 72012083445617138502422165)
    ·
      refine ⟨3375566411513303367301039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 72012083445617138502422165 3375566411513303367301039)
      ·
        refine ⟨5063349617269955050951559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3375566411513303367301039 5063349617269955050951559)
        ·
          refine ⟨7595024425904932576427339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5063349617269955050951559 7595024425904932576427339)
          ·
            refine ⟨11392536638857398864641009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7595024425904932576427339 11392536638857398864641009)
            ·
              refine ⟨8544402479143049148480757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11392536638857398864641009 8544402479143049148480757)
              ·
                refine ⟨801037732419660857670071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8544402479143049148480757 801037732419660857670071)
                ·
                  refine ⟨1201556598629491286505107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 801037732419660857670071 1201556598629491286505107)
                  ·
                    refine ⟨1802334897944236929757661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1201556598629491286505107 1802334897944236929757661)
                    ·
                      refine ⟨675875586729088848659123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1802334897944236929757661 675875586729088848659123)
                      ·
                        rfl

theorem cell23_1316263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 1, 1, 3].length) (baseStart_1316263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316263 prefixEnd_1316263 := by exact prefixLift 1316263
  have htrace : WordTrace (prefixWord ++ tailWord_1316263) baseStart_1316263 baseEnd_1316263 := by
    simpa [prefixWord, tailWord_1316263, baseEnd_1316263] using wordTrace_append hprefix tailTrace_1316263
  have hstable : (prefixWord ++ tailWord_1316263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316263).length < 2 ^ (prefixWord ++ tailWord_1316263).sum := by decide
  have hdescent : baseEnd_1316263 < baseStart_1316263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316272 : List Nat := [2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 5]
def baseStart_1316272 : Nat := 118140960795 + 1316272 * 2 ^ 59
def prefixEnd_1316272 : Nat := 4983230072969 + 3 ^ 40 * 1316272 * 2
def baseEnd_1316272 : Nat := 675880208054979313446581

theorem tailTrace_1316272 : CollatzResearch.WordTrace tailWord_1316272 prefixEnd_1316272 675880208054979313446581 := by
  unfold tailWord_1316272
  simp only [CollatzResearch.WordTrace]
  refine ⟨24004191943689410102679535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32005589258252546803572713 24004191943689410102679535)
  ·
    refine ⟨36006287915534115154019303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24004191943689410102679535 36006287915534115154019303)
    ·
      refine ⟨54009431873301172731028955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36006287915534115154019303 54009431873301172731028955)
      ·
        refine ⟨81014147809951759096543433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54009431873301172731028955 81014147809951759096543433)
        ·
          refine ⟨60760610857463819322407575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81014147809951759096543433 60760610857463819322407575)
          ·
            refine ⟨91140916286195728983611363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60760610857463819322407575 91140916286195728983611363)
            ·
              refine ⟨136711374429293593475417045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91140916286195728983611363 136711374429293593475417045)
              ·
                refine ⟨3204172838186568597080087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 136711374429293593475417045 3204172838186568597080087)
                ·
                  refine ⟨4806259257279852895620131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3204172838186568597080087 4806259257279852895620131)
                  ·
                    refine ⟨7209388885919779343430197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4806259257279852895620131 7209388885919779343430197)
                    ·
                      refine ⟨675880208054979313446581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7209388885919779343430197 675880208054979313446581)
                      ·
                        rfl

theorem cell23_1316272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 1, 1, 5].length) (baseStart_1316272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316272 prefixEnd_1316272 := by exact prefixLift 1316272
  have htrace : WordTrace (prefixWord ++ tailWord_1316272) baseStart_1316272 baseEnd_1316272 := by
    simpa [prefixWord, tailWord_1316272, baseEnd_1316272] using wordTrace_append hprefix tailTrace_1316272
  have hstable : (prefixWord ++ tailWord_1316272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316272).length < 2 ^ (prefixWord ++ tailWord_1316272).sum := by decide
  have hdescent : baseEnd_1316272 < baseStart_1316272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316309 : List Nat := [1, 3, 2, 3, 1, 1, 5, 7]
def baseStart_1316309 : Nat := 118140960795 + 1316309 * 2 ^ 59
def prefixEnd_1316309 : Nat := 4983230072969 + 3 ^ 40 * 1316309 * 2
def baseEnd_1316309 : Nat := 25033303957007246988293

theorem tailTrace_1316309 : CollatzResearch.WordTrace tailWord_1316309 prefixEnd_1316309 25033303957007246988293 := by
  unfold tailWord_1316309
  simp only [CollatzResearch.WordTrace]
  refine ⟨48009733388244775524455981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32006488925496517016303987 48009733388244775524455981)
  ·
    refine ⟨18003650020591790821670993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48009733388244775524455981 18003650020591790821670993)
    ·
      refine ⟨13502737515443843116253245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18003650020591790821670993 13502737515443843116253245)
      ·
        refine ⟨5063526568291441168594967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13502737515443843116253245 5063526568291441168594967)
        ·
          refine ⟨7595289852437161752892451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5063526568291441168594967 7595289852437161752892451)
          ·
            refine ⟨11392934778655742629338677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7595289852437161752892451 11392934778655742629338677)
            ·
              refine ⟨1068087635498975871500501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11392934778655742629338677 1068087635498975871500501)
              ·
                refine ⟨25033303957007246988293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1068087635498975871500501 25033303957007246988293)
                ·
                  rfl

theorem cell23_1316309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 5, 7].length) (baseStart_1316309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316309 prefixEnd_1316309 := by exact prefixLift 1316309
  have htrace : WordTrace (prefixWord ++ tailWord_1316309) baseStart_1316309 baseEnd_1316309 := by
    simpa [prefixWord, tailWord_1316309, baseEnd_1316309] using wordTrace_append hprefix tailTrace_1316309
  have hstable : (prefixWord ++ tailWord_1316309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316309).length < 2 ^ (prefixWord ++ tailWord_1316309).sum := by decide
  have hdescent : baseEnd_1316309 < baseStart_1316309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316319 : List Nat := [1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 3]
def baseStart_1316319 : Nat := 118140960795 + 1316319 * 2 ^ 59
def prefixEnd_1316319 : Nat := 4983230072969 + 3 ^ 40 * 1316319 * 2
def baseEnd_1316319 : Nat := 675904341645740629558865

theorem tailTrace_1316319 : CollatzResearch.WordTrace tailWord_1316319 prefixEnd_1316319 675904341645740629558865 := by
  unfold tailWord_1316319
  simp only [CollatzResearch.WordTrace]
  refine ⟨48010098118208547232320011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32006732078805698154880007 48010098118208547232320011)
  ·
    refine ⟨72015147177312820848480017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48010098118208547232320011 72015147177312820848480017)
    ·
      refine ⟨54011360382984615636360013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72015147177312820848480017 54011360382984615636360013)
      ·
        refine ⟨20254260143619230863635005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54011360382984615636360013 20254260143619230863635005)
        ·
          refine ⟨7595347553857211573863127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20254260143619230863635005 7595347553857211573863127)
          ·
            refine ⟨11393021330785817360794691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7595347553857211573863127 11393021330785817360794691)
            ·
              refine ⟨17089531996178726041192037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11393021330785817360794691 17089531996178726041192037)
              ·
                refine ⟨3204287249283511132723507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17089531996178726041192037 3204287249283511132723507)
                ·
                  refine ⟨4806430873925266699085261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3204287249283511132723507 4806430873925266699085261)
                  ·
                    refine ⟨1802411577721975012156973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4806430873925266699085261 1802411577721975012156973)
                    ·
                      refine ⟨675904341645740629558865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1802411577721975012156973 675904341645740629558865)
                      ·
                        rfl

theorem cell23_1316319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_1316319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316319 prefixEnd_1316319 := by exact prefixLift 1316319
  have htrace : WordTrace (prefixWord ++ tailWord_1316319) baseStart_1316319 baseEnd_1316319 := by
    simpa [prefixWord, tailWord_1316319, baseEnd_1316319] using wordTrace_append hprefix tailTrace_1316319
  have hstable : (prefixWord ++ tailWord_1316319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316319).length < 2 ^ (prefixWord ++ tailWord_1316319).sum := by decide
  have hdescent : baseEnd_1316319 < baseStart_1316319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316323 : List Nat := [1, 1, 1, 6, 2, 1, 4, 1, 1, 2, 3]
def baseStart_1316323 : Nat := 118140960795 + 1316323 * 2 ^ 59
def prefixEnd_1316323 : Nat := 4983230072969 + 3 ^ 40 * 1316323 * 2
def baseEnd_1316323 : Nat := 675906395568358613908847

theorem tailTrace_1316323 : CollatzResearch.WordTrace tailWord_1316323 prefixEnd_1316323 675906395568358613908847 := by
  unfold tailWord_1316323
  simp only [CollatzResearch.WordTrace]
  refine ⟨48010244010194055915465623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32006829340129370610310415 48010244010194055915465623)
  ·
    refine ⟨72015366015291083873198435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48010244010194055915465623 72015366015291083873198435)
    ·
      refine ⟨108023049022936625809797653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72015366015291083873198435 108023049022936625809797653)
      ·
        refine ⟨5063580422950154334834265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 108023049022936625809797653 5063580422950154334834265)
        ·
          refine ⟨3797685317212615751125699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5063580422950154334834265 3797685317212615751125699)
          ·
            refine ⟨5696527975818923626688549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3797685317212615751125699 5696527975818923626688549)
            ·
              refine ⟨1068098995466048180004103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5696527975818923626688549 1068098995466048180004103)
              ·
                refine ⟨1602148493199072270006155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1068098995466048180004103 1602148493199072270006155)
                ·
                  refine ⟨2403222739798608405009233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1602148493199072270006155 2403222739798608405009233)
                  ·
                    refine ⟨1802417054848956303756925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2403222739798608405009233 1802417054848956303756925)
                    ·
                      refine ⟨675906395568358613908847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1802417054848956303756925 675906395568358613908847)
                      ·
                        rfl

theorem cell23_1316323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_1316323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316323 prefixEnd_1316323 := by exact prefixLift 1316323
  have htrace : WordTrace (prefixWord ++ tailWord_1316323) baseStart_1316323 baseEnd_1316323 := by
    simpa [prefixWord, tailWord_1316323, baseEnd_1316323] using wordTrace_append hprefix tailTrace_1316323
  have hstable : (prefixWord ++ tailWord_1316323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316323).length < 2 ^ (prefixWord ++ tailWord_1316323).sum := by decide
  have hdescent : baseEnd_1316323 < baseStart_1316323 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316330 : List Nat := [3, 1, 3, 1, 5, 1, 1, 2, 2, 4]
def baseStart_1316330 : Nat := 118140960795 + 1316330 * 2 ^ 59
def prefixEnd_1316330 : Nat := 4983230072969 + 3 ^ 40 * 1316330 * 2
def baseEnd_1316330 : Nat := 225303329977646695507105

theorem tailTrace_1316330 : CollatzResearch.WordTrace tailWord_1316330 prefixEnd_1316330 225303329977646695507105 := by
  unfold tailWord_1316330
  simp only [CollatzResearch.WordTrace]
  refine ⟨12002624830292174027742611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32006999547445797407313629 12002624830292174027742611)
  ·
    refine ⟨18003937245438261041613917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12002624830292174027742611 18003937245438261041613917)
    ·
      refine ⟨6751476467039347890605219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18003937245438261041613917 6751476467039347890605219)
      ·
        refine ⟨10127214700559021835907829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6751476467039347890605219 10127214700559021835907829)
        ·
          refine ⟨949426378177408297116359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10127214700559021835907829 949426378177408297116359)
          ·
            refine ⟨1424139567266112445674539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 949426378177408297116359 1424139567266112445674539)
            ·
              refine ⟨2136209350899168668511809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1424139567266112445674539 2136209350899168668511809)
              ·
                refine ⟨1602157013174376501383857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2136209350899168668511809 1602157013174376501383857)
                ·
                  refine ⟨1201617759880782376037893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1602157013174376501383857 1201617759880782376037893)
                  ·
                    refine ⟨225303329977646695507105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1201617759880782376037893 225303329977646695507105)
                    ·
                      rfl

theorem cell23_1316330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_1316330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316330 prefixEnd_1316330 := by exact prefixLift 1316330
  have htrace : WordTrace (prefixWord ++ tailWord_1316330) baseStart_1316330 baseEnd_1316330 := by
    simpa [prefixWord, tailWord_1316330, baseEnd_1316330] using wordTrace_append hprefix tailTrace_1316330
  have hstable : (prefixWord ++ tailWord_1316330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316330).length < 2 ^ (prefixWord ++ tailWord_1316330).sum := by decide
  have hdescent : baseEnd_1316330 < baseStart_1316330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316332 : List Nat := [2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 5]
def baseStart_1316332 : Nat := 118140960795 + 1316332 * 2 ^ 59
def prefixEnd_1316332 : Nat := 4983230072969 + 3 ^ 40 * 1316332 * 2
def baseEnd_1316332 : Nat := 675911016894249078696305

theorem tailTrace_1316332 : CollatzResearch.WordTrace tailWord_1316332 prefixEnd_1316332 675911016894249078696305 := by
  unfold tailWord_1316332
  simp only [CollatzResearch.WordTrace]
  refine ⟨24005286133580725226271625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32007048178107633635028833 24005286133580725226271625)
  ·
    refine ⟨18003964600185543919703719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24005286133580725226271625 18003964600185543919703719)
    ·
      refine ⟨27005946900278315879555579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18003964600185543919703719 27005946900278315879555579)
      ·
        refine ⟨40508920350417473819333369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27005946900278315879555579 40508920350417473819333369)
        ·
          refine ⟨30381690262813105364500027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40508920350417473819333369 30381690262813105364500027)
          ·
            refine ⟨45572535394219658046750041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30381690262813105364500027 45572535394219658046750041)
            ·
              refine ⟨34179401545664743535062531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45572535394219658046750041 34179401545664743535062531)
              ·
                refine ⟨51269102318497115302593797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34179401545664743535062531 51269102318497115302593797)
                ·
                  refine ⟨9612956684718209119236337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51269102318497115302593797 9612956684718209119236337)
                  ·
                    refine ⟨7209717513538656839427253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9612956684718209119236337 7209717513538656839427253)
                    ·
                      refine ⟨675911016894249078696305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7209717513538656839427253 675911016894249078696305)
                      ·
                        rfl

theorem cell23_1316332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 5].length) (baseStart_1316332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316332 prefixEnd_1316332 := by exact prefixLift 1316332
  have htrace : WordTrace (prefixWord ++ tailWord_1316332) baseStart_1316332 baseEnd_1316332 := by
    simpa [prefixWord, tailWord_1316332, baseEnd_1316332] using wordTrace_append hprefix tailTrace_1316332
  have hstable : (prefixWord ++ tailWord_1316332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316332).length < 2 ^ (prefixWord ++ tailWord_1316332).sum := by decide
  have hdescent : baseEnd_1316332 < baseStart_1316332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316336 : List Nat := [2, 1, 1, 1, 3, 5, 1, 1, 4, 1, 3]
def baseStart_1316336 : Nat := 118140960795 + 1316336 * 2 ^ 59
def prefixEnd_1316336 : Nat := 4983230072969 + 3 ^ 40 * 1316336 * 2
def baseEnd_1316336 : Nat := 675913070816867063046287

theorem tailTrace_1316336 : CollatzResearch.WordTrace tailWord_1316336 prefixEnd_1316336 675913070816867063046287 := by
  unfold tailWord_1316336
  simp only [CollatzResearch.WordTrace]
  refine ⟨24005359079573479567844431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32007145439431306090459241 24005359079573479567844431)
  ·
    refine ⟨36008038619360219351766647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24005359079573479567844431 36008038619360219351766647)
    ·
      refine ⟨54012057929040329027649971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36008038619360219351766647 54012057929040329027649971)
      ·
        refine ⟨81018086893560493541474957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54012057929040329027649971 81018086893560493541474957)
        ·
          refine ⟨30381782585085185078053109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81018086893560493541474957 30381782585085185078053109)
          ·
            refine ⟨2848292117351736101067479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 30381782585085185078053109 2848292117351736101067479)
            ·
              refine ⟨4272438176027604151601219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2848292117351736101067479 4272438176027604151601219)
              ·
                refine ⟨6408657264041406227401829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4272438176027604151601219 6408657264041406227401829)
                ·
                  refine ⟨1201623237007763667637843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6408657264041406227401829 1201623237007763667637843)
                  ·
                    refine ⟨1802434855511645501456765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1201623237007763667637843 1802434855511645501456765)
                    ·
                      refine ⟨675913070816867063046287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1802434855511645501456765 675913070816867063046287)
                      ·
                        rfl

theorem cell23_1316336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 1, 4, 1, 3].length) (baseStart_1316336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316336 prefixEnd_1316336 := by exact prefixLift 1316336
  have htrace : WordTrace (prefixWord ++ tailWord_1316336) baseStart_1316336 baseEnd_1316336 := by
    simpa [prefixWord, tailWord_1316336, baseEnd_1316336] using wordTrace_append hprefix tailTrace_1316336
  have hstable : (prefixWord ++ tailWord_1316336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316336).length < 2 ^ (prefixWord ++ tailWord_1316336).sum := by decide
  have hdescent : baseEnd_1316336 < baseStart_1316336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316350 : List Nat := [4, 2, 2, 3, 1, 2, 1, 1, 1, 2, 4]
def baseStart_1316350 : Nat := 118140960795 + 1316350 * 2 ^ 59
def prefixEnd_1316350 : Nat := 4983230072969 + 3 ^ 40 * 1316350 * 2
def baseEnd_1316350 : Nat := 675920259546030008271223

theorem tailTrace_1316350 : CollatzResearch.WordTrace tailWord_1316350 prefixEnd_1316350 675920259546030008271223 := by
  unfold tailWord_1316350
  simp only [CollatzResearch.WordTrace]
  refine ⟨6001403597637029940837313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32007485854064159684465669 6001403597637029940837313)
  ·
    refine ⟨4501052698227772455627985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6001403597637029940837313 4501052698227772455627985)
    ·
      refine ⟨3375789523670829341720989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4501052698227772455627985 3375789523670829341720989)
      ·
        refine ⟨1265921071376561003145371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3375789523670829341720989 1265921071376561003145371)
        ·
          refine ⟨1898881607064841504718057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1265921071376561003145371 1898881607064841504718057)
          ·
            refine ⟨1424161205298631128538543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1898881607064841504718057 1424161205298631128538543)
            ·
              refine ⟨2136241807947946692807815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1424161205298631128538543 2136241807947946692807815)
              ·
                refine ⟨3204362711921920039211723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2136241807947946692807815 3204362711921920039211723)
                ·
                  refine ⟨4806544067882880058817585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3204362711921920039211723 4806544067882880058817585)
                  ·
                    refine ⟨3604908050912160044113189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4806544067882880058817585 3604908050912160044113189)
                    ·
                      refine ⟨675920259546030008271223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3604908050912160044113189 675920259546030008271223)
                      ·
                        rfl

theorem cell23_1316350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_1316350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316350 prefixEnd_1316350 := by exact prefixLift 1316350
  have htrace : WordTrace (prefixWord ++ tailWord_1316350) baseStart_1316350 baseEnd_1316350 := by
    simpa [prefixWord, tailWord_1316350, baseEnd_1316350] using wordTrace_append hprefix tailTrace_1316350
  have hstable : (prefixWord ++ tailWord_1316350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316350).length < 2 ^ (prefixWord ++ tailWord_1316350).sum := by decide
  have hdescent : baseEnd_1316350 < baseStart_1316350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316353 : List Nat := [1, 2, 4, 1, 4, 2, 1, 1, 1, 3, 3]
def baseStart_1316353 : Nat := 118140960795 + 1316353 * 2 ^ 59
def prefixEnd_1316353 : Nat := 4983230072969 + 3 ^ 40 * 1316353 * 2
def baseEnd_1316353 : Nat := 675921799987993496533709

theorem tailTrace_1316353 : CollatzResearch.WordTrace tailWord_1316353 prefixEnd_1316353 675921799987993496533709 := by
  unfold tailWord_1316353
  simp only [CollatzResearch.WordTrace]
  refine ⟨48011338200085371039057713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32007558800056914026038475 48011338200085371039057713)
  ·
    refine ⟨36008503650064028279293285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48011338200085371039057713 36008503650064028279293285)
    ·
      refine ⟨6751594434387005302367491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36008503650064028279293285 6751594434387005302367491)
      ·
        refine ⟨10127391651580507953551237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6751594434387005302367491 10127391651580507953551237)
        ·
          refine ⟨1898885934671345241290857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10127391651580507953551237 1898885934671345241290857)
          ·
            refine ⟨1424164451003508930968143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1898885934671345241290857 1424164451003508930968143)
            ·
              refine ⟨2136246676505263396452215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1424164451003508930968143 2136246676505263396452215)
              ·
                refine ⟨3204370014757895094678323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2136246676505263396452215 3204370014757895094678323)
                ·
                  refine ⟨4806555022136842642017485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3204370014757895094678323 4806555022136842642017485)
                  ·
                    refine ⟨1802458133301315990756557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4806555022136842642017485 1802458133301315990756557)
                    ·
                      refine ⟨675921799987993496533709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1802458133301315990756557 675921799987993496533709)
                      ·
                        rfl

theorem cell23_1316353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_1316353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316353 prefixEnd_1316353 := by exact prefixLift 1316353
  have htrace : WordTrace (prefixWord ++ tailWord_1316353) baseStart_1316353 baseEnd_1316353 := by
    simpa [prefixWord, tailWord_1316353, baseEnd_1316353] using wordTrace_append hprefix tailTrace_1316353
  have hstable : (prefixWord ++ tailWord_1316353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316353).length < 2 ^ (prefixWord ++ tailWord_1316353).sum := by decide
  have hdescent : baseEnd_1316353 < baseStart_1316353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316439 : List Nat := [1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 5]
def baseStart_1316439 : Nat := 118140960795 + 1316439 * 2 ^ 59
def prefixEnd_1316439 : Nat := 4983230072969 + 3 ^ 40 * 1316439 * 2
def baseEnd_1316439 : Nat := 675965959324280160058313

theorem tailTrace_1316439 : CollatzResearch.WordTrace tailWord_1316439 prefixEnd_1316439 675965959324280160058313 := by
  unfold tailWord_1316439
  simp only [CollatzResearch.WordTrace]
  refine ⟨48014474877773807726688371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32009649918515871817792247 48014474877773807726688371)
  ·
    refine ⟨72021712316660711590032557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48014474877773807726688371 72021712316660711590032557)
    ·
      refine ⟨27008142118747766846262209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72021712316660711590032557 27008142118747766846262209)
      ·
        refine ⟨20256106589060825134696657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27008142118747766846262209 20256106589060825134696657)
        ·
          refine ⟨15192079941795618851022493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20256106589060825134696657 15192079941795618851022493)
          ·
            refine ⟨5697029978173357069133435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15192079941795618851022493 5697029978173357069133435)
            ·
              refine ⟨8545544967260035603700153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5697029978173357069133435 8545544967260035603700153)
              ·
                refine ⟨6409158725445026702775115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8545544967260035603700153 6409158725445026702775115)
                ·
                  refine ⟨9613738088167540054162673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6409158725445026702775115 9613738088167540054162673)
                  ·
                    refine ⟨7210303566125655040622005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9613738088167540054162673 7210303566125655040622005)
                    ·
                      refine ⟨675965959324280160058313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7210303566125655040622005 675965959324280160058313)
                      ·
                        rfl

theorem cell23_1316439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 2, 1, 2, 5].length) (baseStart_1316439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316439 prefixEnd_1316439 := by exact prefixLift 1316439
  have htrace : WordTrace (prefixWord ++ tailWord_1316439) baseStart_1316439 baseEnd_1316439 := by
    simpa [prefixWord, tailWord_1316439, baseEnd_1316439] using wordTrace_append hprefix tailTrace_1316439
  have hstable : (prefixWord ++ tailWord_1316439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316439).length < 2 ^ (prefixWord ++ tailWord_1316439).sum := by decide
  have hdescent : baseEnd_1316439 < baseStart_1316439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316456 : List Nat := [2, 1, 4, 3, 1, 1, 2, 1, 1, 2, 5]
def baseStart_1316456 : Nat := 118140960795 + 1316456 * 2 ^ 59
def prefixEnd_1316456 : Nat := 4983230072969 + 3 ^ 40 * 1316456 * 2
def baseEnd_1316456 : Nat := 675974688495406593545735

theorem tailTrace_1316456 : CollatzResearch.WordTrace tailWord_1316456 prefixEnd_1316456 675974688495406593545735 := by
  unfold tailWord_1316456
  simp only [CollatzResearch.WordTrace]
  refine ⟨24007547459356109815028611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32010063279141479753371481 24007547459356109815028611)
  ·
    refine ⟨36011321189034164722542917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24007547459356109815028611 36011321189034164722542917)
    ·
      refine ⟨6752122722943905885476797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36011321189034164722542917 6752122722943905885476797)
      ·
        refine ⟨2532046021103964707053799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6752122722943905885476797 2532046021103964707053799)
        ·
          refine ⟨3798069031655947060580699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2532046021103964707053799 3798069031655947060580699)
          ·
            refine ⟨5697103547483920590871049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3798069031655947060580699 5697103547483920590871049)
            ·
              refine ⟨4272827660612940443153287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5697103547483920590871049 4272827660612940443153287)
              ·
                refine ⟨6409241490919410664729931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4272827660612940443153287 6409241490919410664729931)
                ·
                  refine ⟨9613862236379115997094897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6409241490919410664729931 9613862236379115997094897)
                  ·
                    refine ⟨7210396677284336997821173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9613862236379115997094897 7210396677284336997821173)
                    ·
                      refine ⟨675974688495406593545735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7210396677284336997821173 675974688495406593545735)
                      ·
                        rfl

theorem cell23_1316456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 1, 1, 2, 5].length) (baseStart_1316456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316456 prefixEnd_1316456 := by exact prefixLift 1316456
  have htrace : WordTrace (prefixWord ++ tailWord_1316456) baseStart_1316456 baseEnd_1316456 := by
    simpa [prefixWord, tailWord_1316456, baseEnd_1316456] using wordTrace_append hprefix tailTrace_1316456
  have hstable : (prefixWord ++ tailWord_1316456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316456).length < 2 ^ (prefixWord ++ tailWord_1316456).sum := by decide
  have hdescent : baseEnd_1316456 < baseStart_1316456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316510 : List Nat := [4, 3, 1, 1, 1, 3, 2, 1, 3, 4]
def baseStart_1316510 : Nat := 118140960795 + 1316510 * 2 ^ 59
def prefixEnd_1316510 : Nat := 4983230072969 + 3 ^ 40 * 1316510 * 2
def baseEnd_1316510 : Nat := 225334138816916460756829

theorem tailTrace_1316510 : CollatzResearch.WordTrace tailWord_1316510 prefixEnd_1316510 225334138816916460756829 := by
  unfold tailWord_1316510
  simp only [CollatzResearch.WordTrace]
  refine ⟨6002133057564573356565373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32011376307011057901681989 6002133057564573356565373)
  ·
    refine ⟨2250799896586715008712015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6002133057564573356565373 2250799896586715008712015)
    ·
      refine ⟨3376199844880072513068023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2250799896586715008712015 3376199844880072513068023)
      ·
        refine ⟨5064299767320108769602035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3376199844880072513068023 5064299767320108769602035)
        ·
          refine ⟨7596449650980163154403053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5064299767320108769602035 7596449650980163154403053)
          ·
            refine ⟨2848668619117561182901145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7596449650980163154403053 2848668619117561182901145)
            ·
              refine ⟨2136501464338170887175859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2848668619117561182901145 2136501464338170887175859)
              ·
                refine ⟨3204752196507256330763789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2136501464338170887175859 3204752196507256330763789)
                ·
                  refine ⟨1201782073690221124036421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3204752196507256330763789 1201782073690221124036421)
                  ·
                    refine ⟨225334138816916460756829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1201782073690221124036421 225334138816916460756829)
                    ·
                      rfl

theorem cell23_1316510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_1316510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316510 prefixEnd_1316510 := by exact prefixLift 1316510
  have htrace : WordTrace (prefixWord ++ tailWord_1316510) baseStart_1316510 baseEnd_1316510 := by
    simpa [prefixWord, tailWord_1316510, baseEnd_1316510] using wordTrace_append hprefix tailTrace_1316510
  have hstable : (prefixWord ++ tailWord_1316510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316510).length < 2 ^ (prefixWord ++ tailWord_1316510).sum := by decide
  have hdescent : baseEnd_1316510 < baseStart_1316510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316539 : List Nat := [1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 4]
def baseStart_1316539 : Nat := 118140960795 + 1316539 * 2 ^ 59
def prefixEnd_1316539 : Nat := 4983230072969 + 3 ^ 40 * 1316539 * 2
def baseEnd_1316539 : Nat := 676017307389729768807853

theorem tailTrace_1316539 : CollatzResearch.WordTrace tailWord_1316539 prefixEnd_1316539 676017307389729768807853 := by
  unfold tailWord_1316539
  simp only [CollatzResearch.WordTrace]
  refine ⟨48018122177411524805328671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32012081451607683203552447 48018122177411524805328671)
  ·
    refine ⟨72027183266117287207993007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48018122177411524805328671 72027183266117287207993007)
    ·
      refine ⟨108040774899175930811989511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72027183266117287207993007 108040774899175930811989511)
      ·
        refine ⟨162061162348763896217984267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108040774899175930811989511 162061162348763896217984267)
        ·
          refine ⟨243091743523145844326976401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162061162348763896217984267 243091743523145844326976401)
          ·
            refine ⟨182318807642359383245232301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243091743523145844326976401 182318807642359383245232301)
            ·
              refine ⟨68369552865884768716962113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182318807642359383245232301 68369552865884768716962113)
              ·
                refine ⟨51277164649413576537721585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68369552865884768716962113 51277164649413576537721585)
                ·
                  refine ⟨38457873487060182403291189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51277164649413576537721585 38457873487060182403291189)
                  ·
                    refine ⟨3605425639411892100308549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 38457873487060182403291189 3605425639411892100308549)
                    ·
                      refine ⟨676017307389729768807853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3605425639411892100308549 676017307389729768807853)
                      ·
                        rfl

theorem cell23_1316539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 5, 4].length) (baseStart_1316539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316539 prefixEnd_1316539 := by exact prefixLift 1316539
  have htrace : WordTrace (prefixWord ++ tailWord_1316539) baseStart_1316539 baseEnd_1316539 := by
    simpa [prefixWord, tailWord_1316539, baseEnd_1316539] using wordTrace_append hprefix tailTrace_1316539
  have hstable : (prefixWord ++ tailWord_1316539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316539).length < 2 ^ (prefixWord ++ tailWord_1316539).sum := by decide
  have hdescent : baseEnd_1316539 < baseStart_1316539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316543 : List Nat := [1, 1, 2, 2, 2, 3, 2, 3, 2, 3, 2]
def baseStart_1316543 : Nat := 118140960795 + 1316543 * 2 ^ 59
def prefixEnd_1316543 : Nat := 4983230072969 + 3 ^ 40 * 1316543 * 2
def baseEnd_1316543 : Nat := 676019361312347753157835

theorem tailTrace_1316543 : CollatzResearch.WordTrace tailWord_1316543 prefixEnd_1316543 676019361312347753157835 := by
  unfold tailWord_1316543
  simp only [CollatzResearch.WordTrace]
  refine ⟨48018268069397033488474283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32012178712931355658982855 48018268069397033488474283)
  ·
    refine ⟨72027402104095550232711425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48018268069397033488474283 72027402104095550232711425)
    ·
      refine ⟨54020551578071662674533569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72027402104095550232711425 54020551578071662674533569)
      ·
        refine ⟨40515413683553747005900177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54020551578071662674533569 40515413683553747005900177)
        ·
          refine ⟨30386560262665310254425133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40515413683553747005900177 30386560262665310254425133)
          ·
            refine ⟨11394960098499491345409425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30386560262665310254425133 11394960098499491345409425)
            ·
              refine ⟨8546220073874618509057069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11394960098499491345409425 8546220073874618509057069)
              ·
                refine ⟨3204832527702981940896401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8546220073874618509057069 3204832527702981940896401)
                ·
                  refine ⟨2403624395777236455672301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3204832527702981940896401 2403624395777236455672301)
                  ·
                    refine ⟨901359148416463670877113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2403624395777236455672301 901359148416463670877113)
                    ·
                      refine ⟨676019361312347753157835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 901359148416463670877113 676019361312347753157835)
                      ·
                        rfl

theorem cell23_1316543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 2, 3, 2].length) (baseStart_1316543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316543 prefixEnd_1316543 := by exact prefixLift 1316543
  have htrace : WordTrace (prefixWord ++ tailWord_1316543) baseStart_1316543 baseEnd_1316543 := by
    simpa [prefixWord, tailWord_1316543, baseEnd_1316543] using wordTrace_append hprefix tailTrace_1316543
  have hstable : (prefixWord ++ tailWord_1316543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316543).length < 2 ^ (prefixWord ++ tailWord_1316543).sum := by decide
  have hdescent : baseEnd_1316543 < baseStart_1316543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316567 : List Nat := [1, 1, 3, 2, 1, 3, 5, 2, 1, 1, 3]
def baseStart_1316567 : Nat := 118140960795 + 1316567 * 2 ^ 59
def prefixEnd_1316567 : Nat := 4983230072969 + 3 ^ 40 * 1316567 * 2
def baseEnd_1316567 : Nat := 676031684848055659257725

theorem tailTrace_1316567 : CollatzResearch.WordTrace tailWord_1316567 prefixEnd_1316567 676031684848055659257725 := by
  unfold tailWord_1316567
  simp only [CollatzResearch.WordTrace]
  refine ⟨48019143421310085587347955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32012762280873390391565303 48019143421310085587347955)
  ·
    refine ⟨72028715131965128381021933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48019143421310085587347955 72028715131965128381021933)
    ·
      refine ⟨27010768174486923142883225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72028715131965128381021933 27010768174486923142883225)
      ·
        refine ⟨20258076130865192357162419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27010768174486923142883225 20258076130865192357162419)
        ·
          refine ⟨30387114196297788535743629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20258076130865192357162419 30387114196297788535743629)
          ·
            refine ⟨11395167823611670700903861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30387114196297788535743629 11395167823611670700903861)
            ·
              refine ⟨1068296983463594128209737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11395167823611670700903861 1068296983463594128209737)
              ·
                refine ⟨801222737597695596157303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1068296983463594128209737 801222737597695596157303)
                ·
                  refine ⟨1201834106396543394235955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 801222737597695596157303 1201834106396543394235955)
                  ·
                    refine ⟨1802751159594815091353933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1201834106396543394235955 1802751159594815091353933)
                    ·
                      refine ⟨676031684848055659257725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1802751159594815091353933 676031684848055659257725)
                      ·
                        rfl

theorem cell23_1316567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 5, 2, 1, 1, 3].length) (baseStart_1316567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316567 prefixEnd_1316567 := by exact prefixLift 1316567
  have htrace : WordTrace (prefixWord ++ tailWord_1316567) baseStart_1316567 baseEnd_1316567 := by
    simpa [prefixWord, tailWord_1316567, baseEnd_1316567] using wordTrace_append hprefix tailTrace_1316567
  have hstable : (prefixWord ++ tailWord_1316567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316567).length < 2 ^ (prefixWord ++ tailWord_1316567).sum := by decide
  have hdescent : baseEnd_1316567 < baseStart_1316567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316576 : List Nat := [2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 5]
def baseStart_1316576 : Nat := 118140960795 + 1316576 * 2 ^ 59
def prefixEnd_1316576 : Nat := 4983230072969 + 3 ^ 40 * 1316576 * 2
def baseEnd_1316576 : Nat := 676036306173946124045183

theorem tailTrace_1316576 : CollatzResearch.WordTrace tailWord_1316576 prefixEnd_1316576 676036306173946124045183 := by
  unfold tailWord_1316576
  simp only [CollatzResearch.WordTrace]
  refine ⟨24009735839138740062212791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32012981118851653416283721 24009735839138740062212791)
  ·
    refine ⟨36014603758708110093319187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24009735839138740062212791 36014603758708110093319187)
    ·
      refine ⟨54021905638062165139978781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36014603758708110093319187 54021905638062165139978781)
      ·
        refine ⟨20258214614273311927492043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54021905638062165139978781 20258214614273311927492043)
        ·
          refine ⟨30387321921409967891238065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20258214614273311927492043 30387321921409967891238065)
          ·
            refine ⟨22790491441057475918428549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30387321921409967891238065 22790491441057475918428549)
            ·
              refine ⟨4273217145198276734705353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22790491441057475918428549 4273217145198276734705353)
              ·
                refine ⟨3204912858898707551029015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4273217145198276734705353 3204912858898707551029015)
                ·
                  refine ⟨4807369288348061326543523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3204912858898707551029015 4807369288348061326543523)
                  ·
                    refine ⟨7211053932522091989815285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4807369288348061326543523 7211053932522091989815285)
                    ·
                      refine ⟨676036306173946124045183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7211053932522091989815285 676036306173946124045183)
                      ·
                        rfl

theorem cell23_1316576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_1316576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316576 prefixEnd_1316576 := by exact prefixLift 1316576
  have htrace : WordTrace (prefixWord ++ tailWord_1316576) baseStart_1316576 baseEnd_1316576 := by
    simpa [prefixWord, tailWord_1316576, baseEnd_1316576] using wordTrace_append hprefix tailTrace_1316576
  have hstable : (prefixWord ++ tailWord_1316576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316576).length < 2 ^ (prefixWord ++ tailWord_1316576).sum := by decide
  have hdescent : baseEnd_1316576 < baseStart_1316576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316586 : List Nat := [3, 1, 3, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_1316586 : Nat := 118140960795 + 1316586 * 2 ^ 59
def prefixEnd_1316586 : Nat := 4983230072969 + 3 ^ 40 * 1316586 * 2
def baseEnd_1316586 : Nat := 676041440980491084920137

theorem tailTrace_1316586 : CollatzResearch.WordTrace tailWord_1316586 prefixEnd_1316586 676041440980491084920137 := by
  unfold tailWord_1316586
  simp only [CollatzResearch.WordTrace]
  refine ⟨12004959102060312958072403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32013224272160834554859741 12004959102060312958072403)
  ·
    refine ⟨18007438653090469437108605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12004959102060312958072403 18007438653090469437108605)
    ·
      refine ⟨6752789494908926038915727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18007438653090469437108605 6752789494908926038915727)
      ·
        refine ⟨10129184242363389058373591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6752789494908926038915727 10129184242363389058373591)
        ·
          refine ⟨15193776363545083587560387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10129184242363389058373591 15193776363545083587560387)
          ·
            refine ⟨22790664545317625381340581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15193776363545083587560387 22790664545317625381340581)
            ·
              refine ⟨4273249602247054759001359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22790664545317625381340581 4273249602247054759001359)
              ·
                refine ⟨6409874403370582138502039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4273249602247054759001359 6409874403370582138502039)
                ·
                  refine ⟨9614811605055873207753059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6409874403370582138502039 9614811605055873207753059)
                  ·
                    refine ⟨14422217407583809811629589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9614811605055873207753059 14422217407583809811629589)
                    ·
                      refine ⟨676041440980491084920137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14422217407583809811629589 676041440980491084920137)
                      ·
                        rfl

theorem cell23_1316586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_1316586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316586 prefixEnd_1316586 := by exact prefixLift 1316586
  have htrace : WordTrace (prefixWord ++ tailWord_1316586) baseStart_1316586 baseEnd_1316586 := by
    simpa [prefixWord, tailWord_1316586, baseEnd_1316586] using wordTrace_append hprefix tailTrace_1316586
  have hstable : (prefixWord ++ tailWord_1316586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316586).length < 2 ^ (prefixWord ++ tailWord_1316586).sum := by decide
  have hdescent : baseEnd_1316586 < baseStart_1316586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316590 : List Nat := [4, 1, 2, 1, 1, 2, 2, 1, 5, 2, 2]
def baseStart_1316590 : Nat := 118140960795 + 1316590 * 2 ^ 59
def prefixEnd_1316590 : Nat := 4983230072969 + 3 ^ 40 * 1316590 * 2
def baseEnd_1316590 : Nat := 676043494903109069270119

theorem tailTrace_1316590 : CollatzResearch.WordTrace tailWord_1316590 prefixEnd_1316590 676043494903109069270119 := by
  unfold tailWord_1316590
  simp only [CollatzResearch.WordTrace]
  refine ⟨6002497787528345064429403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32013321533484507010290149 6002497787528345064429403)
  ·
    refine ⟨9003746681292517596644105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6002497787528345064429403 9003746681292517596644105)
    ·
      refine ⟨6752810010969388197483079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9003746681292517596644105 6752810010969388197483079)
      ·
        refine ⟨10129215016454082296224619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6752810010969388197483079 10129215016454082296224619)
        ·
          refine ⟨15193822524681123444336929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10129215016454082296224619 15193822524681123444336929)
          ·
            refine ⟨11395366893510842583252697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15193822524681123444336929 11395366893510842583252697)
            ·
              refine ⟨8546525170133131937439523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11395366893510842583252697 8546525170133131937439523)
              ·
                refine ⟨12819787755199697906159285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8546525170133131937439523 12819787755199697906159285)
                ·
                  refine ⟨1201855102049971678702433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12819787755199697906159285 1201855102049971678702433)
                  ·
                    refine ⟨901391326537478759026825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1201855102049971678702433 901391326537478759026825)
                    ·
                      refine ⟨676043494903109069270119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 901391326537478759026825 676043494903109069270119)
                      ·
                        rfl

theorem cell23_1316590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 2, 1, 5, 2, 2].length) (baseStart_1316590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316590 prefixEnd_1316590 := by exact prefixLift 1316590
  have htrace : WordTrace (prefixWord ++ tailWord_1316590) baseStart_1316590 baseEnd_1316590 := by
    simpa [prefixWord, tailWord_1316590, baseEnd_1316590] using wordTrace_append hprefix tailTrace_1316590
  have hstable : (prefixWord ++ tailWord_1316590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316590).length < 2 ^ (prefixWord ++ tailWord_1316590).sum := by decide
  have hdescent : baseEnd_1316590 < baseStart_1316590 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316593 : List Nat := [1, 2, 2, 2, 2, 4, 1, 1, 3, 2, 3]
def baseStart_1316593 : Nat := 118140960795 + 1316593 * 2 ^ 59
def prefixEnd_1316593 : Nat := 4983230072969 + 3 ^ 40 * 1316593 * 2
def baseEnd_1316593 : Nat := 676045035345072557532605

theorem tailTrace_1316593 : CollatzResearch.WordTrace tailWord_1316593 prefixEnd_1316593 676045035345072557532605 := by
  unfold tailWord_1316593
  simp only [CollatzResearch.WordTrace]
  refine ⟨48020091719215892027794433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32013394479477261351862955 48020091719215892027794433)
  ·
    refine ⟨36015068789411919020845825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48020091719215892027794433 36015068789411919020845825)
    ·
      refine ⟨27011301592058939265634369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36015068789411919020845825 27011301592058939265634369)
      ·
        refine ⟨20258476194044204449225777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27011301592058939265634369 20258476194044204449225777)
        ·
          refine ⟨15193857145533153336919333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20258476194044204449225777 15193857145533153336919333)
          ·
            refine ⟨2848848214787466250672375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15193857145533153336919333 2848848214787466250672375)
            ·
              refine ⟨4273272322181199376008563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2848848214787466250672375 4273272322181199376008563)
              ·
                refine ⟨6409908483271799064012845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4273272322181199376008563 6409908483271799064012845)
                ·
                  refine ⟨2403715681226924649004817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6409908483271799064012845 2403715681226924649004817)
                  ·
                    refine ⟨1802786760920193486753613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2403715681226924649004817 1802786760920193486753613)
                    ·
                      refine ⟨676045035345072557532605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1802786760920193486753613 676045035345072557532605)
                      ·
                        rfl

theorem cell23_1316593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 1, 3, 2, 3].length) (baseStart_1316593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316593 prefixEnd_1316593 := by exact prefixLift 1316593
  have htrace : WordTrace (prefixWord ++ tailWord_1316593) baseStart_1316593 baseEnd_1316593 := by
    simpa [prefixWord, tailWord_1316593, baseEnd_1316593] using wordTrace_append hprefix tailTrace_1316593
  have hstable : (prefixWord ++ tailWord_1316593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316593).length < 2 ^ (prefixWord ++ tailWord_1316593).sum := by decide
  have hdescent : baseEnd_1316593 < baseStart_1316593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316640 : List Nat := [2, 1, 1, 5, 1, 1, 1, 5, 2, 1, 3]
def baseStart_1316640 : Nat := 118140960795 + 1316640 * 2 ^ 59
def prefixEnd_1316640 : Nat := 4983230072969 + 3 ^ 40 * 1316640 * 2
def baseEnd_1316640 : Nat := 676069168935833873644889

theorem tailTrace_1316640 : CollatzResearch.WordTrace tailWord_1316640 prefixEnd_1316640 676069168935833873644889 := by
  unfold tailWord_1316640
  simp only [CollatzResearch.WordTrace]
  refine ⟨24010902975022809527377687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32014537300030412703170249 24010902975022809527377687)
  ·
    refine ⟨36016354462534214291066531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24010902975022809527377687 36016354462534214291066531)
    ·
      refine ⟨54024531693801321436599797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36016354462534214291066531 54024531693801321436599797)
      ·
        refine ⟨5064799846293873884681231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54024531693801321436599797 5064799846293873884681231)
        ·
          refine ⟨7597199769440810827021847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5064799846293873884681231 7597199769440810827021847)
          ·
            refine ⟨11395799654161216240532771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7597199769440810827021847 11395799654161216240532771)
            ·
              refine ⟨17093699481241824360799157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11395799654161216240532771 17093699481241824360799157)
              ·
                refine ⟨1602534326366421033824921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 17093699481241824360799157 1602534326366421033824921)
                ·
                  refine ⟨1201900744774815775368691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1602534326366421033824921 1201900744774815775368691)
                  ·
                    refine ⟨1802851117162223663053037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1201900744774815775368691 1802851117162223663053037)
                    ·
                      refine ⟨676069168935833873644889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1802851117162223663053037 676069168935833873644889)
                      ·
                        rfl

theorem cell23_1316640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_1316640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316640 prefixEnd_1316640 := by exact prefixLift 1316640
  have htrace : WordTrace (prefixWord ++ tailWord_1316640) baseStart_1316640 baseEnd_1316640 := by
    simpa [prefixWord, tailWord_1316640, baseEnd_1316640] using wordTrace_append hprefix tailTrace_1316640
  have hstable : (prefixWord ++ tailWord_1316640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316640).length < 2 ^ (prefixWord ++ tailWord_1316640).sum := by decide
  have hdescent : baseEnd_1316640 < baseStart_1316640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316663 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 3, 4, 2]
def baseStart_1316663 : Nat := 118140960795 + 1316663 * 2 ^ 59
def prefixEnd_1316663 : Nat := 4983230072969 + 3 ^ 40 * 1316663 * 2
def baseEnd_1316663 : Nat := 676080978990887283657283

theorem tailTrace_1316663 : CollatzResearch.WordTrace tailWord_1316663 prefixEnd_1316663 676080978990887283657283 := by
  unfold tailWord_1316663
  simp only [CollatzResearch.WordTrace]
  refine ⟨48022644828962293982842643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32015096552641529321895095 48022644828962293982842643)
  ·
    refine ⟨72033967243443440974263965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48022644828962293982842643 72033967243443440974263965)
    ·
      refine ⟨27012737716291290365348987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72033967243443440974263965 27012737716291290365348987)
      ·
        refine ⟨40519106574436935548023481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27012737716291290365348987 40519106574436935548023481)
        ·
          refine ⟨30389329930827701661017611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40519106574436935548023481 30389329930827701661017611)
          ·
            refine ⟨45583994896241552491526417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30389329930827701661017611 45583994896241552491526417)
            ·
              refine ⟨34187996172181164368644813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45583994896241552491526417 34187996172181164368644813)
              ·
                refine ⟨12820498564567936638241805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34187996172181164368644813 12820498564567936638241805)
                ·
                  refine ⟨4807686961712976239340677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12820498564567936638241805 4807686961712976239340677)
                  ·
                    refine ⟨901441305321183044876377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4807686961712976239340677 901441305321183044876377)
                    ·
                      refine ⟨676080978990887283657283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 901441305321183044876377 676080978990887283657283)
                      ·
                        rfl

theorem cell23_1316663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 3, 4, 2].length) (baseStart_1316663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316663 prefixEnd_1316663 := by exact prefixLift 1316663
  have htrace : WordTrace (prefixWord ++ tailWord_1316663) baseStart_1316663 baseEnd_1316663 := by
    simpa [prefixWord, tailWord_1316663, baseEnd_1316663] using wordTrace_append hprefix tailTrace_1316663
  have hstable : (prefixWord ++ tailWord_1316663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316663).length < 2 ^ (prefixWord ++ tailWord_1316663).sum := by decide
  have hdescent : baseEnd_1316663 < baseStart_1316663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316693 : List Nat := [1, 3, 2, 2, 2, 2, 2, 1, 2, 2, 4]
def baseStart_1316693 : Nat := 118140960795 + 1316693 * 2 ^ 59
def prefixEnd_1316693 : Nat := 4983230072969 + 3 ^ 40 * 1316693 * 2
def baseEnd_1316693 : Nat := 676096383410522166282145

theorem tailTrace_1316693 : CollatzResearch.WordTrace tailWord_1316693 prefixEnd_1316693 676096383410522166282145 := by
  unfold tailWord_1316693
  simp only [CollatzResearch.WordTrace]
  refine ⟨48023739018853609106434733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32015826012569072737623155 48023739018853609106434733)
  ·
    refine ⟨18008902132070103414913025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48023739018853609106434733 18008902132070103414913025)
    ·
      refine ⟨13506676599052577561184769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18008902132070103414913025 13506676599052577561184769)
      ·
        refine ⟨10130007449289433170888577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13506676599052577561184769 10130007449289433170888577)
        ·
          refine ⟨7597505586967074878166433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10130007449289433170888577 7597505586967074878166433)
          ·
            refine ⟨5698129190225306158624825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7597505586967074878166433 5698129190225306158624825)
            ·
              refine ⟨4273596892668979618968619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5698129190225306158624825 4273596892668979618968619)
              ·
                refine ⟨6410395339003469428452929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4273596892668979618968619 6410395339003469428452929)
                ·
                  refine ⟨4807796504252602071339697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6410395339003469428452929 4807796504252602071339697)
                  ·
                    refine ⟨3605847378189451553504773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4807796504252602071339697 3605847378189451553504773)
                    ·
                      refine ⟨676096383410522166282145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3605847378189451553504773 676096383410522166282145)
                      ·
                        rfl

theorem cell23_1316693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_1316693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316693 prefixEnd_1316693 := by exact prefixLift 1316693
  have htrace : WordTrace (prefixWord ++ tailWord_1316693) baseStart_1316693 baseEnd_1316693 := by
    simpa [prefixWord, tailWord_1316693, baseEnd_1316693] using wordTrace_append hprefix tailTrace_1316693
  have hstable : (prefixWord ++ tailWord_1316693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316693).length < 2 ^ (prefixWord ++ tailWord_1316693).sum := by decide
  have hdescent : baseEnd_1316693 < baseStart_1316693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316723 : List Nat := [1, 1, 1, 2, 2, 1, 3, 2, 1, 7, 2]
def baseStart_1316723 : Nat := 118140960795 + 1316723 * 2 ^ 59
def prefixEnd_1316723 : Nat := 4983230072969 + 3 ^ 40 * 1316723 * 2
def baseEnd_1316723 : Nat := 676111787830157048907007

theorem tailTrace_1316723 : CollatzResearch.WordTrace tailWord_1316723 prefixEnd_1316723 676111787830157048907007 := by
  unfold tailWord_1316723
  simp only [CollatzResearch.WordTrace]
  refine ⟨48024833208744924230026823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32016555472496616153351215 48024833208744924230026823)
  ·
    refine ⟨72037249813117386345040235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48024833208744924230026823 72037249813117386345040235)
    ·
      refine ⟨108055874719676079517560353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72037249813117386345040235 108055874719676079517560353)
      ·
        refine ⟨81041906039757059638170265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108055874719676079517560353 81041906039757059638170265)
        ·
          refine ⟨60781429529817794728627699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81041906039757059638170265 60781429529817794728627699)
          ·
            refine ⟨91172144294726692092941549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60781429529817794728627699 91172144294726692092941549)
            ·
              refine ⟨34189554110522509534853081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91172144294726692092941549 34189554110522509534853081)
              ·
                refine ⟨25642165582891882151139811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 34189554110522509534853081 25642165582891882151139811)
                ·
                  refine ⟨38463248374337823226709717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 25642165582891882151139811 38463248374337823226709717)
                  ·
                    refine ⟨901482383773542731876009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 38463248374337823226709717 901482383773542731876009)
                    ·
                      refine ⟨676111787830157048907007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 901482383773542731876009 676111787830157048907007)
                      ·
                        rfl

theorem cell23_1316723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 2, 1, 7, 2].length) (baseStart_1316723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316723 prefixEnd_1316723 := by exact prefixLift 1316723
  have htrace : WordTrace (prefixWord ++ tailWord_1316723) baseStart_1316723 baseEnd_1316723 := by
    simpa [prefixWord, tailWord_1316723, baseEnd_1316723] using wordTrace_append hprefix tailTrace_1316723
  have hstable : (prefixWord ++ tailWord_1316723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316723).length < 2 ^ (prefixWord ++ tailWord_1316723).sum := by decide
  have hdescent : baseEnd_1316723 < baseStart_1316723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316737 : List Nat := [1, 2, 4, 4, 1, 2, 1, 1, 7]
def baseStart_1316737 : Nat := 118140960795 + 1316737 * 2 ^ 59
def prefixEnd_1316737 : Nat := 4983230072969 + 3 ^ 40 * 1316737 * 2
def baseEnd_1316737 : Nat := 75124330728813332681327

theorem tailTrace_1316737 : CollatzResearch.WordTrace tailWord_1316737 prefixEnd_1316737 75124330728813332681327 := by
  unfold tailWord_1316737
  simp only [CollatzResearch.WordTrace]
  refine ⟨48025343830694204621036465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32016895887129469747357643 48025343830694204621036465)
  ·
    refine ⟨36019007873020653465777349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48025343830694204621036465 36019007873020653465777349)
    ·
      refine ⟨6753563976191372524833253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36019007873020653465777349 6753563976191372524833253)
      ·
        refine ⟨1266293245535882348406235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6753563976191372524833253 1266293245535882348406235)
        ·
          refine ⟨1899439868303823522609353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1266293245535882348406235 1899439868303823522609353)
          ·
            refine ⟨1424579901227867641957015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1899439868303823522609353 1424579901227867641957015)
            ·
              refine ⟨2136869851841801462935523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1424579901227867641957015 2136869851841801462935523)
              ·
                refine ⟨3205304777762702194403285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2136869851841801462935523 3205304777762702194403285)
                ·
                  refine ⟨75124330728813332681327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3205304777762702194403285 75124330728813332681327)
                  ·
                    rfl

theorem cell23_1316737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 7].length) (baseStart_1316737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316737 prefixEnd_1316737 := by exact prefixLift 1316737
  have htrace : WordTrace (prefixWord ++ tailWord_1316737) baseStart_1316737 baseEnd_1316737 := by
    simpa [prefixWord, tailWord_1316737, baseEnd_1316737] using wordTrace_append hprefix tailTrace_1316737
  have hstable : (prefixWord ++ tailWord_1316737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316737).length < 2 ^ (prefixWord ++ tailWord_1316737).sum := by decide
  have hdescent : baseEnd_1316737 < baseStart_1316737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316773 : List Nat := [1, 3, 1, 2, 1, 1, 1, 5, 1, 4, 3]
def baseStart_1316773 : Nat := 118140960795 + 1316773 * 2 ^ 59
def prefixEnd_1316773 : Nat := 4983230072969 + 3 ^ 40 * 1316773 * 2
def baseEnd_1316773 : Nat := 676137461862881853281777

theorem tailTrace_1316773 : CollatzResearch.WordTrace tailWord_1316773 prefixEnd_1316773 676137461862881853281777 := by
  unfold tailWord_1316773
  simp only [CollatzResearch.WordTrace]
  refine ⟨48026656858563782769346973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32017771239042521846231315 48026656858563782769346973)
  ·
    refine ⟨18009996321961418538505115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48026656858563782769346973 18009996321961418538505115)
    ·
      refine ⟨27014994482942127807757673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18009996321961418538505115 27014994482942127807757673)
      ·
        refine ⟨20261245862206595855818255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27014994482942127807757673 20261245862206595855818255)
        ·
          refine ⟨30391868793309893783727383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20261245862206595855818255 30391868793309893783727383)
          ·
            refine ⟨45587803189964840675591075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30391868793309893783727383 45587803189964840675591075)
            ·
              refine ⟨68381704784947261013386613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45587803189964840675591075 68381704784947261013386613)
              ·
                refine ⟨6410784823588805720004995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68381704784947261013386613 6410784823588805720004995)
                ·
                  refine ⟨9616177235383208580007493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6410784823588805720004995 9616177235383208580007493)
                  ·
                    refine ⟨1803033231634351608751405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9616177235383208580007493 1803033231634351608751405)
                    ·
                      refine ⟨676137461862881853281777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1803033231634351608751405 676137461862881853281777)
                      ·
                        rfl

theorem cell23_1316773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_1316773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316773 prefixEnd_1316773 := by exact prefixLift 1316773
  have htrace : WordTrace (prefixWord ++ tailWord_1316773) baseStart_1316773 baseEnd_1316773 := by
    simpa [prefixWord, tailWord_1316773, baseEnd_1316773] using wordTrace_append hprefix tailTrace_1316773
  have hstable : (prefixWord ++ tailWord_1316773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316773).length < 2 ^ (prefixWord ++ tailWord_1316773).sum := by decide
  have hdescent : baseEnd_1316773 < baseStart_1316773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316788 : List Nat := [2, 5, 2, 1, 3, 1, 2, 2, 5]
def baseStart_1316788 : Nat := 118140960795 + 1316788 * 2 ^ 59
def prefixEnd_1316788 : Nat := 4983230072969 + 3 ^ 40 * 1316788 * 2
def baseEnd_1316788 : Nat := 75127240452522143843801

theorem tailTrace_1316788 : CollatzResearch.WordTrace tailWord_1316788 prefixEnd_1316788 75127240452522143843801 := by
  unfold tailWord_1316788
  simp only [CollatzResearch.WordTrace]
  refine ⟨24013601976754720165571509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32018135969006293554095345 24013601976754720165571509)
  ·
    refine ⟨2251275185320755015522329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 24013601976754720165571509 2251275185320755015522329)
    ·
      refine ⟨1688456388990566261641747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2251275185320755015522329 1688456388990566261641747)
      ·
        refine ⟨2532684583485849392462621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1688456388990566261641747 2532684583485849392462621)
        ·
          refine ⟨949756718807193522173483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2532684583485849392462621 949756718807193522173483)
          ·
            refine ⟨1424635078210790283260225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 949756718807193522173483 1424635078210790283260225)
            ·
              refine ⟨1068476308658092712445169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1424635078210790283260225 1068476308658092712445169)
              ·
                refine ⟨801357231493569534333877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1068476308658092712445169 801357231493569534333877)
                ·
                  refine ⟨75127240452522143843801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 801357231493569534333877 75127240452522143843801)
                  ·
                    rfl

theorem cell23_1316788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_1316788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316788 prefixEnd_1316788 := by exact prefixLift 1316788
  have htrace : WordTrace (prefixWord ++ tailWord_1316788) baseStart_1316788 baseEnd_1316788 := by
    simpa [prefixWord, tailWord_1316788, baseEnd_1316788] using wordTrace_append hprefix tailTrace_1316788
  have hstable : (prefixWord ++ tailWord_1316788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316788).length < 2 ^ (prefixWord ++ tailWord_1316788).sum := by decide
  have hdescent : baseEnd_1316788 < baseStart_1316788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316823 : List Nat := [1, 1, 3, 2, 1, 1, 3, 3, 3, 5]
def baseStart_1316823 : Nat := 118140960795 + 1316823 * 2 ^ 59
def prefixEnd_1316823 : Nat := 4983230072969 + 3 ^ 40 * 1316823 * 2
def baseEnd_1316823 : Nat := 225387711965202219218849

theorem tailTrace_1316823 : CollatzResearch.WordTrace tailWord_1316823 prefixEnd_1316823 225387711965202219218849 := by
  unfold tailWord_1316823
  simp only [CollatzResearch.WordTrace]
  refine ⟨48028480508382641308667123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32018987005588427539111415 48028480508382641308667123)
  ·
    refine ⟨72042720762573961963000685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48028480508382641308667123 72042720762573961963000685)
    ·
      refine ⟨27016020285965235736125257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72042720762573961963000685 27016020285965235736125257)
      ·
        refine ⟨20262015214473926802093943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27016020285965235736125257 20262015214473926802093943)
        ·
          refine ⟨30393022821710890203140915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20262015214473926802093943 30393022821710890203140915)
          ·
            refine ⟨45589534232566335304711373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30393022821710890203140915 45589534232566335304711373)
            ·
              refine ⟨17096075337212375739266765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45589534232566335304711373 17096075337212375739266765)
              ·
                refine ⟨6411028251454640902225037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17096075337212375739266765 6411028251454640902225037)
                ·
                  refine ⟨2404135594295490338334389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6411028251454640902225037 2404135594295490338334389)
                  ·
                    refine ⟨225387711965202219218849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2404135594295490338334389 225387711965202219218849)
                    ·
                      rfl

theorem cell23_1316823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 3, 3, 3, 5].length) (baseStart_1316823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316823 prefixEnd_1316823 := by exact prefixLift 1316823
  have htrace : WordTrace (prefixWord ++ tailWord_1316823) baseStart_1316823 baseEnd_1316823 := by
    simpa [prefixWord, tailWord_1316823, baseEnd_1316823] using wordTrace_append hprefix tailTrace_1316823
  have hstable : (prefixWord ++ tailWord_1316823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316823).length < 2 ^ (prefixWord ++ tailWord_1316823).sum := by decide
  have hdescent : baseEnd_1316823 < baseStart_1316823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316897 : List Nat := [1, 2, 3, 2, 4, 1, 2, 1, 1, 1, 5]
def baseStart_1316897 : Nat := 118140960795 + 1316897 * 2 ^ 59
def prefixEnd_1316897 : Nat := 4983230072969 + 3 ^ 40 * 1316897 * 2
def baseEnd_1316897 : Nat := 676201133464039368131207

theorem tailTrace_1316897 : CollatzResearch.WordTrace tailWord_1316897 prefixEnd_1316897 676201133464039368131207 := by
  unfold tailWord_1316897
  simp only [CollatzResearch.WordTrace]
  refine ⟨48031179510114551946860945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32020786340076367964573963 48031179510114551946860945)
  ·
    refine ⟨36023384632585913960145709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48031179510114551946860945 36023384632585913960145709)
    ·
      refine ⟨13508769237219717735054641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36023384632585913960145709 13508769237219717735054641)
      ·
        refine ⟨10131576927914788301290981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13508769237219717735054641 10131576927914788301290981)
        ·
          refine ⟨1899670673984022806492059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10131576927914788301290981 1899670673984022806492059)
          ·
            refine ⟨2849506010976034209738089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1899670673984022806492059 2849506010976034209738089)
            ·
              refine ⟨2137129508232025657303567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2849506010976034209738089 2137129508232025657303567)
              ·
                refine ⟨3205694262348038485955351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2137129508232025657303567 3205694262348038485955351)
                ·
                  refine ⟨4808541393522057728933027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3205694262348038485955351 4808541393522057728933027)
                  ·
                    refine ⟨7212812090283086593399541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4808541393522057728933027 7212812090283086593399541)
                    ·
                      refine ⟨676201133464039368131207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7212812090283086593399541 676201133464039368131207)
                      ·
                        rfl

theorem cell23_1316897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_1316897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316897 prefixEnd_1316897 := by exact prefixLift 1316897
  have htrace : WordTrace (prefixWord ++ tailWord_1316897) baseStart_1316897 baseEnd_1316897 := by
    simpa [prefixWord, tailWord_1316897, baseEnd_1316897] using wordTrace_append hprefix tailTrace_1316897
  have hstable : (prefixWord ++ tailWord_1316897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316897).length < 2 ^ (prefixWord ++ tailWord_1316897).sum := by decide
  have hdescent : baseEnd_1316897 < baseStart_1316897 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316921 : List Nat := [1, 2, 1, 5, 3, 2, 2, 1, 2, 4]
def baseStart_1316921 : Nat := 118140960795 + 1316921 * 2 ^ 59
def prefixEnd_1316921 : Nat := 4983230072969 + 3 ^ 40 * 1316921 * 2
def baseEnd_1316921 : Nat := 225404485666582424743699

theorem tailTrace_1316921 : CollatzResearch.WordTrace tailWord_1316921 prefixEnd_1316921 225404485666582424743699 := by
  unfold tailWord_1316921
  simp only [CollatzResearch.WordTrace]
  refine ⟨48032054862027604045734617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32021369908018402697156411 48032054862027604045734617)
  ·
    refine ⟨36024041146520703034300963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48032054862027604045734617 36024041146520703034300963)
    ·
      refine ⟨54036061719781054551451445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36024041146520703034300963 54036061719781054551451445)
      ·
        refine ⟨5065880786229473864198573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 54036061719781054551451445 5065880786229473864198573)
        ·
          refine ⟨1899705294836052699074465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5065880786229473864198573 1899705294836052699074465)
          ·
            refine ⟨1424778971127039524305849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1899705294836052699074465 1424778971127039524305849)
            ·
              refine ⟨1068584228345279643229387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1424778971127039524305849 1068584228345279643229387)
              ·
                refine ⟨1602876342517919464844081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1068584228345279643229387 1602876342517919464844081)
                ·
                  refine ⟨1202157256888439598633061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1602876342517919464844081 1202157256888439598633061)
                  ·
                    refine ⟨225404485666582424743699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1202157256888439598633061 225404485666582424743699)
                    ·
                      rfl

theorem cell23_1316921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 2, 1, 2, 4].length) (baseStart_1316921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316921 prefixEnd_1316921 := by exact prefixLift 1316921
  have htrace : WordTrace (prefixWord ++ tailWord_1316921) baseStart_1316921 baseEnd_1316921 := by
    simpa [prefixWord, tailWord_1316921, baseEnd_1316921] using wordTrace_append hprefix tailTrace_1316921
  have hstable : (prefixWord ++ tailWord_1316921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316921).length < 2 ^ (prefixWord ++ tailWord_1316921).sum := by decide
  have hdescent : baseEnd_1316921 < baseStart_1316921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316923 : List Nat := [1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 5]
def baseStart_1316923 : Nat := 118140960795 + 1316923 * 2 ^ 59
def prefixEnd_1316923 : Nat := 4983230072969 + 3 ^ 40 * 1316923 * 2
def baseEnd_1316923 : Nat := 676214483961056266406087

theorem tailTrace_1316923 : CollatzResearch.WordTrace tailWord_1316923 prefixEnd_1316923 676214483961056266406087 := by
  unfold tailWord_1316923
  simp only [CollatzResearch.WordTrace]
  refine ⟨48032127808020358387307423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32021418538680238924871615 48032127808020358387307423)
  ·
    refine ⟨72048191712030537580961135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48032127808020358387307423 72048191712030537580961135)
    ·
      refine ⟨108072287568045806371441703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72048191712030537580961135 108072287568045806371441703)
      ·
        refine ⟨162108431352068709557162555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108072287568045806371441703 162108431352068709557162555)
        ·
          refine ⟨243162647028103064335743833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162108431352068709557162555 243162647028103064335743833)
          ·
            refine ⟨182371985271077298251807875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243162647028103064335743833 182371985271077298251807875)
            ·
              refine ⟨273557977906615947377711813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182371985271077298251807875 273557977906615947377711813)
              ·
                refine ⟨51292120857490490133320965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 273557977906615947377711813 51292120857490490133320965)
                ·
                  refine ⟨9617272660779466899997681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 51292120857490490133320965 9617272660779466899997681)
                  ·
                    refine ⟨7212954495584600174998261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9617272660779466899997681 7212954495584600174998261)
                    ·
                      refine ⟨676214483961056266406087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7212954495584600174998261 676214483961056266406087)
                      ·
                        rfl

theorem cell23_1316923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 4, 4, 2, 5].length) (baseStart_1316923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316923 prefixEnd_1316923 := by exact prefixLift 1316923
  have htrace : WordTrace (prefixWord ++ tailWord_1316923) baseStart_1316923 baseEnd_1316923 := by
    simpa [prefixWord, tailWord_1316923, baseEnd_1316923] using wordTrace_append hprefix tailTrace_1316923
  have hstable : (prefixWord ++ tailWord_1316923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316923).length < 2 ^ (prefixWord ++ tailWord_1316923).sum := by decide
  have hdescent : baseEnd_1316923 < baseStart_1316923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316933 : List Nat := [1, 3, 1, 1, 1, 3, 1, 1, 1, 2, 8]
def baseStart_1316933 : Nat := 118140960795 + 1316933 * 2 ^ 59
def prefixEnd_1316933 : Nat := 4983230072969 + 3 ^ 40 * 1316933 * 2
def baseEnd_1316933 : Nat := 676219618767601227281041

theorem tailTrace_1316933 : CollatzResearch.WordTrace tailWord_1316933 prefixEnd_1316933 676219618767601227281041 := by
  unfold tailWord_1316933
  simp only [CollatzResearch.WordTrace]
  refine ⟨48032492537984130095171453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32021661691989420063447635 48032492537984130095171453)
  ·
    refine ⟨18012184701744048785689295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48032492537984130095171453 18012184701744048785689295)
    ·
      refine ⟨27018277052616073178533943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18012184701744048785689295 27018277052616073178533943)
      ·
        refine ⟨40527415578924109767800915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27018277052616073178533943 40527415578924109767800915)
        ·
          refine ⟨60791123368386164651701373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40527415578924109767800915 60791123368386164651701373)
          ·
            refine ⟨22796671263144811744388015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 60791123368386164651701373 22796671263144811744388015)
            ·
              refine ⟨34195006894717217616582023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22796671263144811744388015 34195006894717217616582023)
              ·
                refine ⟨51292510342075826424873035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34195006894717217616582023 51292510342075826424873035)
                ·
                  refine ⟨76938765513113739637309553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 51292510342075826424873035 76938765513113739637309553)
                  ·
                    refine ⟨57704074134835304727982165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 76938765513113739637309553 57704074134835304727982165)
                    ·
                      refine ⟨676219618767601227281041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 57704074134835304727982165 676219618767601227281041)
                      ·
                        rfl

theorem cell23_1316933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_1316933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316933 prefixEnd_1316933 := by exact prefixLift 1316933
  have htrace : WordTrace (prefixWord ++ tailWord_1316933) baseStart_1316933 baseEnd_1316933 := by
    simpa [prefixWord, tailWord_1316933, baseEnd_1316933] using wordTrace_append hprefix tailTrace_1316933
  have hstable : (prefixWord ++ tailWord_1316933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316933).length < 2 ^ (prefixWord ++ tailWord_1316933).sum := by decide
  have hdescent : baseEnd_1316933 < baseStart_1316933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316937 : List Nat := [1, 2, 1, 1, 2, 2, 5, 1, 3, 3, 2]
def baseStart_1316937 : Nat := 118140960795 + 1316937 * 2 ^ 59
def prefixEnd_1316937 : Nat := 4983230072969 + 3 ^ 40 * 1316937 * 2
def baseEnd_1316937 : Nat := 676221672690219211631023

theorem tailTrace_1316937 : CollatzResearch.WordTrace tailWord_1316937 prefixEnd_1316937 676221672690219211631023 := by
  unfold tailWord_1316937
  simp only [CollatzResearch.WordTrace]
  refine ⟨48032638429969638778317065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32021758953313092518878043 48032638429969638778317065)
  ·
    refine ⟨36024478822477229083737799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48032638429969638778317065 36024478822477229083737799)
    ·
      refine ⟨54036718233715843625606699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36024478822477229083737799 54036718233715843625606699)
      ·
        refine ⟨81055077350573765438410049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54036718233715843625606699 81055077350573765438410049)
        ·
          refine ⟨60791308012930324078807537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81055077350573765438410049 60791308012930324078807537)
          ·
            refine ⟨45593481009697743059105653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60791308012930324078807537 45593481009697743059105653)
            ·
              refine ⟨4274388844659163411791155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45593481009697743059105653 4274388844659163411791155)
              ·
                refine ⟨6411583266988745117686733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4274388844659163411791155 6411583266988745117686733)
                ·
                  refine ⟨2404343725120779419132525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6411583266988745117686733 2404343725120779419132525)
                  ·
                    refine ⟨901628896920292282174697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2404343725120779419132525 901628896920292282174697)
                    ·
                      refine ⟨676221672690219211631023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 901628896920292282174697 676221672690219211631023)
                      ·
                        rfl

theorem cell23_1316937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 1, 3, 3, 2].length) (baseStart_1316937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316937 prefixEnd_1316937 := by exact prefixLift 1316937
  have htrace : WordTrace (prefixWord ++ tailWord_1316937) baseStart_1316937 baseEnd_1316937 := by
    simpa [prefixWord, tailWord_1316937, baseEnd_1316937] using wordTrace_append hprefix tailTrace_1316937
  have hstable : (prefixWord ++ tailWord_1316937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316937).length < 2 ^ (prefixWord ++ tailWord_1316937).sum := by decide
  have hdescent : baseEnd_1316937 < baseStart_1316937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316943 : List Nat := [1, 1, 2, 1, 1, 2, 2, 4, 1, 8]
def baseStart_1316943 : Nat := 118140960795 + 1316943 * 2 ^ 59
def prefixEnd_1316943 : Nat := 4983230072969 + 3 ^ 40 * 1316943 * 2
def baseEnd_1316943 : Nat := 225408251191382062718665

theorem tailTrace_1316943 : CollatzResearch.WordTrace tailWord_1316943 prefixEnd_1316943 225408251191382062718665 := by
  unfold tailWord_1316943
  simp only [CollatzResearch.WordTrace]
  refine ⟨48032857267947901803035483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32021904845298601202023655 48032857267947901803035483)
  ·
    refine ⟨72049285901921852704553225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48032857267947901803035483 72049285901921852704553225)
    ·
      refine ⟨54036964426441389528414919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72049285901921852704553225 54036964426441389528414919)
      ·
        refine ⟨81055446639662084292622379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54036964426441389528414919 81055446639662084292622379)
        ·
          refine ⟨121583169959493126438933569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81055446639662084292622379 121583169959493126438933569)
          ·
            refine ⟨91187377469619844829200177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121583169959493126438933569 91187377469619844829200177)
            ·
              refine ⟨68390533102214883621900133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91187377469619844829200177 68390533102214883621900133)
              ·
                refine ⟨12823224956665290679106275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68390533102214883621900133 12823224956665290679106275)
                ·
                  refine ⟨19234837434997936018659413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12823224956665290679106275 19234837434997936018659413)
                  ·
                    refine ⟨225408251191382062718665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 19234837434997936018659413 225408251191382062718665)
                    ·
                      rfl

theorem cell23_1316943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 1, 8].length) (baseStart_1316943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316943 prefixEnd_1316943 := by exact prefixLift 1316943
  have htrace : WordTrace (prefixWord ++ tailWord_1316943) baseStart_1316943 baseEnd_1316943 := by
    simpa [prefixWord, tailWord_1316943, baseEnd_1316943] using wordTrace_append hprefix tailTrace_1316943
  have hstable : (prefixWord ++ tailWord_1316943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316943).length < 2 ^ (prefixWord ++ tailWord_1316943).sum := by decide
  have hdescent : baseEnd_1316943 < baseStart_1316943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316962 : List Nat := [3, 3, 2, 2, 2, 2, 2, 2, 1, 2, 2]
def baseStart_1316962 : Nat := 118140960795 + 1316962 * 2 ^ 59
def prefixEnd_1316962 : Nat := 4983230072969 + 3 ^ 40 * 1316962 * 2
def baseEnd_1316962 : Nat := 676234509706581613818409

theorem tailTrace_1316962 : CollatzResearch.WordTrace tailWord_1316962 prefixEnd_1316962 676234509706581613818409 := by
  unfold tailWord_1316962
  simp only [CollatzResearch.WordTrace]
  refine ⟨12008387563719767011994285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32022366836586045365318093 12008387563719767011994285)
  ·
    refine ⟨4503145336394912629497857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12008387563719767011994285 4503145336394912629497857)
    ·
      refine ⟨3377359002296184472123393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4503145336394912629497857 3377359002296184472123393)
      ·
        refine ⟨2533019251722138354092545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3377359002296184472123393 2533019251722138354092545)
        ·
          refine ⟨1899764438791603765569409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2533019251722138354092545 1899764438791603765569409)
          ·
            refine ⟨1424823329093702824177057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1899764438791603765569409 1424823329093702824177057)
            ·
              refine ⟨1068617496820277118132793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1424823329093702824177057 1068617496820277118132793)
              ·
                refine ⟨801463122615207838599595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1068617496820277118132793 801463122615207838599595)
                ·
                  refine ⟨1202194683922811757899393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 801463122615207838599595 1202194683922811757899393)
                  ·
                    refine ⟨901646012942108818424545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1202194683922811757899393 901646012942108818424545)
                    ·
                      refine ⟨676234509706581613818409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 901646012942108818424545 676234509706581613818409)
                      ·
                        rfl

theorem cell23_1316962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_1316962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316962 prefixEnd_1316962 := by exact prefixLift 1316962
  have htrace : WordTrace (prefixWord ++ tailWord_1316962) baseStart_1316962 baseEnd_1316962 := by
    simpa [prefixWord, tailWord_1316962, baseEnd_1316962] using wordTrace_append hprefix tailTrace_1316962
  have hstable : (prefixWord ++ tailWord_1316962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316962).length < 2 ^ (prefixWord ++ tailWord_1316962).sum := by decide
  have hdescent : baseEnd_1316962 < baseStart_1316962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1316967 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 3, 4, 2]
def baseStart_1316967 : Nat := 118140960795 + 1316967 * 2 ^ 59
def prefixEnd_1316967 : Nat := 4983230072969 + 3 ^ 40 * 1316967 * 2
def baseEnd_1316967 : Nat := 676237077109854094255885

theorem tailTrace_1316967 : CollatzResearch.WordTrace tailWord_1316967 prefixEnd_1316967 676237077109854094255885 := by
  unfold tailWord_1316967
  simp only [CollatzResearch.WordTrace]
  refine ⟨48033732619860953901909155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32022488413240635934606103 48033732619860953901909155)
  ·
    refine ⟨72050598929791430852863733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48033732619860953901909155 72050598929791430852863733)
    ·
      refine ⟨6754743649667946642455975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72050598929791430852863733 6754743649667946642455975)
      ·
        refine ⟨10132115474501919963683963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6754743649667946642455975 10132115474501919963683963)
        ·
          refine ⟨15198173211752879945525945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10132115474501919963683963 15198173211752879945525945)
          ·
            refine ⟨11398629908814659959144459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15198173211752879945525945 11398629908814659959144459)
            ·
              refine ⟨17097944863221989938716689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11398629908814659959144459 17097944863221989938716689)
              ·
                refine ⟨12823458647416492454037517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17097944863221989938716689 12823458647416492454037517)
                ·
                  refine ⟨4808796992781184670264069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12823458647416492454037517 4808796992781184670264069)
                  ·
                    refine ⟨901649436146472125674513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4808796992781184670264069 901649436146472125674513)
                    ·
                      refine ⟨676237077109854094255885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 901649436146472125674513 676237077109854094255885)
                      ·
                        rfl

theorem cell23_1316967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_1316967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1316967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1316967 prefixEnd_1316967 := by exact prefixLift 1316967
  have htrace : WordTrace (prefixWord ++ tailWord_1316967) baseStart_1316967 baseEnd_1316967 := by
    simpa [prefixWord, tailWord_1316967, baseEnd_1316967] using wordTrace_append hprefix tailTrace_1316967
  have hstable : (prefixWord ++ tailWord_1316967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1316967).length < 2 ^ (prefixWord ++ tailWord_1316967).sum := by decide
  have hdescent : baseEnd_1316967 < baseStart_1316967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1316967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317037 : List Nat := [1, 5, 2, 1, 2, 1, 1, 2, 1, 7]
def baseStart_1317037 : Nat := 118140960795 + 1317037 * 2 ^ 59
def prefixEnd_1317037 : Nat := 4983230072969 + 3 ^ 40 * 1317037 * 2
def baseEnd_1317037 : Nat := 225424340251889606793521

theorem tailTrace_1317037 : CollatzResearch.WordTrace tailWord_1317037 prefixEnd_1317037 225424340251889606793521 := by
  unfold tailWord_1317037
  simp only [CollatzResearch.WordTrace]
  refine ⟨48036285729607355856957365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32024190486404903904638243 48036285729607355856957365)
  ·
    refine ⟨4503401787150689611589753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48036285729607355856957365 4503401787150689611589753)
    ·
      refine ⟨3377551340363017208692315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4503401787150689611589753 3377551340363017208692315)
      ·
        refine ⟨5066327010544525813038473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3377551340363017208692315 5066327010544525813038473)
        ·
          refine ⟨3799745257908394359778855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5066327010544525813038473 3799745257908394359778855)
          ·
            refine ⟨5699617886862591539668283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3799745257908394359778855 5699617886862591539668283)
            ·
              refine ⟨8549426830293887309502425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5699617886862591539668283 8549426830293887309502425)
              ·
                refine ⟨6412070122720415482126819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8549426830293887309502425 6412070122720415482126819)
                ·
                  refine ⟨9618105184080623223190229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6412070122720415482126819 9618105184080623223190229)
                  ·
                    refine ⟨225424340251889606793521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9618105184080623223190229 225424340251889606793521)
                    ·
                      rfl

theorem cell23_1317037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_1317037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317037 prefixEnd_1317037 := by exact prefixLift 1317037
  have htrace : WordTrace (prefixWord ++ tailWord_1317037) baseStart_1317037 baseEnd_1317037 := by
    simpa [prefixWord, tailWord_1317037, baseEnd_1317037] using wordTrace_append hprefix tailTrace_1317037
  have hstable : (prefixWord ++ tailWord_1317037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317037).length < 2 ^ (prefixWord ++ tailWord_1317037).sum := by decide
  have hdescent : baseEnd_1317037 < baseStart_1317037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317058 : List Nat := [3, 5, 1, 1, 1, 1, 3, 3, 5]
def baseStart_1317058 : Nat := 118140960795 + 1317058 * 2 ^ 59
def prefixEnd_1317058 : Nat := 4983230072969 + 3 ^ 40 * 1317058 * 2
def baseEnd_1317058 : Nat := 75142644872157026468663

theorem tailTrace_1317058 : CollatzResearch.WordTrace tailWord_1317058 prefixEnd_1317058 75142644872157026468663 := by
  unfold tailWord_1317058
  simp only [CollatzResearch.WordTrace]
  refine ⟨12009262915632819110867957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32024701108354184295647885 12009262915632819110867957)
  ·
    refine ⟨1125868398340576791643871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12009262915632819110867957 1125868398340576791643871)
    ·
      refine ⟨1688802597510865187465807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1125868398340576791643871 1688802597510865187465807)
      ·
        refine ⟨2533203896266297781198711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1688802597510865187465807 2533203896266297781198711)
        ·
          refine ⟨3799805844399446671798067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2533203896266297781198711 3799805844399446671798067)
          ·
            refine ⟨5699708766599170007697101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3799805844399446671798067 5699708766599170007697101)
            ·
              refine ⟨2137390787474688752886413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5699708766599170007697101 2137390787474688752886413)
              ·
                refine ⟨801521545303008282332405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2137390787474688752886413 801521545303008282332405)
                ·
                  refine ⟨75142644872157026468663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 801521545303008282332405 75142644872157026468663)
                  ·
                    rfl

theorem cell23_1317058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_1317058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317058 prefixEnd_1317058 := by exact prefixLift 1317058
  have htrace : WordTrace (prefixWord ++ tailWord_1317058) baseStart_1317058 baseEnd_1317058 := by
    simpa [prefixWord, tailWord_1317058, baseEnd_1317058] using wordTrace_append hprefix tailTrace_1317058
  have hstable : (prefixWord ++ tailWord_1317058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317058).length < 2 ^ (prefixWord ++ tailWord_1317058).sum := by decide
  have hdescent : baseEnd_1317058 < baseStart_1317058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317074 : List Nat := [3, 2, 2, 2, 1, 3, 1, 2, 2, 1, 4]
def baseStart_1317074 : Nat := 118140960795 + 1317074 * 2 ^ 59
def prefixEnd_1317074 : Nat := 4983230072969 + 3 ^ 40 * 1317074 * 2
def baseEnd_1317074 : Nat := 676292019539885175617893

theorem tailTrace_1317074 : CollatzResearch.WordTrace tailWord_1317074 prefixEnd_1317074 676292019539885175617893 := by
  unfold tailWord_1317074
  simp only [CollatzResearch.WordTrace]
  refine ⟨12009408807618327794013569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32025090153648874117369517 12009408807618327794013569)
  ·
    refine ⟨9007056605713745845510177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12009408807618327794013569 9007056605713745845510177)
    ·
      refine ⟨6755292454285309384132633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9007056605713745845510177 6755292454285309384132633)
      ·
        refine ⟨5066469340713982038099475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6755292454285309384132633 5066469340713982038099475)
        ·
          refine ⟨7599704011070973057149213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5066469340713982038099475 7599704011070973057149213)
          ·
            refine ⟨2849889004151614896430955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7599704011070973057149213 2849889004151614896430955)
            ·
              refine ⟨4274833506227422344646433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2849889004151614896430955 4274833506227422344646433)
              ·
                refine ⟨3206125129670566758484825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4274833506227422344646433 3206125129670566758484825)
                ·
                  refine ⟨2404593847252925068863619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3206125129670566758484825 2404593847252925068863619)
                  ·
                    refine ⟨3606890770879387603295429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2404593847252925068863619 3606890770879387603295429)
                    ·
                      refine ⟨676292019539885175617893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3606890770879387603295429 676292019539885175617893)
                      ·
                        rfl

theorem cell23_1317074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_1317074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317074 prefixEnd_1317074 := by exact prefixLift 1317074
  have htrace : WordTrace (prefixWord ++ tailWord_1317074) baseStart_1317074 baseEnd_1317074 := by
    simpa [prefixWord, tailWord_1317074, baseEnd_1317074] using wordTrace_append hprefix tailTrace_1317074
  have hstable : (prefixWord ++ tailWord_1317074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317074).length < 2 ^ (prefixWord ++ tailWord_1317074).sum := by decide
  have hdescent : baseEnd_1317074 < baseStart_1317074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317147 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 4]
def baseStart_1317147 : Nat := 118140960795 + 1317147 * 2 ^ 59
def prefixEnd_1317147 : Nat := 4983230072969 + 3 ^ 40 * 1317147 * 2
def baseEnd_1317147 : Nat := 676329503627663390005057

theorem tailTrace_1317147 : CollatzResearch.WordTrace tailWord_1317147 prefixEnd_1317147 676329503627663390005057 := by
  unfold tailWord_1317147
  simp only [CollatzResearch.WordTrace]
  refine ⟨48040297759208844643461695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32026865172805896428974463 48040297759208844643461695)
  ·
    refine ⟨72060446638813266965192543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48040297759208844643461695 72060446638813266965192543)
    ·
      refine ⟨108090669958219900447788815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72060446638813266965192543 108090669958219900447788815)
      ·
        refine ⟨162136004937329850671683223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108090669958219900447788815 162136004937329850671683223)
        ·
          refine ⟨243204007405994776007524835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162136004937329850671683223 243204007405994776007524835)
          ·
            refine ⟨364806011108992164011287253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 243204007405994776007524835 364806011108992164011287253)
            ·
              refine ⟨8550140885367003844014545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 364806011108992164011287253 8550140885367003844014545)
              ·
                refine ⟨6412605664025252883010909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8550140885367003844014545 6412605664025252883010909)
                ·
                  refine ⟨2404727124009469831129091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6412605664025252883010909 2404727124009469831129091)
                  ·
                    refine ⟨3607090686014204746693637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2404727124009469831129091 3607090686014204746693637)
                    ·
                      refine ⟨676329503627663390005057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3607090686014204746693637 676329503627663390005057)
                      ·
                        rfl

theorem cell23_1317147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 3, 1, 4].length) (baseStart_1317147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317147 prefixEnd_1317147 := by exact prefixLift 1317147
  have htrace : WordTrace (prefixWord ++ tailWord_1317147) baseStart_1317147 baseEnd_1317147 := by
    simpa [prefixWord, tailWord_1317147, baseEnd_1317147] using wordTrace_append hprefix tailTrace_1317147
  have hstable : (prefixWord ++ tailWord_1317147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317147).length < 2 ^ (prefixWord ++ tailWord_1317147).sum := by decide
  have hdescent : baseEnd_1317147 < baseStart_1317147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317218 : List Nat := [3, 3, 2, 1, 1, 3, 2, 2, 1, 2, 3]
def baseStart_1317218 : Nat := 118140960795 + 1317218 * 2 ^ 59
def prefixEnd_1317218 : Nat := 4983230072969 + 3 ^ 40 * 1317218 * 2
def baseEnd_1317218 : Nat := 676365960754132612217231

theorem tailTrace_1317218 : CollatzResearch.WordTrace tailWord_1317218 prefixEnd_1317218 676365960754132612217231 := by
  unfold tailWord_1317218
  simp only [CollatzResearch.WordTrace]
  refine ⟨12010721835487905942324077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32028591561301082512864205 12010721835487905942324077)
  ·
    refine ⟨4504020688307964728371529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12010721835487905942324077 4504020688307964728371529)
    ·
      refine ⟨3378015516230973546278647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4504020688307964728371529 3378015516230973546278647)
      ·
        refine ⟨5067023274346460319417971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3378015516230973546278647 5067023274346460319417971)
        ·
          refine ⟨7600534911519690479126957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5067023274346460319417971 7600534911519690479126957)
          ·
            refine ⟨2850200591819883929672609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7600534911519690479126957 2850200591819883929672609)
            ·
              refine ⟨2137650443864912947254457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2850200591819883929672609 2137650443864912947254457)
              ·
                refine ⟨1603237832898684710440843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2137650443864912947254457 1603237832898684710440843)
                ·
                  refine ⟨2404856749348027065661265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1603237832898684710440843 2404856749348027065661265)
                  ·
                    refine ⟨1803642562011020299245949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2404856749348027065661265 1803642562011020299245949)
                    ·
                      refine ⟨676365960754132612217231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1803642562011020299245949 676365960754132612217231)
                      ·
                        rfl

theorem cell23_1317218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_1317218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317218 prefixEnd_1317218 := by exact prefixLift 1317218
  have htrace : WordTrace (prefixWord ++ tailWord_1317218) baseStart_1317218 baseEnd_1317218 := by
    simpa [prefixWord, tailWord_1317218, baseEnd_1317218] using wordTrace_append hprefix tailTrace_1317218
  have hstable : (prefixWord ++ tailWord_1317218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317218).length < 2 ^ (prefixWord ++ tailWord_1317218).sum := by decide
  have hdescent : baseEnd_1317218 < baseStart_1317218 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317238 : List Nat := [5, 1, 1, 4, 2, 1, 9]
def baseStart_1317238 : Nat := 118140960795 + 1317238 * 2 ^ 59
def prefixEnd_1317238 : Nat := 4983230072969 + 3 ^ 40 * 1317238 * 2
def baseEnd_1317238 : Nat := 8350323831694105357619

theorem tailTrace_1317238 : CollatzResearch.WordTrace tailWord_1317238 prefixEnd_1317238 8350323831694105357619 := by
  unfold tailWord_1317238
  simp only [CollatzResearch.WordTrace]
  refine ⟨3002726050117447949064023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32029077867919444790016245 3002726050117447949064023)
  ·
    refine ⟨4504089075176171923596035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3002726050117447949064023 4504089075176171923596035)
    ·
      refine ⟨6756133612764257885394053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4504089075176171923596035 6756133612764257885394053)
      ·
        refine ⟨1266775052393298353511385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6756133612764257885394053 1266775052393298353511385)
        ·
          refine ⟨950081289294973765133539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1266775052393298353511385 950081289294973765133539)
          ·
            refine ⟨1425121933942460647700309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950081289294973765133539 1425121933942460647700309)
            ·
              refine ⟨8350323831694105357619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1425121933942460647700309 8350323831694105357619)
              ·
                rfl

theorem cell23_1317238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 1, 9].length) (baseStart_1317238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317238 prefixEnd_1317238 := by exact prefixLift 1317238
  have htrace : WordTrace (prefixWord ++ tailWord_1317238) baseStart_1317238 baseEnd_1317238 := by
    simpa [prefixWord, tailWord_1317238, baseEnd_1317238] using wordTrace_append hprefix tailTrace_1317238
  have hstable : (prefixWord ++ tailWord_1317238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317238).length < 2 ^ (prefixWord ++ tailWord_1317238).sum := by decide
  have hdescent : baseEnd_1317238 < baseStart_1317238 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317274 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5]
def baseStart_1317274 : Nat := 118140960795 + 1317274 * 2 ^ 59
def prefixEnd_1317274 : Nat := 4983230072969 + 3 ^ 40 * 1317274 * 2
def baseEnd_1317274 : Nat := 676394715670784393116973

theorem tailTrace_1317274 : CollatzResearch.WordTrace tailWord_1317274 prefixEnd_1317274 676394715670784393116973 := by
  unfold tailWord_1317274
  simp only [CollatzResearch.WordTrace]
  refine ⟨12011232457437186333333719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32029953219832496888889917 12011232457437186333333719)
  ·
    refine ⟨18016848686155779500000579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12011232457437186333333719 18016848686155779500000579)
    ·
      refine ⟨27025273029233669250000869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18016848686155779500000579 27025273029233669250000869)
      ·
        refine ⟨5067238692981312984375163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27025273029233669250000869 5067238692981312984375163)
        ·
          refine ⟨7600858039471969476562745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5067238692981312984375163 7600858039471969476562745)
          ·
            refine ⟨5700643529603977107422059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7600858039471969476562745 5700643529603977107422059)
            ·
              refine ⟨8550965294405965661133089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5700643529603977107422059 8550965294405965661133089)
              ·
                refine ⟨6413223970804474245849817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8550965294405965661133089 6413223970804474245849817)
                ·
                  refine ⟨4809917978103355684387363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6413223970804474245849817 4809917978103355684387363)
                  ·
                    refine ⟨7214876967155033526581045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4809917978103355684387363 7214876967155033526581045)
                    ·
                      refine ⟨676394715670784393116973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7214876967155033526581045 676394715670784393116973)
                      ·
                        rfl

theorem cell23_1317274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_1317274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317274 prefixEnd_1317274 := by exact prefixLift 1317274
  have htrace : WordTrace (prefixWord ++ tailWord_1317274) baseStart_1317274 baseEnd_1317274 := by
    simpa [prefixWord, tailWord_1317274, baseEnd_1317274] using wordTrace_append hprefix tailTrace_1317274
  have hstable : (prefixWord ++ tailWord_1317274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317274).length < 2 ^ (prefixWord ++ tailWord_1317274).sum := by decide
  have hdescent : baseEnd_1317274 < baseStart_1317274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317288 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 3, 4, 2]
def baseStart_1317288 : Nat := 118140960795 + 1317288 * 2 ^ 59
def prefixEnd_1317288 : Nat := 4983230072969 + 3 ^ 40 * 1317288 * 2
def baseEnd_1317288 : Nat := 676401904399947338341909

theorem tailTrace_1317288 : CollatzResearch.WordTrace tailWord_1317288 prefixEnd_1317288 676401904399947338341909 := by
  unfold tailWord_1317288
  simp only [CollatzResearch.WordTrace]
  refine ⟨24022720225849012862172259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32030293634465350482896345 24022720225849012862172259)
  ·
    refine ⟨36034080338773519293258389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24022720225849012862172259 36034080338773519293258389)
    ·
      refine ⟨1689097515880008716871487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 36034080338773519293258389 1689097515880008716871487)
      ·
        refine ⟨2533646273820013075307231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1689097515880008716871487 2533646273820013075307231)
        ·
          refine ⟨3800469410730019612960847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2533646273820013075307231 3800469410730019612960847)
          ·
            refine ⟨5700704116095029419441271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3800469410730019612960847 5700704116095029419441271)
            ·
              refine ⟨8551056174142544129161907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5700704116095029419441271 8551056174142544129161907)
              ·
                refine ⟨12826584261213816193742861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8551056174142544129161907 12826584261213816193742861)
                ·
                  refine ⟨4809969097955181072653573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12826584261213816193742861 4809969097955181072653573)
                  ·
                    refine ⟨901869205866596451122545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4809969097955181072653573 901869205866596451122545)
                    ·
                      refine ⟨676401904399947338341909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 901869205866596451122545 676401904399947338341909)
                      ·
                        rfl

theorem cell23_1317288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_1317288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317288 prefixEnd_1317288 := by exact prefixLift 1317288
  have htrace : WordTrace (prefixWord ++ tailWord_1317288) baseStart_1317288 baseEnd_1317288 := by
    simpa [prefixWord, tailWord_1317288, baseEnd_1317288] using wordTrace_append hprefix tailTrace_1317288
  have hstable : (prefixWord ++ tailWord_1317288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317288).length < 2 ^ (prefixWord ++ tailWord_1317288).sum := by decide
  have hdescent : baseEnd_1317288 < baseStart_1317288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317304 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 2, 3, 3]
def baseStart_1317304 : Nat := 118140960795 + 1317304 * 2 ^ 59
def prefixEnd_1317304 : Nat := 4983230072969 + 3 ^ 40 * 1317304 * 2
def baseEnd_1317304 : Nat := 676410120090419275741835

theorem tailTrace_1317304 : CollatzResearch.WordTrace tailWord_1317304 prefixEnd_1317304 676410120090419275741835 := by
  unfold tailWord_1317304
  simp only [CollatzResearch.WordTrace]
  refine ⟨24023012009820030228463483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32030682679760040304617977 24023012009820030228463483)
  ·
    refine ⟨36034518014730045342695225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24023012009820030228463483 36034518014730045342695225)
    ·
      refine ⟨27025888511047534007021419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36034518014730045342695225 27025888511047534007021419)
      ·
        refine ⟨40538832766571301010532129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27025888511047534007021419 40538832766571301010532129)
        ·
          refine ⟨30404124574928475757899097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40538832766571301010532129 30404124574928475757899097)
          ·
            refine ⟨22803093431196356818424323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30404124574928475757899097 22803093431196356818424323)
            ·
              refine ⟨34204640146794535227636485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22803093431196356818424323 34204640146794535227636485)
              ·
                refine ⟨6413370027523975355181841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34204640146794535227636485 6413370027523975355181841)
                ·
                  refine ⟨4810027520642981516386381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6413370027523975355181841 4810027520642981516386381)
                  ·
                    refine ⟨1803760320241118068644893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4810027520642981516386381 1803760320241118068644893)
                    ·
                      refine ⟨676410120090419275741835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1803760320241118068644893 676410120090419275741835)
                      ·
                        rfl

theorem cell23_1317304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 2, 3, 3].length) (baseStart_1317304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317304 prefixEnd_1317304 := by exact prefixLift 1317304
  have htrace : WordTrace (prefixWord ++ tailWord_1317304) baseStart_1317304 baseEnd_1317304 := by
    simpa [prefixWord, tailWord_1317304, baseEnd_1317304] using wordTrace_append hprefix tailTrace_1317304
  have hstable : (prefixWord ++ tailWord_1317304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317304).length < 2 ^ (prefixWord ++ tailWord_1317304).sum := by decide
  have hdescent : baseEnd_1317304 < baseStart_1317304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317305 : List Nat := [1, 2, 1, 4, 3, 2, 2, 2, 2, 2, 2]
def baseStart_1317305 : Nat := 118140960795 + 1317305 * 2 ^ 59
def prefixEnd_1317305 : Nat := 4983230072969 + 3 ^ 40 * 1317305 * 2
def baseEnd_1317305 : Nat := 676410633571073771829331

theorem tailTrace_1317305 : CollatzResearch.WordTrace tailWord_1317305 prefixEnd_1317305 676410633571073771829331 := by
  unfold tailWord_1317305
  simp only [CollatzResearch.WordTrace]
  refine ⟨48046060492636437627713369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32030706995090958418475579 48046060492636437627713369)
  ·
    refine ⟨36034545369477328220785027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48046060492636437627713369 36034545369477328220785027)
    ·
      refine ⟨54051818054215992331177541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36034545369477328220785027 54051818054215992331177541)
      ·
        refine ⟨10134715885165498562095789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54051818054215992331177541 10134715885165498562095789)
        ·
          refine ⟨3800518456937061960785921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10134715885165498562095789 3800518456937061960785921)
          ·
            refine ⟨2850388842702796470589441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3800518456937061960785921 2850388842702796470589441)
            ·
              refine ⟨2137791632027097352942081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2850388842702796470589441 2137791632027097352942081)
              ·
                refine ⟨1603343724020323014706561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2137791632027097352942081 1603343724020323014706561)
                ·
                  refine ⟨1202507793015242261029921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1603343724020323014706561 1202507793015242261029921)
                  ·
                    refine ⟨901880844761431695772441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1202507793015242261029921 901880844761431695772441)
                    ·
                      refine ⟨676410633571073771829331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 901880844761431695772441 676410633571073771829331)
                      ·
                        rfl

theorem cell23_1317305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 2, 2, 2].length) (baseStart_1317305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317305 prefixEnd_1317305 := by exact prefixLift 1317305
  have htrace : WordTrace (prefixWord ++ tailWord_1317305) baseStart_1317305 baseEnd_1317305 := by
    simpa [prefixWord, tailWord_1317305, baseEnd_1317305] using wordTrace_append hprefix tailTrace_1317305
  have hstable : (prefixWord ++ tailWord_1317305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317305).length < 2 ^ (prefixWord ++ tailWord_1317305).sum := by decide
  have hdescent : baseEnd_1317305 < baseStart_1317305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317344 : List Nat := [2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 4]
def baseStart_1317344 : Nat := 118140960795 + 1317344 * 2 ^ 59
def prefixEnd_1317344 : Nat := 4983230072969 + 3 ^ 40 * 1317344 * 2
def baseEnd_1317344 : Nat := 676430659316599119241651

theorem tailTrace_1317344 : CollatzResearch.WordTrace tailWord_1317344 prefixEnd_1317344 676430659316599119241651 := by
  unfold tailWord_1317344
  simp only [CollatzResearch.WordTrace]
  refine ⟨24023741469747573644191543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32031655292996764858922057 24023741469747573644191543)
  ·
    refine ⟨36035612204621360466287315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24023741469747573644191543 36035612204621360466287315)
    ·
      refine ⟨54053418306932040699430973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36035612204621360466287315 54053418306932040699430973)
      ·
        refine ⟨20270031865099515262286615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 54053418306932040699430973 20270031865099515262286615)
        ·
          refine ⟨30405047797649272893429923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20270031865099515262286615 30405047797649272893429923)
          ·
            refine ⟨45607571696473909340144885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30405047797649272893429923 45607571696473909340144885)
            ·
              refine ⟨4275709846544429000638583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 45607571696473909340144885 4275709846544429000638583)
              ·
                refine ⟨6413564769816643500957875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4275709846544429000638583 6413564769816643500957875)
                ·
                  refine ⟨9620347154724965251436813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6413564769816643500957875 9620347154724965251436813)
                  ·
                    refine ⟨3607630183021861969288805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9620347154724965251436813 3607630183021861969288805)
                    ·
                      refine ⟨676430659316599119241651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3607630183021861969288805 676430659316599119241651)
                      ·
                        rfl

theorem cell23_1317344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_1317344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317344 prefixEnd_1317344 := by exact prefixLift 1317344
  have htrace : WordTrace (prefixWord ++ tailWord_1317344) baseStart_1317344 baseEnd_1317344 := by
    simpa [prefixWord, tailWord_1317344, baseEnd_1317344] using wordTrace_append hprefix tailTrace_1317344
  have hstable : (prefixWord ++ tailWord_1317344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317344).length < 2 ^ (prefixWord ++ tailWord_1317344).sum := by decide
  have hdescent : baseEnd_1317344 < baseStart_1317344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317361 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 4, 4, 2]
def baseStart_1317361 : Nat := 118140960795 + 1317361 * 2 ^ 59
def prefixEnd_1317361 : Nat := 4983230072969 + 3 ^ 40 * 1317361 * 2
def baseEnd_1317361 : Nat := 676439388487725552729073

theorem tailTrace_1317361 : CollatzResearch.WordTrace tailWord_1317361 prefixEnd_1317361 676439388487725552729073 := by
  unfold tailWord_1317361
  simp only [CollatzResearch.WordTrace]
  refine ⟨48048102980433559191751937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32032068653622372794501291 48048102980433559191751937)
  ·
    refine ⟨36036077235325169393813953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48048102980433559191751937 36036077235325169393813953)
    ·
      refine ⟨27027057926493877045360465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36036077235325169393813953 27027057926493877045360465)
      ·
        refine ⟨20270293444870407784020349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27027057926493877045360465 20270293444870407784020349)
        ·
          refine ⟨7601360041826402919007631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20270293444870407784020349 7601360041826402919007631)
          ·
            refine ⟨11402040062739604378511447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7601360041826402919007631 11402040062739604378511447)
            ·
              refine ⟨17103060094109406567767171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11402040062739604378511447 17103060094109406567767171)
              ·
                refine ⟨25654590141164109851650757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17103060094109406567767171 25654590141164109851650757)
                ·
                  refine ⟨4810235651468270597184517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 25654590141164109851650757 4810235651468270597184517)
                  ·
                    refine ⟨901919184650300736972097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4810235651468270597184517 901919184650300736972097)
                    ·
                      refine ⟨676439388487725552729073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 901919184650300736972097 676439388487725552729073)
                      ·
                        rfl

theorem cell23_1317361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 4, 4, 2].length) (baseStart_1317361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317361 prefixEnd_1317361 := by exact prefixLift 1317361
  have htrace : WordTrace (prefixWord ++ tailWord_1317361) baseStart_1317361 baseEnd_1317361 := by
    simpa [prefixWord, tailWord_1317361, baseEnd_1317361] using wordTrace_append hprefix tailTrace_1317361
  have hstable : (prefixWord ++ tailWord_1317361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317361).length < 2 ^ (prefixWord ++ tailWord_1317361).sum := by decide
  have hdescent : baseEnd_1317361 < baseStart_1317361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317405 : List Nat := [1, 4, 2, 2, 1, 2, 3, 3, 1, 4]
def baseStart_1317405 : Nat := 118140960795 + 1317405 * 2 ^ 59
def prefixEnd_1317405 : Nat := 4983230072969 + 3 ^ 40 * 1317405 * 2
def baseEnd_1317405 : Nat := 225487327212174460192957

theorem tailTrace_1317405 : CollatzResearch.WordTrace tailWord_1317405 prefixEnd_1317405 225487327212174460192957 := by
  unfold tailWord_1317405
  simp only [CollatzResearch.WordTrace]
  refine ⟨48049707792274154706353669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32033138528182769804235779 48049707792274154706353669)
  ·
    refine ⟨9009320211051404007441313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48049707792274154706353669 9009320211051404007441313)
    ·
      refine ⟨6756990158288553005580985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9009320211051404007441313 6756990158288553005580985)
      ·
        refine ⟨5067742618716414754185739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6756990158288553005580985 5067742618716414754185739)
        ·
          refine ⟨7601613928074622131278609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5067742618716414754185739 7601613928074622131278609)
          ·
            refine ⟨5701210446055966598458957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7601613928074622131278609 5701210446055966598458957)
            ·
              refine ⟨2137953917270987474422109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5701210446055966598458957 2137953917270987474422109)
              ·
                refine ⟨801732718976620302908291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2137953917270987474422109 801732718976620302908291)
                ·
                  refine ⟨1202599078464930454362437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 801732718976620302908291 1202599078464930454362437)
                  ·
                    refine ⟨225487327212174460192957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1202599078464930454362437 225487327212174460192957)
                    ·
                      rfl

theorem cell23_1317405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 3, 3, 1, 4].length) (baseStart_1317405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317405 prefixEnd_1317405 := by exact prefixLift 1317405
  have htrace : WordTrace (prefixWord ++ tailWord_1317405) baseStart_1317405 baseEnd_1317405 := by
    simpa [prefixWord, tailWord_1317405, baseEnd_1317405] using wordTrace_append hprefix tailTrace_1317405
  have hstable : (prefixWord ++ tailWord_1317405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317405).length < 2 ^ (prefixWord ++ tailWord_1317405).sum := by decide
  have hdescent : baseEnd_1317405 < baseStart_1317405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317422 : List Nat := [4, 1, 3, 1, 4, 1, 1, 1, 3, 4]
def baseStart_1317422 : Nat := 118140960795 + 1317422 * 2 ^ 59
def prefixEnd_1317422 : Nat := 4983230072969 + 3 ^ 40 * 1317422 * 2
def baseEnd_1317422 : Nat := 225490236935883271355431

theorem tailTrace_1317422 : CollatzResearch.WordTrace tailWord_1317422 prefixEnd_1317422 225490236935883271355431 := by
  unfold tailWord_1317422
  simp only [CollatzResearch.WordTrace]
  refine ⟨6006290979151570826215315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32033551888808377739815013 6006290979151570826215315)
  ·
    refine ⟨9009436468727356239322973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6006290979151570826215315 9009436468727356239322973)
    ·
      refine ⟨3378538675772758589746115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9009436468727356239322973 3378538675772758589746115)
      ·
        refine ⟨5067808013659137884619173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3378538675772758589746115 5067808013659137884619173)
        ·
          refine ⟨950214002561088353366095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5067808013659137884619173 950214002561088353366095)
          ·
            refine ⟨1425321003841632530049143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950214002561088353366095 1425321003841632530049143)
            ·
              refine ⟨2137981505762448795073715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1425321003841632530049143 2137981505762448795073715)
              ·
                refine ⟨3206972258643673192610573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2137981505762448795073715 3206972258643673192610573)
                ·
                  refine ⟨1202614596991377447228965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3206972258643673192610573 1202614596991377447228965)
                  ·
                    refine ⟨225490236935883271355431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1202614596991377447228965 225490236935883271355431)
                    ·
                      rfl

theorem cell23_1317422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_1317422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317422 prefixEnd_1317422 := by exact prefixLift 1317422
  have htrace : WordTrace (prefixWord ++ tailWord_1317422) baseStart_1317422 baseEnd_1317422 := by
    simpa [prefixWord, tailWord_1317422, baseEnd_1317422] using wordTrace_append hprefix tailTrace_1317422
  have hstable : (prefixWord ++ tailWord_1317422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317422).length < 2 ^ (prefixWord ++ tailWord_1317422).sum := by decide
  have hdescent : baseEnd_1317422 < baseStart_1317422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317451 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 2, 6, 2]
def baseStart_1317451 : Nat := 118140960795 + 1317451 * 2 ^ 59
def prefixEnd_1317451 : Nat := 4983230072969 + 3 ^ 40 * 1317451 * 2
def baseEnd_1317451 : Nat := 676485601746630200603659

theorem tailTrace_1317451 : CollatzResearch.WordTrace tailWord_1317451 prefixEnd_1317451 676485601746630200603659 := by
  unfold tailWord_1317451
  simp only [CollatzResearch.WordTrace]
  refine ⟨48051385550107504562528207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32034257033405003041685471 48051385550107504562528207)
  ·
    refine ⟨72077078325161256843792311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48051385550107504562528207 72077078325161256843792311)
    ·
      refine ⟨108115617487741885265688467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72077078325161256843792311 108115617487741885265688467)
      ·
        refine ⟨162173426231612827898532701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108115617487741885265688467 162173426231612827898532701)
        ·
          refine ⟨60815034836854810461949763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 162173426231612827898532701 60815034836854810461949763)
          ·
            refine ⟨91222552255282215692924645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60815034836854810461949763 91222552255282215692924645)
            ·
              refine ⟨17104228547865415442423371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91222552255282215692924645 17104228547865415442423371)
              ·
                refine ⟨25656342821798123163635057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17104228547865415442423371 25656342821798123163635057)
                ·
                  refine ⟨19242257116348592372726293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25656342821798123163635057 19242257116348592372726293)
                  ·
                    refine ⟨901980802328840267471545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19242257116348592372726293 901980802328840267471545)
                    ·
                      refine ⟨676485601746630200603659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 901980802328840267471545 676485601746630200603659)
                      ·
                        rfl

theorem cell23_1317451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 2, 6, 2].length) (baseStart_1317451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317451 prefixEnd_1317451 := by exact prefixLift 1317451
  have htrace : WordTrace (prefixWord ++ tailWord_1317451) baseStart_1317451 baseEnd_1317451 := by
    simpa [prefixWord, tailWord_1317451, baseEnd_1317451] using wordTrace_append hprefix tailTrace_1317451
  have hstable : (prefixWord ++ tailWord_1317451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317451).length < 2 ^ (prefixWord ++ tailWord_1317451).sum := by decide
  have hdescent : baseEnd_1317451 < baseStart_1317451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317461 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 6, 4]
def baseStart_1317461 : Nat := 118140960795 + 1317461 * 2 ^ 59
def prefixEnd_1317461 : Nat := 4983230072969 + 3 ^ 40 * 1317461 * 2
def baseEnd_1317461 : Nat := 225496912184391720492871

theorem tailTrace_1317461 : CollatzResearch.WordTrace tailWord_1317461 prefixEnd_1317461 225496912184391720492871 := by
  unfold tailWord_1317461
  simp only [CollatzResearch.WordTrace]
  refine ⟨48051750280071276270392237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32034500186714184180261491 48051750280071276270392237)
  ·
    refine ⟨18019406355026728601397089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48051750280071276270392237 18019406355026728601397089)
    ·
      refine ⟨13514554766270046451047817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18019406355026728601397089 13514554766270046451047817)
      ·
        refine ⟨10135916074702534838285863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13514554766270046451047817 10135916074702534838285863)
        ·
          refine ⟨15203874112053802257428795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10135916074702534838285863 15203874112053802257428795)
          ·
            refine ⟨22805811168080703386143193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15203874112053802257428795 22805811168080703386143193)
            ·
              refine ⟨17104358376060527539607395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22805811168080703386143193 17104358376060527539607395)
              ·
                refine ⟨25656537564090791309411093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17104358376060527539607395 25656537564090791309411093)
                ·
                  refine ⟨1202650198316755842628645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 25656537564090791309411093 1202650198316755842628645)
                  ·
                    refine ⟨225496912184391720492871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1202650198316755842628645 225496912184391720492871)
                    ·
                      rfl

theorem cell23_1317461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 6, 4].length) (baseStart_1317461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317461 prefixEnd_1317461 := by exact prefixLift 1317461
  have htrace : WordTrace (prefixWord ++ tailWord_1317461) baseStart_1317461 baseEnd_1317461 := by
    simpa [prefixWord, tailWord_1317461, baseEnd_1317461] using wordTrace_append hprefix tailTrace_1317461
  have hstable : (prefixWord ++ tailWord_1317461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317461).length < 2 ^ (prefixWord ++ tailWord_1317461).sum := by decide
  have hdescent : baseEnd_1317461 < baseStart_1317461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317508 : List Nat := [2, 3, 2, 1, 3, 2, 3, 7]
def baseStart_1317508 : Nat := 118140960795 + 1317508 * 2 ^ 59
def prefixEnd_1317508 : Nat := 4983230072969 + 3 ^ 40 * 1317508 * 2
def baseEnd_1317508 : Nat := 25056106301627276947811

theorem tailTrace_1317508 : CollatzResearch.WordTrace tailWord_1317508 prefixEnd_1317508 25056106301627276947811 := by
  unfold tailWord_1317508
  simp only [CollatzResearch.WordTrace]
  refine ⟨24026732255450501648676589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32035643007267335531568785 24026732255450501648676589)
  ·
    refine ⟨9010024595793938118253721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24026732255450501648676589 9010024595793938118253721)
    ·
      refine ⟨6757518446845453588690291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9010024595793938118253721 6757518446845453588690291)
      ·
        refine ⟨10136277670268180383035437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6757518446845453588690291 10136277670268180383035437)
        ·
          refine ⟨3801104126350567643638289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10136277670268180383035437 3801104126350567643638289)
          ·
            refine ⟨2850828094762925732728717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3801104126350567643638289 2850828094762925732728717)
            ·
              refine ⟨1069060535536097149773269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2850828094762925732728717 1069060535536097149773269)
              ·
                refine ⟨25056106301627276947811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1069060535536097149773269 25056106301627276947811)
                ·
                  rfl

theorem cell23_1317508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 3, 7].length) (baseStart_1317508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317508 prefixEnd_1317508 := by exact prefixLift 1317508
  have htrace : WordTrace (prefixWord ++ tailWord_1317508) baseStart_1317508 baseEnd_1317508 := by
    simpa [prefixWord, tailWord_1317508, baseEnd_1317508] using wordTrace_append hprefix tailTrace_1317508
  have hstable : (prefixWord ++ tailWord_1317508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317508).length < 2 ^ (prefixWord ++ tailWord_1317508).sum := by decide
  have hdescent : baseEnd_1317508 < baseStart_1317508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317518 : List Nat := [4, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3]
def baseStart_1317518 : Nat := 118140960795 + 1317518 * 2 ^ 59
def prefixEnd_1317518 : Nat := 4983230072969 + 3 ^ 40 * 1317518 * 2
def baseEnd_1317518 : Nat := 676520004950481438465851

theorem tailTrace_1317518 : CollatzResearch.WordTrace tailWord_1317518 prefixEnd_1317518 676520004950481438465851 := by
  unfold tailWord_1317518
  simp only [CollatzResearch.WordTrace]
  refine ⟨6006728655108096875652151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32035886160576516670144805 6006728655108096875652151)
  ·
    refine ⟨9010092982662145313478227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6006728655108096875652151 9010092982662145313478227)
    ·
      refine ⟨13515139473993217970217341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9010092982662145313478227 13515139473993217970217341)
      ·
        refine ⟨5068177302747456738831503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13515139473993217970217341 5068177302747456738831503)
        ·
          refine ⟨7602265954121185108247255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5068177302747456738831503 7602265954121185108247255)
          ·
            refine ⟨11403398931181777662370883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7602265954121185108247255 11403398931181777662370883)
            ·
              refine ⟨17105098396772666493556325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11403398931181777662370883 17105098396772666493556325)
              ·
                refine ⟨3207205949394874967541811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17105098396772666493556325 3207205949394874967541811)
                ·
                  refine ⟨4810808924092312451312717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3207205949394874967541811 4810808924092312451312717)
                  ·
                    refine ⟨1804053346534617169242269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4810808924092312451312717 1804053346534617169242269)
                    ·
                      refine ⟨676520004950481438465851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1804053346534617169242269 676520004950481438465851)
                      ·
                        rfl

theorem cell23_1317518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 1, 3, 3].length) (baseStart_1317518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317518 prefixEnd_1317518 := by exact prefixLift 1317518
  have htrace : WordTrace (prefixWord ++ tailWord_1317518) baseStart_1317518 baseEnd_1317518 := by
    simpa [prefixWord, tailWord_1317518, baseEnd_1317518] using wordTrace_append hprefix tailTrace_1317518
  have hstable : (prefixWord ++ tailWord_1317518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317518).length < 2 ^ (prefixWord ++ tailWord_1317518).sum := by decide
  have hdescent : baseEnd_1317518 < baseStart_1317518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317522 : List Nat := [3, 2, 3, 1, 2, 1, 4, 1, 1, 2, 3]
def baseStart_1317522 : Nat := 118140960795 + 1317522 * 2 ^ 59
def prefixEnd_1317522 : Nat := 4983230072969 + 3 ^ 40 * 1317522 * 2
def baseEnd_1317522 : Nat := 676522058873099422815833

theorem tailTrace_1317522 : CollatzResearch.WordTrace tailWord_1317522 prefixEnd_1317522 676522058873099422815833 := by
  unfold tailWord_1317522
  simp only [CollatzResearch.WordTrace]
  refine ⟨12013493783212570922090705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32035983421900189125575213 12013493783212570922090705)
  ·
    refine ⟨9010120337409428191568029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12013493783212570922090705 9010120337409428191568029)
    ·
      refine ⟨3378795126528535571838011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9010120337409428191568029 3378795126528535571838011)
      ·
        refine ⟨5068192689792803357757017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3378795126528535571838011 5068192689792803357757017)
        ·
          refine ⟨3801144517344602518317763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5068192689792803357757017 3801144517344602518317763)
          ·
            refine ⟨5701716776016903777476645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3801144517344602518317763 5701716776016903777476645)
            ·
              refine ⟨1069071895503169458276871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5701716776016903777476645 1069071895503169458276871)
              ·
                refine ⟨1603607843254754187415307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1069071895503169458276871 1603607843254754187415307)
                ·
                  refine ⟨2405411764882131281122961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1603607843254754187415307 2405411764882131281122961)
                  ·
                    refine ⟨1804058823661598460842221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2405411764882131281122961 1804058823661598460842221)
                    ·
                      refine ⟨676522058873099422815833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1804058823661598460842221 676522058873099422815833)
                      ·
                        rfl

theorem cell23_1317522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 1, 1, 2, 3].length) (baseStart_1317522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317522 prefixEnd_1317522 := by exact prefixLift 1317522
  have htrace : WordTrace (prefixWord ++ tailWord_1317522) baseStart_1317522 baseEnd_1317522 := by
    simpa [prefixWord, tailWord_1317522, baseEnd_1317522] using wordTrace_append hprefix tailTrace_1317522
  have hstable : (prefixWord ++ tailWord_1317522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317522).length < 2 ^ (prefixWord ++ tailWord_1317522).sum := by decide
  have hdescent : baseEnd_1317522 < baseStart_1317522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317551 : List Nat := [1, 1, 2, 1, 2, 5, 2, 1, 2, 6]
def baseStart_1317551 : Nat := 118140960795 + 1317551 * 2 ^ 59
def prefixEnd_1317551 : Nat := 4983230072969 + 3 ^ 40 * 1317551 * 2
def baseEnd_1317551 : Nat := 225512316604026603117733

theorem tailTrace_1317551 : CollatzResearch.WordTrace tailWord_1317551 prefixEnd_1317551 225512316604026603117733 := by
  unfold tailWord_1317551
  simp only [CollatzResearch.WordTrace]
  refine ⟨48055032849745221641168507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32036688566496814427445671 48055032849745221641168507)
  ·
    refine ⟨72082549274617832461752761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48055032849745221641168507 72082549274617832461752761)
    ·
      refine ⟨54061911955963374346314571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72082549274617832461752761 54061911955963374346314571)
      ·
        refine ⟨81092867933945061519471857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54061911955963374346314571 81092867933945061519471857)
        ·
          refine ⟨60819650950458796139603893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81092867933945061519471857 60819650950458796139603893)
          ·
            refine ⟨5701842276605512138087865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60819650950458796139603893 5701842276605512138087865)
            ·
              refine ⟨4276381707454134103565899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5701842276605512138087865 4276381707454134103565899)
              ·
                refine ⟨6414572561181201155348849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4276381707454134103565899 6414572561181201155348849)
                ·
                  refine ⟨4810929420885900866511637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6414572561181201155348849 4810929420885900866511637)
                  ·
                    refine ⟨225512316604026603117733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4810929420885900866511637 225512316604026603117733)
                    ·
                      rfl

theorem cell23_1317551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 2, 1, 2, 6].length) (baseStart_1317551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317551 prefixEnd_1317551 := by exact prefixLift 1317551
  have htrace : WordTrace (prefixWord ++ tailWord_1317551) baseStart_1317551 baseEnd_1317551 := by
    simpa [prefixWord, tailWord_1317551, baseEnd_1317551] using wordTrace_append hprefix tailTrace_1317551
  have hstable : (prefixWord ++ tailWord_1317551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317551).length < 2 ^ (prefixWord ++ tailWord_1317551).sum := by decide
  have hdescent : baseEnd_1317551 < baseStart_1317551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317561 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 2, 1, 5]
def baseStart_1317561 : Nat := 118140960795 + 1317561 * 2 ^ 59
def prefixEnd_1317561 : Nat := 4983230072969 + 3 ^ 40 * 1317561 * 2
def baseEnd_1317561 : Nat := 676542084618624770228153

theorem tailTrace_1317561 : CollatzResearch.WordTrace tailWord_1317561 prefixEnd_1317561 676542084618624770228153 := by
  unfold tailWord_1317561
  simp only [CollatzResearch.WordTrace]
  refine ⟨48055397579708993349032537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32036931719805995566021691 48055397579708993349032537)
  ·
    refine ⟨36041548184781745011774403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48055397579708993349032537 36041548184781745011774403)
    ·
      refine ⟨54062322277172617517661605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36041548184781745011774403 54062322277172617517661605)
      ·
        refine ⟨10136685426969865784561551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54062322277172617517661605 10136685426969865784561551)
        ·
          refine ⟨15205028140454798676842327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10136685426969865784561551 15205028140454798676842327)
          ·
            refine ⟨22807542210682198015263491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15205028140454798676842327 22807542210682198015263491)
            ·
              refine ⟨34211313316023297022895237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22807542210682198015263491 34211313316023297022895237)
              ·
                refine ⟨6414621246754368191792857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34211313316023297022895237 6414621246754368191792857)
                ·
                  refine ⟨4810965935065776143844643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6414621246754368191792857 4810965935065776143844643)
                  ·
                    refine ⟨7216448902598664215766965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4810965935065776143844643 7216448902598664215766965)
                    ·
                      refine ⟨676542084618624770228153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7216448902598664215766965 676542084618624770228153)
                      ·
                        rfl

theorem cell23_1317561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 2, 1, 5].length) (baseStart_1317561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317561 prefixEnd_1317561 := by exact prefixLift 1317561
  have htrace : WordTrace (prefixWord ++ tailWord_1317561) baseStart_1317561 baseEnd_1317561 := by
    simpa [prefixWord, tailWord_1317561, baseEnd_1317561] using wordTrace_append hprefix tailTrace_1317561
  have hstable : (prefixWord ++ tailWord_1317561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317561).length < 2 ^ (prefixWord ++ tailWord_1317561).sum := by decide
  have hdescent : baseEnd_1317561 < baseStart_1317561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317578 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 2, 1, 5]
def baseStart_1317578 : Nat := 118140960795 + 1317578 * 2 ^ 59
def prefixEnd_1317578 : Nat := 4983230072969 + 3 ^ 40 * 1317578 * 2
def baseEnd_1317578 : Nat := 676550813789751203715575

theorem tailTrace_1317578 : CollatzResearch.WordTrace tailWord_1317578 prefixEnd_1317578 676550813789751203715575 := by
  unfold tailWord_1317578
  simp only [CollatzResearch.WordTrace]
  refine ⟨12014004405161851313100347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32037345080431603501600925 12014004405161851313100347)
  ·
    refine ⟨18021006607742776969650521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12014004405161851313100347 18021006607742776969650521)
    ·
      refine ⟨13515754955807082727237891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18021006607742776969650521 13515754955807082727237891)
      ·
        refine ⟨20273632433710624090856837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13515754955807082727237891 20273632433710624090856837)
        ·
          refine ⟨3801306081320742017035657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20273632433710624090856837 3801306081320742017035657)
          ·
            refine ⟨2850979560990556512776743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3801306081320742017035657 2850979560990556512776743)
            ·
              refine ⟨4276469341485834769165115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2850979560990556512776743 4276469341485834769165115)
              ·
                refine ⟨6414704012228752153747673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4276469341485834769165115 6414704012228752153747673)
                ·
                  refine ⟨4811028009171564115310755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6414704012228752153747673 4811028009171564115310755)
                  ·
                    refine ⟨7216542013757346172966133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4811028009171564115310755 7216542013757346172966133)
                    ·
                      refine ⟨676550813789751203715575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7216542013757346172966133 676550813789751203715575)
                      ·
                        rfl

theorem cell23_1317578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_1317578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317578 prefixEnd_1317578 := by exact prefixLift 1317578
  have htrace : WordTrace (prefixWord ++ tailWord_1317578) baseStart_1317578 baseEnd_1317578 := by
    simpa [prefixWord, tailWord_1317578, baseEnd_1317578] using wordTrace_append hprefix tailTrace_1317578
  have hstable : (prefixWord ++ tailWord_1317578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317578).length < 2 ^ (prefixWord ++ tailWord_1317578).sum := by decide
  have hdescent : baseEnd_1317578 < baseStart_1317578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317611 : List Nat := [1, 1, 1, 1, 2, 4, 1, 1, 6, 5]
def baseStart_1317611 : Nat := 118140960795 + 1317611 * 2 ^ 59
def prefixEnd_1317611 : Nat := 4983230072969 + 3 ^ 40 * 1317611 * 2
def baseEnd_1317611 : Nat := 225522586217116524867641

theorem tailTrace_1317611 : CollatzResearch.WordTrace tailWord_1317611 prefixEnd_1317611 225522586217116524867641 := by
  unfold tailWord_1317611
  simp only [CollatzResearch.WordTrace]
  refine ⟨48057221229527851888352687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32038147486351901258901791 48057221229527851888352687)
  ·
    refine ⟨72085831844291777832529031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48057221229527851888352687 72085831844291777832529031)
    ·
      refine ⟨108128747766437666748793547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72085831844291777832529031 108128747766437666748793547)
      ·
        refine ⟨162193121649656500123190321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108128747766437666748793547 162193121649656500123190321)
        ·
          refine ⟨121644841237242375092392741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 162193121649656500123190321 121644841237242375092392741)
          ·
            refine ⟨22808407731982945329823639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 121644841237242375092392741 22808407731982945329823639)
            ·
              refine ⟨34212611597974417994735459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 22808407731982945329823639 34212611597974417994735459)
              ·
                refine ⟨51318917396961626992103189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 34212611597974417994735459 51318917396961626992103189)
                ·
                  refine ⟨2405574252982576265254837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 51318917396961626992103189 2405574252982576265254837)
                  ·
                    refine ⟨225522586217116524867641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2405574252982576265254837 225522586217116524867641)
                    ·
                      rfl

theorem cell23_1317611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 1, 6, 5].length) (baseStart_1317611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317611 prefixEnd_1317611 := by exact prefixLift 1317611
  have htrace : WordTrace (prefixWord ++ tailWord_1317611) baseStart_1317611 baseEnd_1317611 := by
    simpa [prefixWord, tailWord_1317611, baseEnd_1317611] using wordTrace_append hprefix tailTrace_1317611
  have hstable : (prefixWord ++ tailWord_1317611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317611).length < 2 ^ (prefixWord ++ tailWord_1317611).sum := by decide
  have hdescent : baseEnd_1317611 < baseStart_1317611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317628 : List Nat := [2, 2, 2, 1, 3, 2, 1, 3, 2, 5]
def baseStart_1317628 : Nat := 118140960795 + 1317628 * 2 ^ 59
def prefixEnd_1317628 : Nat := 4983230072969 + 3 ^ 40 * 1317628 * 2
def baseEnd_1317628 : Nat := 225525495940825336030115

theorem tailTrace_1317628 : CollatzResearch.WordTrace tailWord_1317628 prefixEnd_1317628 225525495940825336030115 := by
  unfold tailWord_1317628
  simp only [CollatzResearch.WordTrace]
  refine ⟨24028920635233131895860769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32038560846977509194481025 24028920635233131895860769)
  ·
    refine ⟨18021690476424848921895577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24028920635233131895860769 18021690476424848921895577)
    ·
      refine ⟨13516267857318636691421683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18021690476424848921895577 13516267857318636691421683)
      ·
        refine ⟨20274401785977955037132525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13516267857318636691421683 20274401785977955037132525)
        ·
          refine ⟨7602900669741733138924697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20274401785977955037132525 7602900669741733138924697)
          ·
            refine ⟨5702175502306299854193523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7602900669741733138924697 5702175502306299854193523)
            ·
              refine ⟨8553263253459449781290285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5702175502306299854193523 8553263253459449781290285)
              ·
                refine ⟨3207473720047293667983857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8553263253459449781290285 3207473720047293667983857)
                ·
                  refine ⟨2405605290035470250987893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3207473720047293667983857 2405605290035470250987893)
                  ·
                    refine ⟨225525495940825336030115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2405605290035470250987893 225525495940825336030115)
                    ·
                      rfl

theorem cell23_1317628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_1317628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317628 prefixEnd_1317628 := by exact prefixLift 1317628
  have htrace : WordTrace (prefixWord ++ tailWord_1317628) baseStart_1317628 baseEnd_1317628 := by
    simpa [prefixWord, tailWord_1317628, baseEnd_1317628] using wordTrace_append hprefix tailTrace_1317628
  have hstable : (prefixWord ++ tailWord_1317628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317628).length < 2 ^ (prefixWord ++ tailWord_1317628).sum := by decide
  have hdescent : baseEnd_1317628 < baseStart_1317628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317651 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 5]
def baseStart_1317651 : Nat := 118140960795 + 1317651 * 2 ^ 59
def prefixEnd_1317651 : Nat := 4983230072969 + 3 ^ 40 * 1317651 * 2
def baseEnd_1317651 : Nat := 676588297877529418102739

theorem tailTrace_1317651 : CollatzResearch.WordTrace tailWord_1317651 prefixEnd_1317651 676588297877529418102739 := by
  unfold tailWord_1317651
  simp only [CollatzResearch.WordTrace]
  refine ⟨48058680149382938719808807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32039120099588625813205871 48058680149382938719808807)
  ·
    refine ⟨72088020224074408079713211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48058680149382938719808807 72088020224074408079713211)
    ·
      refine ⟨108132030336111612119569817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72088020224074408079713211 108132030336111612119569817)
      ·
        refine ⟨81099022752083709089677363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108132030336111612119569817 81099022752083709089677363)
        ·
          refine ⟨121648534128125563634516045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81099022752083709089677363 121648534128125563634516045)
          ·
            refine ⟨45618200298047086362943517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121648534128125563634516045 45618200298047086362943517)
            ·
              refine ⟨17106825111767657386103819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 45618200298047086362943517 17106825111767657386103819)
              ·
                refine ⟨25660237667651486079155729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17106825111767657386103819 25660237667651486079155729)
                ·
                  refine ⟨19245178250738614559366797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 25660237667651486079155729 19245178250738614559366797)
                  ·
                    refine ⟨7216941844026980459762549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19245178250738614559366797 7216941844026980459762549)
                    ·
                      refine ⟨676588297877529418102739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7216941844026980459762549 676588297877529418102739)
                      ·
                        rfl

theorem cell23_1317651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_1317651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317651 prefixEnd_1317651 := by exact prefixLift 1317651
  have htrace : WordTrace (prefixWord ++ tailWord_1317651) baseStart_1317651 baseEnd_1317651 := by
    simpa [prefixWord, tailWord_1317651, baseEnd_1317651] using wordTrace_append hprefix tailTrace_1317651
  have hstable : (prefixWord ++ tailWord_1317651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317651).length < 2 ^ (prefixWord ++ tailWord_1317651).sum := by decide
  have hdescent : baseEnd_1317651 < baseStart_1317651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317665 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 2, 4, 2]
def baseStart_1317665 : Nat := 118140960795 + 1317665 * 2 ^ 59
def prefixEnd_1317665 : Nat := 4983230072969 + 3 ^ 40 * 1317665 * 2
def baseEnd_1317665 : Nat := 676595486606692363327675

theorem tailTrace_1317665 : CollatzResearch.WordTrace tailWord_1317665 prefixEnd_1317665 676595486606692363327675 := by
  unfold tailWord_1317665
  simp only [CollatzResearch.WordTrace]
  refine ⟨48059190771332219110818449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32039460514221479407212299 48059190771332219110818449)
  ·
    refine ⟨36044393078499164333113837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48059190771332219110818449 36044393078499164333113837)
    ·
      refine ⟨13516647404437186624917689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 36044393078499164333113837 13516647404437186624917689)
      ·
        refine ⟨10137485553327889968688267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13516647404437186624917689 10137485553327889968688267)
        ·
          refine ⟨15206228329991834953032401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10137485553327889968688267 15206228329991834953032401)
          ·
            refine ⟨11404671247493876214774301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15206228329991834953032401 11404671247493876214774301)
            ·
              refine ⟨4276751717810203580540363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11404671247493876214774301 4276751717810203580540363)
              ·
                refine ⟨6415127576715305370810545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4276751717810203580540363 6415127576715305370810545)
                ·
                  refine ⟨4811345682536479028107909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6415127576715305370810545 4811345682536479028107909)
                  ·
                    refine ⟨902127315475589817770233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4811345682536479028107909 902127315475589817770233)
                    ·
                      refine ⟨676595486606692363327675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 902127315475589817770233 676595486606692363327675)
                      ·
                        rfl

theorem cell23_1317665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_1317665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317665 prefixEnd_1317665 := by exact prefixLift 1317665
  have htrace : WordTrace (prefixWord ++ tailWord_1317665) baseStart_1317665 baseEnd_1317665 := by
    simpa [prefixWord, tailWord_1317665, baseEnd_1317665] using wordTrace_append hprefix tailTrace_1317665
  have hstable : (prefixWord ++ tailWord_1317665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317665).length < 2 ^ (prefixWord ++ tailWord_1317665).sum := by decide
  have hdescent : baseEnd_1317665 < baseStart_1317665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317685 : List Nat := [1, 3, 3, 1, 3, 2, 1, 1, 1, 4, 3]
def baseStart_1317685 : Nat := 118140960795 + 1317685 * 2 ^ 59
def prefixEnd_1317685 : Nat := 4983230072969 + 3 ^ 40 * 1317685 * 2
def baseEnd_1317685 : Nat := 676605756219782285077583

theorem tailTrace_1317685 : CollatzResearch.WordTrace tailWord_1317685 prefixEnd_1317685 676605756219782285077583 := by
  unfold tailWord_1317685
  simp only [CollatzResearch.WordTrace]
  refine ⟨48059920231259762526546509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32039946820839841684364339 48059920231259762526546509)
  ·
    refine ⟨18022470086722410947454941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48059920231259762526546509 18022470086722410947454941)
    ·
      refine ⟨6758426282520904105295603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18022470086722410947454941 6758426282520904105295603)
      ·
        refine ⟨10137639423781356157943405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6758426282520904105295603 10137639423781356157943405)
        ·
          refine ⟨3801614783918008559228777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10137639423781356157943405 3801614783918008559228777)
          ·
            refine ⟨2851211087938506419421583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3801614783918008559228777 2851211087938506419421583)
            ·
              refine ⟨4276816631907759629132375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2851211087938506419421583 4276816631907759629132375)
              ·
                refine ⟨6415224947861639443698563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4276816631907759629132375 6415224947861639443698563)
                ·
                  refine ⟨9622837421792459165547845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6415224947861639443698563 9622837421792459165547845)
                  ·
                    refine ⟨1804282016586086093540221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9622837421792459165547845 1804282016586086093540221)
                    ·
                      refine ⟨676605756219782285077583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1804282016586086093540221 676605756219782285077583)
                      ·
                        rfl

theorem cell23_1317685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_1317685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317685 prefixEnd_1317685 := by exact prefixLift 1317685
  have htrace : WordTrace (prefixWord ++ tailWord_1317685) baseStart_1317685 baseEnd_1317685 := by
    simpa [prefixWord, tailWord_1317685, baseEnd_1317685] using wordTrace_append hprefix tailTrace_1317685
  have hstable : (prefixWord ++ tailWord_1317685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317685).length < 2 ^ (prefixWord ++ tailWord_1317685).sum := by decide
  have hdescent : baseEnd_1317685 < baseStart_1317685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317705 : List Nat := [1, 2, 1, 1, 2, 7, 1, 2, 6]
def baseStart_1317705 : Nat := 118140960795 + 1317705 * 2 ^ 59
def prefixEnd_1317705 : Nat := 4983230072969 + 3 ^ 40 * 1317705 * 2
def baseEnd_1317705 : Nat := 75179558425874689647499

theorem tailTrace_1317705 : CollatzResearch.WordTrace tailWord_1317705 prefixEnd_1317705 75179558425874689647499 := by
  unfold tailWord_1317705
  simp only [CollatzResearch.WordTrace]
  refine ⟨48060649691187305942274569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32040433127458203961516379 48060649691187305942274569)
  ·
    refine ⟨36045487268390479456705927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48060649691187305942274569 36045487268390479456705927)
    ·
      refine ⟨54068230902585719185058891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36045487268390479456705927 54068230902585719185058891)
      ·
        refine ⟨81102346353878578777588337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54068230902585719185058891 81102346353878578777588337)
        ·
          refine ⟨60826759765408934083191253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 81102346353878578777588337 60826759765408934083191253)
          ·
            refine ⟨1425627182001771892574795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 60826759765408934083191253 1425627182001771892574795)
            ·
              refine ⟨2138440773002657838862193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1425627182001771892574795 2138440773002657838862193)
              ·
                refine ⟨1603830579751993379146645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2138440773002657838862193 1603830579751993379146645)
                ·
                  refine ⟨75179558425874689647499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1603830579751993379146645 75179558425874689647499)
                  ·
                    rfl

theorem cell23_1317705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 6].length) (baseStart_1317705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317705 prefixEnd_1317705 := by exact prefixLift 1317705
  have htrace : WordTrace (prefixWord ++ tailWord_1317705) baseStart_1317705 baseEnd_1317705 := by
    simpa [prefixWord, tailWord_1317705, baseEnd_1317705] using wordTrace_append hprefix tailTrace_1317705
  have hstable : (prefixWord ++ tailWord_1317705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317705).length < 2 ^ (prefixWord ++ tailWord_1317705).sum := by decide
  have hdescent : baseEnd_1317705 < baseStart_1317705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317708 : List Nat := [2, 2, 1, 3, 3, 1, 1, 1, 1, 2, 6]
def baseStart_1317708 : Nat := 118140960795 + 1317708 * 2 ^ 59
def prefixEnd_1317708 : Nat := 4983230072969 + 3 ^ 40 * 1317708 * 2
def baseEnd_1317708 : Nat := 676617566274835695089977

theorem tailTrace_1317708 : CollatzResearch.WordTrace tailWord_1317708 prefixEnd_1317708 676617566274835695089977 := by
  unfold tailWord_1317708
  simp only [CollatzResearch.WordTrace]
  refine ⟨24030379555088218727316889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32040506073450958303089185 24030379555088218727316889)
  ·
    refine ⟨18022784666316164045487667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24030379555088218727316889 18022784666316164045487667)
    ·
      refine ⟨27034176999474246068231501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18022784666316164045487667 27034176999474246068231501)
      ·
        refine ⟨10137816374802842275586813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27034176999474246068231501 10137816374802842275586813)
        ·
          refine ⟨3801681140551065853345055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10137816374802842275586813 3801681140551065853345055)
          ·
            refine ⟨5702521710826598780017583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3801681140551065853345055 5702521710826598780017583)
            ·
              refine ⟨8553782566239898170026375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5702521710826598780017583 8553782566239898170026375)
              ·
                refine ⟨12830673849359847255039563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8553782566239898170026375 12830673849359847255039563)
                ·
                  refine ⟨19246010774039770882559345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12830673849359847255039563 19246010774039770882559345)
                  ·
                    refine ⟨14434508080529828161919509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19246010774039770882559345 14434508080529828161919509)
                    ·
                      refine ⟨676617566274835695089977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14434508080529828161919509 676617566274835695089977)
                      ·
                        rfl

theorem cell23_1317708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 1, 1, 1, 2, 6].length) (baseStart_1317708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317708 prefixEnd_1317708 := by exact prefixLift 1317708
  have htrace : WordTrace (prefixWord ++ tailWord_1317708) baseStart_1317708 baseEnd_1317708 := by
    simpa [prefixWord, tailWord_1317708, baseEnd_1317708] using wordTrace_append hprefix tailTrace_1317708
  have hstable : (prefixWord ++ tailWord_1317708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317708).length < 2 ^ (prefixWord ++ tailWord_1317708).sum := by decide
  have hdescent : baseEnd_1317708 < baseStart_1317708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317709 : List Nat := [1, 6, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_1317709 : Nat := 118140960795 + 1317709 * 2 ^ 59
def prefixEnd_1317709 : Nat := 4983230072969 + 3 ^ 40 * 1317709 * 2
def baseEnd_1317709 : Nat := 225539359918496730392491

theorem tailTrace_1317709 : CollatzResearch.WordTrace tailWord_1317709 prefixEnd_1317709 225539359918496730392491 := by
  unfold tailWord_1317709
  simp only [CollatzResearch.WordTrace]
  refine ⟨48060795583172814625420181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32040530388781876416946787 48060795583172814625420181)
  ·
    refine ⟨2252849792961225685566571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 48060795583172814625420181 2252849792961225685566571)
    ·
      refine ⟨3379274689441838528349857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2252849792961225685566571 3379274689441838528349857)
      ·
        refine ⟨2534456017081378896262393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3379274689441838528349857 2534456017081378896262393)
        ·
          refine ⟨1900842012811034172196795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2534456017081378896262393 1900842012811034172196795)
          ·
            refine ⟨2851263019216551258295193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1900842012811034172196795 2851263019216551258295193)
            ·
              refine ⟨2138447264412413443721395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2851263019216551258295193 2138447264412413443721395)
              ·
                refine ⟨3207670896618620165582093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2138447264412413443721395 3207670896618620165582093)
                ·
                  refine ⟨1202876586231982562093285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3207670896618620165582093 1202876586231982562093285)
                  ·
                    refine ⟨225539359918496730392491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1202876586231982562093285 225539359918496730392491)
                    ·
                      rfl

theorem cell23_1317709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_1317709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317709 prefixEnd_1317709 := by exact prefixLift 1317709
  have htrace : WordTrace (prefixWord ++ tailWord_1317709) baseStart_1317709 baseEnd_1317709 := by
    simpa [prefixWord, tailWord_1317709, baseEnd_1317709] using wordTrace_append hprefix tailTrace_1317709
  have hstable : (prefixWord ++ tailWord_1317709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317709).length < 2 ^ (prefixWord ++ tailWord_1317709).sum := by decide
  have hdescent : baseEnd_1317709 < baseStart_1317709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317732 : List Nat := [2, 3, 1, 1, 4, 1, 2, 2, 3, 1, 3]
def baseStart_1317732 : Nat := 118140960795 + 1317732 * 2 ^ 59
def prefixEnd_1317732 : Nat := 4983230072969 + 3 ^ 40 * 1317732 * 2
def baseEnd_1317732 : Nat := 676629889810543601189867

theorem tailTrace_1317732 : CollatzResearch.WordTrace tailWord_1317732 prefixEnd_1317732 676629889810543601189867 := by
  unfold tailWord_1317732
  simp only [CollatzResearch.WordTrace]
  refine ⟨24030817231044744776753725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32041089641392993035671633 24030817231044744776753725)
  ·
    refine ⟨9011556461641779291282647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24030817231044744776753725 9011556461641779291282647)
    ·
      refine ⟨13517334692462668936923971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9011556461641779291282647 13517334692462668936923971)
      ·
        refine ⟨20276002038694003405385957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13517334692462668936923971 20276002038694003405385957)
        ·
          refine ⟨3801750382255125638509867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20276002038694003405385957 3801750382255125638509867)
          ·
            refine ⟨5702625573382688457764801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3801750382255125638509867 5702625573382688457764801)
            ·
              refine ⟨4276969180037016343323601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5702625573382688457764801 4276969180037016343323601)
              ·
                refine ⟨3207726885027762257492701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4276969180037016343323601 3207726885027762257492701)
                ·
                  refine ⟨1202897581885410846559763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3207726885027762257492701 1202897581885410846559763)
                  ·
                    refine ⟨1804346372828116269839645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1202897581885410846559763 1804346372828116269839645)
                    ·
                      refine ⟨676629889810543601189867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1804346372828116269839645 676629889810543601189867)
                      ·
                        rfl

theorem cell23_1317732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 2, 2, 3, 1, 3].length) (baseStart_1317732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317732 prefixEnd_1317732 := by exact prefixLift 1317732
  have htrace : WordTrace (prefixWord ++ tailWord_1317732) baseStart_1317732 baseEnd_1317732 := by
    simpa [prefixWord, tailWord_1317732, baseEnd_1317732] using wordTrace_append hprefix tailTrace_1317732
  have hstable : (prefixWord ++ tailWord_1317732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317732).length < 2 ^ (prefixWord ++ tailWord_1317732).sum := by decide
  have hdescent : baseEnd_1317732 < baseStart_1317732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317735 : List Nat := [1, 1, 5, 1, 2, 2, 1, 4, 1, 5]
def baseStart_1317735 : Nat := 118140960795 + 1317735 * 2 ^ 59
def prefixEnd_1317735 : Nat := 4983230072969 + 3 ^ 40 * 1317735 * 2
def baseEnd_1317735 : Nat := 225543810084169029817451

theorem tailTrace_1317735 : CollatzResearch.WordTrace tailWord_1317735 prefixEnd_1317735 225543810084169029817451 := by
  unfold tailWord_1317735
  simp only [CollatzResearch.WordTrace]
  refine ⟨48061743881078621065866659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32041162587385747377244439 48061743881078621065866659)
  ·
    refine ⟨72092615821617931598799989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48061743881078621065866659 72092615821617931598799989)
    ·
      refine ⟨6758682733276681087387499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 72092615821617931598799989 6758682733276681087387499)
      ·
        refine ⟨10138024099915021631081249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6758682733276681087387499 10138024099915021631081249)
        ·
          refine ⟨7603518074936266223310937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10138024099915021631081249 7603518074936266223310937)
          ·
            refine ⟨5702638556202199667483203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7603518074936266223310937 5702638556202199667483203)
            ·
              refine ⟨8553957834303299501224805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5702638556202199667483203 8553957834303299501224805)
              ·
                refine ⟨1603867093931868656479651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8553957834303299501224805 1603867093931868656479651)
                ·
                  refine ⟨2405800640897802984719477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1603867093931868656479651 2405800640897802984719477)
                  ·
                    refine ⟨225543810084169029817451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2405800640897802984719477 225543810084169029817451)
                    ·
                      rfl

theorem cell23_1317735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 4, 1, 5].length) (baseStart_1317735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317735 prefixEnd_1317735 := by exact prefixLift 1317735
  have htrace : WordTrace (prefixWord ++ tailWord_1317735) baseStart_1317735 baseEnd_1317735 := by
    simpa [prefixWord, tailWord_1317735, baseEnd_1317735] using wordTrace_append hprefix tailTrace_1317735
  have hstable : (prefixWord ++ tailWord_1317735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317735).length < 2 ^ (prefixWord ++ tailWord_1317735).sum := by decide
  have hdescent : baseEnd_1317735 < baseStart_1317735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317755 : List Nat := [1, 1, 1, 1, 1, 5, 4, 3, 1, 1, 4]
def baseStart_1317755 : Nat := 118140960795 + 1317755 * 2 ^ 59
def prefixEnd_1317755 : Nat := 4983230072969 + 3 ^ 40 * 1317755 * 2
def baseEnd_1317755 : Nat := 676641699865597011202261

theorem tailTrace_1317755 : CollatzResearch.WordTrace tailWord_1317755 prefixEnd_1317755 676641699865597011202261 := by
  unfold tailWord_1317755
  simp only [CollatzResearch.WordTrace]
  refine ⟨48062473341006164481594719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32041648894004109654396479 48062473341006164481594719)
  ·
    refine ⟨72093710011509246722392079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48062473341006164481594719 72093710011509246722392079)
    ·
      refine ⟨108140565017263870083588119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72093710011509246722392079 108140565017263870083588119)
      ·
        refine ⟨162210847525895805125382179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 108140565017263870083588119 162210847525895805125382179)
        ·
          refine ⟨243316271288843707688073269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 162210847525895805125382179 243316271288843707688073269)
          ·
            refine ⟨22810900433329097595756869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 243316271288843707688073269 22810900433329097595756869)
            ·
              refine ⟨4277043831249205799204413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 22810900433329097595756869 4277043831249205799204413)
              ·
                refine ⟨1603891436718452174701655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4277043831249205799204413 1603891436718452174701655)
                ·
                  refine ⟨2405837155077678262052483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1603891436718452174701655 2405837155077678262052483)
                  ·
                    refine ⟨3608755732616517393078725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2405837155077678262052483 3608755732616517393078725)
                    ·
                      refine ⟨676641699865597011202261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3608755732616517393078725 676641699865597011202261)
                      ·
                        rfl

theorem cell23_1317755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 3, 1, 1, 4].length) (baseStart_1317755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317755 prefixEnd_1317755 := by exact prefixLift 1317755
  have htrace : WordTrace (prefixWord ++ tailWord_1317755) baseStart_1317755 baseEnd_1317755 := by
    simpa [prefixWord, tailWord_1317755, baseEnd_1317755] using wordTrace_append hprefix tailTrace_1317755
  have hstable : (prefixWord ++ tailWord_1317755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317755).length < 2 ^ (prefixWord ++ tailWord_1317755).sum := by decide
  have hdescent : baseEnd_1317755 < baseStart_1317755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317765 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 4, 4]
def baseStart_1317765 : Nat := 118140960795 + 1317765 * 2 ^ 59
def prefixEnd_1317765 : Nat := 4983230072969 + 3 ^ 40 * 1317765 * 2
def baseEnd_1317765 : Nat := 225548944890713990692405

theorem tailTrace_1317765 : CollatzResearch.WordTrace tailWord_1317765 prefixEnd_1317765 225548944890713990692405 := by
  unfold tailWord_1317765
  simp only [CollatzResearch.WordTrace]
  refine ⟨48062838070969936189458749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32041892047313290792972499 48062838070969936189458749)
  ·
    refine ⟨18023564276613726071047031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48062838070969936189458749 18023564276613726071047031)
    ·
      refine ⟨27035346414920589106570547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18023564276613726071047031 27035346414920589106570547)
      ·
        refine ⟨40553019622380883659855821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27035346414920589106570547 40553019622380883659855821)
        ·
          refine ⟨15207382358392831372445933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40553019622380883659855821 15207382358392831372445933)
          ·
            refine ⟨5702768384397311764667225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15207382358392831372445933 5702768384397311764667225)
            ·
              refine ⟨4277076288297983823500419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5702768384397311764667225 4277076288297983823500419)
              ·
                refine ⟨6415614432446975735250629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4277076288297983823500419 6415614432446975735250629)
                ·
                  refine ⟨1202927706083807950359493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6415614432446975735250629 1202927706083807950359493)
                  ·
                    refine ⟨225548944890713990692405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1202927706083807950359493 225548944890713990692405)
                    ·
                      rfl

theorem cell23_1317765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 4, 4].length) (baseStart_1317765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317765 prefixEnd_1317765 := by exact prefixLift 1317765
  have htrace : WordTrace (prefixWord ++ tailWord_1317765) baseStart_1317765 baseEnd_1317765 := by
    simpa [prefixWord, tailWord_1317765, baseEnd_1317765] using wordTrace_append hprefix tailTrace_1317765
  have hstable : (prefixWord ++ tailWord_1317765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317765).length < 2 ^ (prefixWord ++ tailWord_1317765).sum := by decide
  have hdescent : baseEnd_1317765 < baseStart_1317765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317792 : List Nat := [2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 3]
def baseStart_1317792 : Nat := 118140960795 + 1317792 * 2 ^ 59
def prefixEnd_1317792 : Nat := 4983230072969 + 3 ^ 40 * 1317792 * 2
def baseEnd_1317792 : Nat := 676660698649813366439591

theorem tailTrace_1317792 : CollatzResearch.WordTrace tailWord_1317792 prefixEnd_1317792 676660698649813366439591 := by
  unfold tailWord_1317792
  simp only [CollatzResearch.WordTrace]
  refine ⟨24031911420936059900345815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32042548561248079867127753 24031911420936059900345815)
  ·
    refine ⟨36047867131404089850518723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24031911420936059900345815 36047867131404089850518723)
    ·
      refine ⟨54071800697106134775778085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36047867131404089850518723 54071800697106134775778085)
      ·
        refine ⟨10138462630707400270458391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54071800697106134775778085 10138462630707400270458391)
        ·
          refine ⟨15207693946061100405687587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10138462630707400270458391 15207693946061100405687587)
          ·
            refine ⟨22811540919091650608531381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15207693946061100405687587 22811540919091650608531381)
            ·
              refine ⟨2138581961164842244549817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22811540919091650608531381 2138581961164842244549817)
              ·
                refine ⟨1603936470873631683412363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2138581961164842244549817 1603936470873631683412363)
                ·
                  refine ⟨2405904706310447525118545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1603936470873631683412363 2405904706310447525118545)
                  ·
                    refine ⟨1804428529732835643838909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2405904706310447525118545 1804428529732835643838909)
                    ·
                      refine ⟨676660698649813366439591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1804428529732835643838909 676660698649813366439591)
                      ·
                        rfl

theorem cell23_1317792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_1317792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317792 prefixEnd_1317792 := by exact prefixLift 1317792
  have htrace : WordTrace (prefixWord ++ tailWord_1317792) baseStart_1317792 baseEnd_1317792 := by
    simpa [prefixWord, tailWord_1317792, baseEnd_1317792] using wordTrace_append hprefix tailTrace_1317792
  have hstable : (prefixWord ++ tailWord_1317792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317792).length < 2 ^ (prefixWord ++ tailWord_1317792).sum := by decide
  have hdescent : baseEnd_1317792 < baseStart_1317792 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317809 : List Nat := [1, 2, 2, 4, 4, 1, 1, 1, 1, 1, 5]
def baseStart_1317809 : Nat := 118140960795 + 1317809 * 2 ^ 59
def prefixEnd_1317809 : Nat := 4983230072969 + 3 ^ 40 * 1317809 * 2
def baseEnd_1317809 : Nat := 676669427820939799927013

theorem tailTrace_1317809 : CollatzResearch.WordTrace tailWord_1317809 prefixEnd_1317809 676669427820939799927013 := by
  unfold tailWord_1317809
  simp only [CollatzResearch.WordTrace]
  refine ⟨48064442882810531704060481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32042961921873687802706987 48064442882810531704060481)
  ·
    refine ⟨36048332162107898778045361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48064442882810531704060481 36048332162107898778045361)
    ·
      refine ⟨27036249121580924083534021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36048332162107898778045361 27036249121580924083534021)
      ·
        refine ⟨5069296710296423265662629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27036249121580924083534021 5069296710296423265662629)
        ·
          refine ⟨950493133180579362311743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5069296710296423265662629 950493133180579362311743)
          ·
            refine ⟨1425739699770869043467615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950493133180579362311743 1425739699770869043467615)
            ·
              refine ⟨2138609549656303565201423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1425739699770869043467615 2138609549656303565201423)
              ·
                refine ⟨3207914324484455347802135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2138609549656303565201423 3207914324484455347802135)
                ·
                  refine ⟨4811871486726683021703203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3207914324484455347802135 4811871486726683021703203)
                  ·
                    refine ⟨7217807230090024532554805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4811871486726683021703203 7217807230090024532554805)
                    ·
                      refine ⟨676669427820939799927013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7217807230090024532554805 676669427820939799927013)
                      ·
                        rfl

theorem cell23_1317809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 1, 1, 5].length) (baseStart_1317809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317809 prefixEnd_1317809 := by exact prefixLift 1317809
  have htrace : WordTrace (prefixWord ++ tailWord_1317809) baseStart_1317809 baseEnd_1317809 := by
    simpa [prefixWord, tailWord_1317809, baseEnd_1317809] using wordTrace_append hprefix tailTrace_1317809
  have hstable : (prefixWord ++ tailWord_1317809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317809).length < 2 ^ (prefixWord ++ tailWord_1317809).sum := by decide
  have hdescent : baseEnd_1317809 < baseStart_1317809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317866 : List Nat := [3, 1, 3, 1, 2, 2, 4, 1, 1, 3, 2]
def baseStart_1317866 : Nat := 118140960795 + 1317866 * 2 ^ 59
def prefixEnd_1317866 : Nat := 4983230072969 + 3 ^ 40 * 1317866 * 2
def baseEnd_1317866 : Nat := 676698696218246076914251

theorem tailTrace_1317866 : CollatzResearch.WordTrace tailWord_1317866 prefixEnd_1317866 676698696218246076914251 := by
  unfold tailWord_1317866
  simp only [CollatzResearch.WordTrace]
  refine ⟨12016630460901007609721363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32044347895736020292590301 12016630460901007609721363)
  ·
    refine ⟨18024945691351511414582045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12016630460901007609721363 18024945691351511414582045)
    ·
      refine ⟨6759354634256816780468267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18024945691351511414582045 6759354634256816780468267)
      ·
        refine ⟨10139031951385225170702401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6759354634256816780468267 10139031951385225170702401)
        ·
          refine ⟨7604273963538918878026801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10139031951385225170702401 7604273963538918878026801)
          ·
            refine ⟨5703205472654189158520101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7604273963538918878026801 5703205472654189158520101)
            ·
              refine ⟨1069351026122660467222519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5703205472654189158520101 1069351026122660467222519)
              ·
                refine ⟨1604026539183990700833779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1069351026122660467222519 1604026539183990700833779)
                ·
                  refine ⟨2406039808775986051250669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1604026539183990700833779 2406039808775986051250669)
                  ·
                    refine ⟨902264928290994769219001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2406039808775986051250669 902264928290994769219001)
                    ·
                      refine ⟨676698696218246076914251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 902264928290994769219001 676698696218246076914251)
                      ·
                        rfl

theorem cell23_1317866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_1317866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317866 prefixEnd_1317866 := by exact prefixLift 1317866
  have htrace : WordTrace (prefixWord ++ tailWord_1317866) baseStart_1317866 baseEnd_1317866 := by
    simpa [prefixWord, tailWord_1317866, baseEnd_1317866] using wordTrace_append hprefix tailTrace_1317866
  have hstable : (prefixWord ++ tailWord_1317866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317866).length < 2 ^ (prefixWord ++ tailWord_1317866).sum := by decide
  have hdescent : baseEnd_1317866 < baseStart_1317866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317890 : List Nat := [3, 4, 1, 3, 1, 1, 3, 1, 2, 1, 3]
def baseStart_1317890 : Nat := 118140960795 + 1317890 * 2 ^ 59
def prefixEnd_1317890 : Nat := 4983230072969 + 3 ^ 40 * 1317890 * 2
def baseEnd_1317890 : Nat := 676711019753953983014141

theorem tailTrace_1317890 : CollatzResearch.WordTrace tailWord_1317890 prefixEnd_1317890 676711019753953983014141 := by
  unfold tailWord_1317890
  simp only [CollatzResearch.WordTrace]
  refine ⟨12016849298879270634439781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32044931463678055025172749 12016849298879270634439781)
  ·
    refine ⟨2253159243539863243957459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12016849298879270634439781 2253159243539863243957459)
    ·
      refine ⟨3379738865309794865936189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2253159243539863243957459 3379738865309794865936189)
      ·
        refine ⟨1267402074491173074726071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3379738865309794865936189 1267402074491173074726071)
        ·
          refine ⟨1901103111736759612089107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1267402074491173074726071 1901103111736759612089107)
          ·
            refine ⟨2851654667605139418133661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1901103111736759612089107 2851654667605139418133661)
            ·
              refine ⟨1069370500351927281800123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2851654667605139418133661 1069370500351927281800123)
              ·
                refine ⟨1604055750527890922700185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1069370500351927281800123 1604055750527890922700185)
                ·
                  refine ⟨1203041812895918192025139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1604055750527890922700185 1203041812895918192025139)
                  ·
                    refine ⟨1804562719343877288037709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1203041812895918192025139 1804562719343877288037709)
                    ·
                      refine ⟨676711019753953983014141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1804562719343877288037709 676711019753953983014141)
                      ·
                        rfl

theorem cell23_1317890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_1317890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317890 prefixEnd_1317890 := by exact prefixLift 1317890
  have htrace : WordTrace (prefixWord ++ tailWord_1317890) baseStart_1317890 baseEnd_1317890 := by
    simpa [prefixWord, tailWord_1317890, baseEnd_1317890] using wordTrace_append hprefix tailTrace_1317890
  have hstable : (prefixWord ++ tailWord_1317890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317890).length < 2 ^ (prefixWord ++ tailWord_1317890).sum := by decide
  have hdescent : baseEnd_1317890 < baseStart_1317890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317919 : List Nat := [1, 1, 2, 4, 1, 5, 1, 3, 5]
def baseStart_1317919 : Nat := 118140960795 + 1317919 * 2 ^ 59
def prefixEnd_1317919 : Nat := 4983230072969 + 3 ^ 40 * 1317919 * 2
def baseEnd_1317919 : Nat := 75191767854770485505723

theorem tailTrace_1317919 : CollatzResearch.WordTrace tailWord_1317919 prefixEnd_1317919 75191767854770485505723 := by
  unfold tailWord_1317919
  simp only [CollatzResearch.WordTrace]
  refine ⟨48068454912412020490564811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32045636608274680327043207 48068454912412020490564811)
  ·
    refine ⟨72102682368618030735847217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48068454912412020490564811 72102682368618030735847217)
    ·
      refine ⟨54077011776463523051885413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72102682368618030735847217 54077011776463523051885413)
      ·
        refine ⟨10139439708086910572228515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54077011776463523051885413 10139439708086910572228515)
        ·
          refine ⟨15209159562130365858342773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10139439708086910572228515 15209159562130365858342773)
          ·
            refine ⟨1425858708949721799219635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 15209159562130365858342773 1425858708949721799219635)
            ·
              refine ⟨2138788063424582698829453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1425858708949721799219635 2138788063424582698829453)
              ·
                refine ⟨802045523784218512061045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2138788063424582698829453 802045523784218512061045)
                ·
                  refine ⟨75191767854770485505723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 802045523784218512061045 75191767854770485505723)
                  ·
                    rfl

theorem cell23_1317919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 5].length) (baseStart_1317919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317919 prefixEnd_1317919 := by exact prefixLift 1317919
  have htrace : WordTrace (prefixWord ++ tailWord_1317919) baseStart_1317919 baseEnd_1317919 := by
    simpa [prefixWord, tailWord_1317919, baseEnd_1317919] using wordTrace_append hprefix tailTrace_1317919
  have hstable : (prefixWord ++ tailWord_1317919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317919).length < 2 ^ (prefixWord ++ tailWord_1317919).sum := by decide
  have hdescent : baseEnd_1317919 < baseStart_1317919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317925 : List Nat := [1, 3, 1, 2, 2, 2, 2, 2, 1, 2, 5]
def baseStart_1317925 : Nat := 118140960795 + 1317925 * 2 ^ 59
def prefixEnd_1317925 : Nat := 4983230072969 + 3 ^ 40 * 1317925 * 2
def baseEnd_1317925 : Nat := 676728991576861346076479

theorem tailTrace_1317925 : CollatzResearch.WordTrace tailWord_1317925 prefixEnd_1317925 676728991576861346076479 := by
  unfold tailWord_1317925
  simp only [CollatzResearch.WordTrace]
  refine ⟨48068673750390283515283229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32045782500260189010188819 48068673750390283515283229)
  ·
    refine ⟨18025752656396356318231211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48068673750390283515283229 18025752656396356318231211)
    ·
      refine ⟨27038628984594534477346817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18025752656396356318231211 27038628984594534477346817)
      ·
        refine ⟨20278971738445900858010113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27038628984594534477346817 20278971738445900858010113)
        ·
          refine ⟨15209228803834425643507585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20278971738445900858010113 15209228803834425643507585)
          ·
            refine ⟨11406921602875819232630689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15209228803834425643507585 11406921602875819232630689)
            ·
              refine ⟨8555191202156864424473017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11406921602875819232630689 8555191202156864424473017)
              ·
                refine ⟨6416393401617648318354763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8555191202156864424473017 6416393401617648318354763)
                ·
                  refine ⟨9624590102426472477532145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6416393401617648318354763 9624590102426472477532145)
                  ·
                    refine ⟨7218442576819854358149109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9624590102426472477532145 7218442576819854358149109)
                    ·
                      refine ⟨676728991576861346076479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7218442576819854358149109 676728991576861346076479)
                      ·
                        rfl

theorem cell23_1317925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_1317925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317925 prefixEnd_1317925 := by exact prefixLift 1317925
  have htrace : WordTrace (prefixWord ++ tailWord_1317925) baseStart_1317925 baseEnd_1317925 := by
    simpa [prefixWord, tailWord_1317925, baseEnd_1317925] using wordTrace_append hprefix tailTrace_1317925
  have hstable : (prefixWord ++ tailWord_1317925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317925).length < 2 ^ (prefixWord ++ tailWord_1317925).sum := by decide
  have hdescent : baseEnd_1317925 < baseStart_1317925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317942 : List Nat := [5, 1, 2, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_1317942 : Nat := 118140960795 + 1317942 * 2 ^ 59
def prefixEnd_1317942 : Nat := 4983230072969 + 3 ^ 40 * 1317942 * 2
def baseEnd_1317942 : Nat := 676737720747987779563901

theorem tailTrace_1317942 : CollatzResearch.WordTrace tailWord_1317942 prefixEnd_1317942 676737720747987779563901 := by
  unfold tailWord_1317942
  simp only [CollatzResearch.WordTrace]
  refine ⟨3004330861958043463665755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32046195860885796945768053 3004330861958043463665755)
  ·
    refine ⟨4506496292937065195498633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3004330861958043463665755 4506496292937065195498633)
    ·
      refine ⟨3379872219702798896623975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4506496292937065195498633 3379872219702798896623975)
      ·
        refine ⟨5069808329554198344935963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3379872219702798896623975 5069808329554198344935963)
        ·
          refine ⟨7604712494331297517403945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5069808329554198344935963 7604712494331297517403945)
          ·
            refine ⟨5703534370748473138052959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7604712494331297517403945 5703534370748473138052959)
            ·
              refine ⟨8555301556122709707079439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5703534370748473138052959 8555301556122709707079439)
              ·
                refine ⟨12832952334184064560619159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8555301556122709707079439 12832952334184064560619159)
                ·
                  refine ⟨19249428501276096840928739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12832952334184064560619159 19249428501276096840928739)
                  ·
                    refine ⟨28874142751914145261393109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19249428501276096840928739 28874142751914145261393109)
                    ·
                      refine ⟨676737720747987779563901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 28874142751914145261393109 676737720747987779563901)
                      ·
                        rfl

theorem cell23_1317942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_1317942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317942 prefixEnd_1317942 := by exact prefixLift 1317942
  have htrace : WordTrace (prefixWord ++ tailWord_1317942) baseStart_1317942 baseEnd_1317942 := by
    simpa [prefixWord, tailWord_1317942, baseEnd_1317942] using wordTrace_append hprefix tailTrace_1317942
  have hstable : (prefixWord ++ tailWord_1317942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317942).length < 2 ^ (prefixWord ++ tailWord_1317942).sum := by decide
  have hdescent : baseEnd_1317942 < baseStart_1317942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317952 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 1, 6, 2]
def baseStart_1317952 : Nat := 118140960795 + 1317952 * 2 ^ 59
def prefixEnd_1317952 : Nat := 4983230072969 + 3 ^ 40 * 1317952 * 2
def baseEnd_1317952 : Nat := 676742855554532740438855

theorem tailTrace_1317952 : CollatzResearch.WordTrace tailWord_1317952 prefixEnd_1317952 676742855554532740438855 := by
  unfold tailWord_1317952
  simp only [CollatzResearch.WordTrace]
  refine ⟨24034829260646233563258055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32046439014194978084344073 24034829260646233563258055)
  ·
    refine ⟨36052243890969350344887083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24034829260646233563258055 36052243890969350344887083)
    ·
      refine ⟨54078365836454025517330625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36052243890969350344887083 54078365836454025517330625)
      ·
        refine ⟨40558774377340519137997969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54078365836454025517330625 40558774377340519137997969)
        ·
          refine ⟨30419080783005389353498477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40558774377340519137997969 30419080783005389353498477)
          ·
            refine ⟨11407155293627021007561929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30419080783005389353498477 11407155293627021007561929)
            ·
              refine ⟨8555366470220265755671447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11407155293627021007561929 8555366470220265755671447)
              ·
                refine ⟨12833049705330398633507171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8555366470220265755671447 12833049705330398633507171)
                ·
                  refine ⟨19249574557995597950260757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12833049705330398633507171 19249574557995597950260757)
                  ·
                    refine ⟨902323807406043653918473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19249574557995597950260757 902323807406043653918473)
                    ·
                      refine ⟨676742855554532740438855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 902323807406043653918473 676742855554532740438855)
                      ·
                        rfl

theorem cell23_1317952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 1, 6, 2].length) (baseStart_1317952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317952 prefixEnd_1317952 := by exact prefixLift 1317952
  have htrace : WordTrace (prefixWord ++ tailWord_1317952) baseStart_1317952 baseEnd_1317952 := by
    simpa [prefixWord, tailWord_1317952, baseEnd_1317952] using wordTrace_append hprefix tailTrace_1317952
  have hstable : (prefixWord ++ tailWord_1317952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317952).length < 2 ^ (prefixWord ++ tailWord_1317952).sum := by decide
  have hdescent : baseEnd_1317952 < baseStart_1317952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317962 : List Nat := [3, 1, 2, 1, 1, 2, 2, 4, 3, 4]
def baseStart_1317962 : Nat := 118140960795 + 1317962 * 2 ^ 59
def prefixEnd_1317962 : Nat := 4983230072969 + 3 ^ 40 * 1317962 * 2
def baseEnd_1317962 : Nat := 225582663453692567104603

theorem tailTrace_1317962 : CollatzResearch.WordTrace tailWord_1317962 prefixEnd_1317962 225582663453692567104603 := by
  unfold tailWord_1317962
  simp only [CollatzResearch.WordTrace]
  refine ⟨12017505812814059708595035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32046682167504159222920093 12017505812814059708595035)
  ·
    refine ⟨18026258719221089562892553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12017505812814059708595035 18026258719221089562892553)
    ·
      refine ⟨13519694039415817172169415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18026258719221089562892553 13519694039415817172169415)
      ·
        refine ⟨20279541059123725758254123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13519694039415817172169415 20279541059123725758254123)
        ·
          refine ⟨30419311588685588637381185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20279541059123725758254123 30419311588685588637381185)
          ·
            refine ⟨22814483691514191478035889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30419311588685588637381185 22814483691514191478035889)
            ·
              refine ⟨17110862768635643608526917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22814483691514191478035889 17110862768635643608526917)
              ·
                refine ⟨3208286769119183176598797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17110862768635643608526917 3208286769119183176598797)
                ·
                  refine ⟨1203107538419693691224549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3208286769119183176598797 1203107538419693691224549)
                  ·
                    refine ⟨225582663453692567104603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1203107538419693691224549 225582663453692567104603)
                    ·
                      rfl

theorem cell23_1317962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_1317962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317962 prefixEnd_1317962 := by exact prefixLift 1317962
  have htrace : WordTrace (prefixWord ++ tailWord_1317962) baseStart_1317962 baseEnd_1317962 := by
    simpa [prefixWord, tailWord_1317962, baseEnd_1317962] using wordTrace_append hprefix tailTrace_1317962
  have hstable : (prefixWord ++ tailWord_1317962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317962).length < 2 ^ (prefixWord ++ tailWord_1317962).sum := by decide
  have hdescent : baseEnd_1317962 < baseStart_1317962 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1317972 : List Nat := [2, 4, 1, 1, 1, 1, 2, 3, 1, 4, 3]
def baseStart_1317972 : Nat := 118140960795 + 1317972 * 2 ^ 59
def prefixEnd_1317972 : Nat := 4983230072969 + 3 ^ 40 * 1317972 * 2
def baseEnd_1317972 : Nat := 676753125167622662188763

theorem tailTrace_1317972 : CollatzResearch.WordTrace tailWord_1317972 prefixEnd_1317972 676753125167622662188763 := by
  unfold tailWord_1317972
  simp only [CollatzResearch.WordTrace]
  refine ⟨24035193990610005271122085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32046925320813340361496113 24035193990610005271122085)
  ·
    refine ⟨4506598873239375988335391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 24035193990610005271122085 4506598873239375988335391)
    ·
      refine ⟨6759898309859063982503087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4506598873239375988335391 6759898309859063982503087)
      ·
        refine ⟨10139847464788595973754631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6759898309859063982503087 10139847464788595973754631)
        ·
          refine ⟨15209771197182893960631947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10139847464788595973754631 15209771197182893960631947)
          ·
            refine ⟨22814656795774340940947921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15209771197182893960631947 22814656795774340940947921)
            ·
              refine ⟨17110992596830755705710941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22814656795774340940947921 17110992596830755705710941)
              ·
                refine ⟨6416622223811533389641603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17110992596830755705710941 6416622223811533389641603)
                ·
                  refine ⟨9624933335717300084462405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6416622223811533389641603 9624933335717300084462405)
                  ·
                    refine ⟨1804675000446993765836701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9624933335717300084462405 1804675000446993765836701)
                    ·
                      refine ⟨676753125167622662188763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1804675000446993765836701 676753125167622662188763)
                      ·
                        rfl

theorem cell23_1317972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_1317972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1317972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1317972 prefixEnd_1317972 := by exact prefixLift 1317972
  have htrace : WordTrace (prefixWord ++ tailWord_1317972) baseStart_1317972 baseEnd_1317972 := by
    simpa [prefixWord, tailWord_1317972, baseEnd_1317972] using wordTrace_append hprefix tailTrace_1317972
  have hstable : (prefixWord ++ tailWord_1317972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1317972).length < 2 ^ (prefixWord ++ tailWord_1317972).sum := by decide
  have hdescent : baseEnd_1317972 < baseStart_1317972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1317972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318019 : List Nat := [1, 1, 1, 3, 3, 2, 3, 2, 3, 1, 3]
def baseStart_1318019 : Nat := 118140960795 + 1318019 * 2 ^ 59
def prefixEnd_1318019 : Nat := 4983230072969 + 3 ^ 40 * 1318019 * 2
def baseEnd_1318019 : Nat := 676777258758383978301047

theorem tailTrace_1318019 : CollatzResearch.WordTrace tailWord_1318019 prefixEnd_1318019 676777258758383978301047 := by
  unfold tailWord_1318019
  simp only [CollatzResearch.WordTrace]
  refine ⟨48072102212049737569205111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32048068141366491712803407 48072102212049737569205111)
  ·
    refine ⟨72108153318074606353807667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48072102212049737569205111 72108153318074606353807667)
    ·
      refine ⟨108162229977111909530711501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72108153318074606353807667 108162229977111909530711501)
      ·
        refine ⟨40560836241416966074016813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 108162229977111909530711501 40560836241416966074016813)
        ·
          refine ⟨15210313590531362277756305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 40560836241416966074016813 15210313590531362277756305)
          ·
            refine ⟨11407735192898521708317229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15210313590531362277756305 11407735192898521708317229)
            ·
              refine ⟨4277900697336945640618961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11407735192898521708317229 4277900697336945640618961)
              ·
                refine ⟨3208425523002709230464221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4277900697336945640618961 3208425523002709230464221)
                ·
                  refine ⟨1203159571126015961424083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3208425523002709230464221 1203159571126015961424083)
                  ·
                    refine ⟨1804739356689023942136125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1203159571126015961424083 1804739356689023942136125)
                    ·
                      refine ⟨676777258758383978301047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1804739356689023942136125 676777258758383978301047)
                      ·
                        rfl

theorem cell23_1318019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 3, 2, 3, 1, 3].length) (baseStart_1318019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318019 prefixEnd_1318019 := by exact prefixLift 1318019
  have htrace : WordTrace (prefixWord ++ tailWord_1318019) baseStart_1318019 baseEnd_1318019 := by
    simpa [prefixWord, tailWord_1318019, baseEnd_1318019] using wordTrace_append hprefix tailTrace_1318019
  have hstable : (prefixWord ++ tailWord_1318019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318019).length < 2 ^ (prefixWord ++ tailWord_1318019).sum := by decide
  have hdescent : baseEnd_1318019 < baseStart_1318019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318039 : List Nat := [1, 1, 3, 3, 3, 2, 1, 3, 1, 5]
def baseStart_1318039 : Nat := 118140960795 + 1318039 * 2 ^ 59
def prefixEnd_1318039 : Nat := 4983230072969 + 3 ^ 40 * 1318039 * 2
def baseEnd_1318039 : Nat := 225595842790491300016985

theorem tailTrace_1318039 : CollatzResearch.WordTrace tailWord_1318039 prefixEnd_1318039 225595842790491300016985 := by
  unfold tailWord_1318039
  simp only [CollatzResearch.WordTrace]
  refine ⟨48072831671977280984933171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32048554447984853989955447 48072831671977280984933171)
  ·
    refine ⟨72109247507965921477399757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48072831671977280984933171 72109247507965921477399757)
    ·
      refine ⟨27040967815487220554024909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72109247507965921477399757 27040967815487220554024909)
      ·
        refine ⟨10140362930807707707759341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27040967815487220554024909 10140362930807707707759341)
        ·
          refine ⟨3802636099052890390409753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10140362930807707707759341 3802636099052890390409753)
          ·
            refine ⟨2851977074289667792807315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3802636099052890390409753 2851977074289667792807315)
            ·
              refine ⟨4277965611434501689210973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2851977074289667792807315 4277965611434501689210973)
              ·
                refine ⟨1604237104287938133454115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4277965611434501689210973 1604237104287938133454115)
                ·
                  refine ⟨2406355656431907200181173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1604237104287938133454115 2406355656431907200181173)
                  ·
                    refine ⟨225595842790491300016985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2406355656431907200181173 225595842790491300016985)
                    ·
                      rfl

theorem cell23_1318039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 1, 3, 1, 5].length) (baseStart_1318039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318039 prefixEnd_1318039 := by exact prefixLift 1318039
  have htrace : WordTrace (prefixWord ++ tailWord_1318039) baseStart_1318039 baseEnd_1318039 := by
    simpa [prefixWord, tailWord_1318039, baseEnd_1318039] using wordTrace_append hprefix tailTrace_1318039
  have hstable : (prefixWord ++ tailWord_1318039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318039).length < 2 ^ (prefixWord ++ tailWord_1318039).sum := by decide
  have hdescent : baseEnd_1318039 < baseStart_1318039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318072 : List Nat := [2, 1, 2, 1, 2, 1, 2, 5, 1, 2, 4]
def baseStart_1318072 : Nat := 118140960795 + 1318072 * 2 ^ 59
def prefixEnd_1318072 : Nat := 4983230072969 + 3 ^ 40 * 1318072 * 2
def baseEnd_1318072 : Nat := 676804473233072270938303

theorem tailTrace_1318072 : CollatzResearch.WordTrace tailWord_1318072 prefixEnd_1318072 676804473233072270938303 := by
  unfold tailWord_1318072
  simp only [CollatzResearch.WordTrace]
  refine ⟨24037017640428863810442235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32049356853905151747256313 24037017640428863810442235)
  ·
    refine ⟨36055526460643295715663353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24037017640428863810442235 36055526460643295715663353)
    ·
      refine ⟨27041644845482471786747515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36055526460643295715663353 27041644845482471786747515)
      ·
        refine ⟨40562467268223707680121273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27041644845482471786747515 40562467268223707680121273)
        ·
          refine ⟨30421850451167780760090955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40562467268223707680121273 30421850451167780760090955)
          ·
            refine ⟨45632775676751671140136433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30421850451167780760090955 45632775676751671140136433)
            ·
              refine ⟨34224581757563753355102325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45632775676751671140136433 34224581757563753355102325)
              ·
                refine ⟨3208554539771601877040843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 34224581757563753355102325 3208554539771601877040843)
                ·
                  refine ⟨4812831809657402815561265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3208554539771601877040843 4812831809657402815561265)
                  ·
                    refine ⟨3609623857243052111670949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4812831809657402815561265 3609623857243052111670949)
                    ·
                      refine ⟨676804473233072270938303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3609623857243052111670949 676804473233072270938303)
                      ·
                        rfl

theorem cell23_1318072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_1318072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318072 prefixEnd_1318072 := by exact prefixLift 1318072
  have htrace : WordTrace (prefixWord ++ tailWord_1318072) baseStart_1318072 baseEnd_1318072 := by
    simpa [prefixWord, tailWord_1318072, baseEnd_1318072] using wordTrace_append hprefix tailTrace_1318072
  have hstable : (prefixWord ++ tailWord_1318072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318072).length < 2 ^ (prefixWord ++ tailWord_1318072).sum := by decide
  have hdescent : baseEnd_1318072 < baseStart_1318072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318076 : List Nat := [2, 2, 2, 3, 2, 2, 2, 2, 1, 1, 4]
def baseStart_1318076 : Nat := 118140960795 + 1318076 * 2 ^ 59
def prefixEnd_1318076 : Nat := 4983230072969 + 3 ^ 40 * 1318076 * 2
def baseEnd_1318076 : Nat := 676806527155690255288285

theorem tailTrace_1318076 : CollatzResearch.WordTrace tailWord_1318076 prefixEnd_1318076 676806527155690255288285 := by
  unfold tailWord_1318076
  simp only [CollatzResearch.WordTrace]
  refine ⟨24037090586421618152015041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32049454115228824202686721 24037090586421618152015041)
  ·
    refine ⟨18027817939816213614011281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24037090586421618152015041 18027817939816213614011281)
    ·
      refine ⟨13520863454862160210508461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18027817939816213614011281 13520863454862160210508461)
      ·
        refine ⟨5070323795573310078940673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13520863454862160210508461 5070323795573310078940673)
        ·
          refine ⟨3802742846679982559205505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5070323795573310078940673 3802742846679982559205505)
          ·
            refine ⟨2852057135009986919404129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3802742846679982559205505 2852057135009986919404129)
            ·
              refine ⟨2139042851257490189553097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2852057135009986919404129 2139042851257490189553097)
              ·
                refine ⟨1604282138443117642164823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2139042851257490189553097 1604282138443117642164823)
                ·
                  refine ⟨2406423207664676463247235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1604282138443117642164823 2406423207664676463247235)
                  ·
                    refine ⟨3609634811497014694870853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2406423207664676463247235 3609634811497014694870853)
                    ·
                      refine ⟨676806527155690255288285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3609634811497014694870853 676806527155690255288285)
                      ·
                        rfl

theorem cell23_1318076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 1, 1, 4].length) (baseStart_1318076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318076 prefixEnd_1318076 := by exact prefixLift 1318076
  have htrace : WordTrace (prefixWord ++ tailWord_1318076) baseStart_1318076 baseEnd_1318076 := by
    simpa [prefixWord, tailWord_1318076, baseEnd_1318076] using wordTrace_append hprefix tailTrace_1318076
  have hstable : (prefixWord ++ tailWord_1318076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318076).length < 2 ^ (prefixWord ++ tailWord_1318076).sum := by decide
  have hdescent : baseEnd_1318076 < baseStart_1318076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318079 : List Nat := [1, 1, 2, 2, 2, 2, 3, 4, 1, 2, 3]
def baseStart_1318079 : Nat := 118140960795 + 1318079 * 2 ^ 59
def prefixEnd_1318079 : Nat := 4983230072969 + 3 ^ 40 * 1318079 * 2
def baseEnd_1318079 : Nat := 676808067597653743550771

theorem tailTrace_1318079 : CollatzResearch.WordTrace tailWord_1318079 prefixEnd_1318079 676808067597653743550771 := by
  unfold tailWord_1318079
  simp only [CollatzResearch.WordTrace]
  refine ⟨48074290591832367816389291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32049527061221578544259527 48074290591832367816389291)
  ·
    refine ⟨72111435887748551724583937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48074290591832367816389291 72111435887748551724583937)
    ·
      refine ⟨54083576915811413793437953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72111435887748551724583937 54083576915811413793437953)
      ·
        refine ⟨40562682686858560345078465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54083576915811413793437953 40562682686858560345078465)
        ·
          refine ⟨30422012015143920258808849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40562682686858560345078465 30422012015143920258808849)
          ·
            refine ⟨22816509011357940194106637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 30422012015143920258808849 22816509011357940194106637)
            ·
              refine ⟨8556190879259227572789989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 22816509011357940194106637 8556190879259227572789989)
              ·
                refine ⟨1604285789861105169898123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8556190879259227572789989 1604285789861105169898123)
                ·
                  refine ⟨2406428684791657754847185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1604285789861105169898123 2406428684791657754847185)
                  ·
                    refine ⟨1804821513593743316135389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2406428684791657754847185 1804821513593743316135389)
                    ·
                      refine ⟨676808067597653743550771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1804821513593743316135389 676808067597653743550771)
                      ·
                        rfl

theorem cell23_1318079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 2, 3].length) (baseStart_1318079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318079 prefixEnd_1318079 := by exact prefixLift 1318079
  have htrace : WordTrace (prefixWord ++ tailWord_1318079) baseStart_1318079 baseEnd_1318079 := by
    simpa [prefixWord, tailWord_1318079, baseEnd_1318079] using wordTrace_append hprefix tailTrace_1318079
  have hstable : (prefixWord ++ tailWord_1318079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318079).length < 2 ^ (prefixWord ++ tailWord_1318079).sum := by decide
  have hdescent : baseEnd_1318079 < baseStart_1318079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318130 : List Nat := [3, 2, 1, 3, 4, 1, 1, 2, 1, 2, 3]
def baseStart_1318130 : Nat := 118140960795 + 1318130 * 2 ^ 59
def prefixEnd_1318130 : Nat := 4983230072969 + 3 ^ 40 * 1318130 * 2
def baseEnd_1318130 : Nat := 676834255111033044013037

theorem tailTrace_1318130 : CollatzResearch.WordTrace tailWord_1318130 prefixEnd_1318130 676834255111033044013037 := by
  unfold tailWord_1318130
  simp only [CollatzResearch.WordTrace]
  refine ⟨12019037678661900881623961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32050767143098402350997229 12019037678661900881623961)
  ·
    refine ⟨9014278258996425661217971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12019037678661900881623961 9014278258996425661217971)
    ·
      refine ⟨13521417388494638491826957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9014278258996425661217971 13521417388494638491826957)
      ·
        refine ⟨5070531520685489434435109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13521417388494638491826957 5070531520685489434435109)
        ·
          refine ⟨950724660128529268956583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5070531520685489434435109 950724660128529268956583)
          ·
            refine ⟨1426086990192793903434875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 950724660128529268956583 1426086990192793903434875)
            ·
              refine ⟨2139130485289190855152313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1426086990192793903434875 2139130485289190855152313)
              ·
                refine ⟨1604347863966893141364235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2139130485289190855152313 1604347863966893141364235)
                ·
                  refine ⟨2406521795950339712046353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1604347863966893141364235 2406521795950339712046353)
                  ·
                    refine ⟨1804891346962754784034765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2406521795950339712046353 1804891346962754784034765)
                    ·
                      refine ⟨676834255111033044013037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1804891346962754784034765 676834255111033044013037)
                      ·
                        rfl

theorem cell23_1318130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_1318130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318130 prefixEnd_1318130 := by exact prefixLift 1318130
  have htrace : WordTrace (prefixWord ++ tailWord_1318130) baseStart_1318130 baseEnd_1318130 := by
    simpa [prefixWord, tailWord_1318130, baseEnd_1318130] using wordTrace_append hprefix tailTrace_1318130
  have hstable : (prefixWord ++ tailWord_1318130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318130).length < 2 ^ (prefixWord ++ tailWord_1318130).sum := by decide
  have hdescent : baseEnd_1318130 < baseStart_1318130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318153 : List Nat := [1, 2, 1, 1, 3, 3, 5, 1, 1, 3, 2]
def baseStart_1318153 : Nat := 118140960795 + 1318153 * 2 ^ 59
def prefixEnd_1318153 : Nat := 4983230072969 + 3 ^ 40 * 1318153 * 2
def baseEnd_1318153 : Nat := 676846065166086454025431

theorem tailTrace_1318153 : CollatzResearch.WordTrace tailWord_1318153 prefixEnd_1318153 676846065166086454025431 := by
  unfold tailWord_1318153
  simp only [CollatzResearch.WordTrace]
  refine ⟨48076989593564278454583113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32051326395709518969722075 48076989593564278454583113)
  ·
    refine ⟨36057742195173208840937335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48076989593564278454583113 36057742195173208840937335)
    ·
      refine ⟨54086613292759813261406003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36057742195173208840937335 54086613292759813261406003)
      ·
        refine ⟨81129919939139719892109005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54086613292759813261406003 81129919939139719892109005)
        ·
          refine ⟨30423719977177394959540877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 81129919939139719892109005 30423719977177394959540877)
          ·
            refine ⟨11408894991441523109827829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 30423719977177394959540877 11408894991441523109827829)
            ·
              refine ⟨1069583905447642791546359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11408894991441523109827829 1069583905447642791546359)
              ·
                refine ⟨1604375858171464187319539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1069583905447642791546359 1604375858171464187319539)
                ·
                  refine ⟨2406563787257196280979309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1604375858171464187319539 2406563787257196280979309)
                  ·
                    refine ⟨902461420221448605367241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2406563787257196280979309 902461420221448605367241)
                    ·
                      refine ⟨676846065166086454025431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 902461420221448605367241 676846065166086454025431)
                      ·
                        rfl

theorem cell23_1318153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 5, 1, 1, 3, 2].length) (baseStart_1318153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318153 prefixEnd_1318153 := by exact prefixLift 1318153
  have htrace : WordTrace (prefixWord ++ tailWord_1318153) baseStart_1318153 baseEnd_1318153 := by
    simpa [prefixWord, tailWord_1318153, baseEnd_1318153] using wordTrace_append hprefix tailTrace_1318153
  have hstable : (prefixWord ++ tailWord_1318153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318153).length < 2 ^ (prefixWord ++ tailWord_1318153).sum := by decide
  have hdescent : baseEnd_1318153 < baseStart_1318153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318179 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 4]
def baseStart_1318179 : Nat := 118140960795 + 1318179 * 2 ^ 59
def prefixEnd_1318179 : Nat := 4983230072969 + 3 ^ 40 * 1318179 * 2
def baseEnd_1318179 : Nat := 676859415663103352300311

theorem tailTrace_1318179 : CollatzResearch.WordTrace tailWord_1318179 prefixEnd_1318179 676859415663103352300311 := by
  unfold tailWord_1318179
  simp only [CollatzResearch.WordTrace]
  refine ⟨48077937891470084895029591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32051958594313389930019727 48077937891470084895029591)
  ·
    refine ⟨72116906837205127342544387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48077937891470084895029591 72116906837205127342544387)
    ·
      refine ⟨108175360255807691013816581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72116906837205127342544387 108175360255807691013816581)
      ·
        refine ⟨20282880047963942065090609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108175360255807691013816581 20282880047963942065090609)
        ·
          refine ⟨15212160035972956548817957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20282880047963942065090609 15212160035972956548817957)
          ·
            refine ⟨2852280006744929352903367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15212160035972956548817957 2852280006744929352903367)
            ·
              refine ⟨4278420010117394029355051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2852280006744929352903367 4278420010117394029355051)
              ·
                refine ⟨6417630015176091044032577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4278420010117394029355051 6417630015176091044032577)
                ·
                  refine ⟨4813222511382068283024433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6417630015176091044032577 4813222511382068283024433)
                  ·
                    refine ⟨3609916883536551212268325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4813222511382068283024433 3609916883536551212268325)
                    ·
                      refine ⟨676859415663103352300311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3609916883536551212268325 676859415663103352300311)
                      ·
                        rfl

theorem cell23_1318179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 2, 4].length) (baseStart_1318179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318179 prefixEnd_1318179 := by exact prefixLift 1318179
  have htrace : WordTrace (prefixWord ++ tailWord_1318179) baseStart_1318179 baseEnd_1318179 := by
    simpa [prefixWord, tailWord_1318179, baseEnd_1318179] using wordTrace_append hprefix tailTrace_1318179
  have hstable : (prefixWord ++ tailWord_1318179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318179).length < 2 ^ (prefixWord ++ tailWord_1318179).sum := by decide
  have hdescent : baseEnd_1318179 < baseStart_1318179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318249 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 5, 4]
def baseStart_1318249 : Nat := 118140960795 + 1318249 * 2 ^ 59
def prefixEnd_1318249 : Nat := 4983230072969 + 3 ^ 40 * 1318249 * 2
def baseEnd_1318249 : Nat := 225631786436306026141663

theorem tailTrace_1318249 : CollatzResearch.WordTrace tailWord_1318249 prefixEnd_1318249 225631786436306026141663 := by
  unfold tailWord_1318249
  simp only [CollatzResearch.WordTrace]
  refine ⟨48080491001216486850077801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32053660667477657900051867 48080491001216486850077801)
  ·
    refine ⟨36060368250912365137558351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48080491001216486850077801 36060368250912365137558351)
    ·
      refine ⟨54090552376368547706337527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36060368250912365137558351 54090552376368547706337527)
      ·
        refine ⟨81135828564552821559506291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54090552376368547706337527 81135828564552821559506291)
        ·
          refine ⟨121703742846829232339259437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81135828564552821559506291 121703742846829232339259437)
          ·
            refine ⟨45638903567560962127222289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 121703742846829232339259437 45638903567560962127222289)
            ·
              refine ⟨34229177675670721595416717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45638903567560962127222289 34229177675670721595416717)
              ·
                refine ⟨12835941628376520598281269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34229177675670721595416717 12835941628376520598281269)
                ·
                  refine ⟨1203369527660298806088869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12835941628376520598281269 1203369527660298806088869)
                  ·
                    refine ⟨225631786436306026141663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1203369527660298806088869 225631786436306026141663)
                    ·
                      rfl

theorem cell23_1318249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 5, 4].length) (baseStart_1318249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318249 prefixEnd_1318249 := by exact prefixLift 1318249
  have htrace : WordTrace (prefixWord ++ tailWord_1318249) baseStart_1318249 baseEnd_1318249 := by
    simpa [prefixWord, tailWord_1318249, baseEnd_1318249] using wordTrace_append hprefix tailTrace_1318249
  have hstable : (prefixWord ++ tailWord_1318249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318249).length < 2 ^ (prefixWord ++ tailWord_1318249).sum := by decide
  have hdescent : baseEnd_1318249 < baseStart_1318249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318270 : List Nat := [4, 2, 3, 2, 1, 1, 1, 2, 2, 5]
def baseStart_1318270 : Nat := 118140960795 + 1318270 * 2 ^ 59
def prefixEnd_1318270 : Nat := 4983230072969 + 3 ^ 40 * 1318270 * 2
def baseEnd_1318270 : Nat := 225635380800887498754131

theorem tailTrace_1318270 : CollatzResearch.WordTrace tailWord_1318270 prefixEnd_1318270 225635380800887498754131 := by
  unfold tailWord_1318270
  simp only [CollatzResearch.WordTrace]
  refine ⟨6010157116767550929574033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32054171289426938291061509 6010157116767550929574033)
  ·
    refine ⟨4507617837575663197180525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6010157116767550929574033 4507617837575663197180525)
    ·
      refine ⟨1690356689090873698942697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4507617837575663197180525 1690356689090873698942697)
      ·
        refine ⟨1267767516818155274207023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1690356689090873698942697 1267767516818155274207023)
        ·
          refine ⟨1901651275227232911310535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1267767516818155274207023 1901651275227232911310535)
          ·
            refine ⟨2852476912840849366965803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1901651275227232911310535 2852476912840849366965803)
            ·
              refine ⟨4278715369261274050448705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2852476912840849366965803 4278715369261274050448705)
              ·
                refine ⟨3209036526945955537836529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4278715369261274050448705 3209036526945955537836529)
                ·
                  refine ⟨2406777395209466653377397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3209036526945955537836529 2406777395209466653377397)
                  ·
                    refine ⟨225635380800887498754131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2406777395209466653377397 225635380800887498754131)
                    ·
                      rfl

theorem cell23_1318270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_1318270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318270 prefixEnd_1318270 := by exact prefixLift 1318270
  have htrace : WordTrace (prefixWord ++ tailWord_1318270) baseStart_1318270 baseEnd_1318270 := by
    simpa [prefixWord, tailWord_1318270, baseEnd_1318270] using wordTrace_append hprefix tailTrace_1318270
  have hstable : (prefixWord ++ tailWord_1318270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318270).length < 2 ^ (prefixWord ++ tailWord_1318270).sum := by decide
  have hdescent : baseEnd_1318270 < baseStart_1318270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318273 : List Nat := [1, 2, 4, 3, 2, 1, 1, 2, 2, 1, 4]
def baseStart_1318273 : Nat := 118140960795 + 1318273 * 2 ^ 59
def prefixEnd_1318273 : Nat := 4983230072969 + 3 ^ 40 * 1318273 * 2
def baseEnd_1318273 : Nat := 676907682844625984524879

theorem tailTrace_1318273 : CollatzResearch.WordTrace tailWord_1318273 prefixEnd_1318273 676907682844625984524879 := by
  unfold tailWord_1318273
  simp only [CollatzResearch.WordTrace]
  refine ⟨48081366353129538948951473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32054244235419692632634315 48081366353129538948951473)
  ·
    refine ⟨36061024764847154211713605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48081366353129538948951473 36061024764847154211713605)
    ·
      refine ⟨6761442143408841414696301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36061024764847154211713605 6761442143408841414696301)
      ·
        refine ⟨2535540803778315530511113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6761442143408841414696301 2535540803778315530511113)
        ·
          refine ⟨1901655602833736647883335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2535540803778315530511113 1901655602833736647883335)
          ·
            refine ⟨2852483404250604971825003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1901655602833736647883335 2852483404250604971825003)
            ·
              refine ⟨4278725106375907457737505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2852483404250604971825003 4278725106375907457737505)
              ·
                refine ⟨3209043829781930593303129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4278725106375907457737505 3209043829781930593303129)
                ·
                  refine ⟨2406782872336447944977347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3209043829781930593303129 2406782872336447944977347)
                  ·
                    refine ⟨3610174308504671917466021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2406782872336447944977347 3610174308504671917466021)
                    ·
                      refine ⟨676907682844625984524879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3610174308504671917466021 676907682844625984524879)
                      ·
                        rfl

theorem cell23_1318273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_1318273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318273 prefixEnd_1318273 := by exact prefixLift 1318273
  have htrace : WordTrace (prefixWord ++ tailWord_1318273) baseStart_1318273 baseEnd_1318273 := by
    simpa [prefixWord, tailWord_1318273, baseEnd_1318273] using wordTrace_append hprefix tailTrace_1318273
  have hstable : (prefixWord ++ tailWord_1318273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318273).length < 2 ^ (prefixWord ++ tailWord_1318273).sum := by decide
  have hdescent : baseEnd_1318273 < baseStart_1318273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318276 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 4, 2, 3]
def baseStart_1318276 : Nat := 118140960795 + 1318276 * 2 ^ 59
def prefixEnd_1318276 : Nat := 4983230072969 + 3 ^ 40 * 1318276 * 2
def baseEnd_1318276 : Nat := 676909223286589472787365

theorem tailTrace_1318276 : CollatzResearch.WordTrace tailWord_1318276 prefixEnd_1318276 676909223286589472787365 := by
  unfold tailWord_1318276
  simp only [CollatzResearch.WordTrace]
  refine ⟨24040737886059335230655341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32054317181412446974207121 24040737886059335230655341)
  ·
    refine ⟨9015276707272250711495753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24040737886059335230655341 9015276707272250711495753)
    ·
      refine ⟨6761457530454188033621815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9015276707272250711495753 6761457530454188033621815)
      ·
        refine ⟨10142186295681282050432723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6761457530454188033621815 10142186295681282050432723)
        ·
          refine ⟨15213279443521923075649085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10142186295681282050432723 15213279443521923075649085)
          ·
            refine ⟨5704979791320721153368407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15213279443521923075649085 5704979791320721153368407)
            ·
              refine ⟨8557469686981081730052611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5704979791320721153368407 8557469686981081730052611)
              ·
                refine ⟨12836204530471622595078917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8557469686981081730052611 12836204530471622595078917)
                ·
                  refine ⟨2406788349463429236577297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12836204530471622595078917 2406788349463429236577297)
                  ·
                    refine ⟨1805091262097571927432973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2406788349463429236577297 1805091262097571927432973)
                    ·
                      refine ⟨676909223286589472787365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1805091262097571927432973 676909223286589472787365)
                      ·
                        rfl

theorem cell23_1318276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 4, 2, 3].length) (baseStart_1318276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318276 prefixEnd_1318276 := by exact prefixLift 1318276
  have htrace : WordTrace (prefixWord ++ tailWord_1318276) baseStart_1318276 baseEnd_1318276 := by
    simpa [prefixWord, tailWord_1318276, baseEnd_1318276] using wordTrace_append hprefix tailTrace_1318276
  have hstable : (prefixWord ++ tailWord_1318276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318276).length < 2 ^ (prefixWord ++ tailWord_1318276).sum := by decide
  have hdescent : baseEnd_1318276 < baseStart_1318276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318279 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 8]
def baseStart_1318279 : Nat := 118140960795 + 1318279 * 2 ^ 59
def prefixEnd_1318279 : Nat := 4983230072969 + 3 ^ 40 * 1318279 * 2
def baseEnd_1318279 : Nat := 75212307080950329005539

theorem tailTrace_1318279 : CollatzResearch.WordTrace tailWord_1318279 prefixEnd_1318279 75212307080950329005539 := by
  unfold tailWord_1318279
  simp only [CollatzResearch.WordTrace]
  refine ⟨48081585191107801973669891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32054390127405201315779927 48081585191107801973669891)
  ·
    refine ⟨72122377786661702960504837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48081585191107801973669891 72122377786661702960504837)
    ·
      refine ⟨13522945834999069305094657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 72122377786661702960504837 13522945834999069305094657)
      ·
        refine ⟨10142209376249301978820993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13522945834999069305094657 10142209376249301978820993)
        ·
          refine ⟨7606657032186976484115745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10142209376249301978820993 7606657032186976484115745)
          ·
            refine ⟨5704992774140232363086809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7606657032186976484115745 5704992774140232363086809)
            ·
              refine ⟨4278744580605174272315107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5704992774140232363086809 4278744580605174272315107)
              ·
                refine ⟨6418116870907761408472661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4278744580605174272315107 6418116870907761408472661)
                ·
                  refine ⟨75212307080950329005539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6418116870907761408472661 75212307080950329005539)
                  ·
                    rfl

theorem cell23_1318279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 8].length) (baseStart_1318279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318279 prefixEnd_1318279 := by exact prefixLift 1318279
  have htrace : WordTrace (prefixWord ++ tailWord_1318279) baseStart_1318279 baseEnd_1318279 := by
    simpa [prefixWord, tailWord_1318279, baseEnd_1318279] using wordTrace_append hprefix tailTrace_1318279
  have hstable : (prefixWord ++ tailWord_1318279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318279).length < 2 ^ (prefixWord ++ tailWord_1318279).sum := by decide
  have hdescent : baseEnd_1318279 < baseStart_1318279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318316 : List Nat := [2, 2, 1, 1, 1, 1, 4, 3, 1, 5, 2]
def baseStart_1318316 : Nat := 118140960795 + 1318316 * 2 ^ 59
def prefixEnd_1318316 : Nat := 4983230072969 + 3 ^ 40 * 1318316 * 2
def baseEnd_1318316 : Nat := 676929762512769316287181

theorem tailTrace_1318316 : CollatzResearch.WordTrace tailWord_1318316 prefixEnd_1318316 676929762512769316287181 := by
  unfold tailWord_1318316
  simp only [CollatzResearch.WordTrace]
  refine ⟨24041467345986878646383401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32055289794649171528511201 24041467345986878646383401)
  ·
    refine ⟨18031100509490158984787551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24041467345986878646383401 18031100509490158984787551)
    ·
      refine ⟨27046650764235238477181327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18031100509490158984787551 27046650764235238477181327)
      ·
        refine ⟨40569976146352857715771991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27046650764235238477181327 40569976146352857715771991)
        ·
          refine ⟨60854964219529286573657987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40569976146352857715771991 60854964219529286573657987)
          ·
            refine ⟨91282446329293929860486981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60854964219529286573657987 91282446329293929860486981)
            ·
              refine ⟨17115458686742611848841309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 91282446329293929860486981 17115458686742611848841309)
              ·
                refine ⟨6418297007528479443315491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17115458686742611848841309 6418297007528479443315491)
                ·
                  refine ⟨9627445511292719164973237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6418297007528479443315491 9627445511292719164973237)
                  ·
                    refine ⟨902573016683692421716241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9627445511292719164973237 902573016683692421716241)
                    ·
                      refine ⟨676929762512769316287181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 902573016683692421716241 676929762512769316287181)
                      ·
                        rfl

theorem cell23_1318316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 5, 2].length) (baseStart_1318316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318316 prefixEnd_1318316 := by exact prefixLift 1318316
  have htrace : WordTrace (prefixWord ++ tailWord_1318316) baseStart_1318316 baseEnd_1318316 := by
    simpa [prefixWord, tailWord_1318316, baseEnd_1318316] using wordTrace_append hprefix tailTrace_1318316
  have hstable : (prefixWord ++ tailWord_1318316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318316).length < 2 ^ (prefixWord ++ tailWord_1318316).sum := by decide
  have hdescent : baseEnd_1318316 < baseStart_1318316 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318333 : List Nat := [1, 4, 1, 2, 2, 1, 1, 4, 2, 3, 2]
def baseStart_1318333 : Nat := 118140960795 + 1318333 * 2 ^ 59
def prefixEnd_1318333 : Nat := 4983230072969 + 3 ^ 40 * 1318333 * 2
def baseEnd_1318333 : Nat := 676938491683895749774603

theorem tailTrace_1318333 : CollatzResearch.WordTrace tailWord_1318333 prefixEnd_1318333 676938491683895749774603 := by
  unfold tailWord_1318333
  simp only [CollatzResearch.WordTrace]
  refine ⟨48083554732912169196135653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32055703155274779464090435 48083554732912169196135653)
  ·
    refine ⟨9015666512421031724275435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48083554732912169196135653 9015666512421031724275435)
    ·
      refine ⟨13523499768631547586413153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9015666512421031724275435 13523499768631547586413153)
      ·
        refine ⟨10142624826473660689809865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13523499768631547586413153 10142624826473660689809865)
        ·
          refine ⟨7606968619855245517357399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10142624826473660689809865 7606968619855245517357399)
          ·
            refine ⟨11410452929782868276036099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7606968619855245517357399 11410452929782868276036099)
            ·
              refine ⟨17115679394674302414054149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11410452929782868276036099 17115679394674302414054149)
              ·
                refine ⟨3209189886501431702635153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17115679394674302414054149 3209189886501431702635153)
                ·
                  refine ⟨2406892414876073776976365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3209189886501431702635153 2406892414876073776976365)
                  ·
                    refine ⟨902584655578527666366137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2406892414876073776976365 902584655578527666366137)
                    ·
                      refine ⟨676938491683895749774603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 902584655578527666366137 676938491683895749774603)
                      ·
                        rfl

theorem cell23_1318333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 4, 2, 3, 2].length) (baseStart_1318333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318333 prefixEnd_1318333 := by exact prefixLift 1318333
  have htrace : WordTrace (prefixWord ++ tailWord_1318333) baseStart_1318333 baseEnd_1318333 := by
    simpa [prefixWord, tailWord_1318333, baseEnd_1318333] using wordTrace_append hprefix tailTrace_1318333
  have hstable : (prefixWord ++ tailWord_1318333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318333).length < 2 ^ (prefixWord ++ tailWord_1318333).sum := by decide
  have hdescent : baseEnd_1318333 < baseStart_1318333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318346 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 3, 1, 4]
def baseStart_1318346 : Nat := 118140960795 + 1318346 * 2 ^ 59
def prefixEnd_1318346 : Nat := 4983230072969 + 3 ^ 40 * 1318346 * 2
def baseEnd_1318346 : Nat := 676945166932404198912043

theorem tailTrace_1318346 : CollatzResearch.WordTrace tailWord_1318346 prefixEnd_1318346 676945166932404198912043 := by
  unfold tailWord_1318346
  simp only [CollatzResearch.WordTrace]
  refine ⟨12021007220466268104089723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32056019254576714944239261 12021007220466268104089723)
  ·
    refine ⟨18031510830699402156134585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12021007220466268104089723 18031510830699402156134585)
    ·
      refine ⟨13523633123024551617100939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18031510830699402156134585 13523633123024551617100939)
      ·
        refine ⟨20285449684536827425651409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13523633123024551617100939 20285449684536827425651409)
        ·
          refine ⟨15214087263402620569238557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20285449684536827425651409 15214087263402620569238557)
          ·
            refine ⟨5705282723775982713464459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15214087263402620569238557 5705282723775982713464459)
            ·
              refine ⟨8557924085663974070196689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5705282723775982713464459 8557924085663974070196689)
              ·
                refine ⟨6418443064247980552647517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8557924085663974070196689 6418443064247980552647517)
                ·
                  refine ⟨2406916149092992707242819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6418443064247980552647517 2406916149092992707242819)
                  ·
                    refine ⟨3610374223639489060864229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2406916149092992707242819 3610374223639489060864229)
                    ·
                      refine ⟨676945166932404198912043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3610374223639489060864229 676945166932404198912043)
                      ·
                        rfl

theorem cell23_1318346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_1318346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318346 prefixEnd_1318346 := by exact prefixLift 1318346
  have htrace : WordTrace (prefixWord ++ tailWord_1318346) baseStart_1318346 baseEnd_1318346 := by
    simpa [prefixWord, tailWord_1318346, baseEnd_1318346] using wordTrace_append hprefix tailTrace_1318346
  have hstable : (prefixWord ++ tailWord_1318346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318346).length < 2 ^ (prefixWord ++ tailWord_1318346).sum := by decide
  have hdescent : baseEnd_1318346 < baseStart_1318346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318359 : List Nat := [1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 6]
def baseStart_1318359 : Nat := 118140960795 + 1318359 * 2 ^ 59
def prefixEnd_1318359 : Nat := 4983230072969 + 3 ^ 40 * 1318359 * 2
def baseEnd_1318359 : Nat := 676951842180912648049483

theorem tailTrace_1318359 : CollatzResearch.WordTrace tailWord_1318359 prefixEnd_1318359 676951842180912648049483 := by
  unfold tailWord_1318359
  simp only [CollatzResearch.WordTrace]
  refine ⟨48084503030817975636582131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32056335353878650424388087 48084503030817975636582131)
  ·
    refine ⟨72126754546226963454873197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48084503030817975636582131 72126754546226963454873197)
    ·
      refine ⟨27047532954835111295577449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 72126754546226963454873197 27047532954835111295577449)
      ·
        refine ⟨20285649716126333471683087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27047532954835111295577449 20285649716126333471683087)
        ·
          refine ⟨30428474574189500207524631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20285649716126333471683087 30428474574189500207524631)
          ·
            refine ⟨45642711861284250311286947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30428474574189500207524631 45642711861284250311286947)
            ·
              refine ⟨68464067791926375466930421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 45642711861284250311286947 68464067791926375466930421)
              ·
                refine ⟨6418506355493097700024727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 68464067791926375466930421 6418506355493097700024727)
                ·
                  refine ⟨9627759533239646550037091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6418506355493097700024727 9627759533239646550037091)
                  ·
                    refine ⟨14441639299859469825055637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9627759533239646550037091 14441639299859469825055637)
                    ·
                      refine ⟨676951842180912648049483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14441639299859469825055637 676951842180912648049483)
                      ·
                        rfl

theorem cell23_1318359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_1318359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318359 prefixEnd_1318359 := by exact prefixLift 1318359
  have htrace : WordTrace (prefixWord ++ tailWord_1318359) baseStart_1318359 baseEnd_1318359 := by
    simpa [prefixWord, tailWord_1318359, baseEnd_1318359] using wordTrace_append hprefix tailTrace_1318359
  have hstable : (prefixWord ++ tailWord_1318359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318359).length < 2 ^ (prefixWord ++ tailWord_1318359).sum := by decide
  have hdescent : baseEnd_1318359 < baseStart_1318359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318376 : List Nat := [2, 1, 4, 1, 1, 2, 1, 4, 1, 2, 4]
def baseStart_1318376 : Nat := 118140960795 + 1318376 * 2 ^ 59
def prefixEnd_1318376 : Nat := 4983230072969 + 3 ^ 40 * 1318376 * 2
def baseEnd_1318376 : Nat := 676960571352039081536905

theorem tailTrace_1318376 : CollatzResearch.WordTrace tailWord_1318376 prefixEnd_1318376 676960571352039081536905 := by
  unfold tailWord_1318376
  simp only [CollatzResearch.WordTrace]
  refine ⟨24042561535878193769975491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32056748714504258359967321 24042561535878193769975491)
  ·
    refine ⟨36063842303817290654963237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24042561535878193769975491 36063842303817290654963237)
    ·
      refine ⟨6761970431965741997805607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36063842303817290654963237 6761970431965741997805607)
      ·
        refine ⟨10142955647948612996708411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6761970431965741997805607 10142955647948612996708411)
        ·
          refine ⟨15214433471922919495062617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10142955647948612996708411 15214433471922919495062617)
          ·
            refine ⟨11410825103942189621296963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15214433471922919495062617 11410825103942189621296963)
            ·
              refine ⟨17116237655913284431945445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11410825103942189621296963 17116237655913284431945445)
              ·
                refine ⟨3209294560483740830989771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17116237655913284431945445 3209294560483740830989771)
                ·
                  refine ⟨4813941840725611246484657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3209294560483740830989771 4813941840725611246484657)
                  ·
                    refine ⟨3610456380544208434863493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4813941840725611246484657 3610456380544208434863493)
                    ·
                      refine ⟨676960571352039081536905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3610456380544208434863493 676960571352039081536905)
                      ·
                        rfl

theorem cell23_1318376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 1, 2, 4].length) (baseStart_1318376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318376 prefixEnd_1318376 := by exact prefixLift 1318376
  have htrace : WordTrace (prefixWord ++ tailWord_1318376) baseStart_1318376 baseEnd_1318376 := by
    simpa [prefixWord, tailWord_1318376, baseEnd_1318376] using wordTrace_append hprefix tailTrace_1318376
  have hstable : (prefixWord ++ tailWord_1318376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318376).length < 2 ^ (prefixWord ++ tailWord_1318376).sum := by decide
  have hdescent : baseEnd_1318376 < baseStart_1318376 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318386 : List Nat := [3, 2, 1, 4, 1, 2, 10]
def baseStart_1318386 : Nat := 118140960795 + 1318386 * 2 ^ 59
def prefixEnd_1318386 : Nat := 4983230072969 + 3 ^ 40 * 1318386 * 2
def baseEnd_1318386 : Nat := 8357601310599802992739

theorem tailTrace_1318386 : CollatzResearch.WordTrace tailWord_1318386 prefixEnd_1318386 8357601310599802992739 := by
  unfold tailWord_1318386
  simp only [CollatzResearch.WordTrace]
  refine ⟨12021371950430039811953753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 32056991867813439498543341 12021371950430039811953753)
  ·
    refine ⟨9016028962822529858965315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12021371950430039811953753 9016028962822529858965315)
    ·
      refine ⟨13524043444233794788447973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9016028962822529858965315 13524043444233794788447973)
      ·
        refine ⟨2535758145793836522833995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13524043444233794788447973 2535758145793836522833995)
        ·
          refine ⟨3803637218690754784250993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2535758145793836522833995 3803637218690754784250993)
          ·
            refine ⟨2852727914018066088188245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3803637218690754784250993 2852727914018066088188245)
            ·
              refine ⟨8357601310599802992739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2852727914018066088188245 8357601310599802992739)
              ·
                rfl

theorem cell23_1318386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 2, 10].length) (baseStart_1318386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318386 prefixEnd_1318386 := by exact prefixLift 1318386
  have htrace : WordTrace (prefixWord ++ tailWord_1318386) baseStart_1318386 baseEnd_1318386 := by
    simpa [prefixWord, tailWord_1318386, baseEnd_1318386] using wordTrace_append hprefix tailTrace_1318386
  have hstable : (prefixWord ++ tailWord_1318386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318386).length < 2 ^ (prefixWord ++ tailWord_1318386).sum := by decide
  have hdescent : baseEnd_1318386 < baseStart_1318386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318390 : List Nat := [5, 1, 1, 1, 2, 2, 3, 2, 2, 4]
def baseStart_1318390 : Nat := 118140960795 + 1318390 * 2 ^ 59
def prefixEnd_1318390 : Nat := 4983230072969 + 3 ^ 40 * 1318390 * 2
def baseEnd_1318390 : Nat := 225655920027067342253947

theorem tailTrace_1318390 : CollatzResearch.WordTrace tailWord_1318390 prefixEnd_1318390 225655920027067342253947 := by
  unfold tailWord_1318390
  simp only [CollatzResearch.WordTrace]
  refine ⟨3005352105856604245685039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 32057089129137111953973749 3005352105856604245685039)
  ·
    refine ⟨4508028158784906368527559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3005352105856604245685039 4508028158784906368527559)
    ·
      refine ⟨6762042238177359552791339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4508028158784906368527559 6762042238177359552791339)
      ·
        refine ⟨10143063357266039329187009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6762042238177359552791339 10143063357266039329187009)
        ·
          refine ⟨7607297517949529496890257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10143063357266039329187009 7607297517949529496890257)
          ·
            refine ⟨5705473138462147122667693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7607297517949529496890257 5705473138462147122667693)
            ·
              refine ⟨2139552426923305171000385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5705473138462147122667693 2139552426923305171000385)
              ·
                refine ⟨1604664320192478878250289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2139552426923305171000385 1604664320192478878250289)
                ·
                  refine ⟨1203498240144359158687717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1604664320192478878250289 1203498240144359158687717)
                  ·
                    refine ⟨225655920027067342253947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1203498240144359158687717 225655920027067342253947)
                    ·
                      rfl

theorem cell23_1318390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_1318390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318390 prefixEnd_1318390 := by exact prefixLift 1318390
  have htrace : WordTrace (prefixWord ++ tailWord_1318390) baseStart_1318390 baseEnd_1318390 := by
    simpa [prefixWord, tailWord_1318390, baseEnd_1318390] using wordTrace_append hprefix tailTrace_1318390
  have hstable : (prefixWord ++ tailWord_1318390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318390).length < 2 ^ (prefixWord ++ tailWord_1318390).sum := by decide
  have hdescent : baseEnd_1318390 < baseStart_1318390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318396 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 3, 3, 3]
def baseStart_1318396 : Nat := 118140960795 + 1318396 * 2 ^ 59
def prefixEnd_1318396 : Nat := 4983230072969 + 3 ^ 40 * 1318396 * 2
def baseEnd_1318396 : Nat := 676970840965129003286813

theorem tailTrace_1318396 : CollatzResearch.WordTrace tailWord_1318396 prefixEnd_1318396 676970840965129003286813 := by
  unfold tailWord_1318396
  simp only [CollatzResearch.WordTrace]
  refine ⟨24042926265841965477839521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32057235021122620637119361 24042926265841965477839521)
  ·
    refine ⟨18032194699381474108379641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24042926265841965477839521 18032194699381474108379641)
    ·
      refine ⟨13524146024536105581284731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18032194699381474108379641 13524146024536105581284731)
      ·
        refine ⟨20286219036804158371927097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13524146024536105581284731 20286219036804158371927097)
        ·
          refine ⟨15214664277603118778945323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20286219036804158371927097 15214664277603118778945323)
          ·
            refine ⟨22821996416404678168417985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15214664277603118778945323 22821996416404678168417985)
            ·
              refine ⟨17116497312303508626313489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 22821996416404678168417985 17116497312303508626313489)
              ·
                refine ⟨12837372984227631469735117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17116497312303508626313489 12837372984227631469735117)
                ·
                  refine ⟨4814014869085361801150669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12837372984227631469735117 4814014869085361801150669)
                  ·
                    refine ⟨1805255575907010675431501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4814014869085361801150669 1805255575907010675431501)
                    ·
                      refine ⟨676970840965129003286813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1805255575907010675431501 676970840965129003286813)
                      ·
                        rfl

theorem cell23_1318396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_1318396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318396 prefixEnd_1318396 := by exact prefixLift 1318396
  have htrace : WordTrace (prefixWord ++ tailWord_1318396) baseStart_1318396 baseEnd_1318396 := by
    simpa [prefixWord, tailWord_1318396, baseEnd_1318396] using wordTrace_append hprefix tailTrace_1318396
  have hstable : (prefixWord ++ tailWord_1318396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318396).length < 2 ^ (prefixWord ++ tailWord_1318396).sum := by decide
  have hdescent : baseEnd_1318396 < baseStart_1318396 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318397 : List Nat := [1, 4, 1, 1, 1, 4, 2, 4, 1, 2, 2]
def baseStart_1318397 : Nat := 118140960795 + 1318397 * 2 ^ 59
def prefixEnd_1318397 : Nat := 4983230072969 + 3 ^ 40 * 1318397 * 2
def baseEnd_1318397 : Nat := 676971354445783499374309

theorem tailTrace_1318397 : CollatzResearch.WordTrace tailWord_1318397 prefixEnd_1318397 676971354445783499374309 := by
  unfold tailWord_1318397
  simp only [CollatzResearch.WordTrace]
  refine ⟨48085889004680308126465445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32057259336453538750976963 48085889004680308126465445)
  ·
    refine ⟨9016104188377557773712271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48085889004680308126465445 9016104188377557773712271)
    ·
      refine ⟨13524156282566336660568407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9016104188377557773712271 13524156282566336660568407)
      ·
        refine ⟨20286234423849504990852611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13524156282566336660568407 20286234423849504990852611)
        ·
          refine ⟨30429351635774257486278917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20286234423849504990852611 30429351635774257486278917)
          ·
            refine ⟨5705503431707673278677297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 30429351635774257486278917 5705503431707673278677297)
            ·
              refine ⟨4279127573780754959007973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5705503431707673278677297 4279127573780754959007973)
              ·
                refine ⟨802336420083891554813995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4279127573780754959007973 802336420083891554813995)
                ·
                  refine ⟨1203504630125837332220993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 802336420083891554813995 1203504630125837332220993)
                  ·
                    refine ⟨902628472594377999165745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1203504630125837332220993 902628472594377999165745)
                    ·
                      refine ⟨676971354445783499374309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 902628472594377999165745 676971354445783499374309)
                      ·
                        rfl

theorem cell23_1318397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 4, 1, 2, 2].length) (baseStart_1318397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318397 prefixEnd_1318397 := by exact prefixLift 1318397
  have htrace : WordTrace (prefixWord ++ tailWord_1318397) baseStart_1318397 baseEnd_1318397 := by
    simpa [prefixWord, tailWord_1318397, baseEnd_1318397] using wordTrace_append hprefix tailTrace_1318397
  have hstable : (prefixWord ++ tailWord_1318397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318397).length < 2 ^ (prefixWord ++ tailWord_1318397).sum := by decide
  have hdescent : baseEnd_1318397 < baseStart_1318397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318399 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 2, 7]
def baseStart_1318399 : Nat := 118140960795 + 1318399 * 2 ^ 59
def prefixEnd_1318399 : Nat := 4983230072969 + 3 ^ 40 * 1318399 * 2
def baseEnd_1318399 : Nat := 225657460469030830516433

theorem tailTrace_1318399 : CollatzResearch.WordTrace tailWord_1318399 prefixEnd_1318399 225657460469030830516433 := by
  unfold tailWord_1318399
  simp only [CollatzResearch.WordTrace]
  refine ⟨48085961950673062468038251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32057307967115374978692167 48085961950673062468038251)
  ·
    refine ⟨72128942926009593702057377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48085961950673062468038251 72128942926009593702057377)
    ·
      refine ⟨54096707194507195276543033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72128942926009593702057377 54096707194507195276543033)
      ·
        refine ⟨40572530395880396457407275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54096707194507195276543033 40572530395880396457407275)
        ·
          refine ⟨60858795593820594686110913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40572530395880396457407275 60858795593820594686110913)
          ·
            refine ⟨45644096695365446014583185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 60858795593820594686110913 45644096695365446014583185)
            ·
              refine ⟨34233072521524084510937389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 45644096695365446014583185 34233072521524084510937389)
              ·
                refine ⟨12837402195571531691601521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 34233072521524084510937389 12837402195571531691601521)
                ·
                  refine ⟨9628051646678648768701141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12837402195571531691601521 9628051646678648768701141)
                  ·
                    refine ⟨225657460469030830516433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9628051646678648768701141 225657460469030830516433)
                    ·
                      rfl

theorem cell23_1318399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 2, 7].length) (baseStart_1318399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318399 prefixEnd_1318399 := by exact prefixLift 1318399
  have htrace : WordTrace (prefixWord ++ tailWord_1318399) baseStart_1318399 baseEnd_1318399 := by
    simpa [prefixWord, tailWord_1318399, baseEnd_1318399] using wordTrace_append hprefix tailTrace_1318399
  have hstable : (prefixWord ++ tailWord_1318399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318399).length < 2 ^ (prefixWord ++ tailWord_1318399).sum := by decide
  have hdescent : baseEnd_1318399 < baseStart_1318399 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318504 : List Nat := [2, 1, 4, 3, 1, 2, 2, 2, 2, 2, 2]
def baseStart_1318504 : Nat := 118140960795 + 1318504 * 2 ^ 59
def prefixEnd_1318504 : Nat := 4983230072969 + 3 ^ 40 * 1318504 * 2
def baseEnd_1318504 : Nat := 677026296875814580736317

theorem tailTrace_1318504 : CollatzResearch.WordTrace tailWord_1318504 prefixEnd_1318504 677026296875814580736317 := by
  unfold tailWord_1318504
  simp only [CollatzResearch.WordTrace]
  refine ⟨24044895807646332700305283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32059861076861776933740377 24044895807646332700305283)
  ·
    refine ⟨36067343711469499050457925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24044895807646332700305283 36067343711469499050457925)
    ·
      refine ⟨6762626945900531071960861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36067343711469499050457925 6762626945900531071960861)
      ·
        refine ⟨2535985104712699151985323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6762626945900531071960861 2535985104712699151985323)
        ·
          refine ⟨3803977657069048727977985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2535985104712699151985323 3803977657069048727977985)
          ·
            refine ⟨2852983242801786545983489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3803977657069048727977985 2852983242801786545983489)
            ·
              refine ⟨2139737432101339909487617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2852983242801786545983489 2139737432101339909487617)
              ·
                refine ⟨1604803074076004932115713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2139737432101339909487617 1604803074076004932115713)
                ·
                  refine ⟨1203602305557003699086785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1604803074076004932115713 1203602305557003699086785)
                  ·
                    refine ⟨902701729167752774315089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1203602305557003699086785 902701729167752774315089)
                    ·
                      refine ⟨677026296875814580736317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 902701729167752774315089 677026296875814580736317)
                      ·
                        rfl

theorem cell23_1318504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 2, 2, 2, 2].length) (baseStart_1318504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318504 prefixEnd_1318504 := by exact prefixLift 1318504
  have htrace : WordTrace (prefixWord ++ tailWord_1318504) baseStart_1318504 baseEnd_1318504 := by
    simpa [prefixWord, tailWord_1318504, baseEnd_1318504] using wordTrace_append hprefix tailTrace_1318504
  have hstable : (prefixWord ++ tailWord_1318504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318504).length < 2 ^ (prefixWord ++ tailWord_1318504).sum := by decide
  have hdescent : baseEnd_1318504 < baseStart_1318504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318543 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 6, 4, 2]
def baseStart_1318543 : Nat := 118140960795 + 1318543 * 2 ^ 59
def prefixEnd_1318543 : Nat := 4983230072969 + 3 ^ 40 * 1318543 * 2
def baseEnd_1318543 : Nat := 677046322621339928148637

theorem tailTrace_1318543 : CollatzResearch.WordTrace tailWord_1318543 prefixEnd_1318543 677046322621339928148637 := by
  unfold tailWord_1318543
  simp only [CollatzResearch.WordTrace]
  refine ⟨48091214062151375061280283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32060809374767583374186855 48091214062151375061280283)
  ·
    refine ⟨72136821093227062591920425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48091214062151375061280283 72136821093227062591920425)
    ·
      refine ⟨54102615819920296943940319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72136821093227062591920425 54102615819920296943940319)
      ·
        refine ⟨81153923729880445415910479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54102615819920296943940319 81153923729880445415910479)
        ·
          refine ⟨121730885594820668123865719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81153923729880445415910479 121730885594820668123865719)
          ·
            refine ⟨182596328392231002185798579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121730885594820668123865719 182596328392231002185798579)
            ·
              refine ⟨273894492588346503278697869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182596328392231002185798579 273894492588346503278697869)
              ·
                refine ⟨102710434720629938729511701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 273894492588346503278697869 102710434720629938729511701)
                ·
                  refine ⟨4814551627529528377945861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 102710434720629938729511701 4814551627529528377945861)
                  ·
                    refine ⟨902728430161786570864849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4814551627529528377945861 902728430161786570864849)
                    ·
                      refine ⟨677046322621339928148637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 902728430161786570864849 677046322621339928148637)
                      ·
                        rfl

theorem cell23_1318543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 6, 4, 2].length) (baseStart_1318543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318543 prefixEnd_1318543 := by exact prefixLift 1318543
  have htrace : WordTrace (prefixWord ++ tailWord_1318543) baseStart_1318543 baseEnd_1318543 := by
    simpa [prefixWord, tailWord_1318543, baseEnd_1318543] using wordTrace_append hprefix tailTrace_1318543
  have hstable : (prefixWord ++ tailWord_1318543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318543).length < 2 ^ (prefixWord ++ tailWord_1318543).sum := by decide
  have hdescent : baseEnd_1318543 < baseStart_1318543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318560 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 2, 4, 2]
def baseStart_1318560 : Nat := 118140960795 + 1318560 * 2 ^ 59
def prefixEnd_1318560 : Nat := 4983230072969 + 3 ^ 40 * 1318560 * 2
def baseEnd_1318560 : Nat := 677055051792466361636059

theorem tailTrace_1318560 : CollatzResearch.WordTrace tailWord_1318560 prefixEnd_1318560 677055051792466361636059 := by
  unfold tailWord_1318560
  simp only [CollatzResearch.WordTrace]
  refine ⟨24045917051544893482324567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32061222735393191309766089 24045917051544893482324567)
  ·
    refine ⟨36068875577317340223486851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24045917051544893482324567 36068875577317340223486851)
    ·
      refine ⟨54103313365976010335230277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36068875577317340223486851 54103313365976010335230277)
      ·
        refine ⟨10144371256120501937855677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 54103313365976010335230277 10144371256120501937855677)
        ·
          refine ⟨3804139221045188226695879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10144371256120501937855677 3804139221045188226695879)
          ·
            refine ⟨5706208831567782340043819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3804139221045188226695879 5706208831567782340043819)
            ·
              refine ⟨8559313247351673510065729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5706208831567782340043819 8559313247351673510065729)
              ·
                refine ⟨6419484935513755132549297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8559313247351673510065729 6419484935513755132549297)
                ·
                  refine ⟨4814613701635316349411973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6419484935513755132549297 4814613701635316349411973)
                  ·
                    refine ⟨902740069056621815514745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4814613701635316349411973 902740069056621815514745)
                    ·
                      refine ⟨677055051792466361636059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 902740069056621815514745 677055051792466361636059)
                      ·
                        rfl

theorem cell23_1318560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_1318560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318560 prefixEnd_1318560 := by exact prefixLift 1318560
  have htrace : WordTrace (prefixWord ++ tailWord_1318560) baseStart_1318560 baseEnd_1318560 := by
    simpa [prefixWord, tailWord_1318560, baseEnd_1318560] using wordTrace_append hprefix tailTrace_1318560
  have hstable : (prefixWord ++ tailWord_1318560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318560).length < 2 ^ (prefixWord ++ tailWord_1318560).sum := by decide
  have hdescent : baseEnd_1318560 < baseStart_1318560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318563 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 3]
def baseStart_1318563 : Nat := 118140960795 + 1318563 * 2 ^ 59
def prefixEnd_1318563 : Nat := 4983230072969 + 3 ^ 40 * 1318563 * 2
def baseEnd_1318563 : Nat := 677056592234429849898545

theorem tailTrace_1318563 : CollatzResearch.WordTrace tailWord_1318563 prefixEnd_1318563 677056592234429849898545 := by
  unfold tailWord_1318563
  simp only [CollatzResearch.WordTrace]
  refine ⟨48091943522078918477008343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32061295681385945651338895 48091943522078918477008343)
  ·
    refine ⟨72137915283118377715512515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48091943522078918477008343 72137915283118377715512515)
    ·
      refine ⟨108206872924677566573268773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 72137915283118377715512515 108206872924677566573268773)
      ·
        refine ⟨20288788673377043732487895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 108206872924677566573268773 20288788673377043732487895)
        ·
          refine ⟨30433183010065565598731843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20288788673377043732487895 30433183010065565598731843)
          ·
            refine ⟨45649774515098348398097765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30433183010065565598731843 45649774515098348398097765)
            ·
              refine ⟨8559332721580940324643331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45649774515098348398097765 8559332721580940324643331)
              ·
                refine ⟨12838999082371410486964997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8559332721580940324643331 12838999082371410486964997)
                ·
                  refine ⟨2407312327944639466305937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12838999082371410486964997 2407312327944639466305937)
                  ·
                    refine ⟨1805484245958479599729453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2407312327944639466305937 1805484245958479599729453)
                    ·
                      refine ⟨677056592234429849898545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1805484245958479599729453 677056592234429849898545)
                      ·
                        rfl

theorem cell23_1318563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 2, 3].length) (baseStart_1318563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318563 prefixEnd_1318563 := by exact prefixLift 1318563
  have htrace : WordTrace (prefixWord ++ tailWord_1318563) baseStart_1318563 baseEnd_1318563 := by
    simpa [prefixWord, tailWord_1318563, baseEnd_1318563] using wordTrace_append hprefix tailTrace_1318563
  have hstable : (prefixWord ++ tailWord_1318563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318563).length < 2 ^ (prefixWord ++ tailWord_1318563).sum := by decide
  have hdescent : baseEnd_1318563 < baseStart_1318563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318573 : List Nat := [1, 5, 2, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_1318573 : Nat := 118140960795 + 1318573 * 2 ^ 59
def prefixEnd_1318573 : Nat := 4983230072969 + 3 ^ 40 * 1318573 * 2
def baseEnd_1318573 : Nat := 677061727040974810773499

theorem tailTrace_1318573 : CollatzResearch.WordTrace tailWord_1318573 prefixEnd_1318573 677061727040974810773499 := by
  unfold tailWord_1318573
  simp only [CollatzResearch.WordTrace]
  refine ⟨48092308252042690184872373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32061538834695126789914915 48092308252042690184872373)
  ·
    refine ⟨4508653898629002204831785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 48092308252042690184872373 4508653898629002204831785)
    ·
      refine ⟨3381490423971751653623839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4508653898629002204831785 3381490423971751653623839)
      ·
        refine ⟨5072235635957627480435759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3381490423971751653623839 5072235635957627480435759)
        ·
          refine ⟨7608353453936441220653639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5072235635957627480435759 7608353453936441220653639)
          ·
            refine ⟨11412530180904661830980459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7608353453936441220653639 11412530180904661830980459)
            ·
              refine ⟨17118795271356992746470689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11412530180904661830980459 17118795271356992746470689)
              ·
                refine ⟨12839096453517744559853017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17118795271356992746470689 12839096453517744559853017)
                ·
                  refine ⟨9629322340138308419889763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12839096453517744559853017 9629322340138308419889763)
                  ·
                    refine ⟨14443983510207462629834645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9629322340138308419889763 14443983510207462629834645)
                    ·
                      refine ⟨677061727040974810773499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 14443983510207462629834645 677061727040974810773499)
                      ·
                        rfl

theorem cell23_1318573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_1318573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318573 prefixEnd_1318573 := by exact prefixLift 1318573
  have htrace : WordTrace (prefixWord ++ tailWord_1318573) baseStart_1318573 baseEnd_1318573 := by
    simpa [prefixWord, tailWord_1318573, baseEnd_1318573] using wordTrace_append hprefix tailTrace_1318573
  have hstable : (prefixWord ++ tailWord_1318573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318573).length < 2 ^ (prefixWord ++ tailWord_1318573).sum := by decide
  have hdescent : baseEnd_1318573 < baseStart_1318573 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318621 : List Nat := [1, 4, 3, 3, 2, 1, 1, 1, 3, 4]
def baseStart_1318621 : Nat := 118140960795 + 1318621 * 2 ^ 59
def prefixEnd_1318621 : Nat := 4983230072969 + 3 ^ 40 * 1318621 * 2
def baseEnd_1318621 : Nat := 225695458037463540991093

theorem tailTrace_1318621 : CollatzResearch.WordTrace tailWord_1318621 prefixEnd_1318621 225695458037463540991093 := by
  unfold tailWord_1318621
  simp only [CollatzResearch.WordTrace]
  refine ⟨48094058955868794382619717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32062705970579196255079811 48094058955868794382619717)
  ·
    refine ⟨9017636054225398946741197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48094058955868794382619717 9017636054225398946741197)
    ·
      refine ⟨3381613520334524605027949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9017636054225398946741197 3381613520334524605027949)
      ·
        refine ⟨1268105070125446726885481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3381613520334524605027949 1268105070125446726885481)
        ·
          refine ⟨951078802594085045164111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1268105070125446726885481 951078802594085045164111)
          ·
            refine ⟨1426618203891127567746167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 951078802594085045164111 1426618203891127567746167)
            ·
              refine ⟨2139927305836691351619251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1426618203891127567746167 2139927305836691351619251)
              ·
                refine ⟨3209890958755037027428877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2139927305836691351619251 3209890958755037027428877)
                ·
                  refine ⟨1203709109533138885285829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3209890958755037027428877 1203709109533138885285829)
                  ·
                    refine ⟨225695458037463540991093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1203709109533138885285829 225695458037463540991093)
                    ·
                      rfl

theorem cell23_1318621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_1318621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318621 prefixEnd_1318621 := by exact prefixLift 1318621
  have htrace : WordTrace (prefixWord ++ tailWord_1318621) baseStart_1318621 baseEnd_1318621 := by
    simpa [prefixWord, tailWord_1318621, baseEnd_1318621] using wordTrace_append hprefix tailTrace_1318621
  have hstable : (prefixWord ++ tailWord_1318621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318621).length < 2 ^ (prefixWord ++ tailWord_1318621).sum := by decide
  have hdescent : baseEnd_1318621 < baseStart_1318621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318633 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 3, 1, 4]
def baseStart_1318633 : Nat := 118140960795 + 1318633 * 2 ^ 59
def prefixEnd_1318633 : Nat := 4983230072969 + 3 ^ 40 * 1318633 * 2
def baseEnd_1318633 : Nat := 677092535880244576023223

theorem tailTrace_1318633 : CollatzResearch.WordTrace tailWord_1318633 prefixEnd_1318633 677092535880244576023223 := by
  unfold tailWord_1318633
  simp only [CollatzResearch.WordTrace]
  refine ⟨48094496631825320432056553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32062997754550213621371035 48094496631825320432056553)
  ·
    refine ⟨36070872473868990324042415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 48094496631825320432056553 36070872473868990324042415)
    ·
      refine ⟨54106308710803485486063623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 36070872473868990324042415 54106308710803485486063623)
      ·
        refine ⟨81159463066205228229095435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54106308710803485486063623 81159463066205228229095435)
        ·
          refine ⟨121739194599307842343643153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81159463066205228229095435 121739194599307842343643153)
          ·
            refine ⟨91304395949480881757732365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121739194599307842343643153 91304395949480881757732365)
            ·
              refine ⟨34239148481055330659149637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 91304395949480881757732365 34239148481055330659149637)
              ·
                refine ⟨6419840340197874498590557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 34239148481055330659149637 6419840340197874498590557)
                ·
                  refine ⟨2407440127574202936971459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6419840340197874498590557 2407440127574202936971459)
                  ·
                    refine ⟨3611160191361304405457189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2407440127574202936971459 3611160191361304405457189)
                    ·
                      refine ⟨677092535880244576023223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3611160191361304405457189 677092535880244576023223)
                      ·
                        rfl

theorem cell23_1318633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 1, 4].length) (baseStart_1318633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318633 prefixEnd_1318633 := by exact prefixLift 1318633
  have htrace : WordTrace (prefixWord ++ tailWord_1318633) baseStart_1318633 baseEnd_1318633 := by
    simpa [prefixWord, tailWord_1318633, baseEnd_1318633] using wordTrace_append hprefix tailTrace_1318633
  have hstable : (prefixWord ++ tailWord_1318633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318633).length < 2 ^ (prefixWord ++ tailWord_1318633).sum := by decide
  have hdescent : baseEnd_1318633 < baseStart_1318633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318660 : List Nat := [2, 3, 2, 2, 1, 3, 1, 2, 1, 6]
def baseStart_1318660 : Nat := 118140960795 + 1318660 * 2 ^ 59
def prefixEnd_1318660 : Nat := 4983230072969 + 3 ^ 40 * 1318660 * 2
def baseEnd_1318660 : Nat := 225702133285971990128533

theorem tailTrace_1318660 : CollatzResearch.WordTrace tailWord_1318660 prefixEnd_1318660 225702133285971990128533 := by
  unfold tailWord_1318660
  simp only [CollatzResearch.WordTrace]
  refine ⟨24047740701363752021644717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32063654268485002695526289 24047740701363752021644717)
  ·
    refine ⟨9017902763011407008116769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24047740701363752021644717 9017902763011407008116769)
    ·
      refine ⟨6763427072258555256087577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9017902763011407008116769 6763427072258555256087577)
      ·
        refine ⟨5072570304193916442065683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6763427072258555256087577 5072570304193916442065683)
        ·
          refine ⟨7608855456290874663098525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5072570304193916442065683 7608855456290874663098525)
          ·
            refine ⟨2853320796109077998661947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7608855456290874663098525 2853320796109077998661947)
            ·
              refine ⟨4279981194163616997992921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2853320796109077998661947 4279981194163616997992921)
              ·
                refine ⟨3209985895622712748494691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4279981194163616997992921 3209985895622712748494691)
                ·
                  refine ⟨4814978843434069122742037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3209985895622712748494691 4814978843434069122742037)
                  ·
                    refine ⟨225702133285971990128533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4814978843434069122742037 225702133285971990128533)
                    ·
                      rfl

theorem cell23_1318660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_1318660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318660 prefixEnd_1318660 := by exact prefixLift 1318660
  have htrace : WordTrace (prefixWord ++ tailWord_1318660) baseStart_1318660 baseEnd_1318660 := by
    simpa [prefixWord, tailWord_1318660, baseEnd_1318660] using wordTrace_append hprefix tailTrace_1318660
  have hstable : (prefixWord ++ tailWord_1318660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318660).length < 2 ^ (prefixWord ++ tailWord_1318660).sum := by decide
  have hdescent : baseEnd_1318660 < baseStart_1318660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318670 : List Nat := [4, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5]
def baseStart_1318670 : Nat := 118140960795 + 1318670 * 2 ^ 59
def prefixEnd_1318670 : Nat := 4983230072969 + 3 ^ 40 * 1318670 * 2
def baseEnd_1318670 : Nat := 677111534664460931260553

theorem tailTrace_1318670 : CollatzResearch.WordTrace tailWord_1318670 prefixEnd_1318670 677111534664460931260553 := by
  unfold tailWord_1318670
  simp only [CollatzResearch.WordTrace]
  refine ⟨6011980766586409468894183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32063897421794183834102309 6011980766586409468894183)
  ·
    refine ⟨9017971149879614203341275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6011980766586409468894183 9017971149879614203341275)
    ·
      refine ⟨13526956724819421305011913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9017971149879614203341275 13526956724819421305011913)
      ·
        refine ⟨10145217543614565978758935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13526956724819421305011913 10145217543614565978758935)
        ·
          refine ⟨15217826315421848968138403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10145217543614565978758935 15217826315421848968138403)
          ·
            refine ⟨22826739473132773452207605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15217826315421848968138403 22826739473132773452207605)
            ·
              refine ⟨2140006825606197511144463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 22826739473132773452207605 2140006825606197511144463)
              ·
                refine ⟨3210010238409296266716695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2140006825606197511144463 3210010238409296266716695)
                ·
                  refine ⟨4815015357613944400075043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3210010238409296266716695 4815015357613944400075043)
                  ·
                    refine ⟨7222523036420916600112565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4815015357613944400075043 7222523036420916600112565)
                    ·
                      refine ⟨677111534664460931260553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7222523036420916600112565 677111534664460931260553)
                      ·
                        rfl

theorem cell23_1318670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 1, 1, 5].length) (baseStart_1318670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318670 prefixEnd_1318670 := by exact prefixLift 1318670
  have htrace : WordTrace (prefixWord ++ tailWord_1318670) baseStart_1318670 baseEnd_1318670 := by
    simpa [prefixWord, tailWord_1318670, baseEnd_1318670] using wordTrace_append hprefix tailTrace_1318670
  have hstable : (prefixWord ++ tailWord_1318670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318670).length < 2 ^ (prefixWord ++ tailWord_1318670).sum := by decide
  have hdescent : baseEnd_1318670 < baseStart_1318670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318677 : List Nat := [1, 3, 2, 1, 2, 4, 2, 2, 2, 4]
def baseStart_1318677 : Nat := 118140960795 + 1318677 * 2 ^ 59
def prefixEnd_1318677 : Nat := 4983230072969 + 3 ^ 40 * 1318677 * 2
def baseEnd_1318677 : Nat := 225705043009680801291007

theorem tailTrace_1318677 : CollatzResearch.WordTrace tailWord_1318677 prefixEnd_1318677 225705043009680801291007 := by
  unfold tailWord_1318677
  simp only [CollatzResearch.WordTrace]
  refine ⟨48096101443665915946658285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32064067629110610631105523 48096101443665915946658285)
  ·
    refine ⟨18036038041374718479996857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 48096101443665915946658285 18036038041374718479996857)
    ·
      refine ⟨13527028531031038859997643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18036038041374718479996857 13527028531031038859997643)
      ·
        refine ⟨20290542796546558289996465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13527028531031038859997643 20290542796546558289996465)
        ·
          refine ⟨15217907097409918717497349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20290542796546558289996465 15217907097409918717497349)
          ·
            refine ⟨2853357580764359759530753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15217907097409918717497349 2853357580764359759530753)
            ·
              refine ⟨2140018185573269819648065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2853357580764359759530753 2140018185573269819648065)
              ·
                refine ⟨1605013639179952364736049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2140018185573269819648065 1605013639179952364736049)
                ·
                  refine ⟨1203760229384964273552037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1605013639179952364736049 1203760229384964273552037)
                  ·
                    refine ⟨225705043009680801291007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1203760229384964273552037 225705043009680801291007)
                    ·
                      rfl

theorem cell23_1318677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_1318677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318677 prefixEnd_1318677 := by exact prefixLift 1318677
  have htrace : WordTrace (prefixWord ++ tailWord_1318677) baseStart_1318677 baseEnd_1318677 := by
    simpa [prefixWord, tailWord_1318677, baseEnd_1318677] using wordTrace_append hprefix tailTrace_1318677
  have hstable : (prefixWord ++ tailWord_1318677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318677).length < 2 ^ (prefixWord ++ tailWord_1318677).sum := by decide
  have hdescent : baseEnd_1318677 < baseStart_1318677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318700 : List Nat := [2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 3]
def baseStart_1318700 : Nat := 118140960795 + 1318700 * 2 ^ 59
def prefixEnd_1318700 : Nat := 4983230072969 + 3 ^ 40 * 1318700 * 2
def baseEnd_1318700 : Nat := 677126939084095813885415

theorem tailTrace_1318700 : CollatzResearch.WordTrace tailWord_1318700 prefixEnd_1318700 677126939084095813885415 := by
  unfold tailWord_1318700
  simp only [CollatzResearch.WordTrace]
  refine ⟨24048470161291295437372777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32064626881721727249830369 24048470161291295437372777)
  ·
    refine ⟨18036352620968471578029583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24048470161291295437372777 18036352620968471578029583)
    ·
      refine ⟨27054528931452707367044375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18036352620968471578029583 27054528931452707367044375)
      ·
        refine ⟨40581793397179061050566563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27054528931452707367044375 40581793397179061050566563)
        ·
          refine ⟨60872690095768591575849845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 40581793397179061050566563 60872690095768591575849845)
          ·
            refine ⟨5706814696478305460235923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 60872690095768591575849845 5706814696478305460235923)
            ·
              refine ⟨8560222044717458190353885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5706814696478305460235923 8560222044717458190353885)
              ·
                refine ⟨3210083266769046821382707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8560222044717458190353885 3210083266769046821382707)
                ·
                  refine ⟨4815124900153570232074061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3210083266769046821382707 4815124900153570232074061)
                  ·
                    refine ⟨1805671837557588837027773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4815124900153570232074061 1805671837557588837027773)
                    ·
                      refine ⟨677126939084095813885415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1805671837557588837027773 677126939084095813885415)
                      ·
                        rfl

theorem cell23_1318700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 3].length) (baseStart_1318700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318700 prefixEnd_1318700 := by exact prefixLift 1318700
  have htrace : WordTrace (prefixWord ++ tailWord_1318700) baseStart_1318700 baseEnd_1318700 := by
    simpa [prefixWord, tailWord_1318700, baseEnd_1318700] using wordTrace_append hprefix tailTrace_1318700
  have hstable : (prefixWord ++ tailWord_1318700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318700).length < 2 ^ (prefixWord ++ tailWord_1318700).sum := by decide
  have hdescent : baseEnd_1318700 < baseStart_1318700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318717 : List Nat := [1, 4, 1, 4, 1, 1, 2, 2, 1, 3, 3]
def baseStart_1318717 : Nat := 118140960795 + 1318717 * 2 ^ 59
def prefixEnd_1318717 : Nat := 4983230072969 + 3 ^ 40 * 1318717 * 2
def baseEnd_1318717 : Nat := 677135668255222247372837

theorem tailTrace_1318717 : CollatzResearch.WordTrace tailWord_1318717 prefixEnd_1318717 677135668255222247372837 := by
  unfold tailWord_1318717
  simp only [CollatzResearch.WordTrace]
  refine ⟨48097560363521002778114405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32065040242347335185409603 48097560363521002778114405)
  ·
    refine ⟨9018292568160188020896451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 48097560363521002778114405 9018292568160188020896451)
    ·
      refine ⟨13527438852240282031344677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9018292568160188020896451 13527438852240282031344677)
      ·
        refine ⟨2536394784795052880877127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 13527438852240282031344677 2536394784795052880877127)
        ·
          refine ⟨3804592177192579321315691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2536394784795052880877127 3804592177192579321315691)
          ·
            refine ⟨5706888265788868981973537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3804592177192579321315691 5706888265788868981973537)
            ·
              refine ⟨4280166199341651736480153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5706888265788868981973537 4280166199341651736480153)
              ·
                refine ⟨3210124649506238802360115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4280166199341651736480153 3210124649506238802360115)
                ·
                  refine ⟨4815186974259358203540173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3210124649506238802360115 4815186974259358203540173)
                  ·
                    refine ⟨1805695115347259326327565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4815186974259358203540173 1805695115347259326327565)
                    ·
                      refine ⟨677135668255222247372837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1805695115347259326327565 677135668255222247372837)
                      ·
                        rfl

theorem cell23_1318717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_1318717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318717 prefixEnd_1318717 := by exact prefixLift 1318717
  have htrace : WordTrace (prefixWord ++ tailWord_1318717) baseStart_1318717 baseEnd_1318717 := by
    simpa [prefixWord, tailWord_1318717, baseEnd_1318717] using wordTrace_append hprefix tailTrace_1318717
  have hstable : (prefixWord ++ tailWord_1318717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318717).length < 2 ^ (prefixWord ++ tailWord_1318717).sum := by decide
  have hdescent : baseEnd_1318717 < baseStart_1318717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318718 : List Nat := [4, 2, 1, 2, 2, 2, 2, 3, 1, 2, 2]
def baseStart_1318718 : Nat := 118140960795 + 1318718 * 2 ^ 59
def prefixEnd_1318718 : Nat := 4983230072969 + 3 ^ 40 * 1318718 * 2
def baseEnd_1318718 : Nat := 677136181735876743460333

theorem tailTrace_1318718 : CollatzResearch.WordTrace tailWord_1318718 prefixEnd_1318718 677136181735876743460333 := by
  unfold tailWord_1318718
  simp only [CollatzResearch.WordTrace]
  refine ⟨6012199604564672493612601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 32065064557678253299267205 6012199604564672493612601)
  ·
    refine ⟨4509149703423504370209451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6012199604564672493612601 4509149703423504370209451)
    ·
      refine ⟨6763724555135256555314177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4509149703423504370209451 6763724555135256555314177)
      ·
        refine ⟨5072793416351442416485633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6763724555135256555314177 5072793416351442416485633)
        ·
          refine ⟨3804595062263581812364225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5072793416351442416485633 3804595062263581812364225)
          ·
            refine ⟨2853446296697686359273169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3804595062263581812364225 2853446296697686359273169)
            ·
              refine ⟨2140084722523264769454877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2853446296697686359273169 2140084722523264769454877)
              ·
                refine ⟨802531770946224288545579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2140084722523264769454877 802531770946224288545579)
                ·
                  refine ⟨1203797656419336432818369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 802531770946224288545579 1203797656419336432818369)
                  ·
                    refine ⟨902848242314502324613777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1203797656419336432818369 902848242314502324613777)
                    ·
                      refine ⟨677136181735876743460333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 902848242314502324613777 677136181735876743460333)
                      ·
                        rfl

theorem cell23_1318718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_1318718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318718 prefixEnd_1318718 := by exact prefixLift 1318718
  have htrace : WordTrace (prefixWord ++ tailWord_1318718) baseStart_1318718 baseEnd_1318718 := by
    simpa [prefixWord, tailWord_1318718, baseEnd_1318718] using wordTrace_append hprefix tailTrace_1318718
  have hstable : (prefixWord ++ tailWord_1318718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318718).length < 2 ^ (prefixWord ++ tailWord_1318718).sum := by decide
  have hdescent : baseEnd_1318718 < baseStart_1318718 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318760 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 2, 1, 5]
def baseStart_1318760 : Nat := 118140960795 + 1318760 * 2 ^ 59
def prefixEnd_1318760 : Nat := 4983230072969 + 3 ^ 40 * 1318760 * 2
def baseEnd_1318760 : Nat := 677157747923365579135139

theorem tailTrace_1318760 : CollatzResearch.WordTrace tailWord_1318760 prefixEnd_1318760 677157747923365579135139 := by
  unfold tailWord_1318760
  simp only [CollatzResearch.WordTrace]
  refine ⟨24049564351182610560964867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32066085801576814081286489 24049564351182610560964867)
  ·
    refine ⟨36074346526773915841447301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24049564351182610560964867 36074346526773915841447301)
    ·
      refine ⟨6763939973770109220271369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 36074346526773915841447301 6763939973770109220271369)
      ·
        refine ⟨5072954980327581915203527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6763939973770109220271369 5072954980327581915203527)
        ·
          refine ⟨7609432470491372872805291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5072954980327581915203527 7609432470491372872805291)
          ·
            refine ⟨11414148705737059309207937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7609432470491372872805291 11414148705737059309207937)
            ·
              refine ⟨8560611529302794481905953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11414148705737059309207937 8560611529302794481905953)
              ·
                refine ⟨6420458646977095861429465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8560611529302794481905953 6420458646977095861429465)
                ·
                  refine ⟨4815343985232821896072099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6420458646977095861429465 4815343985232821896072099)
                  ·
                    refine ⟨7223015977849232844108149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4815343985232821896072099 7223015977849232844108149)
                    ·
                      refine ⟨677157747923365579135139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7223015977849232844108149 677157747923365579135139)
                      ·
                        rfl

theorem cell23_1318760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 2, 1, 5].length) (baseStart_1318760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318760 prefixEnd_1318760 := by exact prefixLift 1318760
  have htrace : WordTrace (prefixWord ++ tailWord_1318760) baseStart_1318760 baseEnd_1318760 := by
    simpa [prefixWord, tailWord_1318760, baseEnd_1318760] using wordTrace_append hprefix tailTrace_1318760
  have hstable : (prefixWord ++ tailWord_1318760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318760).length < 2 ^ (prefixWord ++ tailWord_1318760).sum := by decide
  have hdescent : baseEnd_1318760 < baseStart_1318760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318808 : List Nat := [2, 1, 2, 6, 1, 1, 1, 3, 2, 2, 2]
def baseStart_1318808 : Nat := 118140960795 + 1318808 * 2 ^ 59
def prefixEnd_1318808 : Nat := 4983230072969 + 3 ^ 40 * 1318808 * 2
def baseEnd_1318808 : Nat := 677182394994781391334919

theorem tailTrace_1318808 : CollatzResearch.WordTrace tailWord_1318808 prefixEnd_1318808 677182394994781391334919 := by
  unfold tailWord_1318808
  simp only [CollatzResearch.WordTrace]
  refine ⟨24050439703095662659838539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 32067252937460883546451385 24050439703095662659838539)
  ·
    refine ⟨36075659554643493989757809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24050439703095662659838539 36075659554643493989757809)
    ·
      refine ⟨27056744665982620492318357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 36075659554643493989757809 27056744665982620492318357)
      ·
        refine ⟨1268284906217935335577423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27056744665982620492318357 1268284906217935335577423)
        ·
          refine ⟨1902427359326903003366135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1268284906217935335577423 1902427359326903003366135)
          ·
            refine ⟨2853641038990354505049203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1902427359326903003366135 2853641038990354505049203)
            ·
              refine ⟨4280461558485531757573805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2853641038990354505049203 4280461558485531757573805)
              ·
                refine ⟨1605173084432074409090177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4280461558485531757573805 1605173084432074409090177)
                ·
                  refine ⟨1203879813324055806817633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1605173084432074409090177 1203879813324055806817633)
                  ·
                    refine ⟨902909859993041855113225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1203879813324055806817633 902909859993041855113225)
                    ·
                      refine ⟨677182394994781391334919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 902909859993041855113225 677182394994781391334919)
                      ·
                        rfl

theorem cell23_1318808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 3, 2, 2, 2].length) (baseStart_1318808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318808 prefixEnd_1318808 := by exact prefixLift 1318808
  have htrace : WordTrace (prefixWord ++ tailWord_1318808) baseStart_1318808 baseEnd_1318808 := by
    simpa [prefixWord, tailWord_1318808, baseEnd_1318808] using wordTrace_append hprefix tailTrace_1318808
  have hstable : (prefixWord ++ tailWord_1318808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318808).length < 2 ^ (prefixWord ++ tailWord_1318808).sum := by decide
  have hdescent : baseEnd_1318808 < baseStart_1318808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1318847 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 2, 4, 2]
def baseStart_1318847 : Nat := 118140960795 + 1318847 * 2 ^ 59
def prefixEnd_1318847 : Nat := 4983230072969 + 3 ^ 40 * 1318847 * 2
def baseEnd_1318847 : Nat := 677202420740306738747239

theorem tailTrace_1318847 : CollatzResearch.WordTrace tailWord_1318847 prefixEnd_1318847 677202420740306738747239 := by
  unfold tailWord_1318847
  simp only [CollatzResearch.WordTrace]
  refine ⟨48102301853050034980346795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 32068201235366689986897863 48102301853050034980346795)
  ·
    refine ⟨72153452779575052470520193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 48102301853050034980346795 72153452779575052470520193)
    ·
      refine ⟨54115089584681289352890145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72153452779575052470520193 54115089584681289352890145)
      ·
        refine ⟨40586317188510967014667609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 54115089584681289352890145 40586317188510967014667609)
        ·
          refine ⟨30439737891383225261000707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 40586317188510967014667609 30439737891383225261000707)
          ·
            refine ⟨45659606837074837891501061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 30439737891383225261000707 45659606837074837891501061)
            ·
              refine ⟨8561176281951532104656449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 45659606837074837891501061 8561176281951532104656449)
              ·
                refine ⟨6420882211463649078492337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8561176281951532104656449 6420882211463649078492337)
                ·
                  refine ⟨4815661658597736808869253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6420882211463649078492337 4815661658597736808869253)
                  ·
                    refine ⟨902936560987075651662985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4815661658597736808869253 902936560987075651662985)
                    ·
                      refine ⟨677202420740306738747239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 902936560987075651662985 677202420740306738747239)
                      ·
                        rfl

theorem cell23_1318847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 4, 2].length) (baseStart_1318847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1318847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1318847 prefixEnd_1318847 := by exact prefixLift 1318847
  have htrace : WordTrace (prefixWord ++ tailWord_1318847) baseStart_1318847 baseEnd_1318847 := by
    simpa [prefixWord, tailWord_1318847, baseEnd_1318847] using wordTrace_append hprefix tailTrace_1318847
  have hstable : (prefixWord ++ tailWord_1318847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1318847).length < 2 ^ (prefixWord ++ tailWord_1318847).sum := by decide
  have hdescent : baseEnd_1318847 < baseStart_1318847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1318847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
