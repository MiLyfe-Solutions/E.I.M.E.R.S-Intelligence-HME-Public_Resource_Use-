import V185TrunkScan21Chunk152

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1866102 : List Nat := [5, 1, 1, 4, 2, 8]
def baseStart_1866102 : Nat := 118140960795 + 1866102 * 2 ^ 59
def prefixEnd_1866102 : Nat := 4983230072969 + 3 ^ 40 * 1866102 * 2
def baseEnd_1866102 : Nat := 15772959280931079852559

theorem tailTrace_1866102 : CollatzResearch.WordTrace tailWord_1866102 prefixEnd_1866102 15772959280931079852559 := by
  unfold tailWord_1866102
  simp only [CollatzResearch.WordTrace]
  refine ⟨4253895717839914605832535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45374887656959089128880373 4253895717839914605832535)
  ·
    refine ⟨6380843576759871908748803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4253895717839914605832535 6380843576759871908748803)
    ·
      refine ⟨9571265365139807863123205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6380843576759871908748803 9571265365139807863123205)
      ·
        refine ⟨1794612255963713974335601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9571265365139807863123205 1794612255963713974335601)
        ·
          refine ⟨1345959191972785480751701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1794612255963713974335601 1345959191972785480751701)
          ·
            refine ⟨15772959280931079852559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1345959191972785480751701 15772959280931079852559)
            ·
              rfl

theorem cell21_1866102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 2, 8].length) (baseStart_1866102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1866102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1866102 prefixEnd_1866102 := by exact prefixLift 1866102
  have htrace : WordTrace (prefixWord ++ tailWord_1866102) baseStart_1866102 baseEnd_1866102 := by
    simpa [prefixWord, tailWord_1866102, baseEnd_1866102] using wordTrace_append hprefix tailTrace_1866102
  have hstable : (prefixWord ++ tailWord_1866102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866102).length < 2 ^ (prefixWord ++ tailWord_1866102).sum := by decide
  have hdescent : baseEnd_1866102 < baseStart_1866102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866116 : List Nat := [2, 3, 2, 1, 1, 2, 3, 4, 3]
def baseStart_1866116 : Nat := 118140960795 + 1866116 * 2 ^ 59
def prefixEnd_1866116 : Nat := 4983230072969 + 3 ^ 40 * 1866116 * 2
def baseEnd_1866116 : Nat := 425873095575878242785731

theorem tailTrace_1866116 : CollatzResearch.WordTrace tailWord_1866116 prefixEnd_1866116 425873095575878242785731 := by
  unfold tailWord_1866116
  simp only [CollatzResearch.WordTrace]
  refine ⟨34031421053693957042165101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45375228071591942722886801 34031421053693957042165101)
  ·
    refine ⟨12761782895135233890811913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34031421053693957042165101 12761782895135233890811913)
    ·
      refine ⟨9571337171351425418108935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12761782895135233890811913 9571337171351425418108935)
      ·
        refine ⟨14357005757027138127163403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9571337171351425418108935 14357005757027138127163403)
        ·
          refine ⟨21535508635540707190745105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14357005757027138127163403 21535508635540707190745105)
          ·
            refine ⟨16151631476655530393058829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21535508635540707190745105 16151631476655530393058829)
            ·
              refine ⟨6056861803745823897397061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16151631476655530393058829 6056861803745823897397061)
              ·
                refine ⟨1135661588202341980761949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6056861803745823897397061 1135661588202341980761949)
                ·
                  refine ⟨425873095575878242785731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1135661588202341980761949 425873095575878242785731)
                  ·
                    rfl

theorem cell21_1866116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_1866116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1866116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1866116 prefixEnd_1866116 := by exact prefixLift 1866116
  have htrace : WordTrace (prefixWord ++ tailWord_1866116) baseStart_1866116 baseEnd_1866116 := by
    simpa [prefixWord, tailWord_1866116, baseEnd_1866116] using wordTrace_append hprefix tailTrace_1866116
  have hstable : (prefixWord ++ tailWord_1866116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866116).length < 2 ^ (prefixWord ++ tailWord_1866116).sum := by decide
  have hdescent : baseEnd_1866116 < baseStart_1866116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866164 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 6]
def baseStart_1866164 : Nat := 118140960795 + 1866164 * 2 ^ 59
def prefixEnd_1866164 : Nat := 4983230072969 + 3 ^ 40 * 1866164 * 2
def baseEnd_1866164 : Nat := 425884049829840825985633

theorem tailTrace_1866164 : CollatzResearch.WordTrace tailWord_1866164 prefixEnd_1866164 425884049829840825985633 := by
  unfold tailWord_1866164
  simp only [CollatzResearch.WordTrace]
  refine ⟨34032296405607009141038773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45376395207476012188051697 34032296405607009141038773)
  ·
    refine ⟨3190527788025657106972385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34032296405607009141038773 3190527788025657106972385)
    ·
      refine ⟨2392895841019242830229289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3190527788025657106972385 2392895841019242830229289)
      ·
        refine ⟨1794671880764432122671967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2392895841019242830229289 1794671880764432122671967)
        ·
          refine ⟨2692007821146648184007951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1794671880764432122671967 2692007821146648184007951)
          ·
            refine ⟨4038011731719972276011927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2692007821146648184007951 4038011731719972276011927)
            ·
              refine ⟨6057017597579958414017891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4038011731719972276011927 6057017597579958414017891)
              ·
                refine ⟨9085526396369937621026837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6057017597579958414017891 9085526396369937621026837)
                ·
                  refine ⟨425884049829840825985633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9085526396369937621026837 425884049829840825985633)
                  ·
                    rfl

theorem cell21_1866164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_1866164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1866164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1866164 prefixEnd_1866164 := by exact prefixLift 1866164
  have htrace : WordTrace (prefixWord ++ tailWord_1866164) baseStart_1866164 baseEnd_1866164 := by
    simpa [prefixWord, tailWord_1866164, baseEnd_1866164] using wordTrace_append hprefix tailTrace_1866164
  have hstable : (prefixWord ++ tailWord_1866164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866164).length < 2 ^ (prefixWord ++ tailWord_1866164).sum := by decide
  have hdescent : baseEnd_1866164 < baseStart_1866164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866226 : List Nat := [3, 2, 1, 4, 2, 1, 3, 2, 3]
def baseStart_1866226 : Nat := 118140960795 + 1866226 * 2 ^ 59
def prefixEnd_1866226 : Nat := 4983230072969 + 3 ^ 40 * 1866226 * 2
def baseEnd_1866226 : Nat := 425898199074542495952173

theorem tailTrace_1866226 : CollatzResearch.WordTrace tailWord_1866226 prefixEnd_1866226 425898199074542495952173 := by
  unfold tailWord_1866226
  simp only [CollatzResearch.WordTrace]
  refine ⟨17016713534247350717708633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45377902757992935247223021 17016713534247350717708633)
  ·
    refine ⟨12762535150685513038281475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17016713534247350717708633 12762535150685513038281475)
    ·
      refine ⟨19143802726028269557422213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12762535150685513038281475 19143802726028269557422213)
      ·
        refine ⟨3589463011130300542016665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19143802726028269557422213 3589463011130300542016665)
        ·
          refine ⟨2692097258347725406512499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3589463011130300542016665 2692097258347725406512499)
          ·
            refine ⟨4038145887521588109768749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2692097258347725406512499 4038145887521588109768749)
            ·
              refine ⟨1514304707820595541163281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4038145887521588109768749 1514304707820595541163281)
              ·
                refine ⟨1135728530865446655872461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1514304707820595541163281 1135728530865446655872461)
                ·
                  refine ⟨425898199074542495952173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1135728530865446655872461 425898199074542495952173)
                  ·
                    rfl

theorem cell21_1866226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 2, 3].length) (baseStart_1866226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1866226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1866226 prefixEnd_1866226 := by exact prefixLift 1866226
  have htrace : WordTrace (prefixWord ++ tailWord_1866226) baseStart_1866226 baseEnd_1866226 := by
    simpa [prefixWord, tailWord_1866226, baseEnd_1866226] using wordTrace_append hprefix tailTrace_1866226
  have hstable : (prefixWord ++ tailWord_1866226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866226).length < 2 ^ (prefixWord ++ tailWord_1866226).sum := by decide
  have hdescent : baseEnd_1866226 < baseStart_1866226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866234 : List Nat := [3, 1, 1, 1, 1, 2, 2, 5, 5]
def baseStart_1866234 : Nat := 118140960795 + 1866234 * 2 ^ 59
def prefixEnd_1866234 : Nat := 4983230072969 + 3 ^ 40 * 1866234 * 2
def baseEnd_1866234 : Nat := 425900024783536259818823

theorem tailTrace_1866234 : CollatzResearch.WordTrace tailWord_1866234 prefixEnd_1866234 425900024783536259818823 := by
  unfold tailWord_1866234
  simp only [CollatzResearch.WordTrace]
  refine ⟨17016786480240105059281439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45378097280640280158083837 17016786480240105059281439)
  ·
    refine ⟨25525179720360157588922159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17016786480240105059281439 25525179720360157588922159)
    ·
      refine ⟨38287769580540236383383239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25525179720360157588922159 38287769580540236383383239)
      ·
        refine ⟨57431654370810354575074859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38287769580540236383383239 57431654370810354575074859)
        ·
          refine ⟨86147481556215531862612289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57431654370810354575074859 86147481556215531862612289)
          ·
            refine ⟨64610611167161648896959217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86147481556215531862612289 64610611167161648896959217)
            ·
              refine ⟨48457958375371236672719413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64610611167161648896959217 48457958375371236672719413)
              ·
                refine ⟨4542933597691053438067445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48457958375371236672719413 4542933597691053438067445)
                ·
                  refine ⟨425900024783536259818823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4542933597691053438067445 425900024783536259818823)
                  ·
                    rfl

theorem cell21_1866234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 5, 5].length) (baseStart_1866234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1866234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1866234 prefixEnd_1866234 := by exact prefixLift 1866234
  have htrace : WordTrace (prefixWord ++ tailWord_1866234) baseStart_1866234 baseEnd_1866234 := by
    simpa [prefixWord, tailWord_1866234, baseEnd_1866234] using wordTrace_append hprefix tailTrace_1866234
  have hstable : (prefixWord ++ tailWord_1866234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866234).length < 2 ^ (prefixWord ++ tailWord_1866234).sum := by decide
  have hdescent : baseEnd_1866234 < baseStart_1866234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866282 : List Nat := [3, 1, 4, 1, 1, 2, 1, 4, 4]
def baseStart_1866282 : Nat := 118140960795 + 1866282 * 2 ^ 59
def prefixEnd_1866282 : Nat := 4983230072969 + 3 ^ 40 * 1866282 * 2
def baseEnd_1866282 : Nat := 425910979037498843018725

theorem tailTrace_1866282 : CollatzResearch.WordTrace tailWord_1866282 prefixEnd_1866282 425910979037498843018725 := by
  unfold tailWord_1866282
  simp only [CollatzResearch.WordTrace]
  refine ⟨17017224156196631108718275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45379264416524349623248733 17017224156196631108718275)
  ·
    refine ⟨25525836234294946663077413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17017224156196631108718275 25525836234294946663077413)
    ·
      refine ⟨4786094293930302499327015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25525836234294946663077413 4786094293930302499327015)
      ·
        refine ⟨7179141440895453748990523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4786094293930302499327015 7179141440895453748990523)
        ·
          refine ⟨10768712161343180623485785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7179141440895453748990523 10768712161343180623485785)
          ·
            refine ⟨8076534121007385467614339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10768712161343180623485785 8076534121007385467614339)
            ·
              refine ⟨12114801181511078201421509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8076534121007385467614339 12114801181511078201421509)
              ·
                refine ⟨2271525221533327162766533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12114801181511078201421509 2271525221533327162766533)
                ·
                  refine ⟨425910979037498843018725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2271525221533327162766533 425910979037498843018725)
                  ·
                    rfl

theorem cell21_1866282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_1866282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1866282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1866282 prefixEnd_1866282 := by exact prefixLift 1866282
  have htrace : WordTrace (prefixWord ++ tailWord_1866282) baseStart_1866282 baseEnd_1866282 := by
    simpa [prefixWord, tailWord_1866282, baseEnd_1866282] using wordTrace_append hprefix tailTrace_1866282
  have hstable : (prefixWord ++ tailWord_1866282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866282).length < 2 ^ (prefixWord ++ tailWord_1866282).sum := by decide
  have hdescent : baseEnd_1866282 < baseStart_1866282 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866344 : List Nat := [2, 1, 4, 3, 2, 1, 2, 1, 5]
def baseStart_1866344 : Nat := 118140960795 + 1866344 * 2 ^ 59
def prefixEnd_1866344 : Nat := 4983230072969 + 3 ^ 40 * 1866344 * 2
def baseEnd_1866344 : Nat := 425925128282200512985265

theorem tailTrace_1866344 : CollatzResearch.WordTrace tailWord_1866344 prefixEnd_1866344 425925128282200512985265 := by
  unfold tailWord_1866344
  simp only [CollatzResearch.WordTrace]
  refine ⟨34035578975280954511815043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45380771967041272682420057 34035578975280954511815043)
  ·
    refine ⟨51053368462921431767722565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34035578975280954511815043 51053368462921431767722565)
    ·
      refine ⟨9572506586797768456447981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51053368462921431767722565 9572506586797768456447981)
      ·
        refine ⟨3589689970049163171167993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9572506586797768456447981 3589689970049163171167993)
        ·
          refine ⟨2692267477536872378375995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3589689970049163171167993 2692267477536872378375995)
          ·
            refine ⟨4038401216305308567563993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2692267477536872378375995 4038401216305308567563993)
            ·
              refine ⟨3028800912228981425672995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4038401216305308567563993 3028800912228981425672995)
              ·
                refine ⟨4543201368343472138509493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3028800912228981425672995 4543201368343472138509493)
                ·
                  refine ⟨425925128282200512985265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4543201368343472138509493 425925128282200512985265)
                  ·
                    rfl

theorem cell21_1866344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 5].length) (baseStart_1866344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1866344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1866344 prefixEnd_1866344 := by exact prefixLift 1866344
  have htrace : WordTrace (prefixWord ++ tailWord_1866344) baseStart_1866344 baseEnd_1866344 := by
    simpa [prefixWord, tailWord_1866344, baseEnd_1866344] using wordTrace_append hprefix tailTrace_1866344
  have hstable : (prefixWord ++ tailWord_1866344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866344).length < 2 ^ (prefixWord ++ tailWord_1866344).sum := by decide
  have hdescent : baseEnd_1866344 < baseStart_1866344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866372 : List Nat := [2, 3, 2, 1, 3, 2, 1, 7]
def baseStart_1866372 : Nat := 118140960795 + 1866372 * 2 ^ 59
def prefixEnd_1866372 : Nat := 4983230072969 + 3 ^ 40 * 1866372 * 2
def baseEnd_1866372 : Nat := 141977172754559562172847

theorem tailTrace_1866372 : CollatzResearch.WordTrace tailWord_1866372 prefixEnd_1866372 141977172754559562172847 := by
  unfold tailWord_1866372
  simp only [CollatzResearch.WordTrace]
  refine ⟨34036089597230234902824685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45381452796306979870432913 34036089597230234902824685)
  ·
    refine ⟨12763533598961338088559257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34036089597230234902824685 12763533598961338088559257)
    ·
      refine ⟨9572650199221003566419443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12763533598961338088559257 9572650199221003566419443)
      ·
        refine ⟨14358975298831505349629165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9572650199221003566419443 14358975298831505349629165)
        ·
          refine ⟨5384615737061814506110937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14358975298831505349629165 5384615737061814506110937)
          ·
            refine ⟨4038461802796360879583203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5384615737061814506110937 4038461802796360879583203)
            ·
              refine ⟨6057692704194541319374805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4038461802796360879583203 6057692704194541319374805)
              ·
                refine ⟨141977172754559562172847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6057692704194541319374805 141977172754559562172847)
                ·
                  rfl

theorem cell21_1866372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 2, 1, 7].length) (baseStart_1866372 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1866372 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1866372 prefixEnd_1866372 := by exact prefixLift 1866372
  have htrace : WordTrace (prefixWord ++ tailWord_1866372) baseStart_1866372 baseEnd_1866372 := by
    simpa [prefixWord, tailWord_1866372, baseEnd_1866372] using wordTrace_append hprefix tailTrace_1866372
  have hstable : (prefixWord ++ tailWord_1866372).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866372).length < 2 ^ (prefixWord ++ tailWord_1866372).sum := by decide
  have hdescent : baseEnd_1866372 < baseStart_1866372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866378 : List Nat := [3, 1, 2, 3, 4, 1, 1, 3, 3]
def baseStart_1866378 : Nat := 118140960795 + 1866378 * 2 ^ 59
def prefixEnd_1866378 : Nat := 4983230072969 + 3 ^ 40 * 1866378 * 2
def baseEnd_1866378 : Nat := 425932887545424009418529

theorem tailTrace_1866378 : CollatzResearch.WordTrace tailWord_1866378 prefixEnd_1866378 425932887545424009418529 := by
  unfold tailWord_1866378
  simp only [CollatzResearch.WordTrace]
  refine ⟨17018099508109683207591947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45381598688292488553578525 17018099508109683207591947)
  ·
    refine ⟨25527149262164524811387921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17018099508109683207591947 25527149262164524811387921)
    ·
      refine ⟨19145361946623393608540941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25527149262164524811387921 19145361946623393608540941)
      ·
        refine ⟨7179510729983772603202853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19145361946623393608540941 7179510729983772603202853)
        ·
          refine ⟨1346158261871957363100535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7179510729983772603202853 1346158261871957363100535)
          ·
            refine ⟨2019237392807936044650803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1346158261871957363100535 2019237392807936044650803)
            ·
              refine ⟨3028856089211904066976205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2019237392807936044650803 3028856089211904066976205)
              ·
                refine ⟨1135821033454464025116077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3028856089211904066976205 1135821033454464025116077)
                ·
                  refine ⟨425932887545424009418529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1135821033454464025116077 425932887545424009418529)
                  ·
                    rfl

theorem cell21_1866378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 3, 3].length) (baseStart_1866378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1866378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1866378 prefixEnd_1866378 := by exact prefixLift 1866378
  have htrace : WordTrace (prefixWord ++ tailWord_1866378) baseStart_1866378 baseEnd_1866378 := by
    simpa [prefixWord, tailWord_1866378, baseEnd_1866378] using wordTrace_append hprefix tailTrace_1866378
  have hstable : (prefixWord ++ tailWord_1866378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866378).length < 2 ^ (prefixWord ++ tailWord_1866378).sum := by decide
  have hdescent : baseEnd_1866378 < baseStart_1866378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866431 : List Nat := [1, 1, 2, 2, 2, 4, 2, 7]
def baseStart_1866431 : Nat := 118140960795 + 1866431 * 2 ^ 59
def prefixEnd_1866431 : Nat := 4983230072969 + 3 ^ 40 * 1866431 * 2
def baseEnd_1866431 : Nat := 141981660955835898345029

theorem tailTrace_1866431 : CollatzResearch.WordTrace tailWord_1866431 prefixEnd_1866431 141981660955835898345029 := by
  unfold tailWord_1866431
  simp only [CollatzResearch.WordTrace]
  refine ⟨68074331101246722882047147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45382887400831148588031431 68074331101246722882047147)
  ·
    refine ⟨102111496651870084323070721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68074331101246722882047147 102111496651870084323070721)
    ·
      refine ⟨76583622488902563242303041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102111496651870084323070721 76583622488902563242303041)
      ·
        refine ⟨57437716866676922431727281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76583622488902563242303041 57437716866676922431727281)
        ·
          refine ⟨43078287650007691823795461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57437716866676922431727281 43078287650007691823795461)
          ·
            refine ⟨8077178934376442216961649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43078287650007691823795461 8077178934376442216961649)
            ·
              refine ⟨6057884200782331662721237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8077178934376442216961649 6057884200782331662721237)
              ·
                refine ⟨141981660955835898345029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6057884200782331662721237 141981660955835898345029)
                ·
                  rfl

theorem cell21_1866431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 2, 7].length) (baseStart_1866431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1866431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1866431 prefixEnd_1866431 := by exact prefixLift 1866431
  have htrace : WordTrace (prefixWord ++ tailWord_1866431) baseStart_1866431 baseEnd_1866431 := by
    simpa [prefixWord, tailWord_1866431, baseEnd_1866431] using wordTrace_append hprefix tailTrace_1866431
  have hstable : (prefixWord ++ tailWord_1866431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866431).length < 2 ^ (prefixWord ++ tailWord_1866431).sum := by decide
  have hdescent : baseEnd_1866431 < baseStart_1866431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866476 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 8]
def baseStart_1866476 : Nat := 118140960795 + 1866476 * 2 ^ 59
def prefixEnd_1866476 : Nat := 4983230072969 + 3 ^ 40 * 1866476 * 2
def baseEnd_1866476 : Nat := 425955252480597616784995

theorem tailTrace_1866476 : CollatzResearch.WordTrace tailWord_1866476 prefixEnd_1866476 425955252480597616784995 := by
  unfold tailWord_1866476
  simp only [CollatzResearch.WordTrace]
  refine ⟨34037986193041847783717641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45383981590722463711623521 34037986193041847783717641)
  ·
    refine ⟨25528489644781385837788231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34037986193041847783717641 25528489644781385837788231)
    ·
      refine ⟨38292734467172078756682347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25528489644781385837788231 38292734467172078756682347)
      ·
        refine ⟨57439101700758118135023521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38292734467172078756682347 57439101700758118135023521)
        ·
          refine ⟨43079326275568588601267641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57439101700758118135023521 43079326275568588601267641)
          ·
            refine ⟨32309494706676441450950731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43079326275568588601267641 32309494706676441450950731)
            ·
              refine ⟨48464242060014662176426097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32309494706676441450950731 48464242060014662176426097)
              ·
                refine ⟨36348181545010996632319573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48464242060014662176426097 36348181545010996632319573)
                ·
                  refine ⟨425955252480597616784995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36348181545010996632319573 425955252480597616784995)
                  ·
                    rfl

theorem cell21_1866476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_1866476 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1866476 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1866476 prefixEnd_1866476 := by exact prefixLift 1866476
  have htrace : WordTrace (prefixWord ++ tailWord_1866476) baseStart_1866476 baseEnd_1866476 := by
    simpa [prefixWord, tailWord_1866476, baseEnd_1866476] using wordTrace_append hprefix tailTrace_1866476
  have hstable : (prefixWord ++ tailWord_1866476).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866476).length < 2 ^ (prefixWord ++ tailWord_1866476).sum := by decide
  have hdescent : baseEnd_1866476 < baseStart_1866476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866552 : List Nat := [2, 1, 2, 1, 3, 2, 1, 1, 8]
def baseStart_1866552 : Nat := 118140960795 + 1866552 * 2 ^ 59
def prefixEnd_1866552 : Nat := 4983230072969 + 3 ^ 40 * 1866552 * 2
def baseEnd_1866552 : Nat := 425972596716038373518173

theorem tailTrace_1866552 : CollatzResearch.WordTrace tailWord_1866552 prefixEnd_1866552 425972596716038373518173 := by
  unfold tailWord_1866552
  simp only [CollatzResearch.WordTrace]
  refine ⟨34039372166904180273600955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45385829555872240364801273 34039372166904180273600955)
  ·
    refine ⟨51059058250356270410401433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34039372166904180273600955 51059058250356270410401433)
    ·
      refine ⟨38294293687767202807801075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51059058250356270410401433 38294293687767202807801075)
      ·
        refine ⟨57441440531650804211701613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38294293687767202807801075 57441440531650804211701613)
        ·
          refine ⟨21540540199369051579388105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57441440531650804211701613 21540540199369051579388105)
          ·
            refine ⟨16155405149526788684541079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21540540199369051579388105 16155405149526788684541079)
            ·
              refine ⟨24233107724290183026811619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16155405149526788684541079 24233107724290183026811619)
              ·
                refine ⟨36349661586435274540217429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24233107724290183026811619 36349661586435274540217429)
                ·
                  refine ⟨425972596716038373518173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36349661586435274540217429 425972596716038373518173)
                  ·
                    rfl

theorem cell21_1866552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 1, 1, 8].length) (baseStart_1866552 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1866552 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1866552 prefixEnd_1866552 := by exact prefixLift 1866552
  have htrace : WordTrace (prefixWord ++ tailWord_1866552) baseStart_1866552 baseEnd_1866552 := by
    simpa [prefixWord, tailWord_1866552, baseEnd_1866552] using wordTrace_append hprefix tailTrace_1866552
  have hstable : (prefixWord ++ tailWord_1866552).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866552).length < 2 ^ (prefixWord ++ tailWord_1866552).sum := by decide
  have hdescent : baseEnd_1866552 < baseStart_1866552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866583 : List Nat := [1, 1, 3, 2, 4, 1, 1, 8]
def baseStart_1866583 : Nat := 118140960795 + 1866583 * 2 ^ 59
def prefixEnd_1866583 : Nat := 4983230072969 + 3 ^ 40 * 1866583 * 2
def baseEnd_1866583 : Nat := 141993223779463069500481

theorem tailTrace_1866583 : CollatzResearch.WordTrace tailWord_1866583 prefixEnd_1866583 141993223779463069500481 := by
  unfold tailWord_1866583
  simp only [CollatzResearch.WordTrace]
  refine ⟨68079874996696052841580403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45386583331130701894386935 68079874996696052841580403)
  ·
    refine ⟨102119812495044079262370605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68079874996696052841580403 102119812495044079262370605)
    ·
      refine ⟨38294929685641529723388977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102119812495044079262370605 38294929685641529723388977)
      ·
        refine ⟨28721197264231147292541733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38294929685641529723388977 28721197264231147292541733)
        ·
          refine ⟨5385224487043340117351575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28721197264231147292541733 5385224487043340117351575)
          ·
            refine ⟨8077836730565010176027363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5385224487043340117351575 8077836730565010176027363)
            ·
              refine ⟨12116755095847515264041045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8077836730565010176027363 12116755095847515264041045)
              ·
                refine ⟨141993223779463069500481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12116755095847515264041045 141993223779463069500481)
                ·
                  rfl

theorem cell21_1866583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 8].length) (baseStart_1866583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1866583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1866583 prefixEnd_1866583 := by exact prefixLift 1866583
  have htrace : WordTrace (prefixWord ++ tailWord_1866583) baseStart_1866583 baseEnd_1866583 := by
    simpa [prefixWord, tailWord_1866583, baseEnd_1866583] using wordTrace_append hprefix tailTrace_1866583
  have hstable : (prefixWord ++ tailWord_1866583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866583).length < 2 ^ (prefixWord ++ tailWord_1866583).sum := by decide
  have hdescent : baseEnd_1866583 < baseStart_1866583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866586 : List Nat := [3, 1, 1, 2, 1, 4, 4, 1, 4]
def baseStart_1866586 : Nat := 118140960795 + 1866586 * 2 ^ 59
def prefixEnd_1866586 : Nat := 4983230072969 + 3 ^ 40 * 1866586 * 2
def baseEnd_1866586 : Nat := 425980355979261869951437

theorem tailTrace_1866586 : CollatzResearch.WordTrace tailWord_1866586 prefixEnd_1866586 425980355979261869951437 := by
  unfold tailWord_1866586
  simp only [CollatzResearch.WordTrace]
  refine ⟨17019996103921296088484903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45386656277123456235959741 17019996103921296088484903)
  ·
    refine ⟨25529994155881944132727355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17019996103921296088484903 25529994155881944132727355)
    ·
      refine ⟨38294991233822916199091033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25529994155881944132727355 38294991233822916199091033)
      ·
        refine ⟨28721243425367187149318275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38294991233822916199091033 28721243425367187149318275)
        ·
          refine ⟨43081865138050780723977413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28721243425367187149318275 43081865138050780723977413)
          ·
            refine ⟨8077849713384521385745765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43081865138050780723977413 8077849713384521385745765)
            ·
              refine ⟨1514596821259597759827331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8077849713384521385745765 1514596821259597759827331)
              ·
                refine ⟨2271895231889396639740997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1514596821259597759827331 2271895231889396639740997)
                ·
                  refine ⟨425980355979261869951437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2271895231889396639740997 425980355979261869951437)
                  ·
                    rfl

theorem cell21_1866586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 4, 1, 4].length) (baseStart_1866586 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1866586 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1866586 prefixEnd_1866586 := by exact prefixLift 1866586
  have htrace : WordTrace (prefixWord ++ tailWord_1866586) baseStart_1866586 baseEnd_1866586 := by
    simpa [prefixWord, tailWord_1866586, baseEnd_1866586] using wordTrace_append hprefix tailTrace_1866586
  have hstable : (prefixWord ++ tailWord_1866586).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866586).length < 2 ^ (prefixWord ++ tailWord_1866586).sum := by decide
  have hdescent : baseEnd_1866586 < baseStart_1866586 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866645 : List Nat := [1, 3, 2, 1, 1, 4, 2, 3, 4]
def baseStart_1866645 : Nat := 118140960795 + 1866645 * 2 ^ 59
def prefixEnd_1866645 : Nat := 4983230072969 + 3 ^ 40 * 1866645 * 2
def baseEnd_1866645 : Nat := 425993820583090878467983

theorem tailTrace_1866645 : CollatzResearch.WordTrace tailWord_1866645 prefixEnd_1866645 425993820583090878467983 := by
  unfold tailWord_1866645
  simp only [CollatzResearch.WordTrace]
  refine ⟨68082136322471437430337389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45388090881647624953558259 68082136322471437430337389)
  ·
    refine ⟨25530801120926789036376521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68082136322471437430337389 25530801120926789036376521)
    ·
      refine ⟨19148100840695091777282391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25530801120926789036376521 19148100840695091777282391)
      ·
        refine ⟨28722151261042637665923587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19148100840695091777282391 28722151261042637665923587)
        ·
          refine ⟨43083226891563956498885381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28722151261042637665923587 43083226891563956498885381)
          ·
            refine ⟨8078105042168241843541009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43083226891563956498885381 8078105042168241843541009)
            ·
              refine ⟨6058578781626181382655757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8078105042168241843541009 6058578781626181382655757)
              ·
                refine ⟨2271967043109818018495909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6058578781626181382655757 2271967043109818018495909)
                ·
                  refine ⟨425993820583090878467983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2271967043109818018495909 425993820583090878467983)
                  ·
                    rfl

theorem cell21_1866645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3, 4].length) (baseStart_1866645 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1866645 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1866645 prefixEnd_1866645 := by exact prefixLift 1866645
  have htrace : WordTrace (prefixWord ++ tailWord_1866645) baseStart_1866645 baseEnd_1866645 := by
    simpa [prefixWord, tailWord_1866645, baseEnd_1866645] using wordTrace_append hprefix tailTrace_1866645
  have hstable : (prefixWord ++ tailWord_1866645).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866645).length < 2 ^ (prefixWord ++ tailWord_1866645).sum := by decide
  have hdescent : baseEnd_1866645 < baseStart_1866645 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866710 : List Nat := [5, 2, 1, 1, 2, 3, 2, 5]
def baseStart_1866710 : Nat := 118140960795 + 1866710 * 2 ^ 59
def prefixEnd_1866710 : Nat := 4983230072969 + 3 ^ 40 * 1866710 * 2
def baseEnd_1866710 : Nat := 142002884822888403294839

theorem tailTrace_1866710 : CollatzResearch.WordTrace tailWord_1866710 prefixEnd_1866710 142002884822888403294839 := by
  unfold tailWord_1866710
  simp only [CollatzResearch.WordTrace]
  refine ⟨4255281691702247095715849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45389671378157302354302389 4255281691702247095715849)
  ·
    refine ⟨3191461268776685321786887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4255281691702247095715849 3191461268776685321786887)
    ·
      refine ⟨4787191903165027982680331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3191461268776685321786887 4787191903165027982680331)
      ·
        refine ⟨7180787854747541974020497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4787191903165027982680331 7180787854747541974020497)
        ·
          refine ⟨5385590891060656480515373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7180787854747541974020497 5385590891060656480515373)
          ·
            refine ⟨2019596584147746180193265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5385590891060656480515373 2019596584147746180193265)
            ·
              refine ⟨1514697438110809635144949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2019596584147746180193265 1514697438110809635144949)
              ·
                refine ⟨142002884822888403294839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1514697438110809635144949 142002884822888403294839)
                ·
                  rfl

theorem cell21_1866710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_1866710 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1866710 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1866710 prefixEnd_1866710 := by exact prefixLift 1866710
  have htrace : WordTrace (prefixWord ++ tailWord_1866710) baseStart_1866710 baseEnd_1866710 := by
    simpa [prefixWord, tailWord_1866710, baseEnd_1866710] using wordTrace_append hprefix tailTrace_1866710
  have hstable : (prefixWord ++ tailWord_1866710).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866710).length < 2 ^ (prefixWord ++ tailWord_1866710).sum := by decide
  have hdescent : baseEnd_1866710 < baseStart_1866710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866735 : List Nat := [1, 1, 2, 1, 4, 5, 7]
def baseStart_1866735 : Nat := 118140960795 + 1866735 * 2 ^ 59
def prefixEnd_1866735 : Nat := 4983230072969 + 3 ^ 40 * 1866735 * 2
def baseEnd_1866735 : Nat := 47334928867696746885311

theorem tailTrace_1866735 : CollatzResearch.WordTrace tailWord_1866735 prefixEnd_1866735 47334928867696746885311 := by
  unfold tailWord_1866735
  simp only [CollatzResearch.WordTrace]
  refine ⟨68085418892145382801113659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45390279261430255200742439 68085418892145382801113659)
  ·
    refine ⟨102128128338218074201670489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68085418892145382801113659 102128128338218074201670489)
    ·
      refine ⟨76596096253663555651252867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102128128338218074201670489 76596096253663555651252867)
      ·
        refine ⟨114894144380495333476879301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76596096253663555651252867 114894144380495333476879301)
        ·
          refine ⟨21542652071342875026914869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114894144380495333476879301 21542652071342875026914869)
          ·
            refine ⟨2019623631688394533773269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21542652071342875026914869 2019623631688394533773269)
            ·
              refine ⟨47334928867696746885311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2019623631688394533773269 47334928867696746885311)
              ·
                rfl

theorem cell21_1866735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 5, 7].length) (baseStart_1866735 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1866735 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1866735 prefixEnd_1866735 := by exact prefixLift 1866735
  have htrace : WordTrace (prefixWord ++ tailWord_1866735) baseStart_1866735 baseEnd_1866735 := by
    simpa [prefixWord, tailWord_1866735, baseEnd_1866735] using wordTrace_append hprefix tailTrace_1866735
  have hstable : (prefixWord ++ tailWord_1866735).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866735).length < 2 ^ (prefixWord ++ tailWord_1866735).sum := by decide
  have hdescent : baseEnd_1866735 < baseStart_1866735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866741 : List Nat := [1, 3, 5, 2, 1, 2, 1, 1, 5]
def baseStart_1866741 : Nat := 118140960795 + 1866741 * 2 ^ 59
def prefixEnd_1866741 : Nat := 4983230072969 + 3 ^ 40 * 1866741 * 2
def baseEnd_1866741 : Nat := 426015729091016044867787

theorem tailTrace_1866741 : CollatzResearch.WordTrace tailWord_1866741 prefixEnd_1866741 426015729091016044867787 := by
  unfold tailWord_1866741
  simp only [CollatzResearch.WordTrace]
  refine ⟨68085637730123645825832077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45390425153415763883888051 68085637730123645825832077)
  ·
    refine ⟨25532114148796367184687029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68085637730123645825832077 25532114148796367184687029)
    ·
      refine ⟨2393635701449659423564409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25532114148796367184687029 2393635701449659423564409)
      ·
        refine ⟨1795226776087244567673307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2393635701449659423564409 1795226776087244567673307)
        ·
          refine ⟨2692840164130866851509961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1795226776087244567673307 2692840164130866851509961)
          ·
            refine ⟨2019630123098150138632471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2692840164130866851509961 2019630123098150138632471)
            ·
              refine ⟨3029445184647225207948707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2019630123098150138632471 3029445184647225207948707)
              ·
                refine ⟨4544167776970837811923061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3029445184647225207948707 4544167776970837811923061)
                ·
                  refine ⟨426015729091016044867787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4544167776970837811923061 426015729091016044867787)
                  ·
                    rfl

theorem cell21_1866741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_1866741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1866741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1866741 prefixEnd_1866741 := by exact prefixLift 1866741
  have htrace : WordTrace (prefixWord ++ tailWord_1866741) baseStart_1866741 baseEnd_1866741 := by
    simpa [prefixWord, tailWord_1866741, baseEnd_1866741] using wordTrace_append hprefix tailTrace_1866741
  have hstable : (prefixWord ++ tailWord_1866741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866741).length < 2 ^ (prefixWord ++ tailWord_1866741).sum := by decide
  have hdescent : baseEnd_1866741 < baseStart_1866741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1866814 : List Nat := [4, 2, 1, 3, 1, 1, 2, 3, 4]
def baseStart_1866814 : Nat := 118140960795 + 1866814 * 2 ^ 59
def prefixEnd_1866814 : Nat := 4983230072969 + 3 ^ 40 * 1866814 * 2
def baseEnd_1866814 : Nat := 426032388685584140150971

theorem tailTrace_1866814 : CollatzResearch.WordTrace tailWord_1866814 prefixEnd_1866814 426032388685584140150971 := by
  unfold tailWord_1866814
  simp only [CollatzResearch.WordTrace]
  refine ⟨8511037532357397411654937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45392200172572786195492997 8511037532357397411654937)
  ·
    refine ⟨6383278149268048058741203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8511037532357397411654937 6383278149268048058741203)
    ·
      refine ⟨9574917223902072088111805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6383278149268048058741203 9574917223902072088111805)
      ·
        refine ⟨3590593958963277033041927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9574917223902072088111805 3590593958963277033041927)
        ·
          refine ⟨5385890938444915549562891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3590593958963277033041927 5385890938444915549562891)
          ·
            refine ⟨8078836407667373324344337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5385890938444915549562891 8078836407667373324344337)
            ·
              refine ⟨6059127305750529993258253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8078836407667373324344337 6059127305750529993258253)
              ·
                refine ⟨2272172739656448747471845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6059127305750529993258253 2272172739656448747471845)
                ·
                  refine ⟨426032388685584140150971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2272172739656448747471845 426032388685584140150971)
                  ·
                    rfl

theorem cell21_1866814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 2, 3, 4].length) (baseStart_1866814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1866814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1866814 prefixEnd_1866814 := by exact prefixLift 1866814
  have htrace : WordTrace (prefixWord ++ tailWord_1866814) baseStart_1866814 baseEnd_1866814 := by
    simpa [prefixWord, tailWord_1866814, baseEnd_1866814] using wordTrace_append hprefix tailTrace_1866814
  have hstable : (prefixWord ++ tailWord_1866814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1866814).length < 2 ^ (prefixWord ++ tailWord_1866814).sum := by decide
  have hdescent : baseEnd_1866814 < baseStart_1866814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1866814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867011 : List Nat := [1, 1, 1, 3, 2, 5, 2, 3, 3]
def baseStart_1867011 : Nat := 118140960795 + 1867011 * 2 ^ 59
def prefixEnd_1867011 : Nat := 4983230072969 + 3 ^ 40 * 1867011 * 2
def baseEnd_1867011 : Nat := 426077346769555575367235

theorem tailTrace_1867011 : CollatzResearch.WordTrace tailWord_1867011 prefixEnd_1867011 426077346769555575367235 := by
  unfold tailWord_1867011
  simp only [CollatzResearch.WordTrace]
  refine ⟨68095485439145481938160887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45396990292763654625440591 68095485439145481938160887)
  ·
    refine ⟨102143228158718222907241331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68095485439145481938160887 102143228158718222907241331)
    ·
      refine ⟨153214842238077334360861997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102143228158718222907241331 153214842238077334360861997)
      ·
        refine ⟨57455565839279000385323249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153214842238077334360861997 57455565839279000385323249)
        ·
          refine ⟨43091674379459250288992437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57455565839279000385323249 43091674379459250288992437)
          ·
            refine ⟨4039844473074304714593041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43091674379459250288992437 4039844473074304714593041)
            ·
              refine ⟨3029883354805728535944781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4039844473074304714593041 3029883354805728535944781)
              ·
                refine ⟨1136206258052148200979293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3029883354805728535944781 1136206258052148200979293)
                ·
                  refine ⟨426077346769555575367235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1136206258052148200979293 426077346769555575367235)
                  ·
                    rfl

theorem cell21_1867011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 2, 3, 3].length) (baseStart_1867011 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1867011 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1867011 prefixEnd_1867011 := by exact prefixLift 1867011
  have htrace : WordTrace (prefixWord ++ tailWord_1867011) baseStart_1867011 baseEnd_1867011 := by
    simpa [prefixWord, tailWord_1867011, baseEnd_1867011] using wordTrace_append hprefix tailTrace_1867011
  have hstable : (prefixWord ++ tailWord_1867011).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867011).length < 2 ^ (prefixWord ++ tailWord_1867011).sum := by decide
  have hdescent : baseEnd_1867011 < baseStart_1867011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867062 : List Nat := [5, 1, 2, 3, 1, 2, 1, 3, 3]
def baseStart_1867062 : Nat := 118140960795 + 1867062 * 2 ^ 59
def prefixEnd_1867062 : Nat := 4983230072969 + 3 ^ 40 * 1867062 * 2
def baseEnd_1867062 : Nat := 426088985664390820017131

theorem tailTrace_1867062 : CollatzResearch.WordTrace tailWord_1867062 prefixEnd_1867062 426088985664390820017131 := by
  unfold tailWord_1867062
  simp only [CollatzResearch.WordTrace]
  refine ⟨4256084097622544853016715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45398230374640478432178293 4256084097622544853016715)
  ·
    refine ⟨6384126146433817279525073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4256084097622544853016715 6384126146433817279525073)
    ·
      refine ⟨4788094609825362959643805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6384126146433817279525073 4788094609825362959643805)
      ·
        refine ⟨1795535478684511109866427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4788094609825362959643805 1795535478684511109866427)
        ·
          refine ⟨2693303218026766664799641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1795535478684511109866427 2693303218026766664799641)
          ·
            refine ⟨2019977413520074998599731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2693303218026766664799641 2019977413520074998599731)
            ·
              refine ⟨3029966120280112497899597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2019977413520074998599731 3029966120280112497899597)
              ·
                refine ⟨1136237295105042186712349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3029966120280112497899597 1136237295105042186712349)
                ·
                  refine ⟨426088985664390820017131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1136237295105042186712349 426088985664390820017131)
                  ·
                    rfl

theorem cell21_1867062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_1867062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1867062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1867062 prefixEnd_1867062 := by exact prefixLift 1867062
  have htrace : WordTrace (prefixWord ++ tailWord_1867062) baseStart_1867062 baseEnd_1867062 := by
    simpa [prefixWord, tailWord_1867062, baseEnd_1867062] using wordTrace_append hprefix tailTrace_1867062
  have hstable : (prefixWord ++ tailWord_1867062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867062).length < 2 ^ (prefixWord ++ tailWord_1867062).sum := by decide
  have hdescent : baseEnd_1867062 < baseStart_1867062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867084 : List Nat := [2, 2, 1, 3, 2, 2, 2, 1, 6]
def baseStart_1867084 : Nat := 118140960795 + 1867084 * 2 ^ 59
def prefixEnd_1867084 : Nat := 4983230072969 + 3 ^ 40 * 1867084 * 2
def baseEnd_1867084 : Nat := 426094006364123670650419

theorem tailTrace_1867084 : CollatzResearch.WordTrace tailWord_1867084 prefixEnd_1867084 426094006364123670650419 := by
  unfold tailWord_1867084
  simp only [CollatzResearch.WordTrace]
  refine ⟨34049073983940507702784153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45398765311920676937045537 34049073983940507702784153)
  ·
    refine ⟨25536805487955380777088115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34049073983940507702784153 25536805487955380777088115)
    ·
      refine ⟨38305208231933071165632173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25536805487955380777088115 38305208231933071165632173)
      ·
        refine ⟨14364453086974901687112065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38305208231933071165632173 14364453086974901687112065)
        ·
          refine ⟨10773339815231176265334049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14364453086974901687112065 10773339815231176265334049)
          ·
            refine ⟨8080004861423382199000537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10773339815231176265334049 8080004861423382199000537)
            ·
              refine ⟨6060003646067536649250403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8080004861423382199000537 6060003646067536649250403)
              ·
                refine ⟨9090005469101304973875605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6060003646067536649250403 9090005469101304973875605)
                ·
                  refine ⟨426094006364123670650419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9090005469101304973875605 426094006364123670650419)
                  ·
                    rfl

theorem cell21_1867084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 2, 1, 6].length) (baseStart_1867084 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1867084 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1867084 prefixEnd_1867084 := by exact prefixLift 1867084
  have htrace : WordTrace (prefixWord ++ tailWord_1867084) baseStart_1867084 baseEnd_1867084 := by
    simpa [prefixWord, tailWord_1867084, baseEnd_1867084] using wordTrace_append hprefix tailTrace_1867084
  have hstable : (prefixWord ++ tailWord_1867084).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867084).length < 2 ^ (prefixWord ++ tailWord_1867084).sum := by decide
  have hdescent : baseEnd_1867084 < baseStart_1867084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867098 : List Nat := [3, 1, 1, 2, 1, 2, 3, 8]
def baseStart_1867098 : Nat := 118140960795 + 1867098 * 2 ^ 59
def prefixEnd_1867098 : Nat := 4983230072969 + 3 ^ 40 * 1867098 * 2
def baseEnd_1867098 : Nat := 142032400451620919139019

theorem tailTrace_1867098 : CollatzResearch.WordTrace tailWord_1867098 prefixEnd_1867098 142032400451620919139019 := by
  unfold tailWord_1867098
  simp only [CollatzResearch.WordTrace]
  refine ⟨17024664647457573949144487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45399105726553530531051965 17024664647457573949144487)
  ·
    refine ⟨25536996971186360923716731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17024664647457573949144487 25536996971186360923716731)
    ·
      refine ⟨38305495456779541385575097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25536996971186360923716731 38305495456779541385575097)
      ·
        refine ⟨28729121592584656039181323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38305495456779541385575097 28729121592584656039181323)
        ·
          refine ⟨43093682388876984058771985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28729121592584656039181323 43093682388876984058771985)
          ·
            refine ⟨32320261791657738044078989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43093682388876984058771985 32320261791657738044078989)
            ·
              refine ⟨12120098171871651766529621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32320261791657738044078989 12120098171871651766529621)
              ·
                refine ⟨142032400451620919139019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12120098171871651766529621 142032400451620919139019)
                ·
                  rfl

theorem cell21_1867098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 3, 8].length) (baseStart_1867098 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1867098 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1867098 prefixEnd_1867098 := by exact prefixLift 1867098
  have htrace : WordTrace (prefixWord ++ tailWord_1867098) baseStart_1867098 baseEnd_1867098 := by
    simpa [prefixWord, tailWord_1867098, baseEnd_1867098] using wordTrace_append hprefix tailTrace_1867098
  have hstable : (prefixWord ++ tailWord_1867098).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867098).length < 2 ^ (prefixWord ++ tailWord_1867098).sum := by decide
  have hdescent : baseEnd_1867098 < baseStart_1867098 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867138 : List Nat := [3, 4, 2, 1, 1, 3, 2, 2, 3]
def baseStart_1867138 : Nat := 118140960795 + 1867138 * 2 ^ 59
def prefixEnd_1867138 : Nat := 4983230072969 + 3 ^ 40 * 1867138 * 2
def baseEnd_1867138 : Nat := 426106329899831576750309

theorem tailTrace_1867138 : CollatzResearch.WordTrace tailWord_1867138 prefixEnd_1867138 426106329899831576750309 := by
  unfold tailWord_1867138
  simp only [CollatzResearch.WordTrace]
  refine ⟨17025029377421345657008517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45400078339790255085356045 17025029377421345657008517)
  ·
    refine ⟨3192193008266502310689097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17025029377421345657008517 3192193008266502310689097)
    ·
      refine ⟨2394144756199876733016823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3192193008266502310689097 2394144756199876733016823)
      ·
        refine ⟨3591217134299815099525235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2394144756199876733016823 3591217134299815099525235)
        ·
          refine ⟨5386825701449722649287853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3591217134299815099525235 5386825701449722649287853)
          ·
            refine ⟨2020059638043645993482945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5386825701449722649287853 2020059638043645993482945)
            ·
              refine ⟨1515044728532734495112209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2020059638043645993482945 1515044728532734495112209)
              ·
                refine ⟨1136283546399550871334157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1515044728532734495112209 1136283546399550871334157)
                ·
                  refine ⟨426106329899831576750309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1136283546399550871334157 426106329899831576750309)
                  ·
                    rfl

theorem cell21_1867138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 2, 3].length) (baseStart_1867138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1867138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1867138 prefixEnd_1867138 := by exact prefixLift 1867138
  have htrace : WordTrace (prefixWord ++ tailWord_1867138) baseStart_1867138 baseEnd_1867138 := by
    simpa [prefixWord, tailWord_1867138, baseEnd_1867138] using wordTrace_append hprefix tailTrace_1867138
  have hstable : (prefixWord ++ tailWord_1867138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867138).length < 2 ^ (prefixWord ++ tailWord_1867138).sum := by decide
  have hdescent : baseEnd_1867138 < baseStart_1867138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867239 : List Nat := [1, 1, 5, 2, 1, 2, 3, 3, 3]
def baseStart_1867239 : Nat := 118140960795 + 1867239 * 2 ^ 59
def prefixEnd_1867239 : Nat := 4983230072969 + 3 ^ 40 * 1867239 * 2
def baseEnd_1867239 : Nat := 426129379475877845566769

theorem tailTrace_1867239 : CollatzResearch.WordTrace tailWord_1867239 prefixEnd_1867239 426129379475877845566769 := by
  unfold tailWord_1867239
  simp only [CollatzResearch.WordTrace]
  refine ⟨68103801282319476877460771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45402534188212984584973847 68103801282319476877460771)
  ·
    refine ⟨102155701923479215316191157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68103801282319476877460771 102155701923479215316191157)
    ·
      refine ⟨9577097055326176435892921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102155701923479215316191157 9577097055326176435892921)
      ·
        refine ⟨7182822791494632326919691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9577097055326176435892921 7182822791494632326919691)
        ·
          refine ⟨10774234187241948490379537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7182822791494632326919691 10774234187241948490379537)
          ·
            refine ⟨8080675640431461367784653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10774234187241948490379537 8080675640431461367784653)
            ·
              refine ⟨3030253365161798012919245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8080675640431461367784653 3030253365161798012919245)
              ·
                refine ⟨1136345011935674254844717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3030253365161798012919245 1136345011935674254844717)
                ·
                  refine ⟨426129379475877845566769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1136345011935674254844717 426129379475877845566769)
                  ·
                    rfl

theorem cell21_1867239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 3, 3].length) (baseStart_1867239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1867239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1867239 prefixEnd_1867239 := by exact prefixLift 1867239
  have htrace : WordTrace (prefixWord ++ tailWord_1867239) baseStart_1867239 baseEnd_1867239 := by
    simpa [prefixWord, tailWord_1867239, baseEnd_1867239] using wordTrace_append hprefix tailTrace_1867239
  have hstable : (prefixWord ++ tailWord_1867239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867239).length < 2 ^ (prefixWord ++ tailWord_1867239).sum := by decide
  have hdescent : baseEnd_1867239 < baseStart_1867239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867253 : List Nat := [1, 3, 5, 1, 1, 1, 2, 1, 6]
def baseStart_1867253 : Nat := 118140960795 + 1867253 * 2 ^ 59
def prefixEnd_1867253 : Nat := 4983230072969 + 3 ^ 40 * 1867253 * 2
def baseEnd_1867253 : Nat := 426132574466616932333407

theorem tailTrace_1867253 : CollatzResearch.WordTrace tailWord_1867253 prefixEnd_1867253 426132574466616932333407 := by
  unfold tailWord_1867253
  simp only [CollatzResearch.WordTrace]
  refine ⟨68104311904268757268470413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45402874602845838178980275 68104311904268757268470413)
  ·
    refine ⟨25539116964100783975676405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68104311904268757268470413 25539116964100783975676405)
    ·
      refine ⟨2394292215384448497719663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25539116964100783975676405 2394292215384448497719663)
      ·
        refine ⟨3591438323076672746579495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2394292215384448497719663 3591438323076672746579495)
        ·
          refine ⟨5387157484615009119869243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3591438323076672746579495 5387157484615009119869243)
          ·
            refine ⟨8080736226922513679803865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5387157484615009119869243 8080736226922513679803865)
            ·
              refine ⟨6060552170191885259852899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8080736226922513679803865 6060552170191885259852899)
              ·
                refine ⟨9090828255287827889779349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6060552170191885259852899 9090828255287827889779349)
                ·
                  refine ⟨426132574466616932333407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9090828255287827889779349 426132574466616932333407)
                  ·
                    rfl

theorem cell21_1867253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 6].length) (baseStart_1867253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1867253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1867253 prefixEnd_1867253 := by exact prefixLift 1867253
  have htrace : WordTrace (prefixWord ++ tailWord_1867253) baseStart_1867253 baseEnd_1867253 := by
    simpa [prefixWord, tailWord_1867253, baseEnd_1867253] using wordTrace_append hprefix tailTrace_1867253
  have hstable : (prefixWord ++ tailWord_1867253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867253).length < 2 ^ (prefixWord ++ tailWord_1867253).sum := by decide
  have hdescent : baseEnd_1867253 < baseStart_1867253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867295 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 8]
def baseStart_1867295 : Nat := 118140960795 + 1867295 * 2 ^ 59
def prefixEnd_1867295 : Nat := 4983230072969 + 3 ^ 40 * 1867295 * 2
def baseEnd_1867295 : Nat := 426142159438834192633321

theorem tailTrace_1867295 : CollatzResearch.WordTrace tailWord_1867295 prefixEnd_1867295 426142159438834192633321 := by
  unfold tailWord_1867295
  simp only [CollatzResearch.WordTrace]
  refine ⟨68105843770116598441499339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45403895846744398960999559 68105843770116598441499339)
  ·
    refine ⟨102158765655174897662249009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68105843770116598441499339 102158765655174897662249009)
    ·
      refine ⟨76619074241381173246686757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102158765655174897662249009 76619074241381173246686757)
      ·
        refine ⟨14366076420258969983753767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76619074241381173246686757 14366076420258969983753767)
        ·
          refine ⟨21549114630388454975630651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14366076420258969983753767 21549114630388454975630651)
          ·
            refine ⟨32323671945582682463445977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21549114630388454975630651 32323671945582682463445977)
            ·
              refine ⟨24242753959187011847584483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32323671945582682463445977 24242753959187011847584483)
              ·
                refine ⟨36364130938780517771376725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24242753959187011847584483 36364130938780517771376725)
                ·
                  refine ⟨426142159438834192633321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36364130938780517771376725 426142159438834192633321)
                  ·
                    rfl

theorem cell21_1867295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 8].length) (baseStart_1867295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1867295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1867295 prefixEnd_1867295 := by exact prefixLift 1867295
  have htrace : WordTrace (prefixWord ++ tailWord_1867295) baseStart_1867295 baseEnd_1867295 := by
    simpa [prefixWord, tailWord_1867295, baseEnd_1867295] using wordTrace_append hprefix tailTrace_1867295
  have hstable : (prefixWord ++ tailWord_1867295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867295).length < 2 ^ (prefixWord ++ tailWord_1867295).sum := by decide
  have hdescent : baseEnd_1867295 < baseStart_1867295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867315 : List Nat := [1, 1, 1, 2, 4, 3, 4, 2, 3]
def baseStart_1867315 : Nat := 118140960795 + 1867315 * 2 ^ 59
def prefixEnd_1867315 : Nat := 4983230072969 + 3 ^ 40 * 1867315 * 2
def baseEnd_1867315 : Nat := 426146723711318602299947

theorem tailTrace_1867315 : CollatzResearch.WordTrace tailWord_1867315 prefixEnd_1867315 426146723711318602299947 := by
  unfold tailWord_1867315
  simp only [CollatzResearch.WordTrace]
  refine ⟨68106573230044141857227399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45404382153362761238151599 68106573230044141857227399)
  ·
    refine ⟨102159859845066212785841099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68106573230044141857227399 102159859845066212785841099)
    ·
      refine ⟨153239789767599319178761649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102159859845066212785841099 153239789767599319178761649)
      ·
        refine ⟨114929842325699489384071237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153239789767599319178761649 114929842325699489384071237)
        ·
          refine ⟨21549345436068654259513357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114929842325699489384071237 21549345436068654259513357)
          ·
            refine ⟨8081004538525745347317509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21549345436068654259513357 8081004538525745347317509)
            ·
              refine ⟨1515188350973577252622033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8081004538525745347317509 1515188350973577252622033)
              ·
                refine ⟨1136391263230182939466525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1515188350973577252622033 1136391263230182939466525)
                ·
                  refine ⟨426146723711318602299947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1136391263230182939466525 426146723711318602299947)
                  ·
                    rfl

theorem cell21_1867315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 4, 2, 3].length) (baseStart_1867315 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1867315 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1867315 prefixEnd_1867315 := by exact prefixLift 1867315
  have htrace : WordTrace (prefixWord ++ tailWord_1867315) baseStart_1867315 baseEnd_1867315 := by
    simpa [prefixWord, tailWord_1867315, baseEnd_1867315] using wordTrace_append hprefix tailTrace_1867315
  have hstable : (prefixWord ++ tailWord_1867315).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867315).length < 2 ^ (prefixWord ++ tailWord_1867315).sum := by decide
  have hdescent : baseEnd_1867315 < baseStart_1867315 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867484 : List Nat := [2, 2, 5, 1, 2, 1, 1, 4, 3]
def baseStart_1867484 : Nat := 118140960795 + 1867484 * 2 ^ 59
def prefixEnd_1867484 : Nat := 4983230072969 + 3 ^ 40 * 1867484 * 2
def baseEnd_1867484 : Nat := 426185291813811863982935

theorem tailTrace_1867484 : CollatzResearch.WordTrace tailWord_1867484 prefixEnd_1867484 426185291813811863982935 := by
  unfold tailWord_1867484
  simp only [CollatzResearch.WordTrace]
  refine ⟨34056368583215941860064753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45408491444287922480086337 34056368583215941860064753)
  ·
    refine ⟨25542276437411956395048565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34056368583215941860064753 25542276437411956395048565)
    ·
      refine ⟨2394588416007370912035803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25542276437411956395048565 2394588416007370912035803)
      ·
        refine ⟨3591882624011056368053705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2394588416007370912035803 3591882624011056368053705)
        ·
          refine ⟨2693911968008292276040279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3591882624011056368053705 2693911968008292276040279)
          ·
            refine ⟨4040867952012438414060419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2693911968008292276040279 4040867952012438414060419)
            ·
              refine ⟨6061301928018657621090629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4040867952012438414060419 6061301928018657621090629)
              ·
                refine ⟨1136494111503498303954493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6061301928018657621090629 1136494111503498303954493)
                ·
                  refine ⟨426185291813811863982935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1136494111503498303954493 426185291813811863982935)
                  ·
                    rfl

theorem cell21_1867484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 1, 1, 4, 3].length) (baseStart_1867484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1867484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1867484 prefixEnd_1867484 := by exact prefixLift 1867484
  have htrace : WordTrace (prefixWord ++ tailWord_1867484) baseStart_1867484 baseEnd_1867484 := by
    simpa [prefixWord, tailWord_1867484, baseEnd_1867484] using wordTrace_append hprefix tailTrace_1867484
  have hstable : (prefixWord ++ tailWord_1867484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867484).length < 2 ^ (prefixWord ++ tailWord_1867484).sum := by decide
  have hdescent : baseEnd_1867484 < baseStart_1867484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867554 : List Nat := [3, 3, 1, 1, 2, 1, 2, 8]
def baseStart_1867554 : Nat := 118140960795 + 1867554 * 2 ^ 59
def prefixEnd_1867554 : Nat := 4983230072969 + 3 ^ 40 * 1867554 * 2
def baseEnd_1867554 : Nat := 142067088922502432605375

theorem tailTrace_1867554 : CollatzResearch.WordTrace tailWord_1867554 prefixEnd_1867554 142067088922502432605375 := by
  unfold tailWord_1867554
  simp only [CollatzResearch.WordTrace]
  refine ⟨17028822569044571418794429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45410193517452190450118477 17028822569044571418794429)
  ·
    refine ⟨6385808463391714282047911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17028822569044571418794429 6385808463391714282047911)
    ·
      refine ⟨9578712695087571423071867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6385808463391714282047911 9578712695087571423071867)
      ·
        refine ⟨14368069042631357134607801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9578712695087571423071867 14368069042631357134607801)
        ·
          refine ⟨10776051781973517850955851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14368069042631357134607801 10776051781973517850955851)
          ·
            refine ⟨16164077672960276776433777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10776051781973517850955851 16164077672960276776433777)
            ·
              refine ⟨12123058254720207582325333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16164077672960276776433777 12123058254720207582325333)
              ·
                refine ⟨142067088922502432605375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12123058254720207582325333 142067088922502432605375)
                ·
                  rfl

theorem cell21_1867554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 8].length) (baseStart_1867554 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1867554 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1867554 prefixEnd_1867554 := by exact prefixLift 1867554
  have htrace : WordTrace (prefixWord ++ tailWord_1867554) baseStart_1867554 baseEnd_1867554 := by
    simpa [prefixWord, tailWord_1867554, baseEnd_1867554] using wordTrace_append hprefix tailTrace_1867554
  have hstable : (prefixWord ++ tailWord_1867554).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867554).length < 2 ^ (prefixWord ++ tailWord_1867554).sum := by decide
  have hdescent : baseEnd_1867554 < baseStart_1867554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867557 : List Nat := [1, 3, 1, 2, 3, 3, 3, 1, 4]
def baseStart_1867557 : Nat := 118140960795 + 1867557 * 2 ^ 59
def prefixEnd_1867557 : Nat := 4983230072969 + 3 ^ 40 * 1867557 * 2
def baseEnd_1867557 : Nat := 426201951408379959266119

theorem tailTrace_1867557 : CollatzResearch.WordTrace tailWord_1867557 prefixEnd_1867557 426201951408379959266119 := by
  unfold tailWord_1867557
  simp only [CollatzResearch.WordTrace]
  refine ⟨68115399695167417187536925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45410266463444944791691283 68115399695167417187536925)
  ·
    refine ⟨25543274885687781445326347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68115399695167417187536925 25543274885687781445326347)
    ·
      refine ⟨38314912328531672167989521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25543274885687781445326347 38314912328531672167989521)
      ·
        refine ⟨28736184246398754125992141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38314912328531672167989521 28736184246398754125992141)
        ·
          refine ⟨10776069092399532797247053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28736184246398754125992141 10776069092399532797247053)
          ·
            refine ⟨4041025909649824798967645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10776069092399532797247053 4041025909649824798967645)
            ·
              refine ⟨1515384716118684299612867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4041025909649824798967645 1515384716118684299612867)
              ·
                refine ⟨2273077074178026449419301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1515384716118684299612867 2273077074178026449419301)
                ·
                  refine ⟨426201951408379959266119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2273077074178026449419301 426201951408379959266119)
                  ·
                    rfl

theorem cell21_1867557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 3, 3, 1, 4].length) (baseStart_1867557 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1867557 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1867557 prefixEnd_1867557 := by exact prefixLift 1867557
  have htrace : WordTrace (prefixWord ++ tailWord_1867557) baseStart_1867557 baseEnd_1867557 := by
    simpa [prefixWord, tailWord_1867557, baseEnd_1867557] using wordTrace_append hprefix tailTrace_1867557
  have hstable : (prefixWord ++ tailWord_1867557).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867557).length < 2 ^ (prefixWord ++ tailWord_1867557).sum := by decide
  have hdescent : baseEnd_1867557 < baseStart_1867557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867577 : List Nat := [1, 2, 1, 7, 2, 1, 1, 3, 3]
def baseStart_1867577 : Nat := 118140960795 + 1867577 * 2 ^ 59
def prefixEnd_1867577 : Nat := 4983230072969 + 3 ^ 40 * 1867577 * 2
def baseEnd_1867577 : Nat := 426206515680864368932745

theorem tailTrace_1867577 : CollatzResearch.WordTrace tailWord_1867577 prefixEnd_1867577 426206515680864368932745 := by
  unfold tailWord_1867577
  simp only [CollatzResearch.WordTrace]
  refine ⟨68116129155094960603264985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45410752770063307068843323 68116129155094960603264985)
  ·
    refine ⟨51087096866321220452448739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68116129155094960603264985 51087096866321220452448739)
    ·
      refine ⟨76630645299481830678673109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51087096866321220452448739 76630645299481830678673109)
      ·
        refine ⟨1796030749206605406531401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 76630645299481830678673109 1796030749206605406531401)
        ·
          refine ⟨1347023061904954054898551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1796030749206605406531401 1347023061904954054898551)
          ·
            refine ⟨2020534592857431082347827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347023061904954054898551 2020534592857431082347827)
            ·
              refine ⟨3030801889286146623521741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2020534592857431082347827 3030801889286146623521741)
              ·
                refine ⟨1136550708482304983820653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3030801889286146623521741 1136550708482304983820653)
                ·
                  refine ⟨426206515680864368932745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1136550708482304983820653 426206515680864368932745)
                  ·
                    rfl

theorem cell21_1867577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 3, 3].length) (baseStart_1867577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1867577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1867577 prefixEnd_1867577 := by exact prefixLift 1867577
  have htrace : WordTrace (prefixWord ++ tailWord_1867577) baseStart_1867577 baseEnd_1867577 := by
    simpa [prefixWord, tailWord_1867577, baseEnd_1867577] using wordTrace_append hprefix tailTrace_1867577
  have hstable : (prefixWord ++ tailWord_1867577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867577).length < 2 ^ (prefixWord ++ tailWord_1867577).sum := by decide
  have hdescent : baseEnd_1867577 < baseStart_1867577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867602 : List Nat := [3, 2, 2, 1, 1, 5, 1, 1, 5]
def baseStart_1867602 : Nat := 118140960795 + 1867602 * 2 ^ 59
def prefixEnd_1867602 : Nat := 4983230072969 + 3 ^ 40 * 1867602 * 2
def baseEnd_1867602 : Nat := 426212221021469881016027

theorem tailTrace_1867602 : CollatzResearch.WordTrace tailWord_1867602 prefixEnd_1867602 426212221021469881016027 := by
  unfold tailWord_1867602
  simp only [CollatzResearch.WordTrace]
  refine ⟨17029260245001097468231265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45411360653336259915283373 17029260245001097468231265)
  ·
    refine ⟨12771945183750823101173449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17029260245001097468231265 12771945183750823101173449)
    ·
      refine ⟨9578958887813117325880087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12771945183750823101173449 9578958887813117325880087)
      ·
        refine ⟨14368438331719675988820131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9578958887813117325880087 14368438331719675988820131)
        ·
          refine ⟨21552657497579513983230197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14368438331719675988820131 21552657497579513983230197)
          ·
            refine ⟨2020561640398079435927831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21552657497579513983230197 2020561640398079435927831)
            ·
              refine ⟨3030842460597119153891747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2020561640398079435927831 3030842460597119153891747)
              ·
                refine ⟨4546263690895678730837621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3030842460597119153891747 4546263690895678730837621)
                ·
                  refine ⟨426212221021469881016027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4546263690895678730837621 426212221021469881016027)
                  ·
                    rfl

theorem cell21_1867602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 5, 1, 1, 5].length) (baseStart_1867602 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1867602 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1867602 prefixEnd_1867602 := by exact prefixLift 1867602
  have htrace : WordTrace (prefixWord ++ tailWord_1867602) baseStart_1867602 baseEnd_1867602 := by
    simpa [prefixWord, tailWord_1867602, baseEnd_1867602] using wordTrace_append hprefix tailTrace_1867602
  have hstable : (prefixWord ++ tailWord_1867602).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867602).length < 2 ^ (prefixWord ++ tailWord_1867602).sum := by decide
  have hdescent : baseEnd_1867602 < baseStart_1867602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867616 : List Nat := [2, 1, 1, 3, 3, 3, 1, 3, 4]
def baseStart_1867616 : Nat := 118140960795 + 1867616 * 2 ^ 59
def prefixEnd_1867616 : Nat := 4983230072969 + 3 ^ 40 * 1867616 * 2
def baseEnd_1867616 : Nat := 426215416012208967782665

theorem tailTrace_1867616 : CollatzResearch.WordTrace tailWord_1867616 prefixEnd_1867616 426215416012208967782665 := by
  unfold tailWord_1867616
  simp only [CollatzResearch.WordTrace]
  refine ⟨34058775800976835131967351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45411701067969113509289801 34058775800976835131967351)
  ·
    refine ⟨51088163701465252697951027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34058775800976835131967351 51088163701465252697951027)
    ·
      refine ⟨76632245552197879046926541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51088163701465252697951027 76632245552197879046926541)
      ·
        refine ⟨28737092082074204642597453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76632245552197879046926541 28737092082074204642597453)
        ·
          refine ⟨10776409530777826740974045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28737092082074204642597453 10776409530777826740974045)
          ·
            refine ⟨4041153574041685027865267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10776409530777826740974045 4041153574041685027865267)
            ·
              refine ⟨6061730361062527541797901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4041153574041685027865267 6061730361062527541797901)
              ·
                refine ⟨2273148885398447828174213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6061730361062527541797901 2273148885398447828174213)
                ·
                  refine ⟨426215416012208967782665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2273148885398447828174213 426215416012208967782665)
                  ·
                    rfl

theorem cell21_1867616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 3, 4].length) (baseStart_1867616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1867616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1867616 prefixEnd_1867616 := by exact prefixLift 1867616
  have htrace : WordTrace (prefixWord ++ tailWord_1867616) baseStart_1867616 baseEnd_1867616 := by
    simpa [prefixWord, tailWord_1867616, baseEnd_1867616] using wordTrace_append hprefix tailTrace_1867616
  have hstable : (prefixWord ++ tailWord_1867616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867616).length < 2 ^ (prefixWord ++ tailWord_1867616).sum := by decide
  have hdescent : baseEnd_1867616 < baseStart_1867616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867709 : List Nat := [1, 4, 1, 2, 3, 3, 1, 2, 4]
def baseStart_1867709 : Nat := 118140960795 + 1867709 * 2 ^ 59
def prefixEnd_1867709 : Nat := 4983230072969 + 3 ^ 40 * 1867709 * 2
def baseEnd_1867709 : Nat := 426236639879261472732475

theorem tailTrace_1867709 : CollatzResearch.WordTrace tailWord_1867709 prefixEnd_1867709 426236639879261472732475 := by
  unfold tailWord_1867709
  simp only [CollatzResearch.WordTrace]
  refine ⟨68120943590616747147070181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45413962393744498098046787 68120943590616747147070181)
  ·
    refine ⟨12772676923240640090075659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68120943590616747147070181 12772676923240640090075659)
    ·
      refine ⟨19159015384860960135113489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12772676923240640090075659 19159015384860960135113489)
      ·
        refine ⟨14369261538645720101335117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19159015384860960135113489 14369261538645720101335117)
        ·
          refine ⟨5388473076992145038000669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14369261538645720101335117 5388473076992145038000669)
          ·
            refine ⟨2020677403872054389250251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5388473076992145038000669 2020677403872054389250251)
            ·
              refine ⟨3031016105808081583875377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2020677403872054389250251 3031016105808081583875377)
              ·
                refine ⟨2273262079356061187906533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3031016105808081583875377 2273262079356061187906533)
                ·
                  refine ⟨426236639879261472732475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2273262079356061187906533 426236639879261472732475)
                  ·
                    rfl

theorem cell21_1867709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 3, 1, 2, 4].length) (baseStart_1867709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1867709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1867709 prefixEnd_1867709 := by exact prefixLift 1867709
  have htrace : WordTrace (prefixWord ++ tailWord_1867709) baseStart_1867709 baseEnd_1867709 := by
    simpa [prefixWord, tailWord_1867709, baseEnd_1867709] using wordTrace_append hprefix tailTrace_1867709
  have hstable : (prefixWord ++ tailWord_1867709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867709).length < 2 ^ (prefixWord ++ tailWord_1867709).sum := by decide
  have hdescent : baseEnd_1867709 < baseStart_1867709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867827 : List Nat := [1, 1, 1, 2, 4, 1, 3, 4, 4]
def baseStart_1867827 : Nat := 118140960795 + 1867827 * 2 ^ 59
def prefixEnd_1867827 : Nat := 4983230072969 + 3 ^ 40 * 1867827 * 2
def baseEnd_1867827 : Nat := 426263569086919489765567

theorem tailTrace_1867827 : CollatzResearch.WordTrace tailWord_1867827 prefixEnd_1867827 426263569086919489765567 := by
  unfold tailWord_1867827
  simp only [CollatzResearch.WordTrace]
  refine ⟨68125247404189253299865735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45416831602792835533243823 68125247404189253299865735)
  ·
    refine ⟨102187871106283879949798603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68125247404189253299865735 102187871106283879949798603)
    ·
      refine ⟨153281806659425819924697905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102187871106283879949798603 153281806659425819924697905)
      ·
        refine ⟨114961354994569364943523429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153281806659425819924697905 114961354994569364943523429)
        ·
          refine ⟨21555254061481755926910643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 114961354994569364943523429 21555254061481755926910643)
          ·
            refine ⟨32332881092222633890365965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21555254061481755926910643 32332881092222633890365965)
            ·
              refine ⟨12124830409583487708887237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32332881092222633890365965 12124830409583487708887237)
              ·
                refine ⟨2273405701796903945416357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12124830409583487708887237 2273405701796903945416357)
                ·
                  refine ⟨426263569086919489765567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2273405701796903945416357 426263569086919489765567)
                  ·
                    rfl

theorem cell21_1867827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 3, 4, 4].length) (baseStart_1867827 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1867827 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1867827 prefixEnd_1867827 := by exact prefixLift 1867827
  have htrace : WordTrace (prefixWord ++ tailWord_1867827) baseStart_1867827 baseEnd_1867827 := by
    simpa [prefixWord, tailWord_1867827, baseEnd_1867827] using wordTrace_append hprefix tailTrace_1867827
  have hstable : (prefixWord ++ tailWord_1867827).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867827).length < 2 ^ (prefixWord ++ tailWord_1867827).sum := by decide
  have hdescent : baseEnd_1867827 < baseStart_1867827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867889 : List Nat := [1, 2, 2, 2, 1, 1, 3, 6, 3]
def baseStart_1867889 : Nat := 118140960795 + 1867889 * 2 ^ 59
def prefixEnd_1867889 : Nat := 4983230072969 + 3 ^ 40 * 1867889 * 2
def baseEnd_1867889 : Nat := 426277718331621159732107

theorem tailTrace_1867889 : CollatzResearch.WordTrace tailWord_1867889 prefixEnd_1867889 426277718331621159732107 := by
  unfold tailWord_1867889
  simp only [CollatzResearch.WordTrace]
  refine ⟨68127508729964637888622721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45418339153309758592415147 68127508729964637888622721)
  ·
    refine ⟨51095631547473478416467041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68127508729964637888622721 51095631547473478416467041)
    ·
      refine ⟨38321723660605108812350281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51095631547473478416467041 38321723660605108812350281)
      ·
        refine ⟨28741292745453831609262711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38321723660605108812350281 28741292745453831609262711)
        ·
          refine ⟨43111939118180747413894067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28741292745453831609262711 43111939118180747413894067)
          ·
            refine ⟨64667908677271121120841101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43111939118180747413894067 64667908677271121120841101)
            ·
              refine ⟨24250465753976670420315413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64667908677271121120841101 24250465753976670420315413)
              ·
                refine ⟨1136740582217656425952285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24250465753976670420315413 1136740582217656425952285)
                ·
                  refine ⟨426277718331621159732107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1136740582217656425952285 426277718331621159732107)
                  ·
                    rfl

theorem cell21_1867889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 6, 3].length) (baseStart_1867889 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1867889 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1867889 prefixEnd_1867889 := by exact prefixLift 1867889
  have htrace : WordTrace (prefixWord ++ tailWord_1867889) baseStart_1867889 baseEnd_1867889 := by
    simpa [prefixWord, tailWord_1867889, baseEnd_1867889] using wordTrace_append hprefix tailTrace_1867889
  have hstable : (prefixWord ++ tailWord_1867889).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867889).length < 2 ^ (prefixWord ++ tailWord_1867889).sum := by decide
  have hdescent : baseEnd_1867889 < baseStart_1867889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1867926 : List Nat := [5, 3, 2, 1, 1, 2, 7]
def baseStart_1867926 : Nat := 118140960795 + 1867926 * 2 ^ 59
def prefixEnd_1867926 : Nat := 4983230072969 + 3 ^ 40 * 1867926 * 2
def baseEnd_1867926 : Nat := 47365129137301924179485

theorem tailTrace_1867926 : CollatzResearch.WordTrace tailWord_1867926 prefixEnd_1867926 47365129137301924179485 := by
  unfold tailWord_1867926
  simp only [CollatzResearch.WordTrace]
  refine ⟨4258053639426912075482477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45419238820553728805146421 4258053639426912075482477)
  ·
    refine ⟨1596770114785092028305929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4258053639426912075482477 1596770114785092028305929)
    ·
      refine ⟨1197577586088819021229447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1596770114785092028305929 1197577586088819021229447)
      ·
        refine ⟨1796366379133228531844171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1197577586088819021229447 1796366379133228531844171)
        ·
          refine ⟨2694549568699842797766257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1796366379133228531844171 2694549568699842797766257)
          ·
            refine ⟨2020912176524882098324693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2694549568699842797766257 2020912176524882098324693)
            ·
              refine ⟨47365129137301924179485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2020912176524882098324693 47365129137301924179485)
              ·
                rfl

theorem cell21_1867926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 2, 7].length) (baseStart_1867926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1867926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1867926 prefixEnd_1867926 := by exact prefixLift 1867926
  have htrace : WordTrace (prefixWord ++ tailWord_1867926) baseStart_1867926 baseEnd_1867926 := by
    simpa [prefixWord, tailWord_1867926, baseEnd_1867926] using wordTrace_append hprefix tailTrace_1867926
  have hstable : (prefixWord ++ tailWord_1867926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1867926).length < 2 ^ (prefixWord ++ tailWord_1867926).sum := by decide
  have hdescent : baseEnd_1867926 < baseStart_1867926 := by decide
  rcases family_descends (prefixWord ++ tailWord_1867926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868002 : List Nat := [3, 3, 4, 1, 2, 1, 1, 6]
def baseStart_1868002 : Nat := 118140960795 + 1868002 * 2 ^ 59
def prefixEnd_1868002 : Nat := 4983230072969 + 3 ^ 40 * 1868002 * 2
def baseEnd_1868002 : Nat := 142101168823719358116181

theorem tailTrace_1868002 : CollatzResearch.WordTrace tailWord_1868002 prefixEnd_1868002 142101168823719358116181 := by
  unfold tailWord_1868002
  simp only [CollatzResearch.WordTrace]
  refine ⟨17032907544638814546871565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45421086785703505458324173 17032907544638814546871565)
  ·
    refine ⟨6387340329239555455076837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17032907544638814546871565 6387340329239555455076837)
    ·
      refine ⟨1197626311732416647826907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6387340329239555455076837 1197626311732416647826907)
      ·
        refine ⟨1796439467598624971740361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1197626311732416647826907 1796439467598624971740361)
        ·
          refine ⟨1347329600698968728805271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1796439467598624971740361 1347329600698968728805271)
          ·
            refine ⟨2020994401048453093207907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347329600698968728805271 2020994401048453093207907)
            ·
              refine ⟨3031491601572679639811861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2020994401048453093207907 3031491601572679639811861)
              ·
                refine ⟨142101168823719358116181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3031491601572679639811861 142101168823719358116181)
                ·
                  rfl

theorem cell21_1868002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 2, 1, 1, 6].length) (baseStart_1868002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868002 prefixEnd_1868002 := by exact prefixLift 1868002
  have htrace : WordTrace (prefixWord ++ tailWord_1868002) baseStart_1868002 baseEnd_1868002 := by
    simpa [prefixWord, tailWord_1868002, baseEnd_1868002] using wordTrace_append hprefix tailTrace_1868002
  have hstable : (prefixWord ++ tailWord_1868002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868002).length < 2 ^ (prefixWord ++ tailWord_1868002).sum := by decide
  have hdescent : baseEnd_1868002 < baseStart_1868002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868041 : List Nat := [1, 2, 1, 1, 3, 4, 1, 5, 3]
def baseStart_1868041 : Nat := 118140960795 + 1868041 * 2 ^ 59
def prefixEnd_1868041 : Nat := 4983230072969 + 3 ^ 40 * 1868041 * 2
def baseEnd_1868041 : Nat := 426312406802502673198463

theorem tailTrace_1868041 : CollatzResearch.WordTrace tailWord_1868041 prefixEnd_1868041 426312406802502673198463 := by
  unfold tailWord_1868041
  simp only [CollatzResearch.WordTrace]
  refine ⟨68133052625413967848155977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45422035083609311898770651 68133052625413967848155977)
  ·
    refine ⟨51099789469060475886116983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68133052625413967848155977 51099789469060475886116983)
    ·
      refine ⟨76649684203590713829175475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51099789469060475886116983 76649684203590713829175475)
      ·
        refine ⟨114974526305386070743763213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76649684203590713829175475 114974526305386070743763213)
        ·
          refine ⟨43115447364519776528911205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 114974526305386070743763213 43115447364519776528911205)
          ·
            refine ⟨8084146380847458099170851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43115447364519776528911205 8084146380847458099170851)
            ·
              refine ⟨12126219571271187148756277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8084146380847458099170851 12126219571271187148756277)
              ·
                refine ⟨1136833084806673795195901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12126219571271187148756277 1136833084806673795195901)
                ·
                  refine ⟨426312406802502673198463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1136833084806673795195901 426312406802502673198463)
                  ·
                    rfl

theorem cell21_1868041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 4, 1, 5, 3].length) (baseStart_1868041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868041 prefixEnd_1868041 := by exact prefixLift 1868041
  have htrace : WordTrace (prefixWord ++ tailWord_1868041) baseStart_1868041 baseEnd_1868041 := by
    simpa [prefixWord, tailWord_1868041, baseEnd_1868041] using wordTrace_append hprefix tailTrace_1868041
  have hstable : (prefixWord ++ tailWord_1868041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868041).length < 2 ^ (prefixWord ++ tailWord_1868041).sum := by decide
  have hdescent : baseEnd_1868041 < baseStart_1868041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868055 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 6]
def baseStart_1868055 : Nat := 118140960795 + 1868055 * 2 ^ 59
def prefixEnd_1868055 : Nat := 4983230072969 + 3 ^ 40 * 1868055 * 2
def baseEnd_1868055 : Nat := 426315601793241759965101

theorem tailTrace_1868055 : CollatzResearch.WordTrace tailWord_1868055 prefixEnd_1868055 426315601793241759965101 := by
  unfold tailWord_1868055
  simp only [CollatzResearch.WordTrace]
  refine ⟨68133563247363248239165619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45422375498242165492777079 68133563247363248239165619)
  ·
    refine ⟨102200344871044872358748429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68133563247363248239165619 102200344871044872358748429)
    ·
      refine ⟨38325129326641827134530661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102200344871044872358748429 38325129326641827134530661)
      ·
        refine ⟨7185961748745342587724499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38325129326641827134530661 7185961748745342587724499)
        ·
          refine ⟨10778942623118013881586749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7185961748745342587724499 10778942623118013881586749)
          ·
            refine ⟨4042103483669255205595031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10778942623118013881586749 4042103483669255205595031)
            ·
              refine ⟨6063155225503882808392547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4042103483669255205595031 6063155225503882808392547)
              ·
                refine ⟨9094732838255824212588821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6063155225503882808392547 9094732838255824212588821)
                ·
                  refine ⟨426315601793241759965101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9094732838255824212588821 426315601793241759965101)
                  ·
                    rfl

theorem cell21_1868055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 6].length) (baseStart_1868055 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868055 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868055 prefixEnd_1868055 := by exact prefixLift 1868055
  have htrace : WordTrace (prefixWord ++ tailWord_1868055) baseStart_1868055 baseEnd_1868055 := by
    simpa [prefixWord, tailWord_1868055, baseEnd_1868055] using wordTrace_append hprefix tailTrace_1868055
  have hstable : (prefixWord ++ tailWord_1868055).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868055).length < 2 ^ (prefixWord ++ tailWord_1868055).sum := by decide
  have hdescent : baseEnd_1868055 < baseStart_1868055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868131 : List Nat := [1, 1, 1, 5, 2, 1, 3, 3, 4]
def baseStart_1868131 : Nat := 118140960795 + 1868131 * 2 ^ 59
def prefixEnd_1868131 : Nat := 4983230072969 + 3 ^ 40 * 1868131 * 2
def baseEnd_1868131 : Nat := 426332946028682516698279

theorem tailTrace_1868131 : CollatzResearch.WordTrace tailWord_1868131 prefixEnd_1868131 426332946028682516698279 := by
  unfold tailWord_1868131
  simp only [CollatzResearch.WordTrace]
  refine ⟨68136335195087913218932247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45424223463391942145954831 68136335195087913218932247)
  ·
    refine ⟨102204502792631869828398371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68136335195087913218932247 102204502792631869828398371)
    ·
      refine ⟨153306754188947804742597557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102204502792631869828398371 153306754188947804742597557)
      ·
        refine ⟨14372508205213856694618521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153306754188947804742597557 14372508205213856694618521)
        ·
          refine ⟨10779381153910392520963891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14372508205213856694618521 10779381153910392520963891)
          ·
            refine ⟨16169071730865588781445837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10779381153910392520963891 16169071730865588781445837)
            ·
              refine ⟨6063401899074595793042189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16169071730865588781445837 6063401899074595793042189)
              ·
                refine ⟨2273775712152973422390821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6063401899074595793042189 2273775712152973422390821)
                ·
                  refine ⟨426332946028682516698279, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2273775712152973422390821 426332946028682516698279)
                  ·
                    rfl

theorem cell21_1868131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 3, 3, 4].length) (baseStart_1868131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868131 prefixEnd_1868131 := by exact prefixLift 1868131
  have htrace : WordTrace (prefixWord ++ tailWord_1868131) baseStart_1868131 baseEnd_1868131 := by
    simpa [prefixWord, tailWord_1868131, baseEnd_1868131] using wordTrace_append hprefix tailTrace_1868131
  have hstable : (prefixWord ++ tailWord_1868131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868131).length < 2 ^ (prefixWord ++ tailWord_1868131).sum := by decide
  have hdescent : baseEnd_1868131 < baseStart_1868131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868159 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 7]
def baseStart_1868159 : Nat := 118140960795 + 1868159 * 2 ^ 59
def prefixEnd_1868159 : Nat := 4983230072969 + 3 ^ 40 * 1868159 * 2
def baseEnd_1868159 : Nat := 426339336010160690231555

theorem tailTrace_1868159 : CollatzResearch.WordTrace tailWord_1868159 prefixEnd_1868159 426339336010160690231555 := by
  unfold tailWord_1868159
  simp only [CollatzResearch.WordTrace]
  refine ⟨68137356438986474000951531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45424904292657649333967687 68137356438986474000951531)
  ·
    refine ⟨102206034658479711001427297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68137356438986474000951531 102206034658479711001427297)
    ·
      refine ⟨76654525993859783251070473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102206034658479711001427297 76654525993859783251070473)
      ·
        refine ⟨57490894495394837438302855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76654525993859783251070473 57490894495394837438302855)
        ·
          refine ⟨86236341743092256157454283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57490894495394837438302855 86236341743092256157454283)
          ·
            refine ⟨129354512614638384236181425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86236341743092256157454283 129354512614638384236181425)
            ·
              refine ⟨97015884460978788177136069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 129354512614638384236181425 97015884460978788177136069)
              ·
                refine ⟨18190478336433522783213013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97015884460978788177136069 18190478336433522783213013)
                ·
                  refine ⟨426339336010160690231555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18190478336433522783213013 426339336010160690231555)
                  ·
                    rfl

theorem cell21_1868159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 7].length) (baseStart_1868159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868159 prefixEnd_1868159 := by exact prefixLift 1868159
  have htrace : WordTrace (prefixWord ++ tailWord_1868159) baseStart_1868159 baseEnd_1868159 := by
    simpa [prefixWord, tailWord_1868159, baseEnd_1868159] using wordTrace_append hprefix tailTrace_1868159
  have hstable : (prefixWord ++ tailWord_1868159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868159).length < 2 ^ (prefixWord ++ tailWord_1868159).sum := by decide
  have hdescent : baseEnd_1868159 < baseStart_1868159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868162 : List Nat := [3, 4, 2, 1, 11]
def baseStart_1868162 : Nat := 118140960795 + 1868162 * 2 ^ 59
def prefixEnd_1868162 : Nat := 4983230072969 + 3 ^ 40 * 1868162 * 2
def baseEnd_1868162 : Nat := 5263457045074485823229

theorem tailTrace_1868162 : CollatzResearch.WordTrace tailWord_1868162 prefixEnd_1868162 5263457045074485823229 := by
  unfold tailWord_1868162
  simp only [CollatzResearch.WordTrace]
  refine ⟨17034366464493901378327685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45424977238650403675540493 17034366464493901378327685)
  ·
    refine ⟨3193943712092606508436441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17034366464493901378327685 3193943712092606508436441)
    ·
      refine ⟨2395457784069454881327331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3193943712092606508436441 2395457784069454881327331)
      ·
        refine ⟨3593186676104182321990997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2395457784069454881327331 3593186676104182321990997)
        ·
          refine ⟨5263457045074485823229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 11 3593186676104182321990997 5263457045074485823229)
          ·
            rfl

theorem cell21_1868162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 11].length) (baseStart_1868162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868162 prefixEnd_1868162 := by exact prefixLift 1868162
  have htrace : WordTrace (prefixWord ++ tailWord_1868162) baseStart_1868162 baseEnd_1868162 := by
    simpa [prefixWord, tailWord_1868162, baseEnd_1868162] using wordTrace_append hprefix tailTrace_1868162
  have hstable : (prefixWord ++ tailWord_1868162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868162).length < 2 ^ (prefixWord ++ tailWord_1868162).sum := by decide
  have hdescent : baseEnd_1868162 < baseStart_1868162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868221 : List Nat := [1, 4, 1, 2, 2, 3, 8]
def baseStart_1868221 : Nat := 118140960795 + 1868221 * 2 ^ 59
def prefixEnd_1868221 : Nat := 4983230072969 + 3 ^ 40 * 1868221 * 2
def baseEnd_1868221 : Nat := 47372609472762484466455

theorem tailTrace_1868221 : CollatzResearch.WordTrace tailWord_1868221 prefixEnd_1868221 47372609472762484466455 := by
  unfold tailWord_1868221
  simp only [CollatzResearch.WordTrace]
  refine ⟨68139617764761858589708517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45426411843174572393139011 68139617764761858589708517)
  ·
    refine ⟨12776178330892848485570347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68139617764761858589708517 12776178330892848485570347)
    ·
      refine ⟨19164267496339272728355521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12776178330892848485570347 19164267496339272728355521)
      ·
        refine ⟨14373200622254454546266641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19164267496339272728355521 14373200622254454546266641)
        ·
          refine ⟨10779900466690840909699981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14373200622254454546266641 10779900466690840909699981)
          ·
            refine ⟨4042462675009065341137493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10779900466690840909699981 4042462675009065341137493)
            ·
              refine ⟨47372609472762484466455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4042462675009065341137493 47372609472762484466455)
              ·
                rfl

theorem cell21_1868221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 8].length) (baseStart_1868221 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868221 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868221 prefixEnd_1868221 := by exact prefixLift 1868221
  have htrace : WordTrace (prefixWord ++ tailWord_1868221) baseStart_1868221 baseEnd_1868221 := by
    simpa [prefixWord, tailWord_1868221, baseEnd_1868221] using wordTrace_append hprefix tailTrace_1868221
  have hstable : (prefixWord ++ tailWord_1868221).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868221).length < 2 ^ (prefixWord ++ tailWord_1868221).sum := by decide
  have hdescent : baseEnd_1868221 < baseStart_1868221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868300 : List Nat := [2, 2, 1, 2, 4, 1, 4, 1, 4]
def baseStart_1868300 : Nat := 118140960795 + 1868300 * 2 ^ 59
def prefixEnd_1868300 : Nat := 4983230072969 + 3 ^ 40 * 1868300 * 2
def baseEnd_1868300 : Nat := 426371514131175778381267

theorem tailTrace_1868300 : CollatzResearch.WordTrace tailWord_1868300 prefixEnd_1868300 426371514131175778381267 := by
  unfold tailWord_1868300
  simp only [CollatzResearch.WordTrace]
  refine ⟨34071249565737827540917177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45428332754317103387889569 34071249565737827540917177)
  ·
    refine ⟨25553437174303370655687883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34071249565737827540917177 25553437174303370655687883)
    ·
      refine ⟨38330155761455055983531825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25553437174303370655687883 38330155761455055983531825)
      ·
        refine ⟨28747616821091291987648869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38330155761455055983531825 28747616821091291987648869)
        ·
          refine ⟨5390178153954617247684163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28747616821091291987648869 5390178153954617247684163)
          ·
            refine ⟨8085267230931925871526245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5390178153954617247684163 8085267230931925871526245)
            ·
              refine ⟨1515987605799736100911171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8085267230931925871526245 1515987605799736100911171)
              ·
                refine ⟨2273981408699604151366757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1515987605799736100911171 2273981408699604151366757)
                ·
                  refine ⟨426371514131175778381267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2273981408699604151366757 426371514131175778381267)
                  ·
                    rfl

theorem cell21_1868300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_1868300 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868300 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868300 prefixEnd_1868300 := by exact prefixLift 1868300
  have htrace : WordTrace (prefixWord ++ tailWord_1868300) baseStart_1868300 baseEnd_1868300 := by
    simpa [prefixWord, tailWord_1868300, baseEnd_1868300] using wordTrace_append hprefix tailTrace_1868300
  have hstable : (prefixWord ++ tailWord_1868300).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868300).length < 2 ^ (prefixWord ++ tailWord_1868300).sum := by decide
  have hdescent : baseEnd_1868300 < baseStart_1868300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868345 : List Nat := [1, 2, 1, 5, 1, 1, 3, 4, 3]
def baseStart_1868345 : Nat := 118140960795 + 1868345 * 2 ^ 59
def prefixEnd_1868345 : Nat := 4983230072969 + 3 ^ 40 * 1868345 * 2
def baseEnd_1868345 : Nat := 426381783744265700131175

theorem tailTrace_1868345 : CollatzResearch.WordTrace tailWord_1868345 prefixEnd_1868345 426381783744265700131175 := by
  unfold tailWord_1868345
  simp only [CollatzResearch.WordTrace]
  refine ⟨68144140416312627767222489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45429426944208418511481659 68144140416312627767222489)
  ·
    refine ⟨51108105312234470825416867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68144140416312627767222489 51108105312234470825416867)
    ·
      refine ⟨76662157968351706238125301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51108105312234470825416867 76662157968351706238125301)
      ·
        refine ⟨7187077309532972459824247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76662157968351706238125301 7187077309532972459824247)
        ·
          refine ⟨10780615964299458689736371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7187077309532972459824247 10780615964299458689736371)
          ·
            refine ⟨16170923946449188034604557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10780615964299458689736371 16170923946449188034604557)
            ·
              refine ⟨6064096479918445512976709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16170923946449188034604557 6064096479918445512976709)
              ·
                refine ⟨1137018089984708533683133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6064096479918445512976709 1137018089984708533683133)
                ·
                  refine ⟨426381783744265700131175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1137018089984708533683133 426381783744265700131175)
                  ·
                    rfl

theorem cell21_1868345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 3, 4, 3].length) (baseStart_1868345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868345 prefixEnd_1868345 := by exact prefixLift 1868345
  have htrace : WordTrace (prefixWord ++ tailWord_1868345) baseStart_1868345 baseEnd_1868345 := by
    simpa [prefixWord, tailWord_1868345, baseEnd_1868345] using wordTrace_append hprefix tailTrace_1868345
  have hstable : (prefixWord ++ tailWord_1868345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868345).length < 2 ^ (prefixWord ++ tailWord_1868345).sum := by decide
  have hdescent : baseEnd_1868345 < baseStart_1868345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868359 : List Nat := [1, 1, 4, 1, 4, 1, 2, 3, 4]
def baseStart_1868359 : Nat := 118140960795 + 1868359 * 2 ^ 59
def prefixEnd_1868359 : Nat := 4983230072969 + 3 ^ 40 * 1868359 * 2
def baseEnd_1868359 : Nat := 426384978735004786897813

theorem tailTrace_1868359 : CollatzResearch.WordTrace tailWord_1868359 prefixEnd_1868359 426384978735004786897813 := by
  unfold tailWord_1868359
  simp only [CollatzResearch.WordTrace]
  refine ⟨68144651038261908158232131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45429767358841272105488087 68144651038261908158232131)
  ·
    refine ⟨102216976557392862237348197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68144651038261908158232131 102216976557392862237348197)
    ·
      refine ⟨19165683104511161669502787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102216976557392862237348197 19165683104511161669502787)
      ·
        refine ⟨28748524656766742504254181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19165683104511161669502787 28748524656766742504254181)
        ·
          refine ⟨5390348373143764219547659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28748524656766742504254181 5390348373143764219547659)
          ·
            refine ⟨8085522559715646329321489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5390348373143764219547659 8085522559715646329321489)
            ·
              refine ⟨6064141919786734746991117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8085522559715646329321489 6064141919786734746991117)
              ·
                refine ⟨2274053219920025530121669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6064141919786734746991117 2274053219920025530121669)
                ·
                  refine ⟨426384978735004786897813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2274053219920025530121669 426384978735004786897813)
                  ·
                    rfl

theorem cell21_1868359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 3, 4].length) (baseStart_1868359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868359 prefixEnd_1868359 := by exact prefixLift 1868359
  have htrace : WordTrace (prefixWord ++ tailWord_1868359) baseStart_1868359 baseEnd_1868359 := by
    simpa [prefixWord, tailWord_1868359, baseEnd_1868359] using wordTrace_append hprefix tailTrace_1868359
  have hstable : (prefixWord ++ tailWord_1868359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868359).length < 2 ^ (prefixWord ++ tailWord_1868359).sum := by decide
  have hdescent : baseEnd_1868359 < baseStart_1868359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868387 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 7]
def baseStart_1868387 : Nat := 118140960795 + 1868387 * 2 ^ 59
def prefixEnd_1868387 : Nat := 4983230072969 + 3 ^ 40 * 1868387 * 2
def baseEnd_1868387 : Nat := 426391368716482960431089

theorem tailTrace_1868387 : CollatzResearch.WordTrace tailWord_1868387 prefixEnd_1868387 426391368716482960431089 := by
  unfold tailWord_1868387
  simp only [CollatzResearch.WordTrace]
  refine ⟨68145672282160468940251415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45430448188106979293500943 68145672282160468940251415)
  ·
    refine ⟨102218508423240703410377123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68145672282160468940251415 102218508423240703410377123)
    ·
      refine ⟨153327762634861055115565685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102218508423240703410377123 153327762634861055115565685)
      ·
        refine ⟨14374477747018223917084283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 153327762634861055115565685 14374477747018223917084283)
        ·
          refine ⟨21561716620527335875626425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14374477747018223917084283 21561716620527335875626425)
          ·
            refine ⟨16171287465395501906719819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21561716620527335875626425 16171287465395501906719819)
            ·
              refine ⟨24256931198093252860079729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16171287465395501906719819 24256931198093252860079729)
              ·
                refine ⟨18192698398569939645059797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24256931198093252860079729 18192698398569939645059797)
                ·
                  refine ⟨426391368716482960431089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18192698398569939645059797 426391368716482960431089)
                  ·
                    rfl

theorem cell21_1868387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 7].length) (baseStart_1868387 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868387 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868387 prefixEnd_1868387 := by exact prefixLift 1868387
  have htrace : WordTrace (prefixWord ++ tailWord_1868387) baseStart_1868387 baseEnd_1868387 := by
    simpa [prefixWord, tailWord_1868387, baseEnd_1868387] using wordTrace_append hprefix tailTrace_1868387
  have hstable : (prefixWord ++ tailWord_1868387).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868387).length < 2 ^ (prefixWord ++ tailWord_1868387).sum := by decide
  have hdescent : baseEnd_1868387 < baseStart_1868387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868455 : List Nat := [1, 1, 6, 3, 2, 1, 1, 1, 5]
def baseStart_1868455 : Nat := 118140960795 + 1868455 * 2 ^ 59
def prefixEnd_1868455 : Nat := 4983230072969 + 3 ^ 40 * 1868455 * 2
def baseEnd_1868455 : Nat := 426406887242929953297617

theorem tailTrace_1868455 : CollatzResearch.WordTrace tailWord_1868455 prefixEnd_1868455 426406887242929953297617 := by
  unfold tailWord_1868455
  simp only [CollatzResearch.WordTrace]
  refine ⟨68148152445914116553726819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45432101630609411035817879 68148152445914116553726819)
  ·
    refine ⟨102222228668871174830590229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68148152445914116553726819 102222228668871174830590229)
    ·
      refine ⟨4791666968853336320183917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102222228668871174830590229 4791666968853336320183917)
      ·
        refine ⟨1796875113320001120068969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4791666968853336320183917 1796875113320001120068969)
        ·
          refine ⟨1347656334990000840051727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1796875113320001120068969 1347656334990000840051727)
          ·
            refine ⟨2021484502485001260077591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347656334990000840051727 2021484502485001260077591)
            ·
              refine ⟨3032226753727501890116387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2021484502485001260077591 3032226753727501890116387)
              ·
                refine ⟨4548340130591252835174581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3032226753727501890116387 4548340130591252835174581)
                ·
                  refine ⟨426406887242929953297617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4548340130591252835174581 426406887242929953297617)
                  ·
                    rfl

theorem cell21_1868455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 1, 1, 1, 5].length) (baseStart_1868455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868455 prefixEnd_1868455 := by exact prefixLift 1868455
  have htrace : WordTrace (prefixWord ++ tailWord_1868455) baseStart_1868455 baseEnd_1868455 := by
    simpa [prefixWord, tailWord_1868455, baseEnd_1868455] using wordTrace_append hprefix tailTrace_1868455
  have hstable : (prefixWord ++ tailWord_1868455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868455).length < 2 ^ (prefixWord ++ tailWord_1868455).sum := by decide
  have hdescent : baseEnd_1868455 < baseStart_1868455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868469 : List Nat := [1, 3, 3, 3, 1, 3, 2, 1, 4]
def baseStart_1868469 : Nat := 118140960795 + 1868469 * 2 ^ 59
def prefixEnd_1868469 : Nat := 4983230072969 + 3 ^ 40 * 1868469 * 2
def baseEnd_1868469 : Nat := 426410082233669040064255

theorem tailTrace_1868469 : CollatzResearch.WordTrace tailWord_1868469 prefixEnd_1868469 426410082233669040064255 := by
  unfold tailWord_1868469
  simp only [CollatzResearch.WordTrace]
  refine ⟨68148663067863396944736461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45432442045242264629824307 68148663067863396944736461)
  ·
    refine ⟨25555748650448773854276173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68148663067863396944736461 25555748650448773854276173)
    ·
      refine ⟨9583405743918290195353565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25555748650448773854276173 9583405743918290195353565)
      ·
        refine ⟨3593777153969358823257587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9583405743918290195353565 3593777153969358823257587)
        ·
          refine ⟨5390665730954038234886381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3593777153969358823257587 5390665730954038234886381)
          ·
            refine ⟨2021499649107764338082393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5390665730954038234886381 2021499649107764338082393)
            ·
              refine ⟨1516124736830823253561795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2021499649107764338082393 1516124736830823253561795)
              ·
                refine ⟨2274187105246234880342693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516124736830823253561795 2274187105246234880342693)
                ·
                  refine ⟨426410082233669040064255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2274187105246234880342693 426410082233669040064255)
                  ·
                    rfl

theorem cell21_1868469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_1868469 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868469 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868469 prefixEnd_1868469 := by exact prefixLift 1868469
  have htrace : WordTrace (prefixWord ++ tailWord_1868469) baseStart_1868469 baseEnd_1868469 := by
    simpa [prefixWord, tailWord_1868469, baseEnd_1868469] using wordTrace_append hprefix tailTrace_1868469
  have hstable : (prefixWord ++ tailWord_1868469).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868469).length < 2 ^ (prefixWord ++ tailWord_1868469).sum := by decide
  have hdescent : baseEnd_1868469 < baseStart_1868469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868511 : List Nat := [1, 1, 2, 3, 2, 4, 2, 2, 4]
def baseStart_1868511 : Nat := 118140960795 + 1868511 * 2 ^ 59
def prefixEnd_1868511 : Nat := 4983230072969 + 3 ^ 40 * 1868511 * 2
def baseEnd_1868511 : Nat := 426419667205886300364169

theorem tailTrace_1868511 : CollatzResearch.WordTrace tailWord_1868511 prefixEnd_1868511 426419667205886300364169 := by
  unfold tailWord_1868511
  simp only [CollatzResearch.WordTrace]
  refine ⟨68150194933711238117765387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45433463289140825411843591 68150194933711238117765387)
  ·
    refine ⟨102225292400566857176648081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68150194933711238117765387 102225292400566857176648081)
    ·
      refine ⟨76668969300425142882486061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102225292400566857176648081 76668969300425142882486061)
      ·
        refine ⟨28750863487659428580932273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76668969300425142882486061 28750863487659428580932273)
        ·
          refine ⟨21563147615744571435699205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28750863487659428580932273 21563147615744571435699205)
          ·
            refine ⟨4043090177952107144193601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21563147615744571435699205 4043090177952107144193601)
            ·
              refine ⟨3032317633464080358145201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4043090177952107144193601 3032317633464080358145201)
              ·
                refine ⟨2274238225098060268608901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3032317633464080358145201 2274238225098060268608901)
                ·
                  refine ⟨426419667205886300364169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2274238225098060268608901 426419667205886300364169)
                  ·
                    rfl

theorem cell21_1868511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 2, 4].length) (baseStart_1868511 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868511 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868511 prefixEnd_1868511 := by exact prefixLift 1868511
  have htrace : WordTrace (prefixWord ++ tailWord_1868511) baseStart_1868511 baseEnd_1868511 := by
    simpa [prefixWord, tailWord_1868511, baseEnd_1868511] using wordTrace_append hprefix tailTrace_1868511
  have hstable : (prefixWord ++ tailWord_1868511).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868511).length < 2 ^ (prefixWord ++ tailWord_1868511).sum := by decide
  have hdescent : baseEnd_1868511 < baseStart_1868511 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868562 : List Nat := [3, 2, 4, 1, 3, 1, 1, 2, 4]
def baseStart_1868562 : Nat := 118140960795 + 1868562 * 2 ^ 59
def prefixEnd_1868562 : Nat := 4983230072969 + 3 ^ 40 * 1868562 * 2
def baseEnd_1868562 : Nat := 426431306100721545014065

theorem tailTrace_1868562 : CollatzResearch.WordTrace tailWord_1868562 prefixEnd_1868562 426431306100721545014065 := by
  unfold tailWord_1868562
  simp only [CollatzResearch.WordTrace]
  refine ⟨17038013764131618456967985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45434703371017649218581293 17038013764131618456967985)
  ·
    refine ⟨12778510323098713842725989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17038013764131618456967985 12778510323098713842725989)
    ·
      refine ⟨2395970685581008845511123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12778510323098713842725989 2395970685581008845511123)
      ·
        refine ⟨3593956028371513268266685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2395970685581008845511123 3593956028371513268266685)
        ·
          refine ⟨1347733510639317475600007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3593956028371513268266685 1347733510639317475600007)
          ·
            refine ⟨2021600265958976213400011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1347733510639317475600007 2021600265958976213400011)
            ·
              refine ⟨3032400398938464320100017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2021600265958976213400011 3032400398938464320100017)
              ·
                refine ⟨2274300299203848240075013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3032400398938464320100017 2274300299203848240075013)
                ·
                  refine ⟨426431306100721545014065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2274300299203848240075013 426431306100721545014065)
                  ·
                    rfl

theorem cell21_1868562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 4].length) (baseStart_1868562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868562 prefixEnd_1868562 := by exact prefixLift 1868562
  have htrace : WordTrace (prefixWord ++ tailWord_1868562) baseStart_1868562 baseEnd_1868562 := by
    simpa [prefixWord, tailWord_1868562, baseEnd_1868562] using wordTrace_append hprefix tailTrace_1868562
  have hstable : (prefixWord ++ tailWord_1868562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868562).length < 2 ^ (prefixWord ++ tailWord_1868562).sum := by decide
  have hdescent : baseEnd_1868562 < baseStart_1868562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868570 : List Nat := [3, 1, 1, 3, 2, 1, 3, 1, 6]
def baseStart_1868570 : Nat := 118140960795 + 1868570 * 2 ^ 59
def prefixEnd_1868570 : Nat := 4983230072969 + 3 ^ 40 * 1868570 * 2
def baseEnd_1868570 : Nat := 426433131809715308880715

theorem tailTrace_1868570 : CollatzResearch.WordTrace tailWord_1868570 prefixEnd_1868570 426433131809715308880715 := by
  unfold tailWord_1868570
  simp only [CollatzResearch.WordTrace]
  refine ⟨17038086710124372798540791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45434897893664994129442109 17038086710124372798540791)
  ·
    refine ⟨25557130065186559197811187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17038086710124372798540791 25557130065186559197811187)
    ·
      refine ⟨38335695097779838796716781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25557130065186559197811187 38335695097779838796716781)
      ·
        refine ⟨14375885661667439548768793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38335695097779838796716781 14375885661667439548768793)
        ·
          refine ⟨10781914246250579661576595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14375885661667439548768793 10781914246250579661576595)
          ·
            refine ⟨16172871369375869492364893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10781914246250579661576595 16172871369375869492364893)
            ·
              refine ⟨6064826763515951059636835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16172871369375869492364893 6064826763515951059636835)
              ·
                refine ⟨9097240145273926589455253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6064826763515951059636835 9097240145273926589455253)
                ·
                  refine ⟨426433131809715308880715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9097240145273926589455253 426433131809715308880715)
                  ·
                    rfl

theorem cell21_1868570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 6].length) (baseStart_1868570 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868570 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868570 prefixEnd_1868570 := by exact prefixLift 1868570
  have htrace : WordTrace (prefixWord ++ tailWord_1868570) baseStart_1868570 baseEnd_1868570 := by
    simpa [prefixWord, tailWord_1868570, baseEnd_1868570] using wordTrace_append hprefix tailTrace_1868570
  have hstable : (prefixWord ++ tailWord_1868570).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868570).length < 2 ^ (prefixWord ++ tailWord_1868570).sum := by decide
  have hdescent : baseEnd_1868570 < baseStart_1868570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868632 : List Nat := [2, 1, 2, 2, 1, 1, 1, 8, 3]
def baseStart_1868632 : Nat := 118140960795 + 1868632 * 2 ^ 59
def prefixEnd_1868632 : Nat := 4983230072969 + 3 ^ 40 * 1868632 * 2
def baseEnd_1868632 : Nat := 426447281054416978847255

theorem tailTrace_1868632 : CollatzResearch.WordTrace tailWord_1868632 prefixEnd_1868632 426447281054416978847255 := by
  unfold tailWord_1868632
  simp only [CollatzResearch.WordTrace]
  refine ⟨34077304083136437891460075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45436405444181917188613433 34077304083136437891460075)
  ·
    refine ⟨51115956124704656837190113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34077304083136437891460075 51115956124704656837190113)
    ·
      refine ⟨38336967093528492627892585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51115956124704656837190113 38336967093528492627892585)
      ·
        refine ⟨28752725320146369470919439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38336967093528492627892585 28752725320146369470919439)
        ·
          refine ⟨43129087980219554206379159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28752725320146369470919439 43129087980219554206379159)
          ·
            refine ⟨64693631970329331309568739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43129087980219554206379159 64693631970329331309568739)
            ·
              refine ⟨97040447955493996964353109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64693631970329331309568739 97040447955493996964353109)
              ·
                refine ⟨1137192749478445276926013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 97040447955493996964353109 1137192749478445276926013)
                ·
                  refine ⟨426447281054416978847255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1137192749478445276926013 426447281054416978847255)
                  ·
                    rfl

theorem cell21_1868632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 1, 8, 3].length) (baseStart_1868632 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868632 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868632 prefixEnd_1868632 := by exact prefixLift 1868632
  have htrace : WordTrace (prefixWord ++ tailWord_1868632) baseStart_1868632 baseEnd_1868632 := by
    simpa [prefixWord, tailWord_1868632, baseEnd_1868632] using wordTrace_append hprefix tailTrace_1868632
  have hstable : (prefixWord ++ tailWord_1868632).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868632).length < 2 ^ (prefixWord ++ tailWord_1868632).sum := by decide
  have hdescent : baseEnd_1868632 < baseStart_1868632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868725 : List Nat := [1, 3, 3, 2, 1, 1, 4, 3, 3]
def baseStart_1868725 : Nat := 118140960795 + 1868725 * 2 ^ 59
def prefixEnd_1868725 : Nat := 4983230072969 + 3 ^ 40 * 1868725 * 2
def baseEnd_1868725 : Nat := 426468504921469483797065

theorem tailTrace_1868725 : CollatzResearch.WordTrace tailWord_1868725 prefixEnd_1868725 426468504921469483797065 := by
  unfold tailWord_1868725
  simp only [CollatzResearch.WordTrace]
  refine ⟨68158000154935952666055629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45438666769957301777370419 68158000154935952666055629)
  ·
    refine ⟨25559250058100982249770861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68158000154935952666055629 25559250058100982249770861)
    ·
      refine ⟨9584718771787868343664073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25559250058100982249770861 9584718771787868343664073)
      ·
        refine ⟨7188539078840901257748055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9584718771787868343664073 7188539078840901257748055)
        ·
          refine ⟨10782808618261351886622083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7188539078840901257748055 10782808618261351886622083)
          ·
            refine ⟨16174212927392027829933125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10782808618261351886622083 16174212927392027829933125)
            ·
              refine ⟨3032664923886005218112461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16174212927392027829933125 3032664923886005218112461)
              ·
                refine ⟨1137249346457251956792173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3032664923886005218112461 1137249346457251956792173)
                ·
                  refine ⟨426468504921469483797065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1137249346457251956792173 426468504921469483797065)
                  ·
                    rfl

theorem cell21_1868725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 3, 3].length) (baseStart_1868725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868725 prefixEnd_1868725 := by exact prefixLift 1868725
  have htrace : WordTrace (prefixWord ++ tailWord_1868725) baseStart_1868725 baseEnd_1868725 := by
    simpa [prefixWord, tailWord_1868725, baseEnd_1868725] using wordTrace_append hprefix tailTrace_1868725
  have hstable : (prefixWord ++ tailWord_1868725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868725).length < 2 ^ (prefixWord ++ tailWord_1868725).sum := by decide
  have hdescent : baseEnd_1868725 < baseStart_1868725 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868736 : List Nat := [2, 1, 1, 2, 3, 4, 8]
def baseStart_1868736 : Nat := 118140960795 + 1868736 * 2 ^ 59
def prefixEnd_1868736 : Nat := 4983230072969 + 3 ^ 40 * 1868736 * 2
def baseEnd_1868736 : Nat := 47385668363481767679301

theorem tailTrace_1868736 : CollatzResearch.WordTrace tailWord_1868736 prefixEnd_1868736 47385668363481767679301 := by
  unfold tailWord_1868736
  simp only [CollatzResearch.WordTrace]
  refine ⟨34079200678948050772353031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45438934238597401029804041 34079200678948050772353031)
  ·
    refine ⟨51118801018422076158529547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34079200678948050772353031 51118801018422076158529547)
    ·
      refine ⟨76678201527633114237794321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51118801018422076158529547 76678201527633114237794321)
      ·
        refine ⟨57508651145724835678345741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76678201527633114237794321 57508651145724835678345741)
        ·
          refine ⟨21565744179646813379379653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 57508651145724835678345741 21565744179646813379379653)
          ·
            refine ⟨4043577033683777508633685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21565744179646813379379653 4043577033683777508633685)
            ·
              refine ⟨47385668363481767679301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4043577033683777508633685 47385668363481767679301)
              ·
                rfl

theorem cell21_1868736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 8].length) (baseStart_1868736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868736 prefixEnd_1868736 := by exact prefixLift 1868736
  have htrace : WordTrace (prefixWord ++ tailWord_1868736) baseStart_1868736 baseEnd_1868736 := by
    simpa [prefixWord, tailWord_1868736, baseEnd_1868736] using wordTrace_append hprefix tailTrace_1868736
  have hstable : (prefixWord ++ tailWord_1868736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868736).length < 2 ^ (prefixWord ++ tailWord_1868736).sum := by decide
  have hdescent : baseEnd_1868736 < baseStart_1868736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868756 : List Nat := [2, 4, 1, 2, 1, 3, 3, 1, 4]
def baseStart_1868756 : Nat := 118140960795 + 1868756 * 2 ^ 59
def prefixEnd_1868756 : Nat := 4983230072969 + 3 ^ 40 * 1868756 * 2
def baseEnd_1868756 : Nat := 426475579543820318780335

theorem tailTrace_1868756 : CollatzResearch.WordTrace tailWord_1868756 prefixEnd_1868756 426475579543820318780335 := by
  unfold tailWord_1868756
  simp only [CollatzResearch.WordTrace]
  refine ⟨34079565408911822480217061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45439420545215763306956081 34079565408911822480217061)
  ·
    refine ⟨6389918514170966715040699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34079565408911822480217061 6389918514170966715040699)
    ·
      refine ⟨9584877771256450072561049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6389918514170966715040699 9584877771256450072561049)
      ·
        refine ⟨7188658328442337554420787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9584877771256450072561049 7188658328442337554420787)
        ·
          refine ⟨10782987492663506331631181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7188658328442337554420787 10782987492663506331631181)
          ·
            refine ⟨4043620309748814874361693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10782987492663506331631181 4043620309748814874361693)
            ·
              refine ⟨1516357616155805577885635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4043620309748814874361693 1516357616155805577885635)
              ·
                refine ⟨2274536424233708366828453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1516357616155805577885635 2274536424233708366828453)
                ·
                  refine ⟨426475579543820318780335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2274536424233708366828453 426475579543820318780335)
                  ·
                    rfl

theorem cell21_1868756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_1868756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868756 prefixEnd_1868756 := by exact prefixLift 1868756
  have htrace : WordTrace (prefixWord ++ tailWord_1868756) baseStart_1868756 baseEnd_1868756 := by
    simpa [prefixWord, tailWord_1868756, baseEnd_1868756] using wordTrace_append hprefix tailTrace_1868756
  have hstable : (prefixWord ++ tailWord_1868756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868756).length < 2 ^ (prefixWord ++ tailWord_1868756).sum := by decide
  have hdescent : baseEnd_1868756 < baseStart_1868756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868770 : List Nat := [3, 3, 3, 1, 1, 2, 1, 7]
def baseStart_1868770 : Nat := 118140960795 + 1868770 * 2 ^ 59
def prefixEnd_1868770 : Nat := 4983230072969 + 3 ^ 40 * 1868770 * 2
def baseEnd_1868770 : Nat := 142159591511519801848991

theorem tailTrace_1868770 : CollatzResearch.WordTrace tailWord_1868770 prefixEnd_1868770 142159591511519801848991 := by
  unfold tailWord_1868770
  simp only [CollatzResearch.WordTrace]
  refine ⟨17039910359943231337860941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45439760959848616900962509 17039910359943231337860941)
  ·
    refine ⟨6389966384978711751697853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17039910359943231337860941 6389966384978711751697853)
    ·
      refine ⟨2396237394367016906886695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6389966384978711751697853 2396237394367016906886695)
      ·
        refine ⟨3594356091550525360330043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2396237394367016906886695 3594356091550525360330043)
        ·
          refine ⟨5391534137325788040495065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3594356091550525360330043 5391534137325788040495065)
          ·
            refine ⟨4043650602994341030371299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5391534137325788040495065 4043650602994341030371299)
            ·
              refine ⟨6065475904491511545556949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4043650602994341030371299 6065475904491511545556949)
              ·
                refine ⟨142159591511519801848991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6065475904491511545556949 142159591511519801848991)
                ·
                  rfl

theorem cell21_1868770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 2, 1, 7].length) (baseStart_1868770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868770 prefixEnd_1868770 := by exact prefixLift 1868770
  have htrace : WordTrace (prefixWord ++ tailWord_1868770) baseStart_1868770 baseEnd_1868770 := by
    simpa [prefixWord, tailWord_1868770, baseEnd_1868770] using wordTrace_append hprefix tailTrace_1868770
  have hstable : (prefixWord ++ tailWord_1868770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868770).length < 2 ^ (prefixWord ++ tailWord_1868770).sum := by decide
  have hdescent : baseEnd_1868770 < baseStart_1868770 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868812 : List Nat := [2, 2, 1, 2, 3, 2, 1, 8]
def baseStart_1868812 : Nat := 118140960795 + 1868812 * 2 ^ 59
def prefixEnd_1868812 : Nat := 4983230072969 + 3 ^ 40 * 1868812 * 2
def baseEnd_1868812 : Nat := 142162786502258888615629

theorem tailTrace_1868812 : CollatzResearch.WordTrace tailWord_1868812 prefixEnd_1868812 142162786502258888615629 := by
  unfold tailWord_1868812
  simp only [CollatzResearch.WordTrace]
  refine ⟨34080586652810383262236345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45440782203747177682981793 34080586652810383262236345)
  ·
    refine ⟨25560439989607787446677259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34080586652810383262236345 25560439989607787446677259)
    ·
      refine ⟨38340659984411681170015889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25560439989607787446677259 38340659984411681170015889)
      ·
        refine ⟨28755494988308760877511917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38340659984411681170015889 28755494988308760877511917)
        ·
          refine ⟨10783310620615785329066969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28755494988308760877511917 10783310620615785329066969)
          ·
            refine ⟨8087482965461838996800227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10783310620615785329066969 8087482965461838996800227)
            ·
              refine ⟨12131224448192758495200341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8087482965461838996800227 12131224448192758495200341)
              ·
                refine ⟨142162786502258888615629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12131224448192758495200341 142162786502258888615629)
                ·
                  rfl

theorem cell21_1868812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 1, 8].length) (baseStart_1868812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868812 prefixEnd_1868812 := by exact prefixLift 1868812
  have htrace : WordTrace (prefixWord ++ tailWord_1868812) baseStart_1868812 baseEnd_1868812 := by
    simpa [prefixWord, tailWord_1868812, baseEnd_1868812] using wordTrace_append hprefix tailTrace_1868812
  have hstable : (prefixWord ++ tailWord_1868812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868812).length < 2 ^ (prefixWord ++ tailWord_1868812).sum := by decide
  have hdescent : baseEnd_1868812 < baseStart_1868812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868874 : List Nat := [3, 1, 2, 1, 1, 2, 4, 3, 4]
def baseStart_1868874 : Nat := 118140960795 + 1868874 * 2 ^ 59
def prefixEnd_1868874 : Nat := 4983230072969 + 3 ^ 40 * 1868874 * 2
def baseEnd_1868874 : Nat := 426502508751478335813427

theorem tailTrace_1868874 : CollatzResearch.WordTrace tailWord_1868874 prefixEnd_1868874 426502508751478335813427 := by
  unfold tailWord_1868874
  simp only [CollatzResearch.WordTrace]
  refine ⟨17040858657849037778307419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45442289754264100742153117 17040858657849037778307419)
  ·
    refine ⟨25561287986773556667461129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17040858657849037778307419 25561287986773556667461129)
    ·
      refine ⟨19170965990080167500595847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25561287986773556667461129 19170965990080167500595847)
      ·
        refine ⟨28756448985120251250893771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19170965990080167500595847 28756448985120251250893771)
        ·
          refine ⟨43134673477680376876340657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28756448985120251250893771 43134673477680376876340657)
          ·
            refine ⟨32351005108260282657255493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43134673477680376876340657 32351005108260282657255493)
            ·
              refine ⟨6065813457798802998235405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32351005108260282657255493 6065813457798802998235405)
              ·
                refine ⟨2274680046674551124338277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6065813457798802998235405 2274680046674551124338277)
                ·
                  refine ⟨426502508751478335813427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2274680046674551124338277 426502508751478335813427)
                  ·
                    rfl

theorem cell21_1868874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_1868874 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868874 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868874 prefixEnd_1868874 := by exact prefixLift 1868874
  have htrace : WordTrace (prefixWord ++ tailWord_1868874) baseStart_1868874 baseEnd_1868874 := by
    simpa [prefixWord, tailWord_1868874, baseEnd_1868874] using wordTrace_append hprefix tailTrace_1868874
  have hstable : (prefixWord ++ tailWord_1868874).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868874).length < 2 ^ (prefixWord ++ tailWord_1868874).sum := by decide
  have hdescent : baseEnd_1868874 < baseStart_1868874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868919 : List Nat := [1, 1, 3, 1, 1, 4, 4, 1, 5]
def baseStart_1868919 : Nat := 118140960795 + 1868919 * 2 ^ 59
def prefixEnd_1868919 : Nat := 4983230072969 + 3 ^ 40 * 1868919 * 2
def baseEnd_1868919 : Nat := 426512778364568257563335

theorem tailTrace_1868919 : CollatzResearch.WordTrace tailWord_1868919 prefixEnd_1868919 426512778364568257563335 := by
  unfold tailWord_1868919
  simp only [CollatzResearch.WordTrace]
  refine ⟨68165075916233123798617811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45443383944155415865745207 68165075916233123798617811)
  ·
    refine ⟨102247613874349685697926717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68165075916233123798617811 102247613874349685697926717)
    ·
      refine ⟨38342855202881132136722519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102247613874349685697926717 38342855202881132136722519)
      ·
        refine ⟨57514282804321698205083779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38342855202881132136722519 57514282804321698205083779)
        ·
          refine ⟨86271424206482547307625669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57514282804321698205083779 86271424206482547307625669)
          ·
            refine ⟨16175892038715477620179813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 86271424206482547307625669 16175892038715477620179813)
            ·
              refine ⟨3032979757259152053783715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16175892038715477620179813 3032979757259152053783715)
              ·
                refine ⟨4549469635888728080675573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3032979757259152053783715 4549469635888728080675573)
                ·
                  refine ⟨426512778364568257563335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4549469635888728080675573 426512778364568257563335)
                  ·
                    rfl

theorem cell21_1868919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 4, 1, 5].length) (baseStart_1868919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868919 prefixEnd_1868919 := by exact prefixLift 1868919
  have htrace : WordTrace (prefixWord ++ tailWord_1868919) baseStart_1868919 baseEnd_1868919 := by
    simpa [prefixWord, tailWord_1868919, baseEnd_1868919] using wordTrace_append hprefix tailTrace_1868919
  have hstable : (prefixWord ++ tailWord_1868919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868919).length < 2 ^ (prefixWord ++ tailWord_1868919).sum := by decide
  have hdescent : baseEnd_1868919 < baseStart_1868919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1868964 : List Nat := [2, 3, 1, 2, 3, 1, 9]
def baseStart_1868964 : Nat := 118140960795 + 1868964 * 2 ^ 59
def prefixEnd_1868964 : Nat := 4983230072969 + 3 ^ 40 * 1868964 * 2
def baseEnd_1868964 : Nat := 47391449775295353257027

theorem tailTrace_1868964 : CollatzResearch.WordTrace tailWord_1868964 prefixEnd_1868964 47391449775295353257027 := by
  unfold tailWord_1868964
  simp only [CollatzResearch.WordTrace]
  refine ⟨34083358600535048242002973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45444478134046730989337297 34083358600535048242002973)
  ·
    refine ⟨12781259475200643090751115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34083358600535048242002973 12781259475200643090751115)
    ·
      refine ⟨19171889212800964636126673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12781259475200643090751115 19171889212800964636126673)
      ·
        refine ⟨14378916909600723477095005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19171889212800964636126673 14378916909600723477095005)
        ·
          refine ⟨5392093841100271303910627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14378916909600723477095005 5392093841100271303910627)
          ·
            refine ⟨8088140761650406955865941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5392093841100271303910627 8088140761650406955865941)
            ·
              refine ⟨47391449775295353257027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8088140761650406955865941 47391449775295353257027)
              ·
                rfl

theorem cell21_1868964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 9].length) (baseStart_1868964 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1868964 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1868964 prefixEnd_1868964 := by exact prefixLift 1868964
  have htrace : WordTrace (prefixWord ++ tailWord_1868964) baseStart_1868964 baseEnd_1868964 := by
    simpa [prefixWord, tailWord_1868964, baseEnd_1868964] using wordTrace_append hprefix tailTrace_1868964
  have hstable : (prefixWord ++ tailWord_1868964).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1868964).length < 2 ^ (prefixWord ++ tailWord_1868964).sum := by decide
  have hdescent : baseEnd_1868964 < baseStart_1868964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1868964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869029 : List Nat := [1, 3, 1, 4, 3, 1, 1, 4, 3]
def baseStart_1869029 : Nat := 118140960795 + 1869029 * 2 ^ 59
def prefixEnd_1869029 : Nat := 4983230072969 + 3 ^ 40 * 1869029 * 2
def baseEnd_1869029 : Nat := 426537881863232510729777

theorem tailTrace_1869029 : CollatzResearch.WordTrace tailWord_1869029 prefixEnd_1869029 426537881863232510729777 := by
  unfold tailWord_1869029
  simp only [CollatzResearch.WordTrace]
  refine ⟨68169087945834612585122141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45446058630556408390081427 68169087945834612585122141)
  ·
    refine ⟨25563407979687979719420803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68169087945834612585122141 25563407979687979719420803)
    ·
      refine ⟨38345111969531969579131205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25563407979687979719420803 38345111969531969579131205)
      ·
        refine ⟨7189708494287244296087101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38345111969531969579131205 7189708494287244296087101)
        ·
          refine ⟨2696140685357716611032663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7189708494287244296087101 2696140685357716611032663)
          ·
            refine ⟨4044211028036574916548995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2696140685357716611032663 4044211028036574916548995)
            ·
              refine ⟨6066316542054862374823493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4044211028036574916548995 6066316542054862374823493)
              ·
                refine ⟨1137434351635286695279405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6066316542054862374823493 1137434351635286695279405)
                ·
                  refine ⟨426537881863232510729777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1137434351635286695279405 426537881863232510729777)
                  ·
                    rfl

theorem cell21_1869029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 4, 3].length) (baseStart_1869029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869029 prefixEnd_1869029 := by exact prefixLift 1869029
  have htrace : WordTrace (prefixWord ++ tailWord_1869029) baseStart_1869029 baseEnd_1869029 := by
    simpa [prefixWord, tailWord_1869029, baseEnd_1869029] using wordTrace_append hprefix tailTrace_1869029
  have hstable : (prefixWord ++ tailWord_1869029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869029).length < 2 ^ (prefixWord ++ tailWord_1869029).sum := by decide
  have hdescent : baseEnd_1869029 < baseStart_1869029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869057 : List Nat := [1, 2, 4, 1, 1, 4, 3, 5]
def baseStart_1869057 : Nat := 118140960795 + 1869057 * 2 ^ 59
def prefixEnd_1869057 : Nat := 4983230072969 + 3 ^ 40 * 1869057 * 2
def baseEnd_1869057 : Nat := 142181423948236894754351

theorem tailTrace_1869057 : CollatzResearch.WordTrace tailWord_1869057 prefixEnd_1869057 142181423948236894754351 := by
  unfold tailWord_1869057
  simp only [CollatzResearch.WordTrace]
  refine ⟨68170109189733173367141425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45446739459822115578094283 68170109189733173367141425)
  ·
    refine ⟨51127581892299880025356069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68170109189733173367141425 51127581892299880025356069)
    ·
      refine ⟨9586421604806227504754263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51127581892299880025356069 9586421604806227504754263)
      ·
        refine ⟨14379632407209341257131395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9586421604806227504754263 14379632407209341257131395)
        ·
          refine ⟨21569448610814011885697093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14379632407209341257131395 21569448610814011885697093)
          ·
            refine ⟨4044271614527627228568205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21569448610814011885697093 4044271614527627228568205)
            ·
              refine ⟨1516601855447860210713077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4044271614527627228568205 1516601855447860210713077)
              ·
                refine ⟨142181423948236894754351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1516601855447860210713077 142181423948236894754351)
                ·
                  rfl

theorem cell21_1869057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 3, 5].length) (baseStart_1869057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869057 prefixEnd_1869057 := by exact prefixLift 1869057
  have htrace : WordTrace (prefixWord ++ tailWord_1869057) baseStart_1869057 baseEnd_1869057 := by
    simpa [prefixWord, tailWord_1869057, baseEnd_1869057] using wordTrace_append hprefix tailTrace_1869057
  have hstable : (prefixWord ++ tailWord_1869057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869057).length < 2 ^ (prefixWord ++ tailWord_1869057).sum := by decide
  have hdescent : baseEnd_1869057 < baseStart_1869057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869074 : List Nat := [3, 2, 4, 2, 1, 1, 8]
def baseStart_1869074 : Nat := 118140960795 + 1869074 * 2 ^ 59
def prefixEnd_1869074 : Nat := 4983230072969 + 3 ^ 40 * 1869074 * 2
def baseEnd_1869074 : Nat := 47394239052924714719965

theorem tailTrace_1869074 : CollatzResearch.WordTrace tailWord_1869074 prefixEnd_1869074 47394239052924714719965 := by
  unfold tailWord_1869074
  simp only [CollatzResearch.WordTrace]
  refine ⟨17042682307667896317627569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45447152820447723513673517 17042682307667896317627569)
  ·
    refine ⟨12782011730750922238220677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17042682307667896317627569 12782011730750922238220677)
    ·
      refine ⟨2396627199515797919666377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 12782011730750922238220677 2396627199515797919666377)
      ·
        refine ⟨1797470399636848439749783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2396627199515797919666377 1797470399636848439749783)
        ·
          refine ⟨2696205599455272659624675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1797470399636848439749783 2696205599455272659624675)
          ·
            refine ⟨4044308399182908989437013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2696205599455272659624675 4044308399182908989437013)
            ·
              refine ⟨47394239052924714719965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4044308399182908989437013 47394239052924714719965)
              ·
                rfl

theorem cell21_1869074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 8].length) (baseStart_1869074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869074 prefixEnd_1869074 := by exact prefixLift 1869074
  have htrace : WordTrace (prefixWord ++ tailWord_1869074) baseStart_1869074 baseEnd_1869074 := by
    simpa [prefixWord, tailWord_1869074, baseEnd_1869074] using wordTrace_append hprefix tailTrace_1869074
  have hstable : (prefixWord ++ tailWord_1869074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869074).length < 2 ^ (prefixWord ++ tailWord_1869074).sum := by decide
  have hdescent : baseEnd_1869074 < baseStart_1869074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869088 : List Nat := [2, 1, 1, 5, 3, 1, 2, 1, 5]
def baseStart_1869088 : Nat := 118140960795 + 1869088 * 2 ^ 59
def prefixEnd_1869088 : Nat := 4983230072969 + 3 ^ 40 * 1869088 * 2
def baseEnd_1869088 : Nat := 426551346467061519246323

theorem tailTrace_1869088 : CollatzResearch.WordTrace tailWord_1869088 prefixEnd_1869088 426551346467061519246323 := by
  unfold tailWord_1869088
  simp only [CollatzResearch.WordTrace]
  refine ⟨34085619926310432830759959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45447493235080577107679945 34085619926310432830759959)
  ·
    refine ⟨51128429889465649246139939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34085619926310432830759959 51128429889465649246139939)
    ·
      refine ⟨76692644834198473869209909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51128429889465649246139939 76692644834198473869209909)
      ·
        refine ⟨7189935453206106925238429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76692644834198473869209909 7189935453206106925238429)
        ·
          refine ⟨2696225794952290096964411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7189935453206106925238429 2696225794952290096964411)
          ·
            refine ⟨4044338692428435145446617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2696225794952290096964411 4044338692428435145446617)
            ·
              refine ⟨3033254019321326359084963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4044338692428435145446617 3033254019321326359084963)
              ·
                refine ⟨4549881028981989538627445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3033254019321326359084963 4549881028981989538627445)
                ·
                  refine ⟨426551346467061519246323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4549881028981989538627445 426551346467061519246323)
                  ·
                    rfl

theorem cell21_1869088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 2, 1, 5].length) (baseStart_1869088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869088 prefixEnd_1869088 := by exact prefixLift 1869088
  have htrace : WordTrace (prefixWord ++ tailWord_1869088) baseStart_1869088 baseEnd_1869088 := by
    simpa [prefixWord, tailWord_1869088, baseEnd_1869088] using wordTrace_append hprefix tailTrace_1869088
  have hstable : (prefixWord ++ tailWord_1869088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869088).length < 2 ^ (prefixWord ++ tailWord_1869088).sum := by decide
  have hdescent : baseEnd_1869088 < baseStart_1869088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869116 : List Nat := [2, 2, 2, 2, 1, 4, 1, 7]
def baseStart_1869116 : Nat := 118140960795 + 1869116 * 2 ^ 59
def prefixEnd_1869116 : Nat := 4983230072969 + 3 ^ 40 * 1869116 * 2
def baseEnd_1869116 : Nat := 142185912149513230926533

theorem tailTrace_1869116 : CollatzResearch.WordTrace tailWord_1869116 prefixEnd_1869116 142185912149513230926533 := by
  unfold tailWord_1869116
  simp only [CollatzResearch.WordTrace]
  refine ⟨34086130548259713221769601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45448174064346284295692801 34086130548259713221769601)
  ·
    refine ⟨25564597911194784916327201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34086130548259713221769601 25564597911194784916327201)
    ·
      refine ⟨19173448433396088687245401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25564597911194784916327201 19173448433396088687245401)
      ·
        refine ⟨14380086325047066515434051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19173448433396088687245401 14380086325047066515434051)
        ·
          refine ⟨21570129487570599773151077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14380086325047066515434051 21570129487570599773151077)
          ·
            refine ⟨4044399278919487457465827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21570129487570599773151077 4044399278919487457465827)
            ·
              refine ⟨6066598918379231186198741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4044399278919487457465827 6066598918379231186198741)
              ·
                refine ⟨142185912149513230926533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6066598918379231186198741 142185912149513230926533)
                ·
                  rfl

theorem cell21_1869116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 4, 1, 7].length) (baseStart_1869116 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869116 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869116 prefixEnd_1869116 := by exact prefixLift 1869116
  have htrace : WordTrace (prefixWord ++ tailWord_1869116) baseStart_1869116 baseEnd_1869116 := by
    simpa [prefixWord, tailWord_1869116, baseEnd_1869116] using wordTrace_append hprefix tailTrace_1869116
  have hstable : (prefixWord ++ tailWord_1869116).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869116).length < 2 ^ (prefixWord ++ tailWord_1869116).sum := by decide
  have hdescent : baseEnd_1869116 < baseStart_1869116 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869130 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 7]
def baseStart_1869130 : Nat := 118140960795 + 1869130 * 2 ^ 59
def prefixEnd_1869130 : Nat := 4983230072969 + 3 ^ 40 * 1869130 * 2
def baseEnd_1869130 : Nat := 426560931439278779546237

theorem tailTrace_1869130 : CollatzResearch.WordTrace tailWord_1869130 prefixEnd_1869130 426560931439278779546237 := by
  unfold tailWord_1869130
  simp only [CollatzResearch.WordTrace]
  refine ⟨17043192929617176708637211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45448514478979137889699229 17043192929617176708637211)
  ·
    refine ⟨25564789394425765062955817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17043192929617176708637211 25564789394425765062955817)
    ·
      refine ⟨19173592045819323797216863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25564789394425765062955817 19173592045819323797216863)
      ·
        refine ⟨28760388068728985695825295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19173592045819323797216863 28760388068728985695825295)
        ·
          refine ⟨43140582103093478543737943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28760388068728985695825295 43140582103093478543737943)
          ·
            refine ⟨64710873154640217815606915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43140582103093478543737943 64710873154640217815606915)
            ·
              refine ⟨97066309731960326723410373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64710873154640217815606915 97066309731960326723410373)
              ·
                refine ⟨18199933074742561260639445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97066309731960326723410373 18199933074742561260639445)
                ·
                  refine ⟨426560931439278779546237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18199933074742561260639445 426560931439278779546237)
                  ·
                    rfl

theorem cell21_1869130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_1869130 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869130 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869130 prefixEnd_1869130 := by exact prefixLift 1869130
  have htrace : WordTrace (prefixWord ++ tailWord_1869130) baseStart_1869130 baseEnd_1869130 := by
    simpa [prefixWord, tailWord_1869130, baseEnd_1869130] using wordTrace_append hprefix tailTrace_1869130
  have hstable : (prefixWord ++ tailWord_1869130).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869130).length < 2 ^ (prefixWord ++ tailWord_1869130).sum := by decide
  have hdescent : baseEnd_1869130 < baseStart_1869130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869175 : List Nat := [1, 1, 3, 1, 1, 2, 3, 9]
def baseStart_1869175 : Nat := 118140960795 + 1869175 * 2 ^ 59
def prefixEnd_1869175 : Nat := 4983230072969 + 3 ^ 40 * 1869175 * 2
def baseEnd_1869175 : Nat := 142190400350789567098715

theorem tailTrace_1869175 : CollatzResearch.WordTrace tailWord_1869175 prefixEnd_1869175 142190400350789567098715 := by
  unfold tailWord_1869175
  simp only [CollatzResearch.WordTrace]
  refine ⟨68174413003305679519936979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45449608668870453013291319 68174413003305679519936979)
  ·
    refine ⟨102261619504958519279905469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68174413003305679519936979 102261619504958519279905469)
    ·
      refine ⟨38348107314359444729964551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102261619504958519279905469 38348107314359444729964551)
      ·
        refine ⟨57522160971539167094946827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38348107314359444729964551 57522160971539167094946827)
        ·
          refine ⟨86283241457308750642420241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57522160971539167094946827 86283241457308750642420241)
          ·
            refine ⟨64712431092981562981815181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86283241457308750642420241 64712431092981562981815181)
            ·
              refine ⟨24267161659868086118180693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 64712431092981562981815181 24267161659868086118180693)
              ·
                refine ⟨142190400350789567098715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 24267161659868086118180693 142190400350789567098715)
                ·
                  rfl

theorem cell21_1869175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 3, 9].length) (baseStart_1869175 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869175 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869175 prefixEnd_1869175 := by exact prefixLift 1869175
  have htrace : WordTrace (prefixWord ++ tailWord_1869175) baseStart_1869175 baseEnd_1869175 := by
    simpa [prefixWord, tailWord_1869175, baseEnd_1869175] using wordTrace_append hprefix tailTrace_1869175
  have hstable : (prefixWord ++ tailWord_1869175).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869175).length < 2 ^ (prefixWord ++ tailWord_1869175).sum := by decide
  have hdescent : baseEnd_1869175 < baseStart_1869175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869223 : List Nat := [1, 1, 6, 1, 1, 1, 3, 2, 5]
def baseStart_1869223 : Nat := 118140960795 + 1869223 * 2 ^ 59
def prefixEnd_1869223 : Nat := 4983230072969 + 3 ^ 40 * 1869223 * 2
def baseEnd_1869223 : Nat := 426582155306331284496047

theorem tailTrace_1869223 : CollatzResearch.WordTrace tailWord_1869223 prefixEnd_1869223 426582155306331284496047 := by
  unfold tailWord_1869223
  simp only [CollatzResearch.WordTrace]
  refine ⟨68176163707131783717684323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45450775804754522478456215 68176163707131783717684323)
  ·
    refine ⟨102264245560697675576526485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68176163707131783717684323 102264245560697675576526485)
    ·
      refine ⟨4793636510657703542649679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102264245560697675576526485 4793636510657703542649679)
      ·
        refine ⟨7190454765986555313974519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4793636510657703542649679 7190454765986555313974519)
        ·
          refine ⟨10785682148979832970961779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7190454765986555313974519 10785682148979832970961779)
          ·
            refine ⟨16178523223469749456442669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10785682148979832970961779 16178523223469749456442669)
            ·
              refine ⟨6066946208801156046166001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16178523223469749456442669 6066946208801156046166001)
              ·
                refine ⟨4550209656600867034624501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6066946208801156046166001 4550209656600867034624501)
                ·
                  refine ⟨426582155306331284496047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4550209656600867034624501 426582155306331284496047)
                  ·
                    rfl

theorem cell21_1869223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 3, 2, 5].length) (baseStart_1869223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869223 prefixEnd_1869223 := by exact prefixLift 1869223
  have htrace : WordTrace (prefixWord ++ tailWord_1869223) baseStart_1869223 baseEnd_1869223 := by
    simpa [prefixWord, tailWord_1869223, baseEnd_1869223] using wordTrace_append hprefix tailTrace_1869223
  have hstable : (prefixWord ++ tailWord_1869223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869223).length < 2 ^ (prefixWord ++ tailWord_1869223).sum := by decide
  have hdescent : baseEnd_1869223 < baseStart_1869223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869285 : List Nat := [1, 3, 1, 5, 1, 1, 4, 5]
def baseStart_1869285 : Nat := 118140960795 + 1869285 * 2 ^ 59
def prefixEnd_1869285 : Nat := 4983230072969 + 3 ^ 40 * 1869285 * 2
def baseEnd_1869285 : Nat := 142198768183677651487529

theorem tailTrace_1869285 : CollatzResearch.WordTrace tailWord_1869285 prefixEnd_1869285 142198768183677651487529 := by
  unfold tailWord_1869285
  simp only [CollatzResearch.WordTrace]
  refine ⟨68178425032907168306441309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45452283355271445537627539 68178425032907168306441309)
  ·
    refine ⟨25566909387340188114915491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68178425032907168306441309 25566909387340188114915491)
    ·
      refine ⟨38350364081010282172373237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25566909387340188114915491 38350364081010282172373237)
      ·
        refine ⟨3595346632594713953659991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38350364081010282172373237 3595346632594713953659991)
        ·
          refine ⟨5393019948892070930489987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3595346632594713953659991 5393019948892070930489987)
          ·
            refine ⟨8089529923338106395734981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5393019948892070930489987 8089529923338106395734981)
            ·
              refine ⟨1516786860625894949200309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8089529923338106395734981 1516786860625894949200309)
              ·
                refine ⟨142198768183677651487529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1516786860625894949200309 142198768183677651487529)
                ·
                  rfl

theorem cell21_1869285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 4, 5].length) (baseStart_1869285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869285 prefixEnd_1869285 := by exact prefixLift 1869285
  have htrace : WordTrace (prefixWord ++ tailWord_1869285) baseStart_1869285 baseEnd_1869285 := by
    simpa [prefixWord, tailWord_1869285, baseEnd_1869285] using wordTrace_append hprefix tailTrace_1869285
  have hstable : (prefixWord ++ tailWord_1869285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869285).length < 2 ^ (prefixWord ++ tailWord_1869285).sum := by decide
  have hdescent : baseEnd_1869285 < baseStart_1869285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869299 : List Nat := [1, 1, 1, 2, 2, 2, 2, 7, 3]
def baseStart_1869299 : Nat := 118140960795 + 1869299 * 2 ^ 59
def prefixEnd_1869299 : Nat := 4983230072969 + 3 ^ 40 * 1869299 * 2
def baseEnd_1869299 : Nat := 426599499541772041229225

theorem tailTrace_1869299 : CollatzResearch.WordTrace tailWord_1869299 prefixEnd_1869299 426599499541772041229225 := by
  unfold tailWord_1869299
  simp only [CollatzResearch.WordTrace]
  refine ⟨68178935654856448697450951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45452623769904299131633967 68178935654856448697450951)
  ·
    refine ⟨102268403482284673046176427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68178935654856448697450951 102268403482284673046176427)
    ·
      refine ⟨153402605223427009569264641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102268403482284673046176427 153402605223427009569264641)
      ·
        refine ⟨115051953917570257176948481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153402605223427009569264641 115051953917570257176948481)
        ·
          refine ⟨86288965438177692882711361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115051953917570257176948481 86288965438177692882711361)
          ·
            refine ⟨64716724078633269662033521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86288965438177692882711361 64716724078633269662033521)
            ·
              refine ⟨48537543058974952246525141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64716724078633269662033521 48537543058974952246525141)
              ·
                refine ⟨1137598665444725443277933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 48537543058974952246525141 1137598665444725443277933)
                ·
                  refine ⟨426599499541772041229225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1137598665444725443277933 426599499541772041229225)
                  ·
                    rfl

theorem cell21_1869299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 7, 3].length) (baseStart_1869299 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869299 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869299 prefixEnd_1869299 := by exact prefixLift 1869299
  have htrace : WordTrace (prefixWord ++ tailWord_1869299) baseStart_1869299 baseEnd_1869299 := by
    simpa [prefixWord, tailWord_1869299, baseEnd_1869299] using wordTrace_append hprefix tailTrace_1869299
  have hstable : (prefixWord ++ tailWord_1869299).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869299).length < 2 ^ (prefixWord ++ tailWord_1869299).sum := by decide
  have hdescent : baseEnd_1869299 < baseStart_1869299 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869344 : List Nat := [2, 1, 1, 6, 1, 1, 2, 7]
def baseStart_1869344 : Nat := 118140960795 + 1869344 * 2 ^ 59
def prefixEnd_1869344 : Nat := 4983230072969 + 3 ^ 40 * 1869344 * 2
def baseEnd_1869344 : Nat := 142203256384953987659711

theorem tailTrace_1869344 : CollatzResearch.WordTrace tailWord_1869344 prefixEnd_1869344 142203256384953987659711 := by
  unfold tailWord_1869344
  simp only [CollatzResearch.WordTrace]
  refine ⟨34090288469846710691419543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45453717959795614255226057 34090288469846710691419543)
  ·
    refine ⟨51135432704770066037129315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34090288469846710691419543 51135432704770066037129315)
    ·
      refine ⟨76703149057155099055693973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51135432704770066037129315 76703149057155099055693973)
      ·
        refine ⟨3595460112054145268235655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76703149057155099055693973 3595460112054145268235655)
        ·
          refine ⟨5393190168081217902353483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3595460112054145268235655 5393190168081217902353483)
          ·
            refine ⟨8089785252121826853530225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5393190168081217902353483 8089785252121826853530225)
            ·
              refine ⟨6067338939091370140147669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8089785252121826853530225 6067338939091370140147669)
              ·
                refine ⟨142203256384953987659711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6067338939091370140147669 142203256384953987659711)
                ·
                  rfl

theorem cell21_1869344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 2, 7].length) (baseStart_1869344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869344 prefixEnd_1869344 := by exact prefixLift 1869344
  have htrace : WordTrace (prefixWord ++ tailWord_1869344) baseStart_1869344 baseEnd_1869344 := by
    simpa [prefixWord, tailWord_1869344, baseEnd_1869344] using wordTrace_append hprefix tailTrace_1869344
  have hstable : (prefixWord ++ tailWord_1869344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869344).length < 2 ^ (prefixWord ++ tailWord_1869344).sum := by decide
  have hdescent : baseEnd_1869344 < baseStart_1869344 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869485 : List Nat := [1, 5, 2, 1, 1, 1, 5, 2, 3]
def baseStart_1869485 : Nat := 118140960795 + 1869485 * 2 ^ 59
def prefixEnd_1869485 : Nat := 4983230072969 + 3 ^ 40 * 1869485 * 2
def baseEnd_1869485 : Nat := 426641947275877051128845

theorem tailTrace_1869485 : CollatzResearch.WordTrace tailWord_1869485 prefixEnd_1869485 426641947275877051128845 := by
  unfold tailWord_1869485
  simp only [CollatzResearch.WordTrace]
  refine ⟨68185719632182602463721909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45457146421455068309147939 68185719632182602463721909)
  ·
    refine ⟨6392411215517118980973929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68185719632182602463721909 6392411215517118980973929)
    ·
      refine ⟨4794308411637839235730447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6392411215517118980973929 4794308411637839235730447)
      ·
        refine ⟨7191462617456758853595671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4794308411637839235730447 7191462617456758853595671)
        ·
          refine ⟨10787193926185138280393507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7191462617456758853595671 10787193926185138280393507)
          ·
            refine ⟨16180790889277707420590261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10787193926185138280393507 16180790889277707420590261)
            ·
              refine ⟨1516949145869785070680337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16180790889277707420590261 1516949145869785070680337)
              ·
                refine ⟨1137711859402338803010253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1516949145869785070680337 1137711859402338803010253)
                ·
                  refine ⟨426641947275877051128845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1137711859402338803010253 426641947275877051128845)
                  ·
                    rfl

theorem cell21_1869485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 2, 3].length) (baseStart_1869485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869485 prefixEnd_1869485 := by exact prefixLift 1869485
  have htrace : WordTrace (prefixWord ++ tailWord_1869485) baseStart_1869485 baseEnd_1869485 := by
    simpa [prefixWord, tailWord_1869485, baseEnd_1869485] using wordTrace_append hprefix tailTrace_1869485
  have hstable : (prefixWord ++ tailWord_1869485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869485).length < 2 ^ (prefixWord ++ tailWord_1869485).sum := by decide
  have hdescent : baseEnd_1869485 < baseStart_1869485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869527 : List Nat := [1, 1, 3, 2, 1, 3, 2, 5, 3]
def baseStart_1869527 : Nat := 118140960795 + 1869527 * 2 ^ 59
def prefixEnd_1869527 : Nat := 4983230072969 + 3 ^ 40 * 1869527 * 2
def baseEnd_1869527 : Nat := 426651532248094311428759

theorem tailTrace_1869527 : CollatzResearch.WordTrace tailWord_1869527 prefixEnd_1869527 426651532248094311428759 := by
  unfold tailWord_1869527
  simp only [CollatzResearch.WordTrace]
  refine ⟨68187251498030443636750835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45458167665353629091167223 68187251498030443636750835)
  ·
    refine ⟨102280877247045665455126253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68187251498030443636750835 102280877247045665455126253)
    ·
      refine ⟨38355328967642124545672345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102280877247045665455126253 38355328967642124545672345)
      ·
        refine ⟨28766496725731593409254259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38355328967642124545672345 28766496725731593409254259)
        ·
          refine ⟨43149745088597390113881389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28766496725731593409254259 43149745088597390113881389)
          ·
            refine ⟨16181154408224021292705521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43149745088597390113881389 16181154408224021292705521)
            ·
              refine ⟨12135865806168015969529141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16181154408224021292705521 12135865806168015969529141)
              ·
                refine ⟨1137737419328251497143357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12135865806168015969529141 1137737419328251497143357)
                ·
                  refine ⟨426651532248094311428759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1137737419328251497143357 426651532248094311428759)
                  ·
                    rfl

theorem cell21_1869527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 2, 5, 3].length) (baseStart_1869527 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869527 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869527 prefixEnd_1869527 := by exact prefixLift 1869527
  have htrace : WordTrace (prefixWord ++ tailWord_1869527) baseStart_1869527 baseEnd_1869527 := by
    simpa [prefixWord, tailWord_1869527, baseEnd_1869527] using wordTrace_append hprefix tailTrace_1869527
  have hstable : (prefixWord ++ tailWord_1869527).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869527).length < 2 ^ (prefixWord ++ tailWord_1869527).sum := by decide
  have hdescent : baseEnd_1869527 < baseStart_1869527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869544 : List Nat := [2, 1, 4, 1, 3, 2, 1, 4, 3]
def baseStart_1869544 : Nat := 118140960795 + 1869544 * 2 ^ 59
def prefixEnd_1869544 : Nat := 4983230072969 + 3 ^ 40 * 1869544 * 2
def baseEnd_1869544 : Nat := 426655411879706059645391

theorem tailTrace_1869544 : CollatzResearch.WordTrace tailWord_1869544 prefixEnd_1869544 426655411879706059645391 := by
  unfold tailWord_1869544
  simp only [CollatzResearch.WordTrace]
  refine ⟨34093935769484427770059843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45458581025979237026746457 34093935769484427770059843)
  ·
    refine ⟨51140903654226641655089765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34093935769484427770059843 51140903654226641655089765)
    ·
      refine ⟨9588919435167495310329331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51140903654226641655089765 9588919435167495310329331)
      ·
        refine ⟨14383379152751242965493997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9588919435167495310329331 14383379152751242965493997)
        ·
          refine ⟨5393767182281716112060249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14383379152751242965493997 5393767182281716112060249)
          ·
            refine ⟨4045325386711287084045187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5393767182281716112060249 4045325386711287084045187)
            ·
              refine ⟨6067988080066930626067781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4045325386711287084045187 6067988080066930626067781)
              ·
                refine ⟨1137747765012549492387709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6067988080066930626067781 1137747765012549492387709)
                ·
                  refine ⟨426655411879706059645391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1137747765012549492387709 426655411879706059645391)
                  ·
                    rfl

theorem cell21_1869544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 4, 3].length) (baseStart_1869544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869544 prefixEnd_1869544 := by exact prefixLift 1869544
  have htrace : WordTrace (prefixWord ++ tailWord_1869544) baseStart_1869544 baseEnd_1869544 := by
    simpa [prefixWord, tailWord_1869544, baseEnd_1869544] using wordTrace_append hprefix tailTrace_1869544
  have hstable : (prefixWord ++ tailWord_1869544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869544).length < 2 ^ (prefixWord ++ tailWord_1869544).sum := by decide
  have hdescent : baseEnd_1869544 < baseStart_1869544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869555 : List Nat := [1, 1, 1, 2, 2, 3, 5, 6]
def baseStart_1869555 : Nat := 118140960795 + 1869555 * 2 ^ 59
def prefixEnd_1869555 : Nat := 4983230072969 + 3 ^ 40 * 1869555 * 2
def baseEnd_1869555 : Nat := 142219307409857494987345

theorem tailTrace_1869555 : CollatzResearch.WordTrace tailWord_1869555 prefixEnd_1869555 142219307409857494987345 := by
  unfold tailWord_1869555
  simp only [CollatzResearch.WordTrace]
  refine ⟨68188272741929004418770119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45458848494619336279180079 68188272741929004418770119)
  ·
    refine ⟨102282409112893506628155179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68188272741929004418770119 102282409112893506628155179)
    ·
      refine ⟨153423613669340259942232769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102282409112893506628155179 153423613669340259942232769)
      ·
        refine ⟨115067710252005194956674577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153423613669340259942232769 115067710252005194956674577)
        ·
          refine ⟨86300782689003896217505933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115067710252005194956674577 86300782689003896217505933)
          ·
            refine ⟨32362793508376461081564725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86300782689003896217505933 32362793508376461081564725)
            ·
              refine ⟨3034011891410293226396693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32362793508376461081564725 3034011891410293226396693)
              ·
                refine ⟨142219307409857494987345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3034011891410293226396693 142219307409857494987345)
                ·
                  rfl

theorem cell21_1869555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 5, 6].length) (baseStart_1869555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869555 prefixEnd_1869555 := by exact prefixLift 1869555
  have htrace : WordTrace (prefixWord ++ tailWord_1869555) baseStart_1869555 baseEnd_1869555 := by
    simpa [prefixWord, tailWord_1869555, baseEnd_1869555] using wordTrace_append hprefix tailTrace_1869555
  have hstable : (prefixWord ++ tailWord_1869555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869555).length < 2 ^ (prefixWord ++ tailWord_1869555).sum := by decide
  have hdescent : baseEnd_1869555 < baseStart_1869555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869558 : List Nat := [5, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_1869558 : Nat := 118140960795 + 1869558 * 2 ^ 59
def prefixEnd_1869558 : Nat := 4983230072969 + 3 ^ 40 * 1869558 * 2
def baseEnd_1869558 : Nat := 426658606870445146412029

theorem tailTrace_1869558 : CollatzResearch.WordTrace tailWord_1869558 prefixEnd_1869558 426658606870445146412029 := by
  unfold tailWord_1869558
  simp only [CollatzResearch.WordTrace]
  refine ⟨4261773885057383495695583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45458921440612090620752885 4261773885057383495695583)
  ·
    refine ⟨6392660827586075243543375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4261773885057383495695583 6392660827586075243543375)
    ·
      refine ⟨9588991241379112865315063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6392660827586075243543375 9588991241379112865315063)
      ·
        refine ⟨14383486862068669297972595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9588991241379112865315063 14383486862068669297972595)
        ·
          refine ⟨21575230293103003946958893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14383486862068669297972595 21575230293103003946958893)
          ·
            refine ⟨8090711359913626480109585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21575230293103003946958893 8090711359913626480109585)
            ·
              refine ⟨6068033519935219860082189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8090711359913626480109585 6068033519935219860082189)
              ·
                refine ⟨2275512569975707447530821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6068033519935219860082189 2275512569975707447530821)
                ·
                  refine ⟨426658606870445146412029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2275512569975707447530821 426658606870445146412029)
                  ·
                    rfl

theorem cell21_1869558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_1869558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869558 prefixEnd_1869558 := by exact prefixLift 1869558
  have htrace : WordTrace (prefixWord ++ tailWord_1869558) baseStart_1869558 baseEnd_1869558 := by
    simpa [prefixWord, tailWord_1869558, baseEnd_1869558] using wordTrace_append hprefix tailTrace_1869558
  have hstable : (prefixWord ++ tailWord_1869558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869558).length < 2 ^ (prefixWord ++ tailWord_1869558).sum := by decide
  have hdescent : baseEnd_1869558 < baseStart_1869558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869603 : List Nat := [1, 1, 1, 4, 2, 1, 4, 4, 3]
def baseStart_1869603 : Nat := 118140960795 + 1869603 * 2 ^ 59
def prefixEnd_1869603 : Nat := 4983230072969 + 3 ^ 40 * 1869603 * 2
def baseEnd_1869603 : Nat := 426668876483535068161937

theorem tailTrace_1869603 : CollatzResearch.WordTrace tailWord_1869603 prefixEnd_1869603 426668876483535068161937 := by
  unfold tailWord_1869603
  simp only [CollatzResearch.WordTrace]
  refine ⟨68190023445755108616517463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45460015630503405744344975 68190023445755108616517463)
  ·
    refine ⟨102285035168632662924776195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68190023445755108616517463 102285035168632662924776195)
    ·
      refine ⟨153427552752948994387164293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102285035168632662924776195 153427552752948994387164293)
      ·
        refine ⟨28767666141177936447593305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153427552752948994387164293 28767666141177936447593305)
        ·
          refine ⟨21575749605883452335694979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28767666141177936447593305 21575749605883452335694979)
          ·
            refine ⟨32363624408825178503542469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21575749605883452335694979 32363624408825178503542469)
            ·
              refine ⟨6068179576654720969414213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32363624408825178503542469 6068179576654720969414213)
              ·
                refine ⟨1137783670622760181765165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6068179576654720969414213 1137783670622760181765165)
                ·
                  refine ⟨426668876483535068161937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1137783670622760181765165 426668876483535068161937)
                  ·
                    rfl

theorem cell21_1869603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 3].length) (baseStart_1869603 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869603 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869603 prefixEnd_1869603 := by exact prefixLift 1869603
  have htrace : WordTrace (prefixWord ++ tailWord_1869603) baseStart_1869603 baseEnd_1869603 := by
    simpa [prefixWord, tailWord_1869603, baseEnd_1869603] using wordTrace_append hprefix tailTrace_1869603
  have hstable : (prefixWord ++ tailWord_1869603).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869603).length < 2 ^ (prefixWord ++ tailWord_1869603).sum := by decide
  have hdescent : baseEnd_1869603 < baseStart_1869603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869668 : List Nat := [2, 3, 1, 1, 6, 1, 2, 1, 4]
def baseStart_1869668 : Nat := 118140960795 + 1869668 * 2 ^ 59
def prefixEnd_1869668 : Nat := 4983230072969 + 3 ^ 40 * 1869668 * 2
def baseEnd_1869668 : Nat := 426683710369109399578471

theorem tailTrace_1869668 : CollatzResearch.WordTrace tailWord_1869668 prefixEnd_1869668 426683710369109399578471 := by
  unfold tailWord_1869668
  simp only [CollatzResearch.WordTrace]
  refine ⟨34096197095259812358816829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45461596127013083145089105 34096197095259812358816829)
  ·
    refine ⟨12786073910722429634556311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34096197095259812358816829 12786073910722429634556311)
    ·
      refine ⟨19179110866083644451834467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12786073910722429634556311 19179110866083644451834467)
      ·
        refine ⟨28768666299125466677751701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19179110866083644451834467 28768666299125466677751701)
        ·
          refine ⟨1348531232771506250519611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 28768666299125466677751701 1348531232771506250519611)
          ·
            refine ⟨2022796849157259375779417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1348531232771506250519611 2022796849157259375779417)
            ·
              refine ⟨1517097636867944531834563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2022796849157259375779417 1517097636867944531834563)
              ·
                refine ⟨2275646455301916797751845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1517097636867944531834563 2275646455301916797751845)
                ·
                  refine ⟨426683710369109399578471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2275646455301916797751845 426683710369109399578471)
                  ·
                    rfl

theorem cell21_1869668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_1869668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869668 prefixEnd_1869668 := by exact prefixLift 1869668
  have htrace : WordTrace (prefixWord ++ tailWord_1869668) baseStart_1869668 baseEnd_1869668 := by
    simpa [prefixWord, tailWord_1869668, baseEnd_1869668] using wordTrace_append hprefix tailTrace_1869668
  have hstable : (prefixWord ++ tailWord_1869668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869668).length < 2 ^ (prefixWord ++ tailWord_1869668).sum := by decide
  have hdescent : baseEnd_1869668 < baseStart_1869668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869724 : List Nat := [2, 2, 3, 3, 1, 1, 3, 6]
def baseStart_1869724 : Nat := 118140960795 + 1869724 * 2 ^ 59
def prefixEnd_1869724 : Nat := 4983230072969 + 3 ^ 40 * 1869724 * 2
def baseEnd_1869724 : Nat := 142232163444021915548341

theorem tailTrace_1869724 : CollatzResearch.WordTrace tailWord_1869724 prefixEnd_1869724 142232163444021915548341 := by
  unfold tailWord_1869724
  simp only [CollatzResearch.WordTrace]
  refine ⟨34097218339158373140836113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45462957785544497521114817 34097218339158373140836113)
  ·
    refine ⟨25572913754368779855627085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34097218339158373140836113 25572913754368779855627085)
    ·
      refine ⟨9589842657888292445860157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25572913754368779855627085 9589842657888292445860157)
      ·
        refine ⟨3596190996708109667197559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9589842657888292445860157 3596190996708109667197559)
        ·
          refine ⟨5394286495062164500796339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3596190996708109667197559 5394286495062164500796339)
          ·
            refine ⟨8091429742593246751194509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5394286495062164500796339 8091429742593246751194509)
            ·
              refine ⟨3034286153472467531697941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8091429742593246751194509 3034286153472467531697941)
              ·
                refine ⟨142232163444021915548341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3034286153472467531697941 142232163444021915548341)
                ·
                  rfl

theorem cell21_1869724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 3, 6].length) (baseStart_1869724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869724 prefixEnd_1869724 := by exact prefixLift 1869724
  have htrace : WordTrace (prefixWord ++ tailWord_1869724) baseStart_1869724 baseEnd_1869724 := by
    simpa [prefixWord, tailWord_1869724, baseEnd_1869724] using wordTrace_append hprefix tailTrace_1869724
  have hstable : (prefixWord ++ tailWord_1869724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869724).length < 2 ^ (prefixWord ++ tailWord_1869724).sum := by decide
  have hdescent : baseEnd_1869724 < baseStart_1869724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869752 : List Nat := [2, 1, 2, 1, 2, 3, 2, 2, 6]
def baseStart_1869752 : Nat := 118140960795 + 1869752 * 2 ^ 59
def prefixEnd_1869752 : Nat := 4983230072969 + 3 ^ 40 * 1869752 * 2
def baseEnd_1869752 : Nat := 426702880313543920178299

theorem tailTrace_1869752 : CollatzResearch.WordTrace tailWord_1869752 prefixEnd_1869752 426702880313543920178299 := by
  unfold tailWord_1869752
  simp only [CollatzResearch.WordTrace]
  refine ⟨34097728961107653531845755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45463638614810204709127673 34097728961107653531845755)
  ·
    refine ⟨51146593441661480297768633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34097728961107653531845755 51146593441661480297768633)
    ·
      refine ⟨38359945081246110223326475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51146593441661480297768633 38359945081246110223326475)
      ·
        refine ⟨57539917621869165334989713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38359945081246110223326475 57539917621869165334989713)
        ·
          refine ⟨43154938216401874001242285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57539917621869165334989713 43154938216401874001242285)
          ·
            refine ⟨16183101831150702750465857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43154938216401874001242285 16183101831150702750465857)
            ·
              refine ⟨12137326373363027062849393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16183101831150702750465857 12137326373363027062849393)
              ·
                refine ⟨9102994780022270297137045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12137326373363027062849393 9102994780022270297137045)
                ·
                  refine ⟨426702880313543920178299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9102994780022270297137045 426702880313543920178299)
                  ·
                    rfl

theorem cell21_1869752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 6].length) (baseStart_1869752 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869752 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869752 prefixEnd_1869752 := by exact prefixLift 1869752
  have htrace : WordTrace (prefixWord ++ tailWord_1869752) baseStart_1869752 baseEnd_1869752 := by
    simpa [prefixWord, tailWord_1869752, baseEnd_1869752] using wordTrace_append hprefix tailTrace_1869752
  have hstable : (prefixWord ++ tailWord_1869752).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869752).length < 2 ^ (prefixWord ++ tailWord_1869752).sum := by decide
  have hdescent : baseEnd_1869752 < baseStart_1869752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869831 : List Nat := [1, 1, 4, 3, 1, 4, 1, 1, 5]
def baseStart_1869831 : Nat := 118140960795 + 1869831 * 2 ^ 59
def prefixEnd_1869831 : Nat := 4983230072969 + 3 ^ 40 * 1869831 * 2
def baseEnd_1869831 : Nat := 426720909189857338361471

theorem tailTrace_1869831 : CollatzResearch.WordTrace tailWord_1869831 prefixEnd_1869831 426720909189857338361471 := by
  unfold tailWord_1869831
  simp only [CollatzResearch.WordTrace]
  refine ⟨68198339288929103555817347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45465559525952735703878231 68198339288929103555817347)
  ·
    refine ⟨102297508933393655333726021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68198339288929103555817347 102297508933393655333726021)
    ·
      refine ⟨19180782925011310375073629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102297508933393655333726021 19180782925011310375073629)
      ·
        refine ⟨7192793596879241390652611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19180782925011310375073629 7192793596879241390652611)
        ·
          refine ⟨10789190395318862085978917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7192793596879241390652611 10789190395318862085978917)
          ·
            refine ⟨2022973199122286641121047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10789190395318862085978917 2022973199122286641121047)
            ·
              refine ⟨3034459798683429961681571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2022973199122286641121047 3034459798683429961681571)
              ·
                refine ⟨4551689698025144942522357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3034459798683429961681571 4551689698025144942522357)
                ·
                  refine ⟨426720909189857338361471, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4551689698025144942522357 426720909189857338361471)
                  ·
                    rfl

theorem cell21_1869831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 4, 1, 1, 5].length) (baseStart_1869831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869831 prefixEnd_1869831 := by exact prefixLift 1869831
  have htrace : WordTrace (prefixWord ++ tailWord_1869831) baseStart_1869831 baseEnd_1869831 := by
    simpa [prefixWord, tailWord_1869831, baseEnd_1869831] using wordTrace_append hprefix tailTrace_1869831
  have hstable : (prefixWord ++ tailWord_1869831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869831).length < 2 ^ (prefixWord ++ tailWord_1869831).sum := by decide
  have hdescent : baseEnd_1869831 < baseStart_1869831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869876 : List Nat := [2, 5, 1, 2, 2, 9]
def baseStart_1869876 : Nat := 118140960795 + 1869876 * 2 ^ 59
def prefixEnd_1869876 : Nat := 4983230072969 + 3 ^ 40 * 1869876 * 2
def baseEnd_1869876 : Nat := 15804858474183231855977

theorem tailTrace_1869876 : CollatzResearch.WordTrace tailWord_1869876 prefixEnd_1869876 15804858474183231855977 := by
  unfold tailWord_1869876
  simp only [CollatzResearch.WordTrace]
  refine ⟨34099990286883038120602741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45466653715844050827470321 34099990286883038120602741)
  ·
    refine ⟨3196874089395284823806507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34099990286883038120602741 3196874089395284823806507)
    ·
      refine ⟨4795311134092927235709761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3196874089395284823806507 4795311134092927235709761)
      ·
        refine ⟨3596483350569695426782321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4795311134092927235709761 3596483350569695426782321)
        ·
          refine ⟨2697362512927271570086741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3596483350569695426782321 2697362512927271570086741)
          ·
            refine ⟨15804858474183231855977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2697362512927271570086741 15804858474183231855977)
            ·
              rfl

theorem cell21_1869876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 9].length) (baseStart_1869876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869876 prefixEnd_1869876 := by exact prefixLift 1869876
  have htrace : WordTrace (prefixWord ++ tailWord_1869876) baseStart_1869876 baseEnd_1869876 := by
    simpa [prefixWord, tailWord_1869876, baseEnd_1869876] using wordTrace_append hprefix tailTrace_1869876
  have hstable : (prefixWord ++ tailWord_1869876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869876).length < 2 ^ (prefixWord ++ tailWord_1869876).sum := by decide
  have hdescent : baseEnd_1869876 < baseStart_1869876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869910 : List Nat := [5, 2, 2, 1, 1, 2, 3, 5]
def baseStart_1869910 : Nat := 118140960795 + 1869910 * 2 ^ 59
def prefixEnd_1869910 : Nat := 4983230072969 + 3 ^ 40 * 1869910 * 2
def baseEnd_1869910 : Nat := 142246312688723585514881

theorem tailTrace_1869910 : CollatzResearch.WordTrace tailWord_1869910 prefixEnd_1869910 142246312688723585514881 := by
  unfold tailWord_1869910
  simp only [CollatzResearch.WordTrace]
  refine ⟨4262576290977681252996449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45467480437095266698628789 4262576290977681252996449)
  ·
    refine ⟨3196932218233260939747337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4262576290977681252996449 3196932218233260939747337)
    ·
      refine ⟨2397699163674945704810503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3196932218233260939747337 2397699163674945704810503)
      ·
        refine ⟨3596548745512418557215755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2397699163674945704810503 3596548745512418557215755)
        ·
          refine ⟨5394823118268627835823633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3596548745512418557215755 5394823118268627835823633)
          ·
            refine ⟨4046117338701470876867725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5394823118268627835823633 4046117338701470876867725)
            ·
              refine ⟨1517294002013051578825397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4046117338701470876867725 1517294002013051578825397)
              ·
                refine ⟨142246312688723585514881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1517294002013051578825397 142246312688723585514881)
                ·
                  rfl

theorem cell21_1869910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_1869910 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869910 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869910 prefixEnd_1869910 := by exact prefixLift 1869910
  have htrace : WordTrace (prefixWord ++ tailWord_1869910) baseStart_1869910 baseEnd_1869910 := by
    simpa [prefixWord, tailWord_1869910, baseEnd_1869910] using wordTrace_append hprefix tailTrace_1869910
  have hstable : (prefixWord ++ tailWord_1869910).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869910).length < 2 ^ (prefixWord ++ tailWord_1869910).sum := by decide
  have hdescent : baseEnd_1869910 < baseStart_1869910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869938 : List Nat := [3, 2, 1, 2, 2, 4, 1, 2, 4]
def baseStart_1869938 : Nat := 118140960795 + 1869938 * 2 ^ 59
def prefixEnd_1869938 : Nat := 4983230072969 + 3 ^ 40 * 1869938 * 2
def baseEnd_1869938 : Nat := 426745328047648930077919

theorem tailTrace_1869938 : CollatzResearch.WordTrace tailWord_1869938 prefixEnd_1869938 426745328047648930077919 := by
  unfold tailWord_1869938
  simp only [CollatzResearch.WordTrace]
  refine ⟨17050560474885365207490617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45468161266360973886641645 17050560474885365207490617)
  ·
    refine ⟨12787920356164023905617963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17050560474885365207490617 12787920356164023905617963)
    ·
      refine ⟨19181880534246035858426945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12787920356164023905617963 19181880534246035858426945)
      ·
        refine ⟨14386410400684526893820209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19181880534246035858426945 14386410400684526893820209)
        ·
          refine ⟨10789807800513395170365157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14386410400684526893820209 10789807800513395170365157)
          ·
            refine ⟨2023088962596261594443467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10789807800513395170365157 2023088962596261594443467)
            ·
              refine ⟨3034633443894392391665201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2023088962596261594443467 3034633443894392391665201)
              ·
                refine ⟨2275975082920794293748901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3034633443894392391665201 2275975082920794293748901)
                ·
                  refine ⟨426745328047648930077919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2275975082920794293748901 426745328047648930077919)
                  ·
                    rfl

theorem cell21_1869938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_1869938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869938 prefixEnd_1869938 := by exact prefixLift 1869938
  have htrace : WordTrace (prefixWord ++ tailWord_1869938) baseStart_1869938 baseEnd_1869938 := by
    simpa [prefixWord, tailWord_1869938, baseEnd_1869938] using wordTrace_append hprefix tailTrace_1869938
  have hstable : (prefixWord ++ tailWord_1869938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869938).length < 2 ^ (prefixWord ++ tailWord_1869938).sum := by decide
  have hdescent : baseEnd_1869938 < baseStart_1869938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869980 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 8]
def baseStart_1869980 : Nat := 118140960795 + 1869980 * 2 ^ 59
def prefixEnd_1869980 : Nat := 4983230072969 + 3 ^ 40 * 1869980 * 2
def baseEnd_1869980 : Nat := 426754913019866190377833

theorem tailTrace_1869980 : CollatzResearch.WordTrace tailWord_1869980 prefixEnd_1869980 426754913019866190377833 := by
  unfold tailWord_1869980
  simp only [CollatzResearch.WordTrace]
  refine ⟨34101886882694651001495697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45469182510259534668660929 34101886882694651001495697)
  ·
    refine ⟨25576415162020988251121773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34101886882694651001495697 25576415162020988251121773)
    ·
      refine ⟨9591155685757870594170665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25576415162020988251121773 9591155685757870594170665)
      ·
        refine ⟨7193366764318402945627999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9591155685757870594170665 7193366764318402945627999)
        ·
          refine ⟨10790050146477604418441999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7193366764318402945627999 10790050146477604418441999)
          ·
            refine ⟨16185075219716406627662999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10790050146477604418441999 16185075219716406627662999)
            ·
              refine ⟨24277612829574609941494499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16185075219716406627662999 24277612829574609941494499)
              ·
                refine ⟨36416419244361914912241749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 24277612829574609941494499 36416419244361914912241749)
                ·
                  refine ⟨426754913019866190377833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36416419244361914912241749 426754913019866190377833)
                  ·
                    rfl

theorem cell21_1869980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_1869980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869980 prefixEnd_1869980 := by exact prefixLift 1869980
  have htrace : WordTrace (prefixWord ++ tailWord_1869980) baseStart_1869980 baseEnd_1869980 := by
    simpa [prefixWord, tailWord_1869980, baseEnd_1869980] using wordTrace_append hprefix tailTrace_1869980
  have hstable : (prefixWord ++ tailWord_1869980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869980).length < 2 ^ (prefixWord ++ tailWord_1869980).sum := by decide
  have hdescent : baseEnd_1869980 < baseStart_1869980 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1869997 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 6]
def baseStart_1869997 : Nat := 118140960795 + 1869997 * 2 ^ 59
def prefixEnd_1869997 : Nat := 4983230072969 + 3 ^ 40 * 1869997 * 2
def baseEnd_1869997 : Nat := 426758792651477938594465

theorem tailTrace_1869997 : CollatzResearch.WordTrace tailWord_1869997 prefixEnd_1869997 426758792651477938594465 := by
  unfold tailWord_1869997
  simp only [CollatzResearch.WordTrace]
  refine ⟨68204393806327713906360245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45469595870885142604240163 68204393806327713906360245)
  ·
    refine ⟨6394161919343223178721273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68204393806327713906360245 6394161919343223178721273)
    ·
      refine ⟨4795621439507417384040955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6394161919343223178721273 4795621439507417384040955)
      ·
        refine ⟨7193432159261126076061433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4795621439507417384040955 7193432159261126076061433)
        ·
          refine ⟨5395074119445844557046075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7193432159261126076061433 5395074119445844557046075)
          ·
            refine ⟨8092611179168766835569113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5395074119445844557046075 8092611179168766835569113)
            ·
              refine ⟨6069458384376575126676835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8092611179168766835569113 6069458384376575126676835)
              ·
                refine ⟨9104187576564862690015253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6069458384376575126676835 9104187576564862690015253)
                ·
                  refine ⟨426758792651477938594465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9104187576564862690015253 426758792651477938594465)
                  ·
                    rfl

theorem cell21_1869997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 6].length) (baseStart_1869997 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1869997 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1869997 prefixEnd_1869997 := by exact prefixLift 1869997
  have htrace : WordTrace (prefixWord ++ tailWord_1869997) baseStart_1869997 baseEnd_1869997 := by
    simpa [prefixWord, tailWord_1869997, baseEnd_1869997] using wordTrace_append hprefix tailTrace_1869997
  have hstable : (prefixWord ++ tailWord_1869997).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1869997).length < 2 ^ (prefixWord ++ tailWord_1869997).sum := by decide
  have hdescent : baseEnd_1869997 < baseStart_1869997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1869997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870014 : List Nat := [4, 2, 1, 1, 4, 1, 1, 3, 4]
def baseStart_1870014 : Nat := 118140960795 + 1870014 * 2 ^ 59
def prefixEnd_1870014 : Nat := 4983230072969 + 3 ^ 40 * 1870014 * 2
def baseEnd_1870014 : Nat := 426762672283089686811097

theorem tailTrace_1870014 : CollatzResearch.WordTrace tailWord_1870014 prefixEnd_1870014 426762672283089686811097 := by
  unfold tailWord_1870014
  simp only [CollatzResearch.WordTrace]
  refine ⟨8525626730908265726216137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45470009231510750539819397 8525626730908265726216137)
  ·
    refine ⟨6394220048181199294662103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8525626730908265726216137 6394220048181199294662103)
    ·
      refine ⟨9591330072271798941993155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6394220048181199294662103 9591330072271798941993155)
      ·
        refine ⟨14386995108407698412989733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9591330072271798941993155 14386995108407698412989733)
        ·
          refine ⟨2697561582826443452435575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14386995108407698412989733 2697561582826443452435575)
          ·
            refine ⟨4046342374239665178653363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697561582826443452435575 4046342374239665178653363)
            ·
              refine ⟨6069513561359497767980045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4046342374239665178653363 6069513561359497767980045)
              ·
                refine ⟨2276067585509811662992517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6069513561359497767980045 2276067585509811662992517)
                ·
                  refine ⟨426762672283089686811097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2276067585509811662992517 426762672283089686811097)
                  ·
                    rfl

theorem cell21_1870014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 4].length) (baseStart_1870014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1870014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1870014 prefixEnd_1870014 := by exact prefixLift 1870014
  have htrace : WordTrace (prefixWord ++ tailWord_1870014) baseStart_1870014 baseEnd_1870014 := by
    simpa [prefixWord, tailWord_1870014, baseEnd_1870014] using wordTrace_append hprefix tailTrace_1870014
  have hstable : (prefixWord ++ tailWord_1870014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870014).length < 2 ^ (prefixWord ++ tailWord_1870014).sum := by decide
  have hdescent : baseEnd_1870014 < baseStart_1870014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870191 : List Nat := [1, 1, 2, 1, 3, 1, 2, 2, 8]
def baseStart_1870191 : Nat := 118140960795 + 1870191 * 2 ^ 59
def prefixEnd_1870191 : Nat := 4983230072969 + 3 ^ 40 * 1870191 * 2
def baseEnd_1870191 : Nat := 426803066094576712360735

theorem tailTrace_1870191 : CollatzResearch.WordTrace tailWord_1870191 prefixEnd_1870191 426803066094576712360735 := by
  unfold tailWord_1870191
  simp only [CollatzResearch.WordTrace]
  refine ⟨68211469567624885038922427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45474313045083256692614951 68211469567624885038922427)
  ·
    refine ⟨102317204351437327558383641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68211469567624885038922427 102317204351437327558383641)
    ·
      refine ⟨76737903263577995668787731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102317204351437327558383641 76737903263577995668787731)
      ·
        refine ⟨115106854895366993503181597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76737903263577995668787731 115106854895366993503181597)
        ·
          refine ⟨43165070585762622563693099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115106854895366993503181597 43165070585762622563693099)
          ·
            refine ⟨64747605878643933845539649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43165070585762622563693099 64747605878643933845539649)
            ·
              refine ⟨48560704408982950384154737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64747605878643933845539649 48560704408982950384154737)
              ·
                refine ⟨36420528306737212788116053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 48560704408982950384154737 36420528306737212788116053)
                ·
                  refine ⟨426803066094576712360735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 36420528306737212788116053 426803066094576712360735)
                  ·
                    rfl

theorem cell21_1870191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 2, 8].length) (baseStart_1870191 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1870191 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1870191 prefixEnd_1870191 := by exact prefixLift 1870191
  have htrace : WordTrace (prefixWord ++ tailWord_1870191) baseStart_1870191 baseEnd_1870191 := by
    simpa [prefixWord, tailWord_1870191, baseEnd_1870191] using wordTrace_append hprefix tailTrace_1870191
  have hstable : (prefixWord ++ tailWord_1870191).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870191).length < 2 ^ (prefixWord ++ tailWord_1870191).sum := by decide
  have hdescent : baseEnd_1870191 < baseStart_1870191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870228 : List Nat := [2, 4, 2, 1, 3, 1, 1, 4, 3]
def baseStart_1870228 : Nat := 118140960795 + 1870228 * 2 ^ 59
def prefixEnd_1870228 : Nat := 4983230072969 + 3 ^ 40 * 1870228 * 2
def baseEnd_1870228 : Nat := 426811509998672870243993

theorem tailTrace_1870228 : CollatzResearch.WordTrace tailWord_1870228 prefixEnd_1870228 426811509998672870243993 := by
  unfold tailWord_1870228
  simp only [CollatzResearch.WordTrace]
  refine ⟨34106409534245420179009669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45475212712327226905346225 34106409534245420179009669)
  ·
    refine ⟨6394951787671016283564313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34106409534245420179009669 6394951787671016283564313)
    ·
      refine ⟨4796213840753262212673235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6394951787671016283564313 4796213840753262212673235)
      ·
        refine ⟨7194320761129893319009853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4796213840753262212673235 7194320761129893319009853)
        ·
          refine ⟨2697870285423709994628695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7194320761129893319009853 2697870285423709994628695)
          ·
            refine ⟨4046805428135564991943043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697870285423709994628695 4046805428135564991943043)
            ·
              refine ⟨6070208142203347487914565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4046805428135564991943043 6070208142203347487914565)
              ·
                refine ⟨1138164026663127653983981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6070208142203347487914565 1138164026663127653983981)
                ·
                  refine ⟨426811509998672870243993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1138164026663127653983981 426811509998672870243993)
                  ·
                    rfl

theorem cell21_1870228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_1870228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1870228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1870228 prefixEnd_1870228 := by exact prefixLift 1870228
  have htrace : WordTrace (prefixWord ++ tailWord_1870228) baseStart_1870228 baseEnd_1870228 := by
    simpa [prefixWord, tailWord_1870228, baseEnd_1870228] using wordTrace_append hprefix tailTrace_1870228
  have hstable : (prefixWord ++ tailWord_1870228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870228).length < 2 ^ (prefixWord ++ tailWord_1870228).sum := by decide
  have hdescent : baseEnd_1870228 < baseStart_1870228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870273 : List Nat := [1, 2, 7, 1, 1, 1, 8]
def baseStart_1870273 : Nat := 118140960795 + 1870273 * 2 ^ 59
def prefixEnd_1870273 : Nat := 4983230072969 + 3 ^ 40 * 1870273 * 2
def baseEnd_1870273 : Nat := 47424642179084754665989

theorem tailTrace_1870273 : CollatzResearch.WordTrace tailWord_1870273 prefixEnd_1870273 47424642179084754665989 := by
  unfold tailWord_1870273
  simp only [CollatzResearch.WordTrace]
  refine ⟨68214460353327813043407473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45476306902218542028938315 68214460353327813043407473)
  ·
    refine ⟨51160845264995859782555605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68214460353327813043407473 51160845264995859782555605)
    ·
      refine ⟨1199082310898340463653647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 51160845264995859782555605 1199082310898340463653647)
      ·
        refine ⟨1798623466347510695480471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1199082310898340463653647 1798623466347510695480471)
        ·
          refine ⟨2697935199521266043220707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1798623466347510695480471 2697935199521266043220707)
          ·
            refine ⟨4046902799281899064831061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2697935199521266043220707 4046902799281899064831061)
            ·
              refine ⟨47424642179084754665989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4046902799281899064831061 47424642179084754665989)
              ·
                rfl

theorem cell21_1870273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 8].length) (baseStart_1870273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1870273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1870273 prefixEnd_1870273 := by exact prefixLift 1870273
  have htrace : WordTrace (prefixWord ++ tailWord_1870273) baseStart_1870273 baseEnd_1870273 := by
    simpa [prefixWord, tailWord_1870273, baseEnd_1870273] using wordTrace_append hprefix tailTrace_1870273
  have hstable : (prefixWord ++ tailWord_1870273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870273).length < 2 ^ (prefixWord ++ tailWord_1870273).sum := by decide
  have hdescent : baseEnd_1870273 < baseStart_1870273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870298 : List Nat := [3, 1, 1, 2, 3, 1, 2, 8]
def baseStart_1870298 : Nat := 118140960795 + 1870298 * 2 ^ 59
def prefixEnd_1870298 : Nat := 4983230072969 + 3 ^ 40 * 1870298 * 2
def baseEnd_1870298 : Nat := 142275828317456101359061

theorem tailTrace_1870298 : CollatzResearch.WordTrace tailWord_1870298 prefixEnd_1870298 142275828317456101359061 := by
  unfold tailWord_1870298
  simp only [CollatzResearch.WordTrace]
  refine ⟨17053843044559310578266887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45476914785491494875378365 17053843044559310578266887)
  ·
    refine ⟨25580764566838965867400331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17053843044559310578266887 25580764566838965867400331)
    ·
      refine ⟨38371146850258448801100497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25580764566838965867400331 38371146850258448801100497)
      ·
        refine ⟨28778360137693836600825373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38371146850258448801100497 28778360137693836600825373)
        ·
          refine ⟨10791885051635188725309515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28778360137693836600825373 10791885051635188725309515)
          ·
            refine ⟨16187827577452783087964273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10791885051635188725309515 16187827577452783087964273)
            ·
              refine ⟨12140870683089587315973205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16187827577452783087964273 12140870683089587315973205)
              ·
                refine ⟨142275828317456101359061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12140870683089587315973205 142275828317456101359061)
                ·
                  rfl

theorem cell21_1870298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 2, 8].length) (baseStart_1870298 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1870298 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1870298 prefixEnd_1870298 := by exact prefixLift 1870298
  have htrace : WordTrace (prefixWord ++ tailWord_1870298) baseStart_1870298 baseEnd_1870298 := by
    simpa [prefixWord, tailWord_1870298, baseEnd_1870298] using wordTrace_append hprefix tailTrace_1870298
  have hstable : (prefixWord ++ tailWord_1870298).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870298).length < 2 ^ (prefixWord ++ tailWord_1870298).sum := by decide
  have hdescent : baseEnd_1870298 < baseStart_1870298 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870349 : List Nat := [1, 7, 1, 1, 1, 2, 2, 6]
def baseStart_1870349 : Nat := 118140960795 + 1870349 * 2 ^ 59
def prefixEnd_1870349 : Nat := 4983230072969 + 3 ^ 40 * 1870349 * 2
def baseEnd_1870349 : Nat := 142279707949067849575693

theorem tailTrace_1870349 : CollatzResearch.WordTrace tailWord_1870349 prefixEnd_1870349 142279707949067849575693 := by
  unfold tailWord_1870349
  simp only [CollatzResearch.WordTrace]
  refine ⟨68217232301052478023174101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45478154867368318682116067 68217232301052478023174101)
  ·
    refine ⟨1598841382055917453668143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 68217232301052478023174101 1598841382055917453668143)
    ·
      refine ⟨2398262073083876180502215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1598841382055917453668143 2398262073083876180502215)
      ·
        refine ⟨3597393109625814270753323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2398262073083876180502215 3597393109625814270753323)
        ·
          refine ⟨5396089664438721406129985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3597393109625814270753323 5396089664438721406129985)
          ·
            refine ⟨4047067248329041054597489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5396089664438721406129985 4047067248329041054597489)
            ·
              refine ⟨3035300436246780790948117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4047067248329041054597489 3035300436246780790948117)
              ·
                refine ⟨142279707949067849575693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3035300436246780790948117 142279707949067849575693)
                ·
                  rfl

theorem cell21_1870349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 2, 6].length) (baseStart_1870349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1870349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1870349 prefixEnd_1870349 := by exact prefixLift 1870349
  have htrace : WordTrace (prefixWord ++ tailWord_1870349) baseStart_1870349 baseEnd_1870349 := by
    simpa [prefixWord, tailWord_1870349, baseEnd_1870349] using wordTrace_append hprefix tailTrace_1870349
  have hstable : (prefixWord ++ tailWord_1870349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870349).length < 2 ^ (prefixWord ++ tailWord_1870349).sum := by decide
  have hdescent : baseEnd_1870349 < baseStart_1870349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870453 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 6]
def baseStart_1870453 : Nat := 118140960795 + 1870453 * 2 ^ 59
def prefixEnd_1870453 : Nat := 4983230072969 + 3 ^ 40 * 1870453 * 2
def baseEnd_1870453 : Nat := 426862858064122478993533

theorem tailTrace_1870453 : CollatzResearch.WordTrace tailWord_1870453 prefixEnd_1870453 426862858064122478993533 := by
  unfold tailWord_1870453
  simp only [CollatzResearch.WordTrace]
  refine ⟨68221025492675703784960013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45480683661783802523306675 68221025492675703784960013)
  ·
    refine ⟨25582884559753388919360005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68221025492675703784960013 25582884559753388919360005)
    ·
      refine ⟨4796790854953760422380001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25582884559753388919360005 4796790854953760422380001)
      ·
        refine ⟨3597593141215320316785001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4796790854953760422380001 3597593141215320316785001)
        ·
          refine ⟨2698194855911490237588751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3597593141215320316785001 2698194855911490237588751)
          ·
            refine ⟨4047292283867235356383127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2698194855911490237588751 4047292283867235356383127)
            ·
              refine ⟨6070938425800853034574691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4047292283867235356383127 6070938425800853034574691)
              ·
                refine ⟨9106407638701279551862037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6070938425800853034574691 9106407638701279551862037)
                ·
                  refine ⟨426862858064122478993533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9106407638701279551862037 426862858064122478993533)
                  ·
                    rfl

theorem cell21_1870453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 6].length) (baseStart_1870453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1870453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1870453 prefixEnd_1870453 := by exact prefixLift 1870453
  have htrace : WordTrace (prefixWord ++ tailWord_1870453) baseStart_1870453 baseEnd_1870453 := by
    simpa [prefixWord, tailWord_1870453, baseEnd_1870453] using wordTrace_append hprefix tailTrace_1870453
  have hstable : (prefixWord ++ tailWord_1870453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870453).length < 2 ^ (prefixWord ++ tailWord_1870453).sum := by decide
  have hdescent : baseEnd_1870453 < baseStart_1870453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870484 : List Nat := [2, 4, 2, 2, 1, 1, 4, 5]
def baseStart_1870484 : Nat := 118140960795 + 1870484 * 2 ^ 59
def prefixEnd_1870484 : Nat := 4983230072969 + 3 ^ 40 * 1870484 * 2
def baseEnd_1870484 : Nat := 142289977562157771325601

theorem tailTrace_1870484 : CollatzResearch.WordTrace tailWord_1870484 prefixEnd_1870484 142289977562157771325601 := by
  unfold tailWord_1870484
  simp only [CollatzResearch.WordTrace]
  refine ⟨34111078077781698039669253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45481437437042264052892337 34111078077781698039669253)
  ·
    refine ⟨6395827139584068382437985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34111078077781698039669253 6395827139584068382437985)
    ·
      refine ⟨4796870354688051286828489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6395827139584068382437985 4796870354688051286828489)
      ·
        refine ⟨3597652766016038465121367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4796870354688051286828489 3597652766016038465121367)
        ·
          refine ⟨5396479149024057697682051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3597652766016038465121367 5396479149024057697682051)
          ·
            refine ⟨8094718723536086546523077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5396479149024057697682051 8094718723536086546523077)
            ·
              refine ⟨1517759760663016227473077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8094718723536086546523077 1517759760663016227473077)
              ·
                refine ⟨142289977562157771325601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1517759760663016227473077 142289977562157771325601)
                ·
                  rfl

theorem cell21_1870484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 4, 5].length) (baseStart_1870484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1870484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1870484 prefixEnd_1870484 := by exact prefixLift 1870484
  have htrace : WordTrace (prefixWord ++ tailWord_1870484) baseStart_1870484 baseEnd_1870484 := by
    simpa [prefixWord, tailWord_1870484, baseEnd_1870484] using wordTrace_append hprefix tailTrace_1870484
  have hstable : (prefixWord ++ tailWord_1870484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870484).length < 2 ^ (prefixWord ++ tailWord_1870484).sum := by decide
  have hdescent : baseEnd_1870484 < baseStart_1870484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870515 : List Nat := [1, 1, 1, 2, 3, 5, 3, 2, 3]
def baseStart_1870515 : Nat := 118140960795 + 1870515 * 2 ^ 59
def prefixEnd_1870515 : Nat := 4983230072969 + 3 ^ 40 * 1870515 * 2
def baseEnd_1870515 : Nat := 426877007308824148960073

theorem tailTrace_1870515 : CollatzResearch.WordTrace tailWord_1870515 prefixEnd_1870515 426877007308824148960073 := by
  unfold tailWord_1870515
  simp only [CollatzResearch.WordTrace]
  refine ⟨68223286818451088373716999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45482191212300725582477999 68223286818451088373716999)
  ·
    refine ⟨102334930227676632560575499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68223286818451088373716999 102334930227676632560575499)
    ·
      refine ⟨153502395341514948840863249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102334930227676632560575499 153502395341514948840863249)
      ·
        refine ⟨115126796506136211630647437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153502395341514948840863249 115126796506136211630647437)
        ·
          refine ⟨43172548689801079361492789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115126796506136211630647437 43172548689801079361492789)
          ·
            refine ⟨4047426439668851190139949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 43172548689801079361492789 4047426439668851190139949)
            ·
              refine ⟨1517784914875819196302481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4047426439668851190139949 1517784914875819196302481)
              ·
                refine ⟨1138338686156864397226861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1517784914875819196302481 1138338686156864397226861)
                ·
                  refine ⟨426877007308824148960073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1138338686156864397226861 426877007308824148960073)
                  ·
                    rfl

theorem cell21_1870515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 3].length) (baseStart_1870515 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1870515 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1870515 prefixEnd_1870515 := by exact prefixLift 1870515
  have htrace : WordTrace (prefixWord ++ tailWord_1870515) baseStart_1870515 baseEnd_1870515 := by
    simpa [prefixWord, tailWord_1870515, baseEnd_1870515] using wordTrace_append hprefix tailTrace_1870515
  have hstable : (prefixWord ++ tailWord_1870515).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870515).length < 2 ^ (prefixWord ++ tailWord_1870515).sum := by decide
  have hdescent : baseEnd_1870515 < baseStart_1870515 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870588 : List Nat := [2, 2, 2, 1, 3, 2, 2, 3, 4]
def baseStart_1870588 : Nat := 118140960795 + 1870588 * 2 ^ 59
def prefixEnd_1870588 : Nat := 4983230072969 + 3 ^ 40 * 1870588 * 2
def baseEnd_1870588 : Nat := 426893666903392244243257

theorem tailTrace_1870588 : CollatzResearch.WordTrace tailWord_1870588 prefixEnd_1870588 426893666903392244243257 := by
  unfold tailWord_1870588
  simp only [CollatzResearch.WordTrace]
  refine ⟨34112974673593310920562209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45483966231457747894082945 34112974673593310920562209)
  ·
    refine ⟨25584731005194983190421657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34112974673593310920562209 25584731005194983190421657)
    ·
      refine ⟨19188548253896237392816243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25584731005194983190421657 19188548253896237392816243)
      ·
        refine ⟨28782822380844356089224365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19188548253896237392816243 28782822380844356089224365)
        ·
          refine ⟨10793558392816633533459137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28782822380844356089224365 10793558392816633533459137)
          ·
            refine ⟨8095168794612475150094353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10793558392816633533459137 8095168794612475150094353)
            ·
              refine ⟨6071376595959356362570765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8095168794612475150094353 6071376595959356362570765)
              ·
                refine ⟨2276766223484758635964037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6071376595959356362570765 2276766223484758635964037)
                ·
                  refine ⟨426893666903392244243257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2276766223484758635964037 426893666903392244243257)
                  ·
                    rfl

theorem cell21_1870588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_1870588 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1870588 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1870588 prefixEnd_1870588 := by exact prefixLift 1870588
  have htrace : WordTrace (prefixWord ++ tailWord_1870588) baseStart_1870588 baseEnd_1870588 := by
    simpa [prefixWord, tailWord_1870588, baseEnd_1870588] using wordTrace_append hprefix tailTrace_1870588
  have hstable : (prefixWord ++ tailWord_1870588).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870588).length < 2 ^ (prefixWord ++ tailWord_1870588).sum := by decide
  have hdescent : baseEnd_1870588 < baseStart_1870588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870616 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 9]
def baseStart_1870616 : Nat := 118140960795 + 1870616 * 2 ^ 59
def prefixEnd_1870616 : Nat := 4983230072969 + 3 ^ 40 * 1870616 * 2
def baseEnd_1870616 : Nat := 426900056884870417776533

theorem tailTrace_1870616 : CollatzResearch.WordTrace tailWord_1870616 prefixEnd_1870616 426900056884870417776533 := by
  unfold tailWord_1870616
  simp only [CollatzResearch.WordTrace]
  refine ⟨34113485295542591311571851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45484647060723455082095801 34113485295542591311571851)
  ·
    refine ⟨51170227943313886967357777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34113485295542591311571851 51170227943313886967357777)
    ·
      refine ⟨38377670957485415225518333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51170227943313886967357777 38377670957485415225518333)
      ·
        refine ⟨14391626609057030709569375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38377670957485415225518333 14391626609057030709569375)
        ·
          refine ⟨21587439913585546064354063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14391626609057030709569375 21587439913585546064354063)
          ·
            refine ⟨32381159870378319096531095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21587439913585546064354063 32381159870378319096531095)
            ·
              refine ⟨48571739805567478644796643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32381159870378319096531095 48571739805567478644796643)
              ·
                refine ⟨72857609708351217967194965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48571739805567478644796643 72857609708351217967194965)
                ·
                  refine ⟨426900056884870417776533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72857609708351217967194965 426900056884870417776533)
                  ·
                    rfl

theorem cell21_1870616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 9].length) (baseStart_1870616 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1870616 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1870616 prefixEnd_1870616 := by exact prefixLift 1870616
  have htrace : WordTrace (prefixWord ++ tailWord_1870616) baseStart_1870616 baseEnd_1870616 := by
    simpa [prefixWord, tailWord_1870616, baseEnd_1870616] using wordTrace_append hprefix tailTrace_1870616
  have hstable : (prefixWord ++ tailWord_1870616).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870616).length < 2 ^ (prefixWord ++ tailWord_1870616).sum := by decide
  have hdescent : baseEnd_1870616 < baseStart_1870616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870653 : List Nat := [1, 4, 1, 4, 3, 1, 2, 5]
def baseStart_1870653 : Nat := 118140960795 + 1870653 * 2 ^ 59
def prefixEnd_1870653 : Nat := 4983230072969 + 3 ^ 40 * 1870653 * 2
def baseEnd_1870653 : Nat := 142302833596322191886597

theorem tailTrace_1870653 : CollatzResearch.WordTrace tailWord_1870653 prefixEnd_1870653 142302833596322191886597 := by
  unfold tailWord_1870653
  simp only [CollatzResearch.WordTrace]
  refine ⟨68228320091951137942240613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45485546727967425294827075 68228320091951137942240613)
  ·
    refine ⟨12792810017240838364170115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68228320091951137942240613 12792810017240838364170115)
    ·
      refine ⟨19189215025861257546255173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12792810017240838364170115 19189215025861257546255173)
      ·
        refine ⟨3597977817348985789922845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19189215025861257546255173 3597977817348985789922845)
        ·
          refine ⟨1349241681505869671221067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3597977817348985789922845 1349241681505869671221067)
          ·
            refine ⟨2023862522258804506831601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1349241681505869671221067 2023862522258804506831601)
            ·
              refine ⟨1517896891694103380123701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2023862522258804506831601 1517896891694103380123701)
              ·
                refine ⟨142302833596322191886597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1517896891694103380123701 142302833596322191886597)
                ·
                  rfl

theorem cell21_1870653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 3, 1, 2, 5].length) (baseStart_1870653 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1870653 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1870653 prefixEnd_1870653 := by exact prefixLift 1870653
  have htrace : WordTrace (prefixWord ++ tailWord_1870653) baseStart_1870653 baseEnd_1870653 := by
    simpa [prefixWord, tailWord_1870653, baseEnd_1870653] using wordTrace_append hprefix tailTrace_1870653
  have hstable : (prefixWord ++ tailWord_1870653).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870653).length < 2 ^ (prefixWord ++ tailWord_1870653).sum := by decide
  have hdescent : baseEnd_1870653 < baseStart_1870653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870684 : List Nat := [2, 2, 4, 2, 1, 2, 3, 2, 3]
def baseStart_1870684 : Nat := 118140960795 + 1870684 * 2 ^ 59
def prefixEnd_1870684 : Nat := 4983230072969 + 3 ^ 40 * 1870684 * 2
def baseEnd_1870684 : Nat := 426915575411317410643061

theorem tailTrace_1870684 : CollatzResearch.WordTrace tailWord_1870684 prefixEnd_1870684 426915575411317410643061 := by
  unfold tailWord_1870684
  simp only [CollatzResearch.WordTrace]
  refine ⟨34114725377419415118309553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45486300503225886824412737 34114725377419415118309553)
  ·
    refine ⟨25586044033064561338732165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34114725377419415118309553 25586044033064561338732165)
    ·
      refine ⟨4797383256199605251012281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25586044033064561338732165 4797383256199605251012281)
      ·
        refine ⟨3598037442149703938259211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4797383256199605251012281 3598037442149703938259211)
        ·
          refine ⟨5397056163224555907388817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3598037442149703938259211 5397056163224555907388817)
          ·
            refine ⟨4047792122418416930541613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5397056163224555907388817 4047792122418416930541613)
            ·
              refine ⟨1517922045906906348953105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4047792122418416930541613 1517922045906906348953105)
              ·
                refine ⟨1138441534430179761714829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1517922045906906348953105 1138441534430179761714829)
                ·
                  refine ⟨426915575411317410643061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1138441534430179761714829 426915575411317410643061)
                  ·
                    rfl

theorem cell21_1870684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 2, 3].length) (baseStart_1870684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1870684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1870684 prefixEnd_1870684 := by exact prefixLift 1870684
  have htrace : WordTrace (prefixWord ++ tailWord_1870684) baseStart_1870684 baseEnd_1870684 := by
    simpa [prefixWord, tailWord_1870684, baseEnd_1870684] using wordTrace_append hprefix tailTrace_1870684
  have hstable : (prefixWord ++ tailWord_1870684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870684).length < 2 ^ (prefixWord ++ tailWord_1870684).sum := by decide
  have hdescent : baseEnd_1870684 < baseStart_1870684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870799 : List Nat := [1, 1, 2, 1, 1, 7, 1, 1, 6]
def baseStart_1870799 : Nat := 118140960795 + 1870799 * 2 ^ 59
def prefixEnd_1870799 : Nat := 4983230072969 + 3 ^ 40 * 1870799 * 2
def baseEnd_1870799 : Nat := 426941819978102766226159

theorem tailTrace_1870799 : CollatzResearch.WordTrace tailWord_1870799 prefixEnd_1870799 426941819978102766226159 := by
  unfold tailWord_1870799
  simp only [CollatzResearch.WordTrace]
  refine ⟨68233645149422204877055451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45489096766281469918036967 68233645149422204877055451)
  ·
    refine ⟨102350467724133307315583177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68233645149422204877055451 102350467724133307315583177)
    ·
      refine ⟨76762850793099980486687383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102350467724133307315583177 76762850793099980486687383)
      ·
        refine ⟨115144276189649970730031075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76762850793099980486687383 115144276189649970730031075)
        ·
          refine ⟨172716414284474956095046613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115144276189649970730031075 172716414284474956095046613)
          ·
            refine ⟨4048040959792381783477655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 172716414284474956095046613 4048040959792381783477655)
            ·
              refine ⟨6072061439688572675216483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4048040959792381783477655 6072061439688572675216483)
              ·
                refine ⟨9108092159532859012824725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6072061439688572675216483 9108092159532859012824725)
                ·
                  refine ⟨426941819978102766226159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9108092159532859012824725 426941819978102766226159)
                  ·
                    rfl

theorem cell21_1870799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 6].length) (baseStart_1870799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1870799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1870799 prefixEnd_1870799 := by exact prefixLift 1870799
  have htrace : WordTrace (prefixWord ++ tailWord_1870799) baseStart_1870799 baseEnd_1870799 := by
    simpa [prefixWord, tailWord_1870799, baseEnd_1870799] using wordTrace_append hprefix tailTrace_1870799
  have hstable : (prefixWord ++ tailWord_1870799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870799).length < 2 ^ (prefixWord ++ tailWord_1870799).sum := by decide
  have hdescent : baseEnd_1870799 < baseStart_1870799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870802 : List Nat := [3, 2, 2, 3, 1, 2, 2, 1, 5]
def baseStart_1870802 : Nat := 118140960795 + 1870802 * 2 ^ 59
def prefixEnd_1870802 : Nat := 4983230072969 + 3 ^ 40 * 1870802 * 2
def baseEnd_1870802 : Nat := 426942504618975427676153

theorem tailTrace_1870802 : CollatzResearch.WordTrace tailWord_1870802 prefixEnd_1870802 426942504618975427676153 := by
  unfold tailWord_1870802
  simp only [CollatzResearch.WordTrace]
  refine ⟨17058438642102834097353665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45489169712274224259609773 17058438642102834097353665)
  ·
    refine ⟨12793828981577125573015249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17058438642102834097353665 12793828981577125573015249)
    ·
      refine ⟨9595371736182844179761437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12793828981577125573015249 9595371736182844179761437)
      ·
        refine ⟨3598264401068566567410539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9595371736182844179761437 3598264401068566567410539)
        ·
          refine ⟨5397396601602849851115809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3598264401068566567410539 5397396601602849851115809)
          ·
            refine ⟨4048047451202137388336857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5397396601602849851115809 4048047451202137388336857)
            ·
              refine ⟨3036035588401603041252643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4048047451202137388336857 3036035588401603041252643)
              ·
                refine ⟨4554053382602404561878965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3036035588401603041252643 4554053382602404561878965)
                ·
                  refine ⟨426942504618975427676153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4554053382602404561878965 426942504618975427676153)
                  ·
                    rfl

theorem cell21_1870802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_1870802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1870802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1870802 prefixEnd_1870802 := by exact prefixLift 1870802
  have htrace : WordTrace (prefixWord ++ tailWord_1870802) baseStart_1870802 baseEnd_1870802 := by
    simpa [prefixWord, tailWord_1870802, baseEnd_1870802] using wordTrace_append hprefix tailTrace_1870802
  have hstable : (prefixWord ++ tailWord_1870802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870802).length < 2 ^ (prefixWord ++ tailWord_1870802).sum := by decide
  have hdescent : baseEnd_1870802 < baseStart_1870802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870920 : List Nat := [2, 1, 3, 1, 1, 1, 4, 3, 5]
def baseStart_1870920 : Nat := 118140960795 + 1870920 * 2 ^ 59
def prefixEnd_1870920 : Nat := 4983230072969 + 3 ^ 40 * 1870920 * 2
def baseEnd_1870920 : Nat := 426969433826633444709245

theorem tailTrace_1870920 : CollatzResearch.WordTrace tailWord_1870920 prefixEnd_1870920 426969433826633444709245 := by
  unfold tailWord_1870920
  simp only [CollatzResearch.WordTrace]
  refine ⟨34119029190991921271105107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45492038921322561694806809 34119029190991921271105107)
  ·
    refine ⟨51178543786487881906657661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34119029190991921271105107 51178543786487881906657661)
    ·
      refine ⟨19191953919932955714996623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51178543786487881906657661 19191953919932955714996623)
      ·
        refine ⟨28787930879899433572494935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19191953919932955714996623 28787930879899433572494935)
        ·
          refine ⟨43181896319849150358742403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28787930879899433572494935 43181896319849150358742403)
          ·
            refine ⟨64772844479773725538113605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43181896319849150358742403 64772844479773725538113605)
            ·
              refine ⟨12144908339957573538396301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 64772844479773725538113605 12144908339957573538396301)
              ·
                refine ⟨4554340627484090076898613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12144908339957573538396301 4554340627484090076898613)
                ·
                  refine ⟨426969433826633444709245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4554340627484090076898613 426969433826633444709245)
                  ·
                    rfl

theorem cell21_1870920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 5].length) (baseStart_1870920 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1870920 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1870920 prefixEnd_1870920 := by exact prefixLift 1870920
  have htrace : WordTrace (prefixWord ++ tailWord_1870920) baseStart_1870920 baseEnd_1870920 := by
    simpa [prefixWord, tailWord_1870920, baseEnd_1870920] using wordTrace_append hprefix tailTrace_1870920
  have hstable : (prefixWord ++ tailWord_1870920).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870920).length < 2 ^ (prefixWord ++ tailWord_1870920).sum := by decide
  have hdescent : baseEnd_1870920 < baseStart_1870920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870954 : List Nat := [3, 1, 3, 2, 2, 1, 1, 5, 3]
def baseStart_1870954 : Nat := 118140960795 + 1870954 * 2 ^ 59
def prefixEnd_1870954 : Nat := 4983230072969 + 3 ^ 40 * 1870954 * 2
def baseEnd_1870954 : Nat := 426977193089856941142509

theorem tailTrace_1870954 : CollatzResearch.WordTrace tailWord_1870954 prefixEnd_1870954 426977193089856941142509 := by
  unfold tailWord_1870954
  simp only [CollatzResearch.WordTrace]
  refine ⟨17059824615965166587236979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45492865642573777565965277 17059824615965166587236979)
  ·
    refine ⟨25589736923947749880855469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17059824615965166587236979 25589736923947749880855469)
    ·
      refine ⟨9596151346480406205320801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25589736923947749880855469 9596151346480406205320801)
      ·
        refine ⟨7197113509860304653990601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9596151346480406205320801 7197113509860304653990601)
        ·
          refine ⟨5397835132395228490492951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7197113509860304653990601 5397835132395228490492951)
          ·
            refine ⟨8096752698592842735739427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5397835132395228490492951 8096752698592842735739427)
            ·
              refine ⟨12145129047889264103609141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8096752698592842735739427 12145129047889264103609141)
              ·
                refine ⟨1138605848239618509713357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12145129047889264103609141 1138605848239618509713357)
                ·
                  refine ⟨426977193089856941142509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1138605848239618509713357 426977193089856941142509)
                  ·
                    rfl

theorem cell21_1870954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 5, 3].length) (baseStart_1870954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1870954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1870954 prefixEnd_1870954 := by exact prefixLift 1870954
  have htrace : WordTrace (prefixWord ++ tailWord_1870954) baseStart_1870954 baseEnd_1870954 := by
    simpa [prefixWord, tailWord_1870954, baseEnd_1870954] using wordTrace_append hprefix tailTrace_1870954
  have hstable : (prefixWord ++ tailWord_1870954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870954).length < 2 ^ (prefixWord ++ tailWord_1870954).sum := by decide
  have hdescent : baseEnd_1870954 < baseStart_1870954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1870999 : List Nat := [1, 1, 3, 3, 3, 3, 2, 5]
def baseStart_1870999 : Nat := 118140960795 + 1870999 * 2 ^ 59
def prefixEnd_1870999 : Nat := 4983230072969 + 3 ^ 40 * 1870999 * 2
def baseEnd_1870999 : Nat := 142329154234315620964139

theorem tailTrace_1870999 : CollatzResearch.WordTrace tailWord_1870999 prefixEnd_1870999 142329154234315620964139 := by
  unfold tailWord_1870999
  simp only [CollatzResearch.WordTrace]
  refine ⟨68240939748697639034336051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45493959832465092689557367 68240939748697639034336051)
  ·
    refine ⟨102361409623046458551504077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68240939748697639034336051 102361409623046458551504077)
    ·
      refine ⟨38385528608642421956814029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102361409623046458551504077 38385528608642421956814029)
      ·
        refine ⟨14394573228240908233805261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38385528608642421956814029 14394573228240908233805261)
        ·
          refine ⟨5397964960590340587676973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14394573228240908233805261 5397964960590340587676973)
          ·
            refine ⟨2024236860221377720378865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5397964960590340587676973 2024236860221377720378865)
            ·
              refine ⟨1518177645166033290284149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2024236860221377720378865 1518177645166033290284149)
              ·
                refine ⟨142329154234315620964139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1518177645166033290284149 142329154234315620964139)
                ·
                  rfl

theorem cell21_1870999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2, 5].length) (baseStart_1870999 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1870999 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1870999 prefixEnd_1870999 := by exact prefixLift 1870999
  have htrace : WordTrace (prefixWord ++ tailWord_1870999) baseStart_1870999 baseEnd_1870999 := by
    simpa [prefixWord, tailWord_1870999, baseEnd_1870999] using wordTrace_append hprefix tailTrace_1870999
  have hstable : (prefixWord ++ tailWord_1870999).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1870999).length < 2 ^ (prefixWord ++ tailWord_1870999).sum := by decide
  have hdescent : baseEnd_1870999 < baseStart_1870999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1870999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871103 : List Nat := [1, 1, 2, 2, 1, 5, 2, 3, 4]
def baseStart_1871103 : Nat := 118140960795 + 1871103 * 2 ^ 59
def prefixEnd_1871103 : Nat := 4983230072969 + 3 ^ 40 * 1871103 * 2
def baseEnd_1871103 : Nat := 427011196919865793158871

theorem tailTrace_1871103 : CollatzResearch.WordTrace tailWord_1871103 prefixEnd_1871103 427011196919865793158871 := by
  unfold tailWord_1871103
  simp only [CollatzResearch.WordTrace]
  refine ⟨68244732940320864796121963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45496488626880576530747975 68244732940320864796121963)
  ·
    refine ⟨102367099410481297194182945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68244732940320864796121963 102367099410481297194182945)
    ·
      refine ⟨76775324557860972895637209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102367099410481297194182945 76775324557860972895637209)
      ·
        refine ⟨57581493418395729671727907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76775324557860972895637209 57581493418395729671727907)
        ·
          refine ⟨86372240127593594507591861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57581493418395729671727907 86372240127593594507591861)
          ·
            refine ⟨8097397511961899485086737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 86372240127593594507591861 8097397511961899485086737)
            ·
              refine ⟨6073048133971424613815053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8097397511961899485086737 6073048133971424613815053)
              ·
                refine ⟨2277393050239284230180645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6073048133971424613815053 2277393050239284230180645)
                ·
                  refine ⟨427011196919865793158871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2277393050239284230180645 427011196919865793158871)
                  ·
                    rfl

theorem cell21_1871103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 2, 3, 4].length) (baseStart_1871103 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1871103 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1871103 prefixEnd_1871103 := by exact prefixLift 1871103
  have htrace : WordTrace (prefixWord ++ tailWord_1871103) baseStart_1871103 baseEnd_1871103 := by
    simpa [prefixWord, tailWord_1871103, baseEnd_1871103] using wordTrace_append hprefix tailTrace_1871103
  have hstable : (prefixWord ++ tailWord_1871103).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871103).length < 2 ^ (prefixWord ++ tailWord_1871103).sum := by decide
  have hdescent : baseEnd_1871103 < baseStart_1871103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871106 : List Nat := [3, 4, 1, 1, 3, 1, 1, 2, 5]
def baseStart_1871106 : Nat := 118140960795 + 1871106 * 2 ^ 59
def prefixEnd_1871106 : Nat := 4983230072969 + 3 ^ 40 * 1871106 * 2
def baseEnd_1871106 : Nat := 427011881560738454608865

theorem tailTrace_1871106 : CollatzResearch.WordTrace tailWord_1871106 prefixEnd_1871106 427011881560738454608865 := by
  unfold tailWord_1871106
  simp only [CollatzResearch.WordTrace]
  refine ⟨17061210589827499077120293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45496561572873330872320781 17061210589827499077120293)
  ·
    refine ⟨3198976985592656076960055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17061210589827499077120293 3198976985592656076960055)
    ·
      refine ⟨4798465478388984115440083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3198976985592656076960055 4798465478388984115440083)
      ·
        refine ⟨7197698217583476173160125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4798465478388984115440083 7197698217583476173160125)
        ·
          refine ⟨2699136831593803564935047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7197698217583476173160125 2699136831593803564935047)
          ·
            refine ⟨4048705247390705347402571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2699136831593803564935047 4048705247390705347402571)
            ·
              refine ⟨6073057871086058021103857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4048705247390705347402571 6073057871086058021103857)
              ·
                refine ⟨4554793403314543515827893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6073057871086058021103857 4554793403314543515827893)
                ·
                  refine ⟨427011881560738454608865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4554793403314543515827893 427011881560738454608865)
                  ·
                    rfl

theorem cell21_1871106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_1871106 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1871106 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1871106 prefixEnd_1871106 := by exact prefixLift 1871106
  have htrace : WordTrace (prefixWord ++ tailWord_1871106) baseStart_1871106 baseEnd_1871106 := by
    simpa [prefixWord, tailWord_1871106, baseEnd_1871106] using wordTrace_append hprefix tailTrace_1871106
  have hstable : (prefixWord ++ tailWord_1871106).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871106).length < 2 ^ (prefixWord ++ tailWord_1871106).sum := by decide
  have hdescent : baseEnd_1871106 < baseStart_1871106 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871131 : List Nat := [1, 1, 1, 1, 1, 1, 5, 1, 9]
def baseStart_1871131 : Nat := 118140960795 + 1871131 * 2 ^ 59
def prefixEnd_1871131 : Nat := 4983230072969 + 3 ^ 40 * 1871131 * 2
def baseEnd_1871131 : Nat := 427017586901343966692147

theorem tailTrace_1871131 : CollatzResearch.WordTrace tailWord_1871131 prefixEnd_1871131 427017586901343966692147 := by
  unfold tailWord_1871131
  simp only [CollatzResearch.WordTrace]
  refine ⟨68245754184219425578141247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45497169456146283718760831 68245754184219425578141247)
  ·
    refine ⟨102368631276329138367211871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68245754184219425578141247 102368631276329138367211871)
    ·
      refine ⟨153552946914493707550817807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102368631276329138367211871 153552946914493707550817807)
      ·
        refine ⟨230329420371740561326226711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153552946914493707550817807 230329420371740561326226711)
        ·
          refine ⟨345494130557610841989340067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 230329420371740561326226711 345494130557610841989340067)
          ·
            refine ⟨518241195836416262984010101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 345494130557610841989340067 518241195836416262984010101)
            ·
              refine ⟨48585112109664024654750947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 518241195836416262984010101 48585112109664024654750947)
              ·
                refine ⟨72877668164496036982126421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48585112109664024654750947 72877668164496036982126421)
                ·
                  refine ⟨427017586901343966692147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 72877668164496036982126421 427017586901343966692147)
                  ·
                    rfl

theorem cell21_1871131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 1, 9].length) (baseStart_1871131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1871131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1871131 prefixEnd_1871131 := by exact prefixLift 1871131
  have htrace : WordTrace (prefixWord ++ tailWord_1871131) baseStart_1871131 baseEnd_1871131 := by
    simpa [prefixWord, tailWord_1871131, baseEnd_1871131] using wordTrace_append hprefix tailTrace_1871131
  have hstable : (prefixWord ++ tailWord_1871131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871131).length < 2 ^ (prefixWord ++ tailWord_1871131).sum := by decide
  have hdescent : baseEnd_1871131 < baseStart_1871131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871174 : List Nat := [6, 1, 1, 3, 2, 1, 1, 3, 3]
def baseStart_1871174 : Nat := 118140960795 + 1871174 * 2 ^ 59
def prefixEnd_1871174 : Nat := 4983230072969 + 3 ^ 40 * 1871174 * 2
def baseEnd_1871174 : Nat := 427027400087185447475393

theorem tailTrace_1871174 : CollatzResearch.WordTrace tailWord_1871174 prefixEnd_1871174 427027400087185447475393 := by
  unfold tailWord_1871174
  simp only [CollatzResearch.WordTrace]
  refine ⟨2132728828845738872561143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45498215015375762614637717 2132728828845738872561143)
  ·
    refine ⟨3199093243268608308841715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2132728828845738872561143 3199093243268608308841715)
    ·
      refine ⟨4798639864902912463262573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3199093243268608308841715 4798639864902912463262573)
      ·
        refine ⟨1799489949338592173723465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4798639864902912463262573 1799489949338592173723465)
        ·
          refine ⟨1349617462003944130292599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1799489949338592173723465 1349617462003944130292599)
          ·
            refine ⟨2024426193005916195438899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1349617462003944130292599 2024426193005916195438899)
            ·
              refine ⟨3036639289508874293158349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2024426193005916195438899 3036639289508874293158349)
              ·
                refine ⟨1138739733565827859934381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3036639289508874293158349 1138739733565827859934381)
                ·
                  refine ⟨427027400087185447475393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1138739733565827859934381 427027400087185447475393)
                  ·
                    rfl

theorem cell21_1871174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_1871174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1871174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1871174 prefixEnd_1871174 := by exact prefixLift 1871174
  have htrace : WordTrace (prefixWord ++ tailWord_1871174) baseStart_1871174 baseEnd_1871174 := by
    simpa [prefixWord, tailWord_1871174, baseEnd_1871174] using wordTrace_append hprefix tailTrace_1871174
  have hstable : (prefixWord ++ tailWord_1871174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871174).length < 2 ^ (prefixWord ++ tailWord_1871174).sum := by decide
  have hdescent : baseEnd_1871174 < baseStart_1871174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871213 : List Nat := [1, 5, 1, 1, 1, 5, 2, 1, 4]
def baseStart_1871213 : Nat := 118140960795 + 1871213 * 2 ^ 59
def prefixEnd_1871213 : Nat := 4983230072969 + 3 ^ 40 * 1871213 * 2
def baseEnd_1871213 : Nat := 427036300418530046325313

theorem tailTrace_1871213 : CollatzResearch.WordTrace tailWord_1871213 prefixEnd_1871213 427036300418530046325313 := by
  unfold tailWord_1871213
  simp only [CollatzResearch.WordTrace]
  refine ⟨68248744969922353582626293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45499163313281569055084195 68248744969922353582626293)
  ·
    refine ⟨6398319840930220648371215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68248744969922353582626293 6398319840930220648371215)
    ·
      refine ⟨9597479761395330972556823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6398319840930220648371215 9597479761395330972556823)
      ·
        refine ⟨14396219642092996458835235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9597479761395330972556823 14396219642092996458835235)
        ·
          refine ⟨21594329463139494688252853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14396219642092996458835235 21594329463139494688252853)
          ·
            refine ⟨2024468387169327627023705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21594329463139494688252853 2024468387169327627023705)
            ·
              refine ⟨1518351290376995720267779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2024468387169327627023705 1518351290376995720267779)
              ·
                refine ⟨2277526935565493580401669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1518351290376995720267779 2277526935565493580401669)
                ·
                  refine ⟨427036300418530046325313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2277526935565493580401669 427036300418530046325313)
                  ·
                    rfl

theorem cell21_1871213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 4].length) (baseStart_1871213 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1871213 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1871213 prefixEnd_1871213 := by exact prefixLift 1871213
  have htrace : WordTrace (prefixWord ++ tailWord_1871213) baseStart_1871213 baseEnd_1871213 := by
    simpa [prefixWord, tailWord_1871213, baseEnd_1871213] using wordTrace_append hprefix tailTrace_1871213
  have hstable : (prefixWord ++ tailWord_1871213).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871213).length < 2 ^ (prefixWord ++ tailWord_1871213).sum := by decide
  have hdescent : baseEnd_1871213 < baseStart_1871213 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871317 : List Nat := [1, 3, 2, 3, 1, 1, 1, 6, 3]
def baseStart_1871317 : Nat := 118140960795 + 1871317 * 2 ^ 59
def prefixEnd_1871317 : Nat := 4983230072969 + 3 ^ 40 * 1871317 * 2
def baseEnd_1871317 : Nat := 427060034635448976591767

theorem tailTrace_1871317 : CollatzResearch.WordTrace tailWord_1871317 prefixEnd_1871317 427060034635448976591767 := by
  unfold tailWord_1871317
  simp only [CollatzResearch.WordTrace]
  refine ⟨68252538161545579344412205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45501692107697052896274803 68252538161545579344412205)
  ·
    refine ⟨25594701810579592254154577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68252538161545579344412205 25594701810579592254154577)
    ·
      refine ⟨19196026357934694190615933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25594701810579592254154577 19196026357934694190615933)
      ·
        refine ⟨7198509884225510321480975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19196026357934694190615933 7198509884225510321480975)
        ·
          refine ⟨10797764826338265482221463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7198509884225510321480975 10797764826338265482221463)
          ·
            refine ⟨16196647239507398223332195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10797764826338265482221463 16196647239507398223332195)
            ·
              refine ⟨24294970859261097334998293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16196647239507398223332195 24294970859261097334998293)
              ·
                refine ⟨1138826759027863937578045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24294970859261097334998293 1138826759027863937578045)
                ·
                  refine ⟨427060034635448976591767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1138826759027863937578045 427060034635448976591767)
                  ·
                    rfl

theorem cell21_1871317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 6, 3].length) (baseStart_1871317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1871317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1871317 prefixEnd_1871317 := by exact prefixLift 1871317
  have htrace : WordTrace (prefixWord ++ tailWord_1871317) baseStart_1871317 baseEnd_1871317 := by
    simpa [prefixWord, tailWord_1871317, baseEnd_1871317] using wordTrace_append hprefix tailTrace_1871317
  have hstable : (prefixWord ++ tailWord_1871317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871317).length < 2 ^ (prefixWord ++ tailWord_1871317).sum := by decide
  have hdescent : baseEnd_1871317 < baseStart_1871317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871345 : List Nat := [1, 2, 2, 2, 3, 3, 1, 7]
def baseStart_1871345 : Nat := 118140960795 + 1871345 * 2 ^ 59
def prefixEnd_1871345 : Nat := 4983230072969 + 3 ^ 40 * 1871345 * 2
def baseEnd_1871345 : Nat := 142355474872309050041681

theorem tailTrace_1871345 : CollatzResearch.WordTrace tailWord_1871345 prefixEnd_1871345 142355474872309050041681 := by
  unfold tailWord_1871345
  simp only [CollatzResearch.WordTrace]
  refine ⟨68253559405444140126431489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45502372936962760084287659 68253559405444140126431489)
  ·
    refine ⟨51190169554083105094823617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68253559405444140126431489 51190169554083105094823617)
    ·
      refine ⟨38392627165562328821117713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51190169554083105094823617 38392627165562328821117713)
      ·
        refine ⟨28794470374171746615838285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38392627165562328821117713 28794470374171746615838285)
        ·
          refine ⟨10797926390314404980939357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28794470374171746615838285 10797926390314404980939357)
          ·
            refine ⟨4049222396367901867852259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10797926390314404980939357 4049222396367901867852259)
            ·
              refine ⟨6073833594551852801778389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4049222396367901867852259 6073833594551852801778389)
              ·
                refine ⟨142355474872309050041681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6073833594551852801778389 142355474872309050041681)
                ·
                  rfl

theorem cell21_1871345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 3, 1, 7].length) (baseStart_1871345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1871345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1871345 prefixEnd_1871345 := by exact prefixLift 1871345
  have htrace : WordTrace (prefixWord ++ tailWord_1871345) baseStart_1871345 baseEnd_1871345 := by
    simpa [prefixWord, tailWord_1871345, baseEnd_1871345] using wordTrace_append hprefix tailTrace_1871345
  have hstable : (prefixWord ++ tailWord_1871345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871345).length < 2 ^ (prefixWord ++ tailWord_1871345).sum := by decide
  have hdescent : baseEnd_1871345 < baseStart_1871345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871362 : List Nat := [3, 4, 1, 2, 1, 1, 9]
def baseStart_1871362 : Nat := 118140960795 + 1871362 * 2 ^ 59
def prefixEnd_1871362 : Nat := 4983230072969 + 3 ^ 40 * 1871362 * 2
def baseEnd_1871362 : Nat := 47452256027615433149075

theorem tailTrace_1871362 : CollatzResearch.WordTrace tailWord_1871362 prefixEnd_1871362 47452256027615433149075 := by
  unfold tailWord_1871362
  simp only [CollatzResearch.WordTrace]
  refine ⟨17063544861595638007450085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45502786297588368019866893 17063544861595638007450085)
  ·
    refine ⟨3199414661549182126396891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17063544861595638007450085 3199414661549182126396891)
    ·
      refine ⟨4799121992323773189595337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3199414661549182126396891 4799121992323773189595337)
      ·
        refine ⟨3599341494242829892196503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4799121992323773189595337 3599341494242829892196503)
        ·
          refine ⟨5399012241364244838294755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3599341494242829892196503 5399012241364244838294755)
          ·
            refine ⟨8098518362046367257442133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5399012241364244838294755 8098518362046367257442133)
            ·
              refine ⟨47452256027615433149075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 8098518362046367257442133 47452256027615433149075)
              ·
                rfl

theorem cell21_1871362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 9].length) (baseStart_1871362 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1871362 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1871362 prefixEnd_1871362 := by exact prefixLift 1871362
  have htrace : WordTrace (prefixWord ++ tailWord_1871362) baseStart_1871362 baseEnd_1871362 := by
    simpa [prefixWord, tailWord_1871362, baseEnd_1871362] using wordTrace_append hprefix tailTrace_1871362
  have hstable : (prefixWord ++ tailWord_1871362).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871362).length < 2 ^ (prefixWord ++ tailWord_1871362).sum := by decide
  have hdescent : baseEnd_1871362 < baseStart_1871362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871421 : List Nat := [1, 4, 1, 3, 3, 9]
def baseStart_1871421 : Nat := 118140960795 + 1871421 * 2 ^ 59
def prefixEnd_1871421 : Nat := 4983230072969 + 3 ^ 40 * 1871421 * 2
def baseEnd_1871421 : Nat := 15817917364902515068823

theorem tailTrace_1871421 : CollatzResearch.WordTrace tailWord_1871421 prefixEnd_1871421 15817917364902515068823 := by
  unfold tailWord_1871421
  simp only [CollatzResearch.WordTrace]
  refine ⟨68256331353168805106198117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45504220902112536737465411 68256331353168805106198117)
  ·
    refine ⟨12798062128719150957412147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68256331353168805106198117 12798062128719150957412147)
    ·
      refine ⟨19197093193078726436118221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12798062128719150957412147 19197093193078726436118221)
      ·
        refine ⟨7198909947404522413544333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19197093193078726436118221 7198909947404522413544333)
        ·
          refine ⟨2699591230276695905079125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7198909947404522413544333 2699591230276695905079125)
          ·
            refine ⟨15817917364902515068823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2699591230276695905079125 15817917364902515068823)
            ·
              rfl

theorem cell21_1871421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 9].length) (baseStart_1871421 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1871421 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1871421 prefixEnd_1871421 := by exact prefixLift 1871421
  have htrace : WordTrace (prefixWord ++ tailWord_1871421) baseStart_1871421 baseEnd_1871421 := by
    simpa [prefixWord, tailWord_1871421, baseEnd_1871421] using wordTrace_append hprefix tailTrace_1871421
  have hstable : (prefixWord ++ tailWord_1871421).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871421).length < 2 ^ (prefixWord ++ tailWord_1871421).sum := by decide
  have hdescent : baseEnd_1871421 < baseStart_1871421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871435 : List Nat := [1, 1, 1, 1, 3, 1, 3, 5, 5]
def baseStart_1871435 : Nat := 118140960795 + 1871435 * 2 ^ 59
def prefixEnd_1871435 : Nat := 4983230072969 + 3 ^ 40 * 1871435 * 2
def baseEnd_1871435 : Nat := 427086963843106993624859

theorem tailTrace_1871435 : CollatzResearch.WordTrace tailWord_1871435 prefixEnd_1871435 427086963843106993624859 := by
  unfold tailWord_1871435
  simp only [CollatzResearch.WordTrace]
  refine ⟨68256841975118085497207759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45504561316745390331471839 68256841975118085497207759)
  ·
    refine ⟨102385262962677128245811639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68256841975118085497207759 102385262962677128245811639)
    ·
      refine ⟨153577894444015692368717459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102385262962677128245811639 153577894444015692368717459)
      ·
        refine ⟨230366841666023538553076189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153577894444015692368717459 230366841666023538553076189)
        ·
          refine ⟨86387565624758826957403571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 230366841666023538553076189 86387565624758826957403571)
          ·
            refine ⟨129581348437138240436105357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86387565624758826957403571 129581348437138240436105357)
            ·
              refine ⟨48593005663926840163539509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129581348437138240436105357 48593005663926840163539509)
              ·
                refine ⟨4555594280993141265331829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48593005663926840163539509 4555594280993141265331829)
                ·
                  refine ⟨427086963843106993624859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4555594280993141265331829 427086963843106993624859)
                  ·
                    rfl

theorem cell21_1871435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 3, 5, 5].length) (baseStart_1871435 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1871435 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1871435 prefixEnd_1871435 := by exact prefixLift 1871435
  have htrace : WordTrace (prefixWord ++ tailWord_1871435) baseStart_1871435 baseEnd_1871435 := by
    simpa [prefixWord, tailWord_1871435, baseEnd_1871435] using wordTrace_append hprefix tailTrace_1871435
  have hstable : (prefixWord ++ tailWord_1871435).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871435).length < 2 ^ (prefixWord ++ tailWord_1871435).sum := by decide
  have hdescent : baseEnd_1871435 < baseStart_1871435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871452 : List Nat := [2, 2, 4, 1, 2, 1, 1, 1, 7]
def baseStart_1871452 : Nat := 118140960795 + 1871452 * 2 ^ 59
def prefixEnd_1871452 : Nat := 4983230072969 + 3 ^ 40 * 1871452 * 2
def baseEnd_1871452 : Nat := 427090843474718741841491

theorem tailTrace_1871452 : CollatzResearch.WordTrace tailWord_1871452 prefixEnd_1871452 427090843474718741841491 := by
  unfold tailWord_1871452
  simp only [CollatzResearch.WordTrace]
  refine ⟨34128731008028248700288305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45504974677370998267051073 34128731008028248700288305)
  ·
    refine ⟨25596548256021186525216229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34128731008028248700288305 25596548256021186525216229)
    ·
      refine ⟨4799352798003972473478043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25596548256021186525216229 4799352798003972473478043)
      ·
        refine ⟨7199029197005958710217065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4799352798003972473478043 7199029197005958710217065)
        ·
          refine ⟨5399271897754469032662799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7199029197005958710217065 5399271897754469032662799)
          ·
            refine ⟨8098907846631703548994199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5399271897754469032662799 8098907846631703548994199)
            ·
              refine ⟨12148361769947555323491299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8098907846631703548994199 12148361769947555323491299)
              ·
                refine ⟨18222542654921332985236949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12148361769947555323491299 18222542654921332985236949)
                ·
                  refine ⟨427090843474718741841491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18222542654921332985236949 427090843474718741841491)
                  ·
                    rfl

theorem cell21_1871452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_1871452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1871452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1871452 prefixEnd_1871452 := by exact prefixLift 1871452
  have htrace : WordTrace (prefixWord ++ tailWord_1871452) baseStart_1871452 baseEnd_1871452 := by
    simpa [prefixWord, tailWord_1871452, baseEnd_1871452] using wordTrace_append hprefix tailTrace_1871452
  have hstable : (prefixWord ++ tailWord_1871452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871452).length < 2 ^ (prefixWord ++ tailWord_1871452).sum := by decide
  have hdescent : baseEnd_1871452 < baseStart_1871452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871652 : List Nat := [2, 3, 1, 3, 2, 3, 1, 2, 4]
def baseStart_1871652 : Nat := 118140960795 + 1871652 * 2 ^ 59
def prefixEnd_1871652 : Nat := 4983230072969 + 3 ^ 40 * 1871652 * 2
def baseEnd_1871652 : Nat := 427136486199562838507749

theorem tailTrace_1871652 : CollatzResearch.WordTrace tailWord_1871652 prefixEnd_1871652 427136486199562838507749 := by
  unfold tailWord_1871652
  simp only [CollatzResearch.WordTrace]
  refine ⟨34132378307665965778928605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45509837743554621038571473 34132378307665965778928605)
  ·
    refine ⟨12799641865374737167098227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34132378307665965778928605 12799641865374737167098227)
    ·
      refine ⟨19199462798062105750647341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12799641865374737167098227 19199462798062105750647341)
      ·
        refine ⟨7199798549273289656492753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19199462798062105750647341 7199798549273289656492753)
        ·
          refine ⟨5399848911954967242369565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7199798549273289656492753 5399848911954967242369565)
          ·
            refine ⟨2024943341983112715888587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5399848911954967242369565 2024943341983112715888587)
            ·
              refine ⟨3037415012974669073832881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2024943341983112715888587 3037415012974669073832881)
              ·
                refine ⟨2278061259731001805374661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3037415012974669073832881 2278061259731001805374661)
                ·
                  refine ⟨427136486199562838507749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2278061259731001805374661 427136486199562838507749)
                  ·
                    rfl

theorem cell21_1871652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_1871652 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1871652 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1871652 prefixEnd_1871652 := by exact prefixLift 1871652
  have htrace : WordTrace (prefixWord ++ tailWord_1871652) baseStart_1871652 baseEnd_1871652 := by
    simpa [prefixWord, tailWord_1871652, baseEnd_1871652] using wordTrace_append hprefix tailTrace_1871652
  have hstable : (prefixWord ++ tailWord_1871652).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871652).length < 2 ^ (prefixWord ++ tailWord_1871652).sum := by decide
  have hdescent : baseEnd_1871652 < baseStart_1871652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871697 : List Nat := [1, 2, 2, 1, 5, 1, 3, 3, 3]
def baseStart_1871697 : Nat := 118140960795 + 1871697 * 2 ^ 59
def prefixEnd_1871697 : Nat := 4983230072969 + 3 ^ 40 * 1871697 * 2
def baseEnd_1871697 : Nat := 427146755812652760257657

theorem tailTrace_1871697 : CollatzResearch.WordTrace tailWord_1871697 prefixEnd_1871697 427146755812652760257657 := by
  unfold tailWord_1871697
  simp only [CollatzResearch.WordTrace]
  refine ⟨68266397900168904243245345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45510931933445936162163563 68266397900168904243245345)
  ·
    refine ⟨51199798425126678182434009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68266397900168904243245345 51199798425126678182434009)
    ·
      refine ⟨38399848818845008636825507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51199798425126678182434009 38399848818845008636825507)
      ·
        refine ⟨57599773228267512955238261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38399848818845008636825507 57599773228267512955238261)
        ·
          refine ⟨5399978740150079339553587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 57599773228267512955238261 5399978740150079339553587)
          ·
            refine ⟨8099968110225119009330381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5399978740150079339553587 8099968110225119009330381)
            ·
              refine ⟨3037488041334419628498893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8099968110225119009330381 3037488041334419628498893)
              ·
                refine ⟨1139058015500407360687085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3037488041334419628498893 1139058015500407360687085)
                ·
                  refine ⟨427146755812652760257657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1139058015500407360687085 427146755812652760257657)
                  ·
                    rfl

theorem cell21_1871697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 3].length) (baseStart_1871697 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1871697 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1871697 prefixEnd_1871697 := by exact prefixLift 1871697
  have htrace : WordTrace (prefixWord ++ tailWord_1871697) baseStart_1871697 baseEnd_1871697 := by
    simpa [prefixWord, tailWord_1871697, baseEnd_1871697] using wordTrace_append hprefix tailTrace_1871697
  have hstable : (prefixWord ++ tailWord_1871697).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871697).length < 2 ^ (prefixWord ++ tailWord_1871697).sum := by decide
  have hdescent : baseEnd_1871697 < baseStart_1871697 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871742 : List Nat := [4, 2, 3, 1, 1, 1, 2, 7]
def baseStart_1871742 : Nat := 118140960795 + 1871742 * 2 ^ 59
def prefixEnd_1871742 : Nat := 4983230072969 + 3 ^ 40 * 1871742 * 2
def baseEnd_1871742 : Nat := 142385675141914227335855

theorem tailTrace_1871742 : CollatzResearch.WordTrace tailWord_1871742 prefixEnd_1871742 142385675141914227335855 := by
  unfold tailWord_1871742
  simp only [CollatzResearch.WordTrace]
  refine ⟨8533504898125734616079185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45512026123337251285755653 8533504898125734616079185)
  ·
    refine ⟨6400128673594300962059389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8533504898125734616079185 6400128673594300962059389)
    ·
      refine ⟨2400048252597862860772271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6400128673594300962059389 2400048252597862860772271)
      ·
        refine ⟨3600072378896794291158407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2400048252597862860772271 3600072378896794291158407)
        ·
          refine ⟨5400108568345191436737611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3600072378896794291158407 5400108568345191436737611)
          ·
            refine ⟨8100162852517787155106417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5400108568345191436737611 8100162852517787155106417)
            ·
              refine ⟨6075122139388340366329813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8100162852517787155106417 6075122139388340366329813)
              ·
                refine ⟨142385675141914227335855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6075122139388340366329813 142385675141914227335855)
                ·
                  rfl

theorem cell21_1871742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_1871742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1871742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1871742 prefixEnd_1871742 := by exact prefixLift 1871742
  have htrace : WordTrace (prefixWord ++ tailWord_1871742) baseStart_1871742 baseEnd_1871742 := by
    simpa [prefixWord, tailWord_1871742, baseEnd_1871742] using wordTrace_append hprefix tailTrace_1871742
  have hstable : (prefixWord ++ tailWord_1871742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871742).length < 2 ^ (prefixWord ++ tailWord_1871742).sum := by decide
  have hdescent : baseEnd_1871742 < baseStart_1871742 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871756 : List Nat := [2, 2, 1, 2, 1, 2, 1, 7, 3]
def baseStart_1871756 : Nat := 118140960795 + 1871756 * 2 ^ 59
def prefixEnd_1871756 : Nat := 4983230072969 + 3 ^ 40 * 1871756 * 2
def baseEnd_1871756 : Nat := 427160220416481768774203

theorem tailTrace_1871756 : CollatzResearch.WordTrace tailWord_1871756 prefixEnd_1871756 427160220416481768774203 := by
  unfold tailWord_1871756
  simp only [CollatzResearch.WordTrace]
  refine ⟨34134274903477578659821561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45512366537970104879762081 34134274903477578659821561)
  ·
    refine ⟨25600706177608183994866171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34134274903477578659821561 25600706177608183994866171)
    ·
      refine ⟨38401059266412275992299257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25600706177608183994866171 38401059266412275992299257)
      ·
        refine ⟨28800794449809206994224443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38401059266412275992299257 28800794449809206994224443)
        ·
          refine ⟨43201191674713810491336665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28800794449809206994224443 43201191674713810491336665)
          ·
            refine ⟨32400893756035357868502499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43201191674713810491336665 32400893756035357868502499)
            ·
              refine ⟨48601340634053036802753749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32400893756035357868502499 48601340634053036802753749)
              ·
                refine ⟨1139093921110618050064541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 48601340634053036802753749 1139093921110618050064541)
                ·
                  refine ⟨427160220416481768774203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1139093921110618050064541 427160220416481768774203)
                  ·
                    rfl

theorem cell21_1871756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 7, 3].length) (baseStart_1871756 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1871756 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1871756 prefixEnd_1871756 := by exact prefixLift 1871756
  have htrace : WordTrace (prefixWord ++ tailWord_1871756) baseStart_1871756 baseEnd_1871756 := by
    simpa [prefixWord, tailWord_1871756, baseEnd_1871756] using wordTrace_append hprefix tailTrace_1871756
  have hstable : (prefixWord ++ tailWord_1871756).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871756).length < 2 ^ (prefixWord ++ tailWord_1871756).sum := by decide
  have hdescent : baseEnd_1871756 < baseStart_1871756 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871773 : List Nat := [1, 4, 2, 1, 2, 3, 1, 4, 3]
def baseStart_1871773 : Nat := 118140960795 + 1871773 * 2 ^ 59
def prefixEnd_1871773 : Nat := 4983230072969 + 3 ^ 40 * 1871773 * 2
def baseEnd_1871773 : Nat := 427164100048093516990835

theorem tailTrace_1871773 : CollatzResearch.WordTrace tailWord_1871773 prefixEnd_1871773 427164100048093516990835 := by
  unfold tailWord_1871773
  simp only [CollatzResearch.WordTrace]
  refine ⟨68269169847893569223011973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45512779898595712815341315 68269169847893569223011973)
  ·
    refine ⟨12800469346480044229314745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68269169847893569223011973 12800469346480044229314745)
    ·
      refine ⟨9600352009860033171986059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12800469346480044229314745 9600352009860033171986059)
      ·
        refine ⟨14400528014790049757979089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9600352009860033171986059 14400528014790049757979089)
        ·
          refine ⟨10800396011092537318484317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14400528014790049757979089 10800396011092537318484317)
          ·
            refine ⟨4050148504159701494431619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10800396011092537318484317 4050148504159701494431619)
            ·
              refine ⟨6075222756239552241647429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4050148504159701494431619 6075222756239552241647429)
              ·
                refine ⟨1139104266794916045308893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6075222756239552241647429 1139104266794916045308893)
                ·
                  refine ⟨427164100048093516990835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1139104266794916045308893 427164100048093516990835)
                  ·
                    rfl

theorem cell21_1871773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 4, 3].length) (baseStart_1871773 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1871773 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1871773 prefixEnd_1871773 := by exact prefixLift 1871773
  have htrace : WordTrace (prefixWord ++ tailWord_1871773) baseStart_1871773 baseEnd_1871773 := by
    simpa [prefixWord, tailWord_1871773, baseEnd_1871773] using wordTrace_append hprefix tailTrace_1871773
  have hstable : (prefixWord ++ tailWord_1871773).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871773).length < 2 ^ (prefixWord ++ tailWord_1871773).sum := by decide
  have hdescent : baseEnd_1871773 < baseStart_1871773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871801 : List Nat := [1, 2, 1, 4, 2, 1, 5, 5]
def baseStart_1871801 : Nat := 118140960795 + 1871801 * 2 ^ 59
def prefixEnd_1871801 : Nat := 4983230072969 + 3 ^ 40 * 1871801 * 2
def baseEnd_1871801 : Nat := 142390163343190563508037

theorem tailTrace_1871801 : CollatzResearch.WordTrace tailWord_1871801 prefixEnd_1871801 142390163343190563508037 := by
  unfold tailWord_1871801
  simp only [CollatzResearch.WordTrace]
  refine ⟨68270191091792130005031257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45513460727861420003354171 68270191091792130005031257)
  ·
    refine ⟨51202643318844097503773443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68270191091792130005031257 51202643318844097503773443)
    ·
      refine ⟨76803964978266146255660165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51202643318844097503773443 76803964978266146255660165)
      ·
        refine ⟨14400743433424902422936281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76803964978266146255660165 14400743433424902422936281)
        ·
          refine ⟨10800557575068676817202211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14400743433424902422936281 10800557575068676817202211)
          ·
            refine ⟨16200836362603015225803317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10800557575068676817202211 16200836362603015225803317)
            ·
              refine ⟨1518828408994032677419061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16200836362603015225803317 1518828408994032677419061)
              ·
                refine ⟨142390163343190563508037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1518828408994032677419061 142390163343190563508037)
                ·
                  rfl

theorem cell21_1871801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 5].length) (baseStart_1871801 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1871801 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1871801 prefixEnd_1871801 := by exact prefixLift 1871801
  have htrace : WordTrace (prefixWord ++ tailWord_1871801) baseStart_1871801 baseEnd_1871801 := by
    simpa [prefixWord, tailWord_1871801, baseEnd_1871801] using wordTrace_append hprefix tailTrace_1871801
  have hstable : (prefixWord ++ tailWord_1871801).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871801).length < 2 ^ (prefixWord ++ tailWord_1871801).sum := by decide
  have hdescent : baseEnd_1871801 < baseStart_1871801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871832 : List Nat := [2, 1, 2, 2, 2, 2, 1, 6, 3]
def baseStart_1871832 : Nat := 118140960795 + 1871832 * 2 ^ 59
def prefixEnd_1871832 : Nat := 4983230072969 + 3 ^ 40 * 1871832 * 2
def baseEnd_1871832 : Nat := 427177564651922525507381

theorem tailTrace_1871832 : CollatzResearch.WordTrace tailWord_1871832 prefixEnd_1871832 427177564651922525507381 := by
  unfold tailWord_1871832
  simp only [CollatzResearch.WordTrace]
  refine ⟨34135660877339911149704875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45514214503119881532939833 34135660877339911149704875)
  ·
    refine ⟨51203491316009866724557313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34135660877339911149704875 51203491316009866724557313)
    ·
      refine ⟨38402618487007400043417985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51203491316009866724557313 38402618487007400043417985)
      ·
        refine ⟨28801963865255550032563489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38402618487007400043417985 28801963865255550032563489)
        ·
          refine ⟨21601472898941662524422617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28801963865255550032563489 21601472898941662524422617)
          ·
            refine ⟨16201104674206246893316963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21601472898941662524422617 16201104674206246893316963)
            ·
              refine ⟨24301657011309370339975445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16201104674206246893316963 24301657011309370339975445)
              ·
                refine ⟨1139140172405126734686349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 24301657011309370339975445 1139140172405126734686349)
                ·
                  refine ⟨427177564651922525507381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1139140172405126734686349 427177564651922525507381)
                  ·
                    rfl

theorem cell21_1871832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 3].length) (baseStart_1871832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1871832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1871832 prefixEnd_1871832 := by exact prefixLift 1871832
  have htrace : WordTrace (prefixWord ++ tailWord_1871832) baseStart_1871832 baseEnd_1871832 := by
    simpa [prefixWord, tailWord_1871832, baseEnd_1871832] using wordTrace_append hprefix tailTrace_1871832
  have hstable : (prefixWord ++ tailWord_1871832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871832).length < 2 ^ (prefixWord ++ tailWord_1871832).sum := by decide
  have hdescent : baseEnd_1871832 < baseStart_1871832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871891 : List Nat := [1, 1, 1, 2, 1, 4, 5, 1, 5]
def baseStart_1871891 : Nat := 118140960795 + 1871891 * 2 ^ 59
def prefixEnd_1871891 : Nat := 4983230072969 + 3 ^ 40 * 1871891 * 2
def baseEnd_1871891 : Nat := 427191029255751534023927

theorem tailTrace_1871891 : CollatzResearch.WordTrace tailWord_1871891 prefixEnd_1871891 427191029255751534023927 := by
  unfold tailWord_1871891
  simp only [CollatzResearch.WordTrace]
  refine ⟨68273473661466075375807527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45515649107644050250538351 68273473661466075375807527)
  ·
    refine ⟨102410210492199113063711291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68273473661466075375807527 102410210492199113063711291)
    ·
      refine ⟨153615315738298669595566937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102410210492199113063711291 153615315738298669595566937)
      ·
        refine ⟨115211486803724002196675203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153615315738298669595566937 115211486803724002196675203)
        ·
          refine ⟨172817230205586003295012805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115211486803724002196675203 172817230205586003295012805)
          ·
            refine ⟨32403230663547375617814901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 172817230205586003295012805 32403230663547375617814901)
            ·
              refine ⟨3037802874707566464170147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 32403230663547375617814901 3037802874707566464170147)
              ·
                refine ⟨4556704312061349696255221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3037802874707566464170147 4556704312061349696255221)
                ·
                  refine ⟨427191029255751534023927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4556704312061349696255221 427191029255751534023927)
                  ·
                    rfl

theorem cell21_1871891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 5, 1, 5].length) (baseStart_1871891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1871891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1871891 prefixEnd_1871891 := by exact prefixLift 1871891
  have htrace : WordTrace (prefixWord ++ tailWord_1871891) baseStart_1871891 baseEnd_1871891 := by
    simpa [prefixWord, tailWord_1871891, baseEnd_1871891] using wordTrace_append hprefix tailTrace_1871891
  have hstable : (prefixWord ++ tailWord_1871891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871891).length < 2 ^ (prefixWord ++ tailWord_1871891).sum := by decide
  have hdescent : baseEnd_1871891 < baseStart_1871891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871942 : List Nat := [6, 1, 1, 1, 1, 1, 3, 4, 3]
def baseStart_1871942 : Nat := 118140960795 + 1871942 * 2 ^ 59
def prefixEnd_1871942 : Nat := 4983230072969 + 3 ^ 40 * 1871942 * 2
def baseEnd_1871942 : Nat := 427202668150586778673823

theorem tailTrace_1871942 : CollatzResearch.WordTrace tailWord_1871942 prefixEnd_1871942 427202668150586778673823 := by
  unfold tailWord_1871942
  simp only [CollatzResearch.WordTrace]
  refine ⟨2133604180758790971434815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45516889189520874057276053 2133604180758790971434815)
  ·
    refine ⟨3200406271138186457152223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2133604180758790971434815 3200406271138186457152223)
    ·
      refine ⟨4800609406707279685728335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3200406271138186457152223 4800609406707279685728335)
      ·
        refine ⟨7200914110060919528592503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4800609406707279685728335 7200914110060919528592503)
        ·
          refine ⟨10801371165091379292888755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7200914110060919528592503 10801371165091379292888755)
          ·
            refine ⟨16202056747637068939333133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10801371165091379292888755 16202056747637068939333133)
            ·
              refine ⟨6075771280363900852249925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16202056747637068939333133 6075771280363900852249925)
              ·
                refine ⟨1139207115068231409796861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6075771280363900852249925 1139207115068231409796861)
                ·
                  refine ⟨427202668150586778673823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1139207115068231409796861 427202668150586778673823)
                  ·
                    rfl

theorem cell21_1871942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 3, 4, 3].length) (baseStart_1871942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1871942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1871942 prefixEnd_1871942 := by exact prefixLift 1871942
  have htrace : WordTrace (prefixWord ++ tailWord_1871942) baseStart_1871942 baseEnd_1871942 := by
    simpa [prefixWord, tailWord_1871942, baseEnd_1871942] using wordTrace_append hprefix tailTrace_1871942
  have hstable : (prefixWord ++ tailWord_1871942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871942).length < 2 ^ (prefixWord ++ tailWord_1871942).sum := by decide
  have hdescent : baseEnd_1871942 < baseStart_1871942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1871984 : List Nat := [2, 1, 1, 1, 5, 2, 1, 5, 3]
def baseStart_1871984 : Nat := 118140960795 + 1871984 * 2 ^ 59
def prefixEnd_1871984 : Nat := 4983230072969 + 3 ^ 40 * 1871984 * 2
def baseEnd_1871984 : Nat := 427212253122804038973737

theorem tailTrace_1871984 : CollatzResearch.WordTrace tailWord_1871984 prefixEnd_1871984 427212253122804038973737 := by
  unfold tailWord_1871984
  simp only [CollatzResearch.WordTrace]
  refine ⟨34138432825064576129471503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45517910433419434839295337 34138432825064576129471503)
  ·
    refine ⟨51207649237596864194207255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34138432825064576129471503 51207649237596864194207255)
    ·
      refine ⟨76811473856395296291310883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51207649237596864194207255 76811473856395296291310883)
      ·
        refine ⟨115217210784592944436966325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76811473856395296291310883 115217210784592944436966325)
        ·
          refine ⟨10801613511055588540965593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 115217210784592944436966325 10801613511055588540965593)
          ·
            refine ⟨8101210133291691405724195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10801613511055588540965593 8101210133291691405724195)
            ·
              refine ⟨12151815199937537108586293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8101210133291691405724195 12151815199937537108586293)
              ·
                refine ⟨1139232674994144103929965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12151815199937537108586293 1139232674994144103929965)
                ·
                  refine ⟨427212253122804038973737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1139232674994144103929965 427212253122804038973737)
                  ·
                    rfl

theorem cell21_1871984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 5, 3].length) (baseStart_1871984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1871984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1871984 prefixEnd_1871984 := by exact prefixLift 1871984
  have htrace : WordTrace (prefixWord ++ tailWord_1871984) baseStart_1871984 baseEnd_1871984 := by
    simpa [prefixWord, tailWord_1871984, baseEnd_1871984] using wordTrace_append hprefix tailTrace_1871984
  have hstable : (prefixWord ++ tailWord_1871984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1871984).length < 2 ^ (prefixWord ++ tailWord_1871984).sum := by decide
  have hdescent : baseEnd_1871984 < baseStart_1871984 := by decide
  rcases family_descends (prefixWord ++ tailWord_1871984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872029 : List Nat := [1, 4, 2, 1, 1, 3, 4, 5]
def baseStart_1872029 : Nat := 118140960795 + 1872029 * 2 ^ 59
def prefixEnd_1872029 : Nat := 4983230072969 + 3 ^ 40 * 1872029 * 2
def baseEnd_1872029 : Nat := 142407507578631320241215

theorem tailTrace_1872029 : CollatzResearch.WordTrace tailWord_1872029 prefixEnd_1872029 142407507578631320241215 := by
  unfold tailWord_1872029
  simp only [CollatzResearch.WordTrace]
  refine ⟨68278506934966124944331141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45519004623310749962887427 68278506934966124944331141)
  ·
    refine ⟨12802220050306148427062089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68278506934966124944331141 12802220050306148427062089)
    ·
      refine ⟨9601665037729611320296567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12802220050306148427062089 9601665037729611320296567)
      ·
        refine ⟨14402497556594416980444851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9601665037729611320296567 14402497556594416980444851)
        ·
          refine ⟨21603746334891625470667277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14402497556594416980444851 21603746334891625470667277)
          ·
            refine ⟨8101404875584359551500229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21603746334891625470667277 8101404875584359551500229)
            ·
              refine ⟨1519013414172067415906293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8101404875584359551500229 1519013414172067415906293)
              ·
                refine ⟨142407507578631320241215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1519013414172067415906293 142407507578631320241215)
                ·
                  rfl

theorem cell21_1872029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 4, 5].length) (baseStart_1872029 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872029 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872029 prefixEnd_1872029 := by exact prefixLift 1872029
  have htrace : WordTrace (prefixWord ++ tailWord_1872029) baseStart_1872029 baseEnd_1872029 := by
    simpa [prefixWord, tailWord_1872029, baseEnd_1872029] using wordTrace_append hprefix tailTrace_1872029
  have hstable : (prefixWord ++ tailWord_1872029).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872029).length < 2 ^ (prefixWord ++ tailWord_1872029).sum := by decide
  have hdescent : baseEnd_1872029 < baseStart_1872029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872052 : List Nat := [2, 5, 3, 1, 2, 1, 1, 1, 5]
def baseStart_1872052 : Nat := 118140960795 + 1872052 * 2 ^ 59
def prefixEnd_1872052 : Nat := 4983230072969 + 3 ^ 40 * 1872052 * 2
def baseEnd_1872052 : Nat := 427227771649251031840265

theorem tailTrace_1872052 : CollatzResearch.WordTrace tailWord_1872052 prefixEnd_1872052 427227771649251031840265 := by
  unfold tailWord_1872052
  simp only [CollatzResearch.WordTrace]
  refine ⟨34139672906941399936209205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45519563875921866581612273 34139672906941399936209205)
  ·
    refine ⟨3200594335025756244019613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34139672906941399936209205 3200594335025756244019613)
    ·
      refine ⟨1200222875634658591507355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3200594335025756244019613 1200222875634658591507355)
      ·
        refine ⟨1800334313451987887261033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1200222875634658591507355 1800334313451987887261033)
        ·
          refine ⟨1350250735088990915445775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1800334313451987887261033 1350250735088990915445775)
          ·
            refine ⟨2025376102633486373168663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1350250735088990915445775 2025376102633486373168663)
            ·
              refine ⟨3038064153950229559752995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2025376102633486373168663 3038064153950229559752995)
              ·
                refine ⟨4557096230925344339629493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3038064153950229559752995 4557096230925344339629493)
                ·
                  refine ⟨427227771649251031840265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4557096230925344339629493 427227771649251031840265)
                  ·
                    rfl

theorem cell21_1872052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 5].length) (baseStart_1872052 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872052 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872052 prefixEnd_1872052 := by exact prefixLift 1872052
  have htrace : WordTrace (prefixWord ++ tailWord_1872052) baseStart_1872052 baseEnd_1872052 := by
    simpa [prefixWord, tailWord_1872052, baseEnd_1872052] using wordTrace_append hprefix tailTrace_1872052
  have hstable : (prefixWord ++ tailWord_1872052).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872052).length < 2 ^ (prefixWord ++ tailWord_1872052).sum := by decide
  have hdescent : baseEnd_1872052 < baseStart_1872052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872057 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 6]
def baseStart_1872057 : Nat := 118140960795 + 1872057 * 2 ^ 59
def prefixEnd_1872057 : Nat := 4983230072969 + 3 ^ 40 * 1872057 * 2
def baseEnd_1872057 : Nat := 427228912717372134256921

theorem tailTrace_1872057 : CollatzResearch.WordTrace tailWord_1872057 prefixEnd_1872057 427228912717372134256921 := by
  unfold tailWord_1872057
  simp only [CollatzResearch.WordTrace]
  refine ⟨68279528178864685726350425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45519685452576457150900283 68279528178864685726350425)
  ·
    refine ⟨51209646134148514294762819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68279528178864685726350425 51209646134148514294762819)
    ·
      refine ⟨76814469201222771442144229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51209646134148514294762819 76814469201222771442144229)
      ·
        refine ⟨14402712975229269645402043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76814469201222771442144229 14402712975229269645402043)
        ·
          refine ⟨21604069462843904468103065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14402712975229269645402043 21604069462843904468103065)
          ·
            refine ⟨16203052097132928351077299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21604069462843904468103065 16203052097132928351077299)
            ·
              refine ⟨24304578145699392526615949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16203052097132928351077299 24304578145699392526615949)
              ·
                refine ⟨9114216804637272197480981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24304578145699392526615949 9114216804637272197480981)
                ·
                  refine ⟨427228912717372134256921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9114216804637272197480981 427228912717372134256921)
                  ·
                    rfl

theorem cell21_1872057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 6].length) (baseStart_1872057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872057 prefixEnd_1872057 := by exact prefixLift 1872057
  have htrace : WordTrace (prefixWord ++ tailWord_1872057) baseStart_1872057 baseEnd_1872057 := by
    simpa [prefixWord, tailWord_1872057, baseEnd_1872057] using wordTrace_append hprefix tailTrace_1872057
  have hstable : (prefixWord ++ tailWord_1872057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872057).length < 2 ^ (prefixWord ++ tailWord_1872057).sum := by decide
  have hdescent : baseEnd_1872057 < baseStart_1872057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872066 : List Nat := [3, 5, 1, 1, 1, 3, 2, 1, 4]
def baseStart_1872066 : Nat := 118140960795 + 1872066 * 2 ^ 59
def prefixEnd_1872066 : Nat := 4983230072969 + 3 ^ 40 * 1872066 * 2
def baseEnd_1872066 : Nat := 427230966639990118606903

theorem tailTrace_1872066 : CollatzResearch.WordTrace tailWord_1872066 prefixEnd_1872066 427230966639990118606903 := by
  unfold tailWord_1872066
  simp only [CollatzResearch.WordTrace]
  refine ⟨17069964108958020065857013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45519904290554720175618701 17069964108958020065857013)
  ·
    refine ⟨1600309135214814381174095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 17069964108958020065857013 1600309135214814381174095)
    ·
      refine ⟨2400463702822221571761143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1600309135214814381174095 2400463702822221571761143)
      ·
        refine ⟨3600695554233332357641715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2400463702822221571761143 3600695554233332357641715)
        ·
          refine ⟨5401043331349998536462573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3600695554233332357641715 5401043331349998536462573)
          ·
            refine ⟨2025391249256249451173465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5401043331349998536462573 2025391249256249451173465)
            ·
              refine ⟨1519043436942187088380099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2025391249256249451173465 1519043436942187088380099)
              ·
                refine ⟨2278565155413280632570149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1519043436942187088380099 2278565155413280632570149)
                ·
                  refine ⟨427230966639990118606903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2278565155413280632570149 427230966639990118606903)
                  ·
                    rfl

theorem cell21_1872066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_1872066 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872066 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872066 prefixEnd_1872066 := by exact prefixLift 1872066
  have htrace : WordTrace (prefixWord ++ tailWord_1872066) baseStart_1872066 baseEnd_1872066 := by
    simpa [prefixWord, tailWord_1872066, baseEnd_1872066] using wordTrace_append hprefix tailTrace_1872066
  have hstable : (prefixWord ++ tailWord_1872066).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872066).length < 2 ^ (prefixWord ++ tailWord_1872066).sum := by decide
  have hdescent : baseEnd_1872066 < baseStart_1872066 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872074 : List Nat := [3, 1, 2, 1, 3, 1, 3, 3, 4]
def baseStart_1872074 : Nat := 118140960795 + 1872074 * 2 ^ 59
def prefixEnd_1872074 : Nat := 4983230072969 + 3 ^ 40 * 1872074 * 2
def baseEnd_1872074 : Nat := 427232792348983882473553

theorem tailTrace_1872074 : CollatzResearch.WordTrace tailWord_1872074 prefixEnd_1872074 427232792348983882473553 := by
  unfold tailWord_1872074
  simp only [CollatzResearch.WordTrace]
  refine ⟨17070037054950774407429819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45520098813202065086479517 17070037054950774407429819)
  ·
    refine ⟨25605055582426161611144729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17070037054950774407429819 25605055582426161611144729)
    ·
      refine ⟨19203791686819621208358547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25605055582426161611144729 19203791686819621208358547)
      ·
        refine ⟨28805687530229431812537821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19203791686819621208358547 28805687530229431812537821)
        ·
          refine ⟨10802132823836036929701683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28805687530229431812537821 10802132823836036929701683)
          ·
            refine ⟨16203199235754055394552525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10802132823836036929701683 16203199235754055394552525)
            ·
              refine ⟨6076199713407770772957197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16203199235754055394552525 6076199713407770772957197)
              ·
                refine ⟨2278574892527914039858949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6076199713407770772957197 2278574892527914039858949)
                ·
                  refine ⟨427232792348983882473553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2278574892527914039858949 427232792348983882473553)
                  ·
                    rfl

theorem cell21_1872074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 4].length) (baseStart_1872074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872074 prefixEnd_1872074 := by exact prefixLift 1872074
  have htrace : WordTrace (prefixWord ++ tailWord_1872074) baseStart_1872074 baseEnd_1872074 := by
    simpa [prefixWord, tailWord_1872074, baseEnd_1872074] using wordTrace_append hprefix tailTrace_1872074
  have hstable : (prefixWord ++ tailWord_1872074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872074).length < 2 ^ (prefixWord ++ tailWord_1872074).sum := by decide
  have hdescent : baseEnd_1872074 < baseStart_1872074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872088 : List Nat := [2, 1, 2, 2, 4, 1, 2, 7]
def baseStart_1872088 : Nat := 118140960795 + 1872088 * 2 ^ 59
def prefixEnd_1872088 : Nat := 4983230072969 + 3 ^ 40 * 1872088 * 2
def baseEnd_1872088 : Nat := 142411995779907656413397

theorem tailTrace_1872088 : CollatzResearch.WordTrace tailWord_1872088 prefixEnd_1872088 142411995779907656413397 := by
  unfold tailWord_1872088
  simp only [CollatzResearch.WordTrace]
  refine ⟨34140329420876189010364459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45520439227834918680485945 34140329420876189010364459)
  ·
    refine ⟨51210494131314283515546689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34140329420876189010364459 51210494131314283515546689)
    ·
      refine ⟨38407870598485712636660017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51210494131314283515546689 38407870598485712636660017)
      ·
        refine ⟨28805902948864284477495013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38407870598485712636660017 28805902948864284477495013)
        ·
          refine ⟨5401106802912053339530315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 28805902948864284477495013 5401106802912053339530315)
          ·
            refine ⟨8101660204368080009295473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5401106802912053339530315 8101660204368080009295473)
            ·
              refine ⟨6076245153276060006971605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8101660204368080009295473 6076245153276060006971605)
              ·
                refine ⟨142411995779907656413397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6076245153276060006971605 142411995779907656413397)
                ·
                  rfl

theorem cell21_1872088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 7].length) (baseStart_1872088 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872088 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872088 prefixEnd_1872088 := by exact prefixLift 1872088
  have htrace : WordTrace (prefixWord ++ tailWord_1872088) baseStart_1872088 baseEnd_1872088 := by
    simpa [prefixWord, tailWord_1872088, baseEnd_1872088] using wordTrace_append hprefix tailTrace_1872088
  have hstable : (prefixWord ++ tailWord_1872088).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872088).length < 2 ^ (prefixWord ++ tailWord_1872088).sum := by decide
  have hdescent : baseEnd_1872088 < baseStart_1872088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872147 : List Nat := [1, 1, 1, 2, 1, 3, 1, 11]
def baseStart_1872147 : Nat := 118140960795 + 1872147 * 2 ^ 59
def prefixEnd_1872147 : Nat := 4983230072969 + 3 ^ 40 * 1872147 * 2
def baseEnd_1872147 : Nat := 142416483981183992585579

theorem tailTrace_1872147 : CollatzResearch.WordTrace tailWord_1872147 prefixEnd_1872147 142416483981183992585579 := by
  unfold tailWord_1872147
  simp only [CollatzResearch.WordTrace]
  refine ⟨68282810748538631097126695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45521873832359087398084463 68282810748538631097126695)
  ·
    refine ⟨102424216122807946645690043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68282810748538631097126695 102424216122807946645690043)
    ·
      refine ⟨153636324184211919968535065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102424216122807946645690043 153636324184211919968535065)
      ·
        refine ⟨115227243138158939976401299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153636324184211919968535065 115227243138158939976401299)
        ·
          refine ⟨172840864707238409964601949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115227243138158939976401299 172840864707238409964601949)
          ·
            refine ⟨64815324265214403736725731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 172840864707238409964601949 64815324265214403736725731)
            ·
              refine ⟨97222986397821605605088597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64815324265214403736725731 97222986397821605605088597)
              ·
                refine ⟨142416483981183992585579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 97222986397821605605088597 142416483981183992585579)
                ·
                  rfl

theorem cell21_1872147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 11].length) (baseStart_1872147 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872147 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872147 prefixEnd_1872147 := by exact prefixLift 1872147
  have htrace : WordTrace (prefixWord ++ tailWord_1872147) baseStart_1872147 baseEnd_1872147 := by
    simpa [prefixWord, tailWord_1872147, baseEnd_1872147] using wordTrace_append hprefix tailTrace_1872147
  have hstable : (prefixWord ++ tailWord_1872147).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872147).length < 2 ^ (prefixWord ++ tailWord_1872147).sum := by decide
  have hdescent : baseEnd_1872147 < baseStart_1872147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872164 : List Nat := [2, 3, 1, 3, 1, 3, 8]
def baseStart_1872164 : Nat := 118140960795 + 1872164 * 2 ^ 59
def prefixEnd_1872164 : Nat := 4983230072969 + 3 ^ 40 * 1872164 * 2
def baseEnd_1872164 : Nat := 47472592397240413997041

theorem tailTrace_1872164 : CollatzResearch.WordTrace tailWord_1872164 prefixEnd_1872164 47472592397240413997041 := by
  unfold tailWord_1872164
  simp only [CollatzResearch.WordTrace]
  refine ⟨34141715394738521500247773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45522287192984695333663697 34141715394738521500247773)
  ·
    refine ⟨12803143273026945562592915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34141715394738521500247773 12803143273026945562592915)
    ·
      refine ⟨19204714909540418343889373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12803143273026945562592915 19204714909540418343889373)
      ·
        refine ⟨7201768091077656878958515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19204714909540418343889373 7201768091077656878958515)
        ·
          refine ⟨10802652136616485318437773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7201768091077656878958515 10802652136616485318437773)
          ·
            refine ⟨4050994551231181994414165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10802652136616485318437773 4050994551231181994414165)
            ·
              refine ⟨47472592397240413997041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 4050994551231181994414165 47472592397240413997041)
              ·
                rfl

theorem cell21_1872164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 3, 8].length) (baseStart_1872164 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872164 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872164 prefixEnd_1872164 := by exact prefixLift 1872164
  have htrace : WordTrace (prefixWord ++ tailWord_1872164) baseStart_1872164 baseEnd_1872164 := by
    simpa [prefixWord, tailWord_1872164, baseEnd_1872164] using wordTrace_append hprefix tailTrace_1872164
  have hstable : (prefixWord ++ tailWord_1872164).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872164).length < 2 ^ (prefixWord ++ tailWord_1872164).sum := by decide
  have hdescent : baseEnd_1872164 < baseStart_1872164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872209 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 6]
def baseStart_1872209 : Nat := 118140960795 + 1872209 * 2 ^ 59
def prefixEnd_1872209 : Nat := 4983230072969 + 3 ^ 40 * 1872209 * 2
def baseEnd_1872209 : Nat := 427263601188253647723277

theorem tailTrace_1872209 : CollatzResearch.WordTrace tailWord_1872209 prefixEnd_1872209 427263601188253647723277 := by
  unfold tailWord_1872209
  simp only [CollatzResearch.WordTrace]
  refine ⟨68285072074314015685883681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45523381382876010457255787 68285072074314015685883681)
  ·
    refine ⟨51213804055735511764412761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68285072074314015685883681 51213804055735511764412761)
    ·
      refine ⟨38410353041801633823309571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51213804055735511764412761 38410353041801633823309571)
      ·
        refine ⟨57615529562702450734964357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38410353041801633823309571 57615529562702450734964357)
        ·
          refine ⟨10802911793006709512805817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 57615529562702450734964357 10802911793006709512805817)
          ·
            refine ⟨8102183844755032134604363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10802911793006709512805817 8102183844755032134604363)
            ·
              refine ⟨12153275767132548201906545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8102183844755032134604363 12153275767132548201906545)
              ·
                refine ⟨9114956825349411151429909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12153275767132548201906545 9114956825349411151429909)
                ·
                  refine ⟨427263601188253647723277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9114956825349411151429909 427263601188253647723277)
                  ·
                    rfl

theorem cell21_1872209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 6].length) (baseStart_1872209 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872209 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872209 prefixEnd_1872209 := by exact prefixLift 1872209
  have htrace : WordTrace (prefixWord ++ tailWord_1872209) baseStart_1872209 baseEnd_1872209 := by
    simpa [prefixWord, tailWord_1872209, baseEnd_1872209] using wordTrace_append hprefix tailTrace_1872209
  have hstable : (prefixWord ++ tailWord_1872209).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872209).length < 2 ^ (prefixWord ++ tailWord_1872209).sum := by decide
  have hdescent : baseEnd_1872209 < baseStart_1872209 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872223 : List Nat := [1, 1, 2, 3, 1, 2, 11]
def baseStart_1872223 : Nat := 118140960795 + 1872223 * 2 ^ 59
def prefixEnd_1872223 : Nat := 4983230072969 + 3 ^ 40 * 1872223 * 2
def baseEnd_1872223 : Nat := 47474088464332526054435

theorem tailTrace_1872223 : CollatzResearch.WordTrace tailWord_1872223 prefixEnd_1872223 47474088464332526054435 := by
  unfold tailWord_1872223
  simp only [CollatzResearch.WordTrace]
  refine ⟨68285582696263296076893323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45523721797508864051262215 68285582696263296076893323)
  ·
    refine ⟨102428374044394944115339985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68285582696263296076893323 102428374044394944115339985)
    ·
      refine ⟨76821280533296208086504989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102428374044394944115339985 76821280533296208086504989)
      ·
        refine ⟨28807980199986078032439371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76821280533296208086504989 28807980199986078032439371)
        ·
          refine ⟨43211970299979117048659057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28807980199986078032439371 43211970299979117048659057)
          ·
            refine ⟨32408977724984337786494293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 43211970299979117048659057 32408977724984337786494293)
            ·
              refine ⟨47474088464332526054435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 32408977724984337786494293 47474088464332526054435)
              ·
                rfl

theorem cell21_1872223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 11].length) (baseStart_1872223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872223 prefixEnd_1872223 := by exact prefixLift 1872223
  have htrace : WordTrace (prefixWord ++ tailWord_1872223) baseStart_1872223 baseEnd_1872223 := by
    simpa [prefixWord, tailWord_1872223, baseEnd_1872223] using wordTrace_append hprefix tailTrace_1872223
  have hstable : (prefixWord ++ tailWord_1872223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872223).length < 2 ^ (prefixWord ++ tailWord_1872223).sum := by decide
  have hdescent : baseEnd_1872223 < baseStart_1872223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872226 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 6]
def baseStart_1872226 : Nat := 118140960795 + 1872226 * 2 ^ 59
def prefixEnd_1872226 : Nat := 4983230072969 + 3 ^ 40 * 1872226 * 2
def baseEnd_1872226 : Nat := 427267480819865395939909

theorem tailTrace_1872226 : CollatzResearch.WordTrace tailWord_1872226 prefixEnd_1872226 427267480819865395939909 := by
  unfold tailWord_1872226
  simp only [CollatzResearch.WordTrace]
  refine ⟨17071423028813106897313133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45523794743501618392835021 17071423028813106897313133)
  ·
    refine ⟨6401783635804915086492425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17071423028813106897313133 6401783635804915086492425)
    ·
      refine ⟨4801337726853686314869319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6401783635804915086492425 4801337726853686314869319)
      ·
        refine ⟨7202006590280529472303979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4801337726853686314869319 7202006590280529472303979)
        ·
          refine ⟨10803009885420794208455969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7202006590280529472303979 10803009885420794208455969)
          ·
            refine ⟨8102257414065595656341977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10803009885420794208455969 8102257414065595656341977)
            ·
              refine ⟨6076693060549196742256483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8102257414065595656341977 6076693060549196742256483)
              ·
                refine ⟨9115039590823795113384725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6076693060549196742256483 9115039590823795113384725)
                ·
                  refine ⟨427267480819865395939909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9115039590823795113384725 427267480819865395939909)
                  ·
                    rfl

theorem cell21_1872226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_1872226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872226 prefixEnd_1872226 := by exact prefixLift 1872226
  have htrace : WordTrace (prefixWord ++ tailWord_1872226) baseStart_1872226 baseEnd_1872226 := by
    simpa [prefixWord, tailWord_1872226, baseEnd_1872226] using wordTrace_append hprefix tailTrace_1872226
  have hstable : (prefixWord ++ tailWord_1872226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872226).length < 2 ^ (prefixWord ++ tailWord_1872226).sum := by decide
  have hdescent : baseEnd_1872226 < baseStart_1872226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872229 : List Nat := [1, 3, 1, 3, 1, 4, 3, 2, 3]
def baseStart_1872229 : Nat := 118140960795 + 1872229 * 2 ^ 59
def prefixEnd_1872229 : Nat := 4983230072969 + 3 ^ 40 * 1872229 * 2
def baseEnd_1872229 : Nat := 427268165460738057389903

theorem tailTrace_1872229 : CollatzResearch.WordTrace tailWord_1872229 prefixEnd_1872229 427268165460738057389903 := by
  unfold tailWord_1872229
  simp only [CollatzResearch.WordTrace]
  refine ⟨68285801534241559101611741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45523867689494372734407827 68285801534241559101611741)
  ·
    refine ⟨25607175575340584663104403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68285801534241559101611741 25607175575340584663104403)
    ·
      refine ⟨38410763363010876994656605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25607175575340584663104403 38410763363010876994656605)
      ·
        refine ⟨14404036261129078872996227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38410763363010876994656605 14404036261129078872996227)
        ·
          refine ⟨21606054391693618309494341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14404036261129078872996227 21606054391693618309494341)
          ·
            refine ⟨4051135198442553433030189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21606054391693618309494341 4051135198442553433030189)
            ·
              refine ⟨1519175699415957537386321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4051135198442553433030189 1519175699415957537386321)
              ·
                refine ⟨1139381774561968153039741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1519175699415957537386321 1139381774561968153039741)
                ·
                  refine ⟨427268165460738057389903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1139381774561968153039741 427268165460738057389903)
                  ·
                    rfl

theorem cell21_1872229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 3, 2, 3].length) (baseStart_1872229 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872229 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872229 prefixEnd_1872229 := by exact prefixLift 1872229
  have htrace : WordTrace (prefixWord ++ tailWord_1872229) baseStart_1872229 baseEnd_1872229 := by
    simpa [prefixWord, tailWord_1872229, baseEnd_1872229] using wordTrace_append hprefix tailTrace_1872229
  have hstable : (prefixWord ++ tailWord_1872229).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872229).length < 2 ^ (prefixWord ++ tailWord_1872229).sum := by decide
  have hdescent : baseEnd_1872229 < baseStart_1872229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872240 : List Nat := [2, 1, 1, 1, 4, 4, 2, 6]
def baseStart_1872240 : Nat := 118140960795 + 1872240 * 2 ^ 59
def prefixEnd_1872240 : Nat := 4983230072969 + 3 ^ 40 * 1872240 * 2
def baseEnd_1872240 : Nat := 142423558603534827568849

theorem tailTrace_1872240 : CollatzResearch.WordTrace tailWord_1872240 prefixEnd_1872240 142423558603534827568849 := by
  unfold tailWord_1872240
  simp only [CollatzResearch.WordTrace]
  refine ⟨34143101368600853990131087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45524135158134471986841449 34143101368600853990131087)
  ·
    refine ⟨51214652052901280985196631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34143101368600853990131087 51214652052901280985196631)
    ·
      refine ⟨76821978079351921477794947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51214652052901280985196631 76821978079351921477794947)
      ·
        refine ⟨115232967119027882216692421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76821978079351921477794947 115232967119027882216692421)
        ·
          refine ⟨21606181334817727915629829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115232967119027882216692421 21606181334817727915629829)
          ·
            refine ⟨4051159000278323984180593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21606181334817727915629829 4051159000278323984180593)
            ·
              refine ⟨3038369250208742988135445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4051159000278323984180593 3038369250208742988135445)
              ·
                refine ⟨142423558603534827568849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3038369250208742988135445 142423558603534827568849)
                ·
                  rfl

theorem cell21_1872240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 6].length) (baseStart_1872240 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872240 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872240 prefixEnd_1872240 := by exact prefixLift 1872240
  have htrace : WordTrace (prefixWord ++ tailWord_1872240) baseStart_1872240 baseEnd_1872240 := by
    simpa [prefixWord, tailWord_1872240, baseEnd_1872240] using wordTrace_append hprefix tailTrace_1872240
  have hstable : (prefixWord ++ tailWord_1872240).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872240).length < 2 ^ (prefixWord ++ tailWord_1872240).sum := by decide
  have hdescent : baseEnd_1872240 < baseStart_1872240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872288 : List Nat := [2, 1, 1, 4, 1, 4, 1, 4, 3]
def baseStart_1872288 : Nat := 118140960795 + 1872288 * 2 ^ 59
def prefixEnd_1872288 : Nat := 4983230072969 + 3 ^ 40 * 1872288 * 2
def baseEnd_1872288 : Nat := 427281630064567065906449

theorem tailTrace_1872288 : CollatzResearch.WordTrace tailWord_1872288 prefixEnd_1872288 427281630064567065906449 := by
  unfold tailWord_1872288
  simp only [CollatzResearch.WordTrace]
  refine ⟨34143976720513906089004759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45525302294018541452006345 34143976720513906089004759)
  ·
    refine ⟨51215965080770859133507139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34143976720513906089004759 51215965080770859133507139)
    ·
      refine ⟨76823947621156288700260709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51215965080770859133507139 76823947621156288700260709)
      ·
        refine ⟨14404490178966804131298883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76823947621156288700260709 14404490178966804131298883)
        ·
          refine ⟨21606735268450206196948325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14404490178966804131298883 21606735268450206196948325)
          ·
            refine ⟨4051262862834413661927811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21606735268450206196948325 4051262862834413661927811)
            ·
              refine ⟨6076894294251620492891717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4051262862834413661927811 6076894294251620492891717)
              ·
                refine ⟨1139417680172178842417197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6076894294251620492891717 1139417680172178842417197)
                ·
                  refine ⟨427281630064567065906449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1139417680172178842417197 427281630064567065906449)
                  ·
                    rfl

theorem cell21_1872288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 3].length) (baseStart_1872288 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872288 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872288 prefixEnd_1872288 := by exact prefixLift 1872288
  have htrace : WordTrace (prefixWord ++ tailWord_1872288) baseStart_1872288 baseEnd_1872288 := by
    simpa [prefixWord, tailWord_1872288, baseEnd_1872288] using wordTrace_append hprefix tailTrace_1872288
  have hstable : (prefixWord ++ tailWord_1872288).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872288).length < 2 ^ (prefixWord ++ tailWord_1872288).sum := by decide
  have hdescent : baseEnd_1872288 < baseStart_1872288 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872330 : List Nat := [3, 1, 2, 1, 2, 2, 1, 2, 7]
def baseStart_1872330 : Nat := 118140960795 + 1872330 * 2 ^ 59
def prefixEnd_1872330 : Nat := 4983230072969 + 3 ^ 40 * 1872330 * 2
def baseEnd_1872330 : Nat := 427291215036784326206363

theorem tailTrace_1872330 : CollatzResearch.WordTrace tailWord_1872330 prefixEnd_1872330 427291215036784326206363 := by
  unfold tailWord_1872330
  simp only [CollatzResearch.WordTrace]
  refine ⟨17072371326718913337759611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45526323537917102234025629 17072371326718913337759611)
  ·
    refine ⟨25608556990078370006639417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17072371326718913337759611 25608556990078370006639417)
    ·
      refine ⟨19206417742558777504979563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25608556990078370006639417 19206417742558777504979563)
      ·
        refine ⟨28809626613838166257469345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19206417742558777504979563 28809626613838166257469345)
        ·
          refine ⟨21607219960378624693102009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28809626613838166257469345 21607219960378624693102009)
          ·
            refine ⟨16205414970283968519826507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21607219960378624693102009 16205414970283968519826507)
            ·
              refine ⟨24308122455425952779739761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16205414970283968519826507 24308122455425952779739761)
              ·
                refine ⟨18231091841569464584804821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24308122455425952779739761 18231091841569464584804821)
                ·
                  refine ⟨427291215036784326206363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18231091841569464584804821 427291215036784326206363)
                  ·
                    rfl

theorem cell21_1872330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_1872330 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872330 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872330 prefixEnd_1872330 := by exact prefixLift 1872330
  have htrace : WordTrace (prefixWord ++ tailWord_1872330) baseStart_1872330 baseEnd_1872330 := by
    simpa [prefixWord, tailWord_1872330, baseEnd_1872330] using wordTrace_append hprefix tailTrace_1872330
  have hstable : (prefixWord ++ tailWord_1872330).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872330).length < 2 ^ (prefixWord ++ tailWord_1872330).sum := by decide
  have hdescent : baseEnd_1872330 < baseStart_1872330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872468 : List Nat := [2, 4, 1, 1, 1, 3, 3, 6]
def baseStart_1872468 : Nat := 118140960795 + 1872468 * 2 ^ 59
def prefixEnd_1872468 : Nat := 4983230072969 + 3 ^ 40 * 1872468 * 2
def baseEnd_1872468 : Nat := 142440902838975584302027

theorem tailTrace_1872468 : CollatzResearch.WordTrace tailWord_1872468 prefixEnd_1872468 142440902838975584302027 := by
  unfold tailWord_1872468
  simp only [CollatzResearch.WordTrace]
  refine ⟨34147259290187851459781029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45529679053583801946374705 34147259290187851459781029)
  ·
    refine ⟨6402611116910222148708943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34147259290187851459781029 6402611116910222148708943)
    ·
      refine ⟨9603916675365333223063415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6402611116910222148708943 9603916675365333223063415)
      ·
        refine ⟨14405875013047999834595123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9603916675365333223063415 14405875013047999834595123)
        ·
          refine ⟨21608812519571999751892685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14405875013047999834595123 21608812519571999751892685)
          ·
            refine ⟨8103304694839499906959757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21608812519571999751892685 8103304694839499906959757)
            ·
              refine ⟨3038739260564812465109909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8103304694839499906959757 3038739260564812465109909)
              ·
                refine ⟨142440902838975584302027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3038739260564812465109909 142440902838975584302027)
                ·
                  rfl

theorem cell21_1872468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 6].length) (baseStart_1872468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872468 prefixEnd_1872468 := by exact prefixLift 1872468
  have htrace : WordTrace (prefixWord ++ tailWord_1872468) baseStart_1872468 baseEnd_1872468 := by
    simpa [prefixWord, tailWord_1872468, baseEnd_1872468] using wordTrace_append hprefix tailTrace_1872468
  have hstable : (prefixWord ++ tailWord_1872468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872468).length < 2 ^ (prefixWord ++ tailWord_1872468).sum := by decide
  have hdescent : baseEnd_1872468 < baseStart_1872468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872485 : List Nat := [1, 3, 1, 3, 4, 1, 3, 5]
def baseStart_1872485 : Nat := 118140960795 + 1872485 * 2 ^ 59
def prefixEnd_1872485 : Nat := 4983230072969 + 3 ^ 40 * 1872485 * 2
def baseEnd_1872485 : Nat := 142442196049512833707571

theorem tailTrace_1872485 : CollatzResearch.WordTrace tailWord_1872485 prefixEnd_1872485 142442196049512833707571 := by
  unfold tailWord_1872485
  simp only [CollatzResearch.WordTrace]
  refine ⟨68295138621314114822930909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45530092414209409881953939 68295138621314114822930909)
  ·
    refine ⟨25610676982992793058599091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68295138621314114822930909 25610676982992793058599091)
    ·
      refine ⟨38416015474489189587898637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25610676982992793058599091 38416015474489189587898637)
      ·
        refine ⟨14406005802933446095461989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38416015474489189587898637 14406005802933446095461989)
        ·
          refine ⟨2701126088050021142899123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14406005802933446095461989 2701126088050021142899123)
          ·
            refine ⟨4051689132075031714348685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2701126088050021142899123 4051689132075031714348685)
            ·
              refine ⟨1519383424528136892880757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4051689132075031714348685 1519383424528136892880757)
              ·
                refine ⟨142442196049512833707571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1519383424528136892880757 142442196049512833707571)
                ·
                  rfl

theorem cell21_1872485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3, 5].length) (baseStart_1872485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872485 prefixEnd_1872485 := by exact prefixLift 1872485
  have htrace : WordTrace (prefixWord ++ tailWord_1872485) baseStart_1872485 baseEnd_1872485 := by
    simpa [prefixWord, tailWord_1872485, baseEnd_1872485] using wordTrace_append hprefix tailTrace_1872485
  have hstable : (prefixWord ++ tailWord_1872485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872485).length < 2 ^ (prefixWord ++ tailWord_1872485).sum := by decide
  have hdescent : baseEnd_1872485 < baseStart_1872485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872513 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 6]
def baseStart_1872513 : Nat := 118140960795 + 1872513 * 2 ^ 59
def prefixEnd_1872513 : Nat := 4983230072969 + 3 ^ 40 * 1872513 * 2
def baseEnd_1872513 : Nat := 427332978130016674655989

theorem tailTrace_1872513 : CollatzResearch.WordTrace tailWord_1872513 prefixEnd_1872513 427332978130016674655989 := by
  unfold tailWord_1872513
  simp only [CollatzResearch.WordTrace]
  refine ⟨68296159865212675604950193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45530773243475117069966795 68296159865212675604950193)
  ·
    refine ⟨51222119898909506703712645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68296159865212675604950193 51222119898909506703712645)
    ·
      refine ⟨9604147481045532506946121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51222119898909506703712645 9604147481045532506946121)
      ·
        refine ⟨7203110610784149380209591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9604147481045532506946121 7203110610784149380209591)
        ·
          refine ⟨10804665916176224070314387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7203110610784149380209591 10804665916176224070314387)
          ·
            refine ⟨16206998874264336105471581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10804665916176224070314387 16206998874264336105471581)
            ·
              refine ⟨6077624577849126039551843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16206998874264336105471581 6077624577849126039551843)
              ·
                refine ⟨9116436866773689059327765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6077624577849126039551843 9116436866773689059327765)
                ·
                  refine ⟨427332978130016674655989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9116436866773689059327765 427332978130016674655989)
                  ·
                    rfl

theorem cell21_1872513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 6].length) (baseStart_1872513 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872513 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872513 prefixEnd_1872513 := by exact prefixLift 1872513
  have htrace : WordTrace (prefixWord ++ tailWord_1872513) baseStart_1872513 baseEnd_1872513 := by
    simpa [prefixWord, tailWord_1872513, baseEnd_1872513] using wordTrace_append hprefix tailTrace_1872513
  have hstable : (prefixWord ++ tailWord_1872513).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872513).length < 2 ^ (prefixWord ++ tailWord_1872513).sum := by decide
  have hdescent : baseEnd_1872513 < baseStart_1872513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872516 : List Nat := [2, 3, 2, 1, 3, 1, 2, 4, 3]
def baseStart_1872516 : Nat := 118140960795 + 1872516 * 2 ^ 59
def prefixEnd_1872516 : Nat := 4983230072969 + 3 ^ 40 * 1872516 * 2
def baseEnd_1872516 : Nat := 427333662770889336105983

theorem tailTrace_1872516 : CollatzResearch.WordTrace tailWord_1872516 prefixEnd_1872516 427333662770889336105983 := by
  unfold tailWord_1872516
  simp only [CollatzResearch.WordTrace]
  refine ⟨34148134642100903558654701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45530846189467871411539601 34148134642100903558654701)
  ·
    refine ⟨12805550490787838834495513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34148134642100903558654701 12805550490787838834495513)
    ·
      refine ⟨9604162868090879125871635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12805550490787838834495513 9604162868090879125871635)
      ·
        refine ⟨14406244302136318688807453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9604162868090879125871635 14406244302136318688807453)
        ·
          refine ⟨5402341613301119508302795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14406244302136318688807453 5402341613301119508302795)
          ·
            refine ⟨8103512419951679262454193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5402341613301119508302795 8103512419951679262454193)
            ·
              refine ⟨6077634314963759446840645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8103512419951679262454193 6077634314963759446840645)
              ·
                refine ⟨1139556434055704896282621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6077634314963759446840645 1139556434055704896282621)
                ·
                  refine ⟨427333662770889336105983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1139556434055704896282621 427333662770889336105983)
                  ·
                    rfl

theorem cell21_1872516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 2, 4, 3].length) (baseStart_1872516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872516 prefixEnd_1872516 := by exact prefixLift 1872516
  have htrace : WordTrace (prefixWord ++ tailWord_1872516) baseStart_1872516 baseEnd_1872516 := by
    simpa [prefixWord, tailWord_1872516, baseEnd_1872516] using wordTrace_append hprefix tailTrace_1872516
  have hstable : (prefixWord ++ tailWord_1872516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872516).length < 2 ^ (prefixWord ++ tailWord_1872516).sum := by decide
  have hdescent : baseEnd_1872516 < baseStart_1872516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872544 : List Nat := [2, 1, 1, 4, 4, 1, 1, 7]
def baseStart_1872544 : Nat := 118140960795 + 1872544 * 2 ^ 59
def prefixEnd_1872544 : Nat := 4983230072969 + 3 ^ 40 * 1872544 * 2
def baseEnd_1872544 : Nat := 142446684250789169879753

theorem tailTrace_1872544 : CollatzResearch.WordTrace tailWord_1872544 prefixEnd_1872544 142446684250789169879753 := by
  unfold tailWord_1872544
  simp only [CollatzResearch.WordTrace]
  refine ⟨34148645264050183949664343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45531527018733578599552457 34148645264050183949664343)
  ·
    refine ⟨51222967896075275924496515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34148645264050183949664343 51222967896075275924496515)
    ·
      refine ⟨76834451844112913886744773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51222967896075275924496515 76834451844112913886744773)
      ·
        refine ⟨14406459720771171353764645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76834451844112913886744773 14406459720771171353764645)
        ·
          refine ⟨2701211197644594628830871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14406459720771171353764645 2701211197644594628830871)
          ·
            refine ⟨4051816796466891943246307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2701211197644594628830871 4051816796466891943246307)
            ·
              refine ⟨6077725194700337914869461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4051816796466891943246307 6077725194700337914869461)
              ·
                refine ⟨142446684250789169879753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6077725194700337914869461 142446684250789169879753)
                ·
                  rfl

theorem cell21_1872544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 7].length) (baseStart_1872544 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872544 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872544 prefixEnd_1872544 := by exact prefixLift 1872544
  have htrace : WordTrace (prefixWord ++ tailWord_1872544) baseStart_1872544 baseEnd_1872544 := by
    simpa [prefixWord, tailWord_1872544, baseEnd_1872544] using wordTrace_append hprefix tailTrace_1872544
  have hstable : (prefixWord ++ tailWord_1872544).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872544).length < 2 ^ (prefixWord ++ tailWord_1872544).sum := by decide
  have hdescent : baseEnd_1872544 < baseStart_1872544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872561 : List Nat := [1, 2, 2, 6, 1, 2, 7]
def baseStart_1872561 : Nat := 118140960795 + 1872561 * 2 ^ 59
def prefixEnd_1872561 : Nat := 4983230072969 + 3 ^ 40 * 1872561 * 2
def baseEnd_1872561 : Nat := 47482659153775473095099

theorem tailTrace_1872561 : CollatzResearch.WordTrace tailWord_1872561 prefixEnd_1872561 47482659153775473095099 := by
  unfold tailWord_1872561
  simp only [CollatzResearch.WordTrace]
  refine ⟨68297910569038779802697537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45531940379359186535131691 68297910569038779802697537)
  ·
    refine ⟨51223432926779084852023153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68297910569038779802697537 51223432926779084852023153)
    ·
      refine ⟨38417574695084313639017365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51223432926779084852023153 38417574695084313639017365)
      ·
        refine ⟨1800823813832077201828939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38417574695084313639017365 1800823813832077201828939)
        ·
          refine ⟨2701235720748115802743409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1800823813832077201828939 2701235720748115802743409)
          ·
            refine ⟨2025926790561086852057557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2701235720748115802743409 2025926790561086852057557)
            ·
              refine ⟨47482659153775473095099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2025926790561086852057557 47482659153775473095099)
              ·
                rfl

theorem cell21_1872561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 7].length) (baseStart_1872561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872561 prefixEnd_1872561 := by exact prefixLift 1872561
  have htrace : WordTrace (prefixWord ++ tailWord_1872561) baseStart_1872561 baseEnd_1872561 := by
    simpa [prefixWord, tailWord_1872561, baseEnd_1872561] using wordTrace_append hprefix tailTrace_1872561
  have hstable : (prefixWord ++ tailWord_1872561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872561).length < 2 ^ (prefixWord ++ tailWord_1872561).sum := by decide
  have hdescent : baseEnd_1872561 < baseStart_1872561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872575 : List Nat := [1, 1, 2, 2, 2, 6, 1, 1, 5]
def baseStart_1872575 : Nat := 118140960795 + 1872575 * 2 ^ 59
def prefixEnd_1872575 : Nat := 4983230072969 + 3 ^ 40 * 1872575 * 2
def baseEnd_1872575 : Nat := 427347127374718344622529

theorem tailTrace_1872575 : CollatzResearch.WordTrace tailWord_1872575 prefixEnd_1872575 427347127374718344622529 := by
  unfold tailWord_1872575
  simp only [CollatzResearch.WordTrace]
  refine ⟨68298421190988060193707179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45532280793992040129138119 68298421190988060193707179)
  ·
    refine ⟨102447631786482090290560769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68298421190988060193707179 102447631786482090290560769)
    ·
      refine ⟨76835723839861567717920577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102447631786482090290560769 76835723839861567717920577)
      ·
        refine ⟨57626792879896175788440433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76835723839861567717920577 57626792879896175788440433)
        ·
          refine ⟨43220094659922131841330325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 57626792879896175788440433 43220094659922131841330325)
          ·
            refine ⟨2025941937183849930062359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 43220094659922131841330325 2025941937183849930062359)
            ·
              refine ⟨3038912905775774895093539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2025941937183849930062359 3038912905775774895093539)
              ·
                refine ⟨4558369358663662342640309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3038912905775774895093539 4558369358663662342640309)
                ·
                  refine ⟨427347127374718344622529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4558369358663662342640309 427347127374718344622529)
                  ·
                    rfl

theorem cell21_1872575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 5].length) (baseStart_1872575 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872575 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872575 prefixEnd_1872575 := by exact prefixLift 1872575
  have htrace : WordTrace (prefixWord ++ tailWord_1872575) baseStart_1872575 baseEnd_1872575 := by
    simpa [prefixWord, tailWord_1872575, baseEnd_1872575] using wordTrace_append hprefix tailTrace_1872575
  have hstable : (prefixWord ++ tailWord_1872575).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872575).length < 2 ^ (prefixWord ++ tailWord_1872575).sum := by decide
  have hdescent : baseEnd_1872575 < baseStart_1872575 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872668 : List Nat := [2, 2, 3, 1, 1, 4, 2, 3, 3]
def baseStart_1872668 : Nat := 118140960795 + 1872668 * 2 ^ 59
def prefixEnd_1872668 : Nat := 4983230072969 + 3 ^ 40 * 1872668 * 2
def baseEnd_1872668 : Nat := 427368351241770849572339

theorem tailTrace_1872668 : CollatzResearch.WordTrace tailWord_1872668 prefixEnd_1872668 427368351241770849572339 := by
  unfold tailWord_1872668
  simp only [CollatzResearch.WordTrace]
  refine ⟨34150906589825568538421329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45534542119767424717895105 34150906589825568538421329)
  ·
    refine ⟨25613179942369176403815997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34150906589825568538421329 25613179942369176403815997)
    ·
      refine ⟨9604942478388441151430999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25613179942369176403815997 9604942478388441151430999)
      ·
        refine ⟨14407413717582661727146499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9604942478388441151430999 14407413717582661727146499)
        ·
          refine ⟨21611120576373992590719749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14407413717582661727146499 21611120576373992590719749)
          ·
            refine ⟨4052085108070123610759953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21611120576373992590719749 4052085108070123610759953)
            ·
              refine ⟨3039063831052592708069965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4052085108070123610759953 3039063831052592708069965)
              ·
                refine ⟨1139648936644722265526237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3039063831052592708069965 1139648936644722265526237)
                ·
                  refine ⟨427368351241770849572339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1139648936644722265526237 427368351241770849572339)
                  ·
                    rfl

theorem cell21_1872668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 3, 3].length) (baseStart_1872668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872668 prefixEnd_1872668 := by exact prefixLift 1872668
  have htrace : WordTrace (prefixWord ++ tailWord_1872668) baseStart_1872668 baseEnd_1872668 := by
    simpa [prefixWord, tailWord_1872668, baseEnd_1872668] using wordTrace_append hprefix tailTrace_1872668
  have hstable : (prefixWord ++ tailWord_1872668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872668).length < 2 ^ (prefixWord ++ tailWord_1872668).sum := by decide
  have hdescent : baseEnd_1872668 < baseStart_1872668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872685 : List Nat := [1, 5, 3, 2, 1, 1, 2, 1, 5]
def baseStart_1872685 : Nat := 118140960795 + 1872685 * 2 ^ 59
def prefixEnd_1872685 : Nat := 4983230072969 + 3 ^ 40 * 1872685 * 2
def baseEnd_1872685 : Nat := 427372230873382597788971

theorem tailTrace_1872685 : CollatzResearch.WordTrace tailWord_1872685 prefixEnd_1872685 427372230873382597788971 := by
  unfold tailWord_1872685
  simp only [CollatzResearch.WordTrace]
  refine ⟨68302433220589548980211509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45534955480393032653474339 68302433220589548980211509)
  ·
    refine ⟨6403353114430270216894829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68302433220589548980211509 6403353114430270216894829)
    ·
      refine ⟨2401257417911351331335561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6403353114430270216894829 2401257417911351331335561)
      ·
        refine ⟨1800943063433513498501671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2401257417911351331335561 1800943063433513498501671)
        ·
          refine ⟨2701414595150270247752507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1800943063433513498501671 2701414595150270247752507)
          ·
            refine ⟨4052121892725405371628761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2701414595150270247752507 4052121892725405371628761)
            ·
              refine ⟨3039091419544054028721571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4052121892725405371628761 3039091419544054028721571)
              ·
                refine ⟨4558637129316081043082357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3039091419544054028721571 4558637129316081043082357)
                ·
                  refine ⟨427372230873382597788971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4558637129316081043082357 427372230873382597788971)
                  ·
                    rfl

theorem cell21_1872685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_1872685 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872685 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872685 prefixEnd_1872685 := by exact prefixLift 1872685
  have htrace : WordTrace (prefixWord ++ tailWord_1872685) baseStart_1872685 baseEnd_1872685 := by
    simpa [prefixWord, tailWord_1872685, baseEnd_1872685] using wordTrace_append hprefix tailTrace_1872685
  have hstable : (prefixWord ++ tailWord_1872685).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872685).length < 2 ^ (prefixWord ++ tailWord_1872685).sum := by decide
  have hdescent : baseEnd_1872685 < baseStart_1872685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872800 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 6]
def baseStart_1872800 : Nat := 118140960795 + 1872800 * 2 ^ 59
def prefixEnd_1872800 : Nat := 4983230072969 + 3 ^ 40 * 1872800 * 2
def baseEnd_1872800 : Nat := 427398475440167953372069

theorem tailTrace_1872800 : CollatzResearch.WordTrace tailWord_1872800 prefixEnd_1872800 427398475440167953372069 := by
  unfold tailWord_1872800
  simp only [CollatzResearch.WordTrace]
  refine ⟨34153313807586461810323927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45537751743448615747098569 34153313807586461810323927)
  ·
    refine ⟨51229970711379692715485891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34153313807586461810323927 51229970711379692715485891)
    ·
      refine ⟨76844956067069539073228837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51229970711379692715485891 76844956067069539073228837)
      ·
        refine ⟨14408429262575538576230407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76844956067069539073228837 14408429262575538576230407)
        ·
          refine ⟨21612643893863307864345611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14408429262575538576230407 21612643893863307864345611)
          ·
            refine ⟨32418965840794961796518417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21612643893863307864345611 32418965840794961796518417)
            ·
              refine ⟨24314224380596221347388813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 32418965840794961796518417 24314224380596221347388813)
              ·
                refine ⟨9117834142723583005270805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24314224380596221347388813 9117834142723583005270805)
                ·
                  refine ⟨427398475440167953372069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9117834142723583005270805 427398475440167953372069)
                  ·
                    rfl

theorem cell21_1872800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 6].length) (baseStart_1872800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872800 prefixEnd_1872800 := by exact prefixLift 1872800
  have htrace : WordTrace (prefixWord ++ tailWord_1872800) baseStart_1872800 baseEnd_1872800 := by
    simpa [prefixWord, tailWord_1872800, baseEnd_1872800] using wordTrace_append hprefix tailTrace_1872800
  have hstable : (prefixWord ++ tailWord_1872800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872800).length < 2 ^ (prefixWord ++ tailWord_1872800).sum := by decide
  have hdescent : baseEnd_1872800 < baseStart_1872800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872820 : List Nat := [2, 5, 2, 1, 1, 2, 1, 2, 5]
def baseStart_1872820 : Nat := 118140960795 + 1872820 * 2 ^ 59
def prefixEnd_1872820 : Nat := 4983230072969 + 3 ^ 40 * 1872820 * 2
def baseEnd_1872820 : Nat := 427403039712652363038695

theorem tailTrace_1872820 : CollatzResearch.WordTrace tailWord_1872820 prefixEnd_1872820 427403039712652363038695 := by
  unfold tailWord_1872820
  simp only [CollatzResearch.WordTrace]
  refine ⟨34153678537550233518187957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45538238050066978024250609 34153678537550233518187957)
  ·
    refine ⟨3201907362895334392330121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 34153678537550233518187957 3201907362895334392330121)
    ·
      refine ⟨2401430522171500794247591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3201907362895334392330121 2401430522171500794247591)
      ·
        refine ⟨3602145783257251191371387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2401430522171500794247591 3602145783257251191371387)
        ·
          refine ⟨5403218674885876787057081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3602145783257251191371387 5403218674885876787057081)
          ·
            refine ⟨4052414006164407590292811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5403218674885876787057081 4052414006164407590292811)
            ·
              refine ⟨6078621009246611385439217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4052414006164407590292811 6078621009246611385439217)
              ·
                refine ⟨4558965756934958539079413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6078621009246611385439217 4558965756934958539079413)
                ·
                  refine ⟨427403039712652363038695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4558965756934958539079413 427403039712652363038695)
                  ·
                    rfl

theorem cell21_1872820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_1872820 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872820 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872820 prefixEnd_1872820 := by exact prefixLift 1872820
  have htrace : WordTrace (prefixWord ++ tailWord_1872820) baseStart_1872820 baseEnd_1872820 := by
    simpa [prefixWord, tailWord_1872820, baseEnd_1872820] using wordTrace_append hprefix tailTrace_1872820
  have hstable : (prefixWord ++ tailWord_1872820).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872820).length < 2 ^ (prefixWord ++ tailWord_1872820).sum := by decide
  have hdescent : baseEnd_1872820 < baseStart_1872820 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872882 : List Nat := [3, 2, 1, 5, 1, 2, 2, 5]
def baseStart_1872882 : Nat := 118140960795 + 1872882 * 2 ^ 59
def prefixEnd_1872882 : Nat := 4983230072969 + 3 ^ 40 * 1872882 * 2
def baseEnd_1872882 : Nat := 142472396319118011001745

theorem tailTrace_1872882 : CollatzResearch.WordTrace tailWord_1872882 prefixEnd_1872882 142472396319118011001745 := by
  unfold tailWord_1872882
  simp only [CollatzResearch.WordTrace]
  refine ⟨17077404600218962906283225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45539745600583901083421933 17077404600218962906283225)
  ·
    refine ⟨12808053450164222179712419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17077404600218962906283225 12808053450164222179712419)
    ·
      refine ⟨19212080175246333269568629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12808053450164222179712419 19212080175246333269568629)
      ·
        refine ⟨1801132516429343744022059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19212080175246333269568629 1801132516429343744022059)
        ·
          refine ⟨2701698774644015616033089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1801132516429343744022059 2701698774644015616033089)
          ·
            refine ⟨2026274080983011712024817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2701698774644015616033089 2026274080983011712024817)
            ·
              refine ⟨1519705560737258784018613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2026274080983011712024817 1519705560737258784018613)
              ·
                refine ⟨142472396319118011001745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1519705560737258784018613 142472396319118011001745)
                ·
                  rfl

theorem cell21_1872882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_1872882 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872882 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872882 prefixEnd_1872882 := by exact prefixLift 1872882
  have htrace : WordTrace (prefixWord ++ tailWord_1872882) baseStart_1872882 baseEnd_1872882 := by
    simpa [prefixWord, tailWord_1872882, baseEnd_1872882] using wordTrace_append hprefix tailTrace_1872882
  have hstable : (prefixWord ++ tailWord_1872882).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872882).length < 2 ^ (prefixWord ++ tailWord_1872882).sum := by decide
  have hdescent : baseEnd_1872882 < baseStart_1872882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872907 : List Nat := [1, 1, 1, 1, 6, 4, 7]
def baseStart_1872907 : Nat := 118140960795 + 1872907 * 2 ^ 59
def prefixEnd_1872907 : Nat := 4983230072969 + 3 ^ 40 * 1872907 * 2
def baseEnd_1872907 : Nat := 47491432699773282787613

theorem tailTrace_1872907 : CollatzResearch.WordTrace tailWord_1872907 prefixEnd_1872907 47491432699773282787613 := by
  unfold tailWord_1872907
  simp only [CollatzResearch.WordTrace]
  refine ⟨68310530225785280894792975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45540353483856853929861983 68310530225785280894792975)
  ·
    refine ⟨102465795338677921342189463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68310530225785280894792975 102465795338677921342189463)
    ·
      refine ⟨153698693008016882013284195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102465795338677921342189463 153698693008016882013284195)
      ·
        refine ⟨230548039512025323019926293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153698693008016882013284195 230548039512025323019926293)
        ·
          refine ⟨10806939352126187016559045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 230548039512025323019926293 10806939352126187016559045)
          ·
            refine ⟨2026301128523660065604821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10806939352126187016559045 2026301128523660065604821)
            ·
              refine ⟨47491432699773282787613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2026301128523660065604821 47491432699773282787613)
              ·
                rfl

theorem cell21_1872907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 4, 7].length) (baseStart_1872907 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872907 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872907 prefixEnd_1872907 := by exact prefixLift 1872907
  have htrace : WordTrace (prefixWord ++ tailWord_1872907) baseStart_1872907 baseEnd_1872907 := by
    simpa [prefixWord, tailWord_1872907, baseEnd_1872907] using wordTrace_append hprefix tailTrace_1872907
  have hstable : (prefixWord ++ tailWord_1872907).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872907).length < 2 ^ (prefixWord ++ tailWord_1872907).sum := by decide
  have hdescent : baseEnd_1872907 < baseStart_1872907 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1872924 : List Nat := [2, 2, 3, 1, 4, 1, 2, 6]
def baseStart_1872924 : Nat := 118140960795 + 1872924 * 2 ^ 59
def prefixEnd_1872924 : Nat := 4983230072969 + 3 ^ 40 * 1872924 * 2
def baseEnd_1872924 : Nat := 142475591309857097768383

theorem tailTrace_1872924 : CollatzResearch.WordTrace tailWord_1872924 prefixEnd_1872924 142475591309857097768383 := by
  unfold tailWord_1872924
  simp only [CollatzResearch.WordTrace]
  refine ⟨34155575133361846399080913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45540766844482461865441217 34155575133361846399080913)
  ·
    refine ⟨25616681350021384799310685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34155575133361846399080913 25616681350021384799310685)
    ·
      refine ⟨9606255506258019299741507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25616681350021384799310685 9606255506258019299741507)
      ·
        refine ⟨14409383259387028949612261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9606255506258019299741507 14409383259387028949612261)
        ·
          refine ⟨2701759361135067928052299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14409383259387028949612261 2701759361135067928052299)
          ·
            refine ⟨4052639041702601892078449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2701759361135067928052299 4052639041702601892078449)
            ·
              refine ⟨3039479281276951419058837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4052639041702601892078449 3039479281276951419058837)
              ·
                refine ⟨142475591309857097768383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3039479281276951419058837 142475591309857097768383)
                ·
                  rfl

theorem cell21_1872924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 6].length) (baseStart_1872924 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1872924 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1872924 prefixEnd_1872924 := by exact prefixLift 1872924
  have htrace : WordTrace (prefixWord ++ tailWord_1872924) baseStart_1872924 baseEnd_1872924 := by
    simpa [prefixWord, tailWord_1872924, baseEnd_1872924] using wordTrace_append hprefix tailTrace_1872924
  have hstable : (prefixWord ++ tailWord_1872924).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1872924).length < 2 ^ (prefixWord ++ tailWord_1872924).sum := by decide
  have hdescent : baseEnd_1872924 < baseStart_1872924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1872924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873014 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_1873014 : Nat := 118140960795 + 1873014 * 2 ^ 59
def prefixEnd_1873014 : Nat := 4983230072969 + 3 ^ 40 * 1873014 * 2
def baseEnd_1873014 : Nat := 427447313155751136804965

theorem tailTrace_1873014 : CollatzResearch.WordTrace tailWord_1873014 prefixEnd_1873014 427447313155751136804965 := by
  unfold tailWord_1873014
  simp only [CollatzResearch.WordTrace]
  refine ⟨4269652052274852385558631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45542955224265092112625397 4269652052274852385558631)
  ·
    refine ⟨6404478078412278578337947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4269652052274852385558631 6404478078412278578337947)
    ·
      refine ⟨9606717117618417867506921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6404478078412278578337947 9606717117618417867506921)
      ·
        refine ⟨7205037838213813400630191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9606717117618417867506921 7205037838213813400630191)
        ·
          refine ⟨10807556757320720100945287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7205037838213813400630191 10807556757320720100945287)
          ·
            refine ⟨16211335135981080151417931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10807556757320720100945287 16211335135981080151417931)
            ·
              refine ⟨24317002703971620227126897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16211335135981080151417931 24317002703971620227126897)
              ·
                refine ⟨18237752027978715170345173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 24317002703971620227126897 18237752027978715170345173)
                ·
                  refine ⟨427447313155751136804965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18237752027978715170345173 427447313155751136804965)
                  ·
                    rfl

theorem cell21_1873014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_1873014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873014 prefixEnd_1873014 := by exact prefixLift 1873014
  have htrace : WordTrace (prefixWord ++ tailWord_1873014) baseStart_1873014 baseEnd_1873014 := by
    simpa [prefixWord, tailWord_1873014, baseEnd_1873014] using wordTrace_append hprefix tailTrace_1873014
  have hstable : (prefixWord ++ tailWord_1873014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873014).length < 2 ^ (prefixWord ++ tailWord_1873014).sum := by decide
  have hdescent : baseEnd_1873014 < baseStart_1873014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873135 : List Nat := [1, 1, 2, 1, 8, 8]
def baseStart_1873135 : Nat := 118140960795 + 1873135 * 2 ^ 59
def prefixEnd_1873135 : Nat := 4983230072969 + 3 ^ 40 * 1873135 * 2
def baseEnd_1873135 : Nat := 15832404703862289455113

theorem tailTrace_1873135 : CollatzResearch.WordTrace tailWord_1873135 prefixEnd_1873135 15832404703862289455113 := by
  unfold tailWord_1873135
  simp only [CollatzResearch.WordTrace]
  refine ⟨68318846068959275834092859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45545897379306183889395239 68318846068959275834092859)
  ·
    refine ⟨102478269103438913751139289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68318846068959275834092859 102478269103438913751139289)
    ·
      refine ⟨76858701827579185313354467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102478269103438913751139289 76858701827579185313354467)
      ·
        refine ⟨115288052741368777970031701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76858701827579185313354467 115288052741368777970031701)
        ·
          refine ⟨1351031868062915366836309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 115288052741368777970031701 1351031868062915366836309)
          ·
            refine ⟨15832404703862289455113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1351031868062915366836309 15832404703862289455113)
            ·
              rfl

theorem cell21_1873135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 8].length) (baseStart_1873135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873135 prefixEnd_1873135 := by exact prefixLift 1873135
  have htrace : WordTrace (prefixWord ++ tailWord_1873135) baseStart_1873135 baseEnd_1873135 := by
    simpa [prefixWord, tailWord_1873135, baseEnd_1873135] using wordTrace_append hprefix tailTrace_1873135
  have hstable : (prefixWord ++ tailWord_1873135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873135).length < 2 ^ (prefixWord ++ tailWord_1873135).sum := by decide
  have hdescent : baseEnd_1873135 < baseStart_1873135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873138 : List Nat := [3, 2, 1, 3, 3, 1, 2, 2, 4]
def baseStart_1873138 : Nat := 118140960795 + 1873138 * 2 ^ 59
def prefixEnd_1873138 : Nat := 4983230072969 + 3 ^ 40 * 1873138 * 2
def baseEnd_1873138 : Nat := 427475611645154476738045

theorem tailTrace_1873138 : CollatzResearch.WordTrace tailWord_1873138 prefixEnd_1873138 427475611645154476738045 := by
  unfold tailWord_1873138
  simp only [CollatzResearch.WordTrace]
  refine ⟨17079738871987101836613017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45545970325298938230968045 17079738871987101836613017)
  ·
    refine ⟨12809804153990326377459763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17079738871987101836613017 12809804153990326377459763)
    ·
      refine ⟨19214706230985489566189645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12809804153990326377459763 19214706230985489566189645)
      ·
        refine ⟨7205514836619558587321117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19214706230985489566189645 7205514836619558587321117)
        ·
          refine ⟨2702068063732334470245419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7205514836619558587321117 2702068063732334470245419)
          ·
            refine ⟨4053102095598501705368129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2702068063732334470245419 4053102095598501705368129)
            ·
              refine ⟨3039826571698876279026097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4053102095598501705368129 3039826571698876279026097)
              ·
                refine ⟨2279869928774157209269573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3039826571698876279026097 2279869928774157209269573)
                ·
                  refine ⟨427475611645154476738045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2279869928774157209269573 427475611645154476738045)
                  ·
                    rfl

theorem cell21_1873138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 2, 4].length) (baseStart_1873138 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873138 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873138 prefixEnd_1873138 := by exact prefixLift 1873138
  have htrace : WordTrace (prefixWord ++ tailWord_1873138) baseStart_1873138 baseEnd_1873138 := by
    simpa [prefixWord, tailWord_1873138, baseEnd_1873138] using wordTrace_append hprefix tailTrace_1873138
  have hstable : (prefixWord ++ tailWord_1873138).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873138).length < 2 ^ (prefixWord ++ tailWord_1873138).sum := by decide
  have hdescent : baseEnd_1873138 < baseStart_1873138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873166 : List Nat := [4, 1, 1, 2, 1, 4, 1, 2, 5]
def baseStart_1873166 : Nat := 118140960795 + 1873166 * 2 ^ 59
def prefixEnd_1873166 : Nat := 4983230072969 + 3 ^ 40 * 1873166 * 2
def baseEnd_1873166 : Nat := 427482001626632650271321

theorem tailTrace_1873166 : CollatzResearch.WordTrace tailWord_1873166 prefixEnd_1873166 427482001626632650271321 := by
  unfold tailWord_1873166
  simp only [CollatzResearch.WordTrace]
  refine ⟨8539997091480871016058919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45546651154564645418980901 8539997091480871016058919)
  ·
    refine ⟨12809995637221306524088379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8539997091480871016058919 12809995637221306524088379)
    ·
      refine ⟨19214993455831959786132569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12809995637221306524088379 19214993455831959786132569)
      ·
        refine ⟨14411245091873969839599427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19214993455831959786132569 14411245091873969839599427)
        ·
          refine ⟨21616867637810954759399141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14411245091873969839599427 21616867637810954759399141)
          ·
            refine ⟨4053162682089554017387339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21616867637810954759399141 4053162682089554017387339)
            ·
              refine ⟨6079744023134331026081009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4053162682089554017387339 6079744023134331026081009)
              ·
                refine ⟨4559808017350748269560757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6079744023134331026081009 4559808017350748269560757)
                ·
                  refine ⟨427482001626632650271321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4559808017350748269560757 427482001626632650271321)
                  ·
                    rfl

theorem cell21_1873166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 5].length) (baseStart_1873166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873166 prefixEnd_1873166 := by exact prefixLift 1873166
  have htrace : WordTrace (prefixWord ++ tailWord_1873166) baseStart_1873166 baseEnd_1873166 := by
    simpa [prefixWord, tailWord_1873166, baseEnd_1873166] using wordTrace_append hprefix tailTrace_1873166
  have hstable : (prefixWord ++ tailWord_1873166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873166).length < 2 ^ (prefixWord ++ tailWord_1873166).sum := by decide
  have hdescent : baseEnd_1873166 < baseStart_1873166 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873214 : List Nat := [4, 2, 1, 2, 1, 1, 5, 1, 4]
def baseStart_1873214 : Nat := 118140960795 + 1873214 * 2 ^ 59
def prefixEnd_1873214 : Nat := 4983230072969 + 3 ^ 40 * 1873214 * 2
def baseEnd_1873214 : Nat := 427492955880595233471223

theorem tailTrace_1873214 : CollatzResearch.WordTrace tailWord_1873214 prefixEnd_1873214 427492955880595233471223 := by
  unfold tailWord_1873214
  simp only [CollatzResearch.WordTrace]
  refine ⟨8540215929459134040777337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45547818290448714884145797 8540215929459134040777337)
  ·
    refine ⟨6405161947094350530583003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8540215929459134040777337 6405161947094350530583003)
    ·
      refine ⟨9607742920641525795874505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6405161947094350530583003 9607742920641525795874505)
      ·
        refine ⟨7205807190481144346905879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9607742920641525795874505 7205807190481144346905879)
        ·
          refine ⟨10808710785721716520358819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7205807190481144346905879 10808710785721716520358819)
          ·
            refine ⟨16213066178582574780538229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10808710785721716520358819 16213066178582574780538229)
            ·
              refine ⟨1519974954242116385675459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16213066178582574780538229 1519974954242116385675459)
              ·
                refine ⟨2279962431363174578513189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1519974954242116385675459 2279962431363174578513189)
                ·
                  refine ⟨427492955880595233471223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2279962431363174578513189 427492955880595233471223)
                  ·
                    rfl

theorem cell21_1873214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5, 1, 4].length) (baseStart_1873214 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873214 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873214 prefixEnd_1873214 := by exact prefixLift 1873214
  have htrace : WordTrace (prefixWord ++ tailWord_1873214) baseStart_1873214 baseEnd_1873214 := by
    simpa [prefixWord, tailWord_1873214, baseEnd_1873214] using wordTrace_append hprefix tailTrace_1873214
  have hstable : (prefixWord ++ tailWord_1873214).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873214).length < 2 ^ (prefixWord ++ tailWord_1873214).sum := by decide
  have hdescent : baseEnd_1873214 < baseStart_1873214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873225 : List Nat := [1, 2, 1, 1, 2, 3, 4, 2, 5]
def baseStart_1873225 : Nat := 118140960795 + 1873225 * 2 ^ 59
def prefixEnd_1873225 : Nat := 4983230072969 + 3 ^ 40 * 1873225 * 2
def baseEnd_1873225 : Nat := 427495466230461658787867

theorem tailTrace_1873225 : CollatzResearch.WordTrace tailWord_1873225 prefixEnd_1873225 427495466230461658787867 := by
  unfold tailWord_1873225
  simp only [CollatzResearch.WordTrace]
  refine ⟨68322128638633221204869129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45548085759088814136579419 68322128638633221204869129)
  ·
    refine ⟨51241596478974915903651847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68322128638633221204869129 51241596478974915903651847)
    ·
      refine ⟨76862394718462373855477771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51241596478974915903651847 76862394718462373855477771)
      ·
        refine ⟨115293592077693560783216657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76862394718462373855477771 115293592077693560783216657)
        ·
          refine ⟨86470194058270170587412493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 115293592077693560783216657 86470194058270170587412493)
          ·
            refine ⟨32426322771851313970279685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86470194058270170587412493 32426322771851313970279685)
            ·
              refine ⟨6079935519722121369427441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32426322771851313970279685 6079935519722121369427441)
              ·
                refine ⟨4559951639791591027070581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6079935519722121369427441 4559951639791591027070581)
                ·
                  refine ⟨427495466230461658787867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4559951639791591027070581 427495466230461658787867)
                  ·
                    rfl

theorem cell21_1873225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 5].length) (baseStart_1873225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873225 prefixEnd_1873225 := by exact prefixLift 1873225
  have htrace : WordTrace (prefixWord ++ tailWord_1873225) baseStart_1873225 baseEnd_1873225 := by
    simpa [prefixWord, tailWord_1873225, baseEnd_1873225] using wordTrace_append hprefix tailTrace_1873225
  have hstable : (prefixWord ++ tailWord_1873225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873225).length < 2 ^ (prefixWord ++ tailWord_1873225).sum := by decide
  have hdescent : baseEnd_1873225 < baseStart_1873225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873228 : List Nat := [2, 2, 1, 3, 2, 4, 2, 5]
def baseStart_1873228 : Nat := 118140960795 + 1873228 * 2 ^ 59
def prefixEnd_1873228 : Nat := 4983230072969 + 3 ^ 40 * 1873228 * 2
def baseEnd_1873228 : Nat := 142498716957111440079287

theorem tailTrace_1873228 : CollatzResearch.WordTrace tailWord_1873228 prefixEnd_1873228 142498716957111440079287 := by
  unfold tailWord_1873228
  simp only [CollatzResearch.WordTrace]
  refine ⟨34161119028811176358614169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45548158705081568478152225 34161119028811176358614169)
  ·
    refine ⟨25620839271608382268960627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34161119028811176358614169 25620839271608382268960627)
    ·
      refine ⟨38431258907412573403440941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25620839271608382268960627 38431258907412573403440941)
      ·
        refine ⟨14411722090279715026290353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38431258907412573403440941 14411722090279715026290353)
        ·
          refine ⟨10808791567709786269717765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14411722090279715026290353 10808791567709786269717765)
          ·
            refine ⟨2026648418945584925572081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10808791567709786269717765 2026648418945584925572081)
            ·
              refine ⟨1519986314209188694179061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2026648418945584925572081 1519986314209188694179061)
              ·
                refine ⟨142498716957111440079287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1519986314209188694179061 142498716957111440079287)
                ·
                  rfl

theorem cell21_1873228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 5].length) (baseStart_1873228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873228 prefixEnd_1873228 := by exact prefixLift 1873228
  have htrace : WordTrace (prefixWord ++ tailWord_1873228) baseStart_1873228 baseEnd_1873228 := by
    simpa [prefixWord, tailWord_1873228, baseEnd_1873228] using wordTrace_append hprefix tailTrace_1873228
  have hstable : (prefixWord ++ tailWord_1873228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873228).length < 2 ^ (prefixWord ++ tailWord_1873228).sum := by decide
  have hdescent : baseEnd_1873228 < baseStart_1873228 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873273 : List Nat := [1, 2, 1, 3, 2, 1, 6, 1, 4]
def baseStart_1873273 : Nat := 118140960795 + 1873273 * 2 ^ 59
def prefixEnd_1873273 : Nat := 4983230072969 + 3 ^ 40 * 1873273 * 2
def baseEnd_1873273 : Nat := 427506420484424241987769

theorem tailTrace_1873273 : CollatzResearch.WordTrace tailWord_1873273 prefixEnd_1873273 427506420484424241987769 := by
  unfold tailWord_1873273
  simp only [CollatzResearch.WordTrace]
  refine ⟨68323879342459325402616473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45549252894972883601744315 68323879342459325402616473)
  ·
    refine ⟨51242909506844494051962355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68323879342459325402616473 51242909506844494051962355)
    ·
      refine ⟨76864364260266741077943533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51242909506844494051962355 76864364260266741077943533)
      ·
        refine ⟨28824136597600027904228825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76864364260266741077943533 28824136597600027904228825)
        ·
          refine ⟨21618102448200020928171619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28824136597600027904228825 21618102448200020928171619)
          ·
            refine ⟨32427153672300031392257429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21618102448200020928171619 32427153672300031392257429)
            ·
              refine ⟨1520022828389063971512067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32427153672300031392257429 1520022828389063971512067)
              ·
                refine ⟨2280034242583595957268101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1520022828389063971512067 2280034242583595957268101)
                ·
                  refine ⟨427506420484424241987769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2280034242583595957268101 427506420484424241987769)
                  ·
                    rfl

theorem cell21_1873273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 4].length) (baseStart_1873273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873273 prefixEnd_1873273 := by exact prefixLift 1873273
  have htrace : WordTrace (prefixWord ++ tailWord_1873273) baseStart_1873273 baseEnd_1873273 := by
    simpa [prefixWord, tailWord_1873273, baseEnd_1873273] using wordTrace_append hprefix tailTrace_1873273
  have hstable : (prefixWord ++ tailWord_1873273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873273).length < 2 ^ (prefixWord ++ tailWord_1873273).sum := by decide
  have hdescent : baseEnd_1873273 < baseStart_1873273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873310 : List Nat := [4, 3, 1, 2, 2, 2, 2, 2, 3]
def baseStart_1873310 : Nat := 118140960795 + 1873310 * 2 ^ 59
def prefixEnd_1873310 : Nat := 4983230072969 + 3 ^ 40 * 1873310 * 2
def baseEnd_1873310 : Nat := 427514864388520399871027

theorem tailTrace_1873310 : CollatzResearch.WordTrace tailWord_1873310 prefixEnd_1873310 427514864388520399871027 := by
  unfold tailWord_1873310
  simp only [CollatzResearch.WordTrace]
  refine ⟨8540653605415660090214173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45550152562216853814475589 8540653605415660090214173)
  ·
    refine ⟨3202745102030872533830315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8540653605415660090214173 3202745102030872533830315)
    ·
      refine ⟨4804117653046308800745473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3202745102030872533830315 4804117653046308800745473)
      ·
        refine ⟨3603088239784731600559105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4804117653046308800745473 3603088239784731600559105)
        ·
          refine ⟨2702316179838548700419329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3603088239784731600559105 2702316179838548700419329)
          ·
            refine ⟨2026737134878911525314497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2702316179838548700419329 2026737134878911525314497)
            ·
              refine ⟨1520052851159183643985873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2026737134878911525314497 1520052851159183643985873)
              ·
                refine ⟨1140039638369387732989405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1520052851159183643985873 1140039638369387732989405)
                ·
                  refine ⟨427514864388520399871027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1140039638369387732989405 427514864388520399871027)
                  ·
                    rfl

theorem cell21_1873310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_1873310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873310 prefixEnd_1873310 := by exact prefixLift 1873310
  have htrace : WordTrace (prefixWord ++ tailWord_1873310) baseStart_1873310 baseEnd_1873310 := by
    simpa [prefixWord, tailWord_1873310, baseEnd_1873310] using wordTrace_append hprefix tailTrace_1873310
  have hstable : (prefixWord ++ tailWord_1873310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873310).length < 2 ^ (prefixWord ++ tailWord_1873310).sum := by decide
  have hdescent : baseEnd_1873310 < baseStart_1873310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873366 : List Nat := [5, 2, 1, 1, 1, 2, 3, 2, 4]
def baseStart_1873366 : Nat := 118140960795 + 1873366 * 2 ^ 59
def prefixEnd_1873366 : Nat := 4983230072969 + 3 ^ 40 * 1873366 * 2
def baseEnd_1873366 : Nat := 427527644351476746937579

theorem tailTrace_1873366 : CollatzResearch.WordTrace tailWord_1873366 prefixEnd_1873366 427527644351476746937579 := by
  unfold tailWord_1873366
  simp only [CollatzResearch.WordTrace]
  refine ⟨4270454458195150142859497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45551514220748268190501301 4270454458195150142859497)
  ·
    refine ⟨3202840843646362607144623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4270454458195150142859497 3202840843646362607144623)
    ·
      refine ⟨4804261265469543910716935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3202840843646362607144623 4804261265469543910716935)
      ·
        refine ⟨7206391898204315866075403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4804261265469543910716935 7206391898204315866075403)
        ·
          refine ⟨10809587847306473799113105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7206391898204315866075403 10809587847306473799113105)
          ·
            refine ⟨8107190885479855349334829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10809587847306473799113105 8107190885479855349334829)
            ·
              refine ⟨3040196582054945756000561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8107190885479855349334829 3040196582054945756000561)
              ·
                refine ⟨2280147436541209317000421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3040196582054945756000561 2280147436541209317000421)
                ·
                  refine ⟨427527644351476746937579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2280147436541209317000421 427527644351476746937579)
                  ·
                    rfl

theorem cell21_1873366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_1873366 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873366 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873366 prefixEnd_1873366 := by exact prefixLift 1873366
  have htrace : WordTrace (prefixWord ++ tailWord_1873366) baseStart_1873366 baseEnd_1873366 := by
    simpa [prefixWord, tailWord_1873366, baseEnd_1873366] using wordTrace_append hprefix tailTrace_1873366
  have hstable : (prefixWord ++ tailWord_1873366).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873366).length < 2 ^ (prefixWord ++ tailWord_1873366).sum := by decide
  have hdescent : baseEnd_1873366 < baseStart_1873366 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873377 : List Nat := [1, 2, 3, 1, 2, 3, 1, 3, 5]
def baseStart_1873377 : Nat := 118140960795 + 1873377 * 2 ^ 59
def prefixEnd_1873377 : Nat := 4983230072969 + 3 ^ 40 * 1873377 * 2
def baseEnd_1873377 : Nat := 427530154701343172254223

theorem tailTrace_1873377 : CollatzResearch.WordTrace tailWord_1873377 prefixEnd_1873377 427530154701343172254223 := by
  unfold tailWord_1873377
  simp only [CollatzResearch.WordTrace]
  refine ⟨68327672534082551164402385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45551781689388367442934923 68327672534082551164402385)
  ·
    refine ⟨51245754400561913373301789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68327672534082551164402385 51245754400561913373301789)
    ·
      refine ⟨19217157900210717514988171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51245754400561913373301789 19217157900210717514988171)
      ·
        refine ⟨28825736850316076272482257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19217157900210717514988171 28825736850316076272482257)
        ·
          refine ⟨21619302637737057204361693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28825736850316076272482257 21619302637737057204361693)
          ·
            refine ⟨8107238489151396451635635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21619302637737057204361693 8107238489151396451635635)
            ·
              refine ⟨12160857733727094677453453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8107238489151396451635635 12160857733727094677453453)
              ·
                refine ⟨4560321650147660504045045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 12160857733727094677453453 4560321650147660504045045)
                ·
                  refine ⟨427530154701343172254223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4560321650147660504045045 427530154701343172254223)
                  ·
                    rfl

theorem cell21_1873377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 5].length) (baseStart_1873377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873377 prefixEnd_1873377 := by exact prefixLift 1873377
  have htrace : WordTrace (prefixWord ++ tailWord_1873377) baseStart_1873377 baseEnd_1873377 := by
    simpa [prefixWord, tailWord_1873377, baseEnd_1873377] using wordTrace_append hprefix tailTrace_1873377
  have hstable : (prefixWord ++ tailWord_1873377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873377).length < 2 ^ (prefixWord ++ tailWord_1873377).sum := by decide
  have hdescent : baseEnd_1873377 < baseStart_1873377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873394 : List Nat := [3, 2, 1, 4, 1, 1, 2, 2, 5]
def baseStart_1873394 : Nat := 118140960795 + 1873394 * 2 ^ 59
def prefixEnd_1873394 : Nat := 4983230072969 + 3 ^ 40 * 1873394 * 2
def baseEnd_1873394 : Nat := 427534034332954920470855

theorem tailTrace_1873394 : CollatzResearch.WordTrace tailWord_1873394 prefixEnd_1873394 427534034332954920470855 := by
  unfold tailWord_1873394
  simp only [CollatzResearch.WordTrace]
  refine ⟨17082073143755240766942809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45552195050013975378514157 17082073143755240766942809)
  ·
    refine ⟨12811554857816430575207107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17082073143755240766942809 12811554857816430575207107)
    ·
      refine ⟨19217332286724645862810661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12811554857816430575207107 19217332286724645862810661)
      ·
        refine ⟨3603249803760871099276999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19217332286724645862810661 3603249803760871099276999)
        ·
          refine ⟨5404874705641306648915499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3603249803760871099276999 5404874705641306648915499)
          ·
            refine ⟨8107312058461959973373249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5404874705641306648915499 8107312058461959973373249)
            ·
              refine ⟨6080484043846469980029937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8107312058461959973373249 6080484043846469980029937)
              ·
                refine ⟨4560363032884852485022453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6080484043846469980029937 4560363032884852485022453)
                ·
                  refine ⟨427534034332954920470855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4560363032884852485022453 427534034332954920470855)
                  ·
                    rfl

theorem cell21_1873394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_1873394 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873394 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873394 prefixEnd_1873394 := by exact prefixLift 1873394
  have htrace : WordTrace (prefixWord ++ tailWord_1873394) baseStart_1873394 baseEnd_1873394 := by
    simpa [prefixWord, tailWord_1873394, baseEnd_1873394] using wordTrace_append hprefix tailTrace_1873394
  have hstable : (prefixWord ++ tailWord_1873394).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873394).length < 2 ^ (prefixWord ++ tailWord_1873394).sum := by decide
  have hdescent : baseEnd_1873394 < baseStart_1873394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873397 : List Nat := [1, 3, 5, 1, 1, 3, 2, 5]
def baseStart_1873397 : Nat := 118140960795 + 1873397 * 2 ^ 59
def prefixEnd_1873397 : Nat := 4983230072969 + 3 ^ 40 * 1873397 * 2
def baseEnd_1873397 : Nat := 142511572991275860640283

theorem tailTrace_1873397 : CollatzResearch.WordTrace tailWord_1873397 prefixEnd_1873397 142511572991275860640283 := by
  unfold tailWord_1873397
  simp only [CollatzResearch.WordTrace]
  refine ⟨68328401994010094580130445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45552267996006729720086963 68328401994010094580130445)
  ·
    refine ⟨25623150747753785467548917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68328401994010094580130445 25623150747753785467548917)
    ·
      refine ⟨2402170382601917387582711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 25623150747753785467548917 2402170382601917387582711)
      ·
        refine ⟨3603255573902876081374067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2402170382601917387582711 3603255573902876081374067)
        ·
          refine ⟨5404883360854314122061101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3603255573902876081374067 5404883360854314122061101)
          ·
            refine ⟨2026831260320367795772913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5404883360854314122061101 2026831260320367795772913)
            ·
              refine ⟨1520123445240275846829685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2026831260320367795772913 1520123445240275846829685)
              ·
                refine ⟨142511572991275860640283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1520123445240275846829685 142511572991275860640283)
                ·
                  rfl

theorem cell21_1873397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 2, 5].length) (baseStart_1873397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873397 prefixEnd_1873397 := by exact prefixLift 1873397
  have htrace : WordTrace (prefixWord ++ tailWord_1873397) baseStart_1873397 baseEnd_1873397 := by
    simpa [prefixWord, tailWord_1873397, baseEnd_1873397] using wordTrace_append hprefix tailTrace_1873397
  have hstable : (prefixWord ++ tailWord_1873397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873397).length < 2 ^ (prefixWord ++ tailWord_1873397).sum := by decide
  have hdescent : baseEnd_1873397 < baseStart_1873397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873414 : List Nat := [6, 2, 1, 1, 2, 2, 7]
def baseStart_1873414 : Nat := 118140960795 + 1873414 * 2 ^ 59
def prefixEnd_1873414 : Nat := 4983230072969 + 3 ^ 40 * 1873414 * 2
def baseEnd_1873414 : Nat := 47504288733937703348609

theorem tailTrace_1873414 : CollatzResearch.WordTrace tailWord_1873414 prefixEnd_1873414 47504288733937703348609 := by
  unfold tailWord_1873414
  simp only [CollatzResearch.WordTrace]
  refine ⟨2135281938592140827609353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 45552681356632337655666197 2135281938592140827609353)
  ·
    refine ⟨1601461453944105620707015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2135281938592140827609353 1601461453944105620707015)
    ·
      refine ⟨2402192180916158431060523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1601461453944105620707015 2402192180916158431060523)
      ·
        refine ⟨3603288271374237646590785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2402192180916158431060523 3603288271374237646590785)
        ·
          refine ⟨2702466203530678234943089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3603288271374237646590785 2702466203530678234943089)
          ·
            refine ⟨2026849652648008676207317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2702466203530678234943089 2026849652648008676207317)
            ·
              refine ⟨47504288733937703348609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2026849652648008676207317 47504288733937703348609)
              ·
                rfl

theorem cell21_1873414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 7].length) (baseStart_1873414 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873414 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873414 prefixEnd_1873414 := by exact prefixLift 1873414
  have htrace : WordTrace (prefixWord ++ tailWord_1873414) baseStart_1873414 baseEnd_1873414 := by
    simpa [prefixWord, tailWord_1873414, baseEnd_1873414] using wordTrace_append hprefix tailTrace_1873414
  have hstable : (prefixWord ++ tailWord_1873414).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873414).length < 2 ^ (prefixWord ++ tailWord_1873414).sum := by decide
  have hdescent : baseEnd_1873414 < baseStart_1873414 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873428 : List Nat := [2, 4, 3, 1, 2, 2, 1, 1, 5]
def baseStart_1873428 : Nat := 118140960795 + 1873428 * 2 ^ 59
def prefixEnd_1873428 : Nat := 4983230072969 + 3 ^ 40 * 1873428 * 2
def baseEnd_1873428 : Nat := 427541793596178416904119

theorem tailTrace_1873428 : CollatzResearch.WordTrace tailWord_1873428 prefixEnd_1873428 427541793596178416904119 := by
  unfold tailWord_1873428
  simp only [CollatzResearch.WordTrace]
  refine ⟨34164766328448893437254469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45553021771265191249672625 34164766328448893437254469)
  ·
    refine ⟨6405893686584167519485213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34164766328448893437254469 6405893686584167519485213)
    ·
      refine ⟨2402210132469062819806955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6405893686584167519485213 2402210132469062819806955)
      ·
        refine ⟨3603315198703594229710433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2402210132469062819806955 3603315198703594229710433)
        ·
          refine ⟨2702486399027695672282825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3603315198703594229710433 2702486399027695672282825)
          ·
            refine ⟨2026864799270771754212119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2702486399027695672282825 2026864799270771754212119)
            ·
              refine ⟨3040297198906157631318179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2026864799270771754212119 3040297198906157631318179)
              ·
                refine ⟨4560445798359236446977269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3040297198906157631318179 4560445798359236446977269)
                ·
                  refine ⟨427541793596178416904119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4560445798359236446977269 427541793596178416904119)
                  ·
                    rfl

theorem cell21_1873428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 5].length) (baseStart_1873428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873428 prefixEnd_1873428 := by exact prefixLift 1873428
  have htrace : WordTrace (prefixWord ++ tailWord_1873428) baseStart_1873428 baseEnd_1873428 := by
    simpa [prefixWord, tailWord_1873428, baseEnd_1873428] using wordTrace_append hprefix tailTrace_1873428
  have hstable : (prefixWord ++ tailWord_1873428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873428).length < 2 ^ (prefixWord ++ tailWord_1873428).sum := by decide
  have hdescent : baseEnd_1873428 < baseStart_1873428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873484 : List Nat := [2, 2, 1, 3, 1, 3, 1, 4, 4]
def baseStart_1873484 : Nat := 118140960795 + 1873484 * 2 ^ 59
def prefixEnd_1873484 : Nat := 4983230072969 + 3 ^ 40 * 1873484 * 2
def baseEnd_1873484 : Nat := 427554573559134763970671

theorem tailTrace_1873484 : CollatzResearch.WordTrace tailWord_1873484 prefixEnd_1873484 427554573559134763970671 := by
  unfold tailWord_1873484
  simp only [CollatzResearch.WordTrace]
  refine ⟨34165787572347454219273753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45554383429796605625698337 34165787572347454219273753)
  ·
    refine ⟨25624340679260590664455315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34165787572347454219273753 25624340679260590664455315)
    ·
      refine ⟨38436511018890885996682973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25624340679260590664455315 38436511018890885996682973)
      ·
        refine ⟨14413691632084082248756115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38436511018890885996682973 14413691632084082248756115)
        ·
          refine ⟨21620537448126123373134173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14413691632084082248756115 21620537448126123373134173)
          ·
            refine ⟨8107701543047296264925315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21620537448126123373134173 8107701543047296264925315)
            ·
              refine ⟨12161552314570944397387973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8107701543047296264925315 12161552314570944397387973)
              ·
                refine ⟨2280291058982052074510245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12161552314570944397387973 2280291058982052074510245)
                ·
                  refine ⟨427554573559134763970671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2280291058982052074510245 427554573559134763970671)
                  ·
                    rfl

theorem cell21_1873484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_1873484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873484 prefixEnd_1873484 := by exact prefixLift 1873484
  have htrace : WordTrace (prefixWord ++ tailWord_1873484) baseStart_1873484 baseEnd_1873484 := by
    simpa [prefixWord, tailWord_1873484, baseEnd_1873484] using wordTrace_append hprefix tailTrace_1873484
  have hstable : (prefixWord ++ tailWord_1873484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873484).length < 2 ^ (prefixWord ++ tailWord_1873484).sum := by decide
  have hdescent : baseEnd_1873484 < baseStart_1873484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873546 : List Nat := [3, 1, 2, 3, 2, 2, 2, 1, 5]
def baseStart_1873546 : Nat := 118140960795 + 1873546 * 2 ^ 59
def prefixEnd_1873546 : Nat := 4983230072969 + 3 ^ 40 * 1873546 * 2
def baseEnd_1873546 : Nat := 427568722803836433937211

theorem tailTrace_1873546 : CollatzResearch.WordTrace tailWord_1873546 prefixEnd_1873546 427568722803836433937211 := by
  unfold tailWord_1873546
  simp only [CollatzResearch.WordTrace]
  refine ⟨17083459117617573256826123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45555890980313528684869661 17083459117617573256826123)
  ·
    refine ⟨25625188676426359885239185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17083459117617573256826123 25625188676426359885239185)
    ·
      refine ⟨19218891507319769913929389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25625188676426359885239185 19218891507319769913929389)
      ·
        refine ⟨7207084315244913717723521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19218891507319769913929389 7207084315244913717723521)
        ·
          refine ⟨5405313236433685288292641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7207084315244913717723521 5405313236433685288292641)
          ·
            refine ⟨4053984927325263966219481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5405313236433685288292641 4053984927325263966219481)
            ·
              refine ⟨3040488695493947974664611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4053984927325263966219481 3040488695493947974664611)
              ·
                refine ⟨4560733043240921961996917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3040488695493947974664611 4560733043240921961996917)
                ·
                  refine ⟨427568722803836433937211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4560733043240921961996917 427568722803836433937211)
                  ·
                    rfl

theorem cell21_1873546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 5].length) (baseStart_1873546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873546 prefixEnd_1873546 := by exact prefixLift 1873546
  have htrace : WordTrace (prefixWord ++ tailWord_1873546) baseStart_1873546 baseEnd_1873546 := by
    simpa [prefixWord, tailWord_1873546, baseEnd_1873546] using wordTrace_append hprefix tailTrace_1873546
  have hstable : (prefixWord ++ tailWord_1873546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873546).length < 2 ^ (prefixWord ++ tailWord_1873546).sum := by decide
  have hdescent : baseEnd_1873546 < baseStart_1873546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873695 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 6]
def baseStart_1873695 : Nat := 118140960795 + 1873695 * 2 ^ 59
def prefixEnd_1873695 : Nat := 4983230072969 + 3 ^ 40 * 1873695 * 2
def baseEnd_1873695 : Nat := 427602726633845285953573

theorem tailTrace_1873695 : CollatzResearch.WordTrace tailWord_1873695 prefixEnd_1873695 427602726633845285953573 := by
  unfold tailWord_1873695
  simp only [CollatzResearch.WordTrace]
  refine ⟨68339270946930491474478539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45559513964620327649652359 68339270946930491474478539)
  ·
    refine ⟨102508906420395737211717809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68339270946930491474478539 102508906420395737211717809)
    ·
      refine ⟨76881679815296802908788357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102508906420395737211717809 76881679815296802908788357)
      ·
        refine ⟨14415314965368150545397817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 76881679815296802908788357 14415314965368150545397817)
        ·
          refine ⟨10811486224026112909048363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14415314965368150545397817 10811486224026112909048363)
          ·
            refine ⟨16217229336039169363572545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10811486224026112909048363 16217229336039169363572545)
            ·
              refine ⟨12162922002029377022679409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16217229336039169363572545 12162922002029377022679409)
              ·
                refine ⟨9122191501522032767009557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 12162922002029377022679409 9122191501522032767009557)
                ·
                  refine ⟨427602726633845285953573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9122191501522032767009557 427602726633845285953573)
                  ·
                    rfl

theorem cell21_1873695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 6].length) (baseStart_1873695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873695 prefixEnd_1873695 := by exact prefixLift 1873695
  have htrace : WordTrace (prefixWord ++ tailWord_1873695) baseStart_1873695 baseEnd_1873695 := by
    simpa [prefixWord, tailWord_1873695, baseEnd_1873695] using wordTrace_append hprefix tailTrace_1873695
  have hstable : (prefixWord ++ tailWord_1873695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873695).length < 2 ^ (prefixWord ++ tailWord_1873695).sum := by decide
  have hdescent : baseEnd_1873695 < baseStart_1873695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873771 : List Nat := [1, 1, 1, 1, 2, 2, 3, 6, 4]
def baseStart_1873771 : Nat := 118140960795 + 1873771 * 2 ^ 59
def prefixEnd_1873771 : Nat := 4983230072969 + 3 ^ 40 * 1873771 * 2
def baseEnd_1873771 : Nat := 427620070869286042686751

theorem tailTrace_1873771 : CollatzResearch.WordTrace tailWord_1873771 prefixEnd_1873771 427620070869286042686751 := by
  unfold tailWord_1873771
  simp only [CollatzResearch.WordTrace]
  refine ⟨68342042894655156454245167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45561361929770104302830111 68342042894655156454245167)
  ·
    refine ⟨102513064341982734681367751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68342042894655156454245167 102513064341982734681367751)
    ·
      refine ⟨153769596512974102022051627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102513064341982734681367751 153769596512974102022051627)
      ·
        refine ⟨230654394769461153033077441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 153769596512974102022051627 230654394769461153033077441)
        ·
          refine ⟨172990796077095864774808081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 230654394769461153033077441 172990796077095864774808081)
          ·
            refine ⟨129743097057821898581106061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 172990796077095864774808081 129743097057821898581106061)
            ·
              refine ⟨48653661396683211967914773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 129743097057821898581106061 48653661396683211967914773)
              ·
                refine ⟨2280640377969525560996005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 48653661396683211967914773 2280640377969525560996005)
                ·
                  refine ⟨427620070869286042686751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2280640377969525560996005 427620070869286042686751)
                  ·
                    rfl

theorem cell21_1873771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 6, 4].length) (baseStart_1873771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873771 prefixEnd_1873771 := by exact prefixLift 1873771
  have htrace : WordTrace (prefixWord ++ tailWord_1873771) baseStart_1873771 baseEnd_1873771 := by
    simpa [prefixWord, tailWord_1873771, baseEnd_1873771] using wordTrace_append hprefix tailTrace_1873771
  have hstable : (prefixWord ++ tailWord_1873771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873771).length < 2 ^ (prefixWord ++ tailWord_1873771).sum := by decide
  have hdescent : baseEnd_1873771 < baseStart_1873771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873774 : List Nat := [4, 1, 2, 3, 1, 1, 3, 1, 5]
def baseStart_1873774 : Nat := 118140960795 + 1873774 * 2 ^ 59
def prefixEnd_1873774 : Nat := 4983230072969 + 3 ^ 40 * 1873774 * 2
def baseEnd_1873774 : Nat := 427620755510158704136745

theorem tailTrace_1873774 : CollatzResearch.WordTrace tailWord_1873774 prefixEnd_1873774 427620755510158704136745 := by
  unfold tailWord_1873774
  simp only [CollatzResearch.WordTrace]
  refine ⟨8542769039205535995825547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45561434875762858644402917 8542769039205535995825547)
  ·
    refine ⟨12814153558808303993738321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8542769039205535995825547 12814153558808303993738321)
    ·
      refine ⟨9610615169106227995303741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12814153558808303993738321 9610615169106227995303741)
      ·
        refine ⟨3603980688414835498238903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9610615169106227995303741 3603980688414835498238903)
        ·
          refine ⟨5405971032622253247358355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3603980688414835498238903 5405971032622253247358355)
          ·
            refine ⟨8108956548933379871037533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5405971032622253247358355 8108956548933379871037533)
            ·
              refine ⟨3040858705850017451639075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8108956548933379871037533 3040858705850017451639075)
              ·
                refine ⟨4561288058775026177458613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3040858705850017451639075 4561288058775026177458613)
                ·
                  refine ⟨427620755510158704136745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4561288058775026177458613 427620755510158704136745)
                  ·
                    rfl

theorem cell21_1873774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_1873774 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873774 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873774 prefixEnd_1873774 := by exact prefixLift 1873774
  have htrace : WordTrace (prefixWord ++ tailWord_1873774) baseStart_1873774 baseEnd_1873774 := by
    simpa [prefixWord, tailWord_1873774, baseEnd_1873774] using wordTrace_append hprefix tailTrace_1873774
  have hstable : (prefixWord ++ tailWord_1873774).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873774).length < 2 ^ (prefixWord ++ tailWord_1873774).sum := by decide
  have hdescent : baseEnd_1873774 < baseStart_1873774 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873825 : List Nat := [1, 2, 3, 4, 3, 1, 2, 2, 3]
def baseStart_1873825 : Nat := 118140960795 + 1873825 * 2 ^ 59
def prefixEnd_1873825 : Nat := 4983230072969 + 3 ^ 40 * 1873825 * 2
def baseEnd_1873825 : Nat := 427632394404993948786641

theorem tailTrace_1873825 : CollatzResearch.WordTrace tailWord_1873825 prefixEnd_1873825 427632394404993948786641 := by
  unfold tailWord_1873825
  simp only [CollatzResearch.WordTrace]
  refine ⟨68344012436459523676710929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45562674957639682451140619 68344012436459523676710929)
  ·
    refine ⟨51258009327344642757533197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68344012436459523676710929 51258009327344642757533197)
    ·
      refine ⟨19221753497754241034074949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51258009327344642757533197 19221753497754241034074949)
      ·
        refine ⟨3604078780828920193889053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19221753497754241034074949 3604078780828920193889053)
        ·
          refine ⟨1351529542810845072708395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3604078780828920193889053 1351529542810845072708395)
          ·
            refine ⟨2027294314216267609062593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351529542810845072708395 2027294314216267609062593)
            ·
              refine ⟨1520470735662200706796945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2027294314216267609062593 1520470735662200706796945)
              ·
                refine ⟨1140353051746650530097709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1520470735662200706796945 1140353051746650530097709)
                ·
                  refine ⟨427632394404993948786641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1140353051746650530097709 427632394404993948786641)
                  ·
                    rfl

theorem cell21_1873825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 2, 3].length) (baseStart_1873825 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873825 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873825 prefixEnd_1873825 := by exact prefixLift 1873825
  have htrace : WordTrace (prefixWord ++ tailWord_1873825) baseStart_1873825 baseEnd_1873825 := by
    simpa [prefixWord, tailWord_1873825, baseEnd_1873825] using wordTrace_append hprefix tailTrace_1873825
  have hstable : (prefixWord ++ tailWord_1873825).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873825).length < 2 ^ (prefixWord ++ tailWord_1873825).sum := by decide
  have hdescent : baseEnd_1873825 < baseStart_1873825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873881 : List Nat := [1, 2, 1, 2, 6, 2, 1, 2, 4]
def baseStart_1873881 : Nat := 118140960795 + 1873881 * 2 ^ 59
def prefixEnd_1873881 : Nat := 4983230072969 + 3 ^ 40 * 1873881 * 2
def baseEnd_1873881 : Nat := 427645174367950295853193

theorem tailTrace_1873881 : CollatzResearch.WordTrace tailWord_1873881 prefixEnd_1873881 427645174367950295853193 := by
  unfold tailWord_1873881
  simp only [CollatzResearch.WordTrace]
  refine ⟨68346054924256645240749497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45564036616171096827166331 68346054924256645240749497)
  ·
    refine ⟨51259541193192483930562123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68346054924256645240749497 51259541193192483930562123)
    ·
      refine ⟨76889311789788725895843185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51259541193192483930562123 76889311789788725895843185)
      ·
        refine ⟨57666983842341544421882389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76889311789788725895843185 57666983842341544421882389)
        ·
          refine ⟨2703139867609759894775737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57666983842341544421882389 2703139867609759894775737)
          ·
            refine ⟨2027354900707319921081803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2703139867609759894775737 2027354900707319921081803)
            ·
              refine ⟨3041032351060979881622705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027354900707319921081803 3041032351060979881622705)
              ·
                refine ⟨2280774263295734911217029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3041032351060979881622705 2280774263295734911217029)
                ·
                  refine ⟨427645174367950295853193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2280774263295734911217029 427645174367950295853193)
                  ·
                    rfl

theorem cell21_1873881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 4].length) (baseStart_1873881 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873881 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873881 prefixEnd_1873881 := by exact prefixLift 1873881
  have htrace : WordTrace (prefixWord ++ tailWord_1873881) baseStart_1873881 baseEnd_1873881 := by
    simpa [prefixWord, tailWord_1873881, baseEnd_1873881] using wordTrace_append hprefix tailTrace_1873881
  have hstable : (prefixWord ++ tailWord_1873881).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873881).length < 2 ^ (prefixWord ++ tailWord_1873881).sum := by decide
  have hdescent : baseEnd_1873881 < baseStart_1873881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873884 : List Nat := [2, 2, 6, 1, 1, 1, 2, 1, 5]
def baseStart_1873884 : Nat := 118140960795 + 1873884 * 2 ^ 59
def prefixEnd_1873884 : Nat := 4983230072969 + 3 ^ 40 * 1873884 * 2
def baseEnd_1873884 : Nat := 427645859008822957303187

theorem tailTrace_1873884 : CollatzResearch.WordTrace tailWord_1873884 prefixEnd_1873884 427645859008822957303187 := by
  unfold tailWord_1873884
  simp only [CollatzResearch.WordTrace]
  refine ⟨34173082171622888376554353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45564109562163851168739137 34173082171622888376554353)
  ·
    refine ⟨25629811628717166282415765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34173082171622888376554353 25629811628717166282415765)
    ·
      refine ⟨1201397420096117169488239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 25629811628717166282415765 1201397420096117169488239)
      ·
        refine ⟨1802096130144175754232359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1201397420096117169488239 1802096130144175754232359)
        ·
          refine ⟨2703144195216263631348539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1802096130144175754232359 2703144195216263631348539)
          ·
            refine ⟨4054716292824395447022809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2703144195216263631348539 4054716292824395447022809)
            ·
              refine ⟨3041037219618296585267107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4054716292824395447022809 3041037219618296585267107)
              ·
                refine ⟨4561555829427444877900661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3041037219618296585267107 4561555829427444877900661)
                ·
                  refine ⟨427645859008822957303187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4561555829427444877900661 427645859008822957303187)
                  ·
                    rfl

theorem cell21_1873884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 5].length) (baseStart_1873884 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873884 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873884 prefixEnd_1873884 := by exact prefixLift 1873884
  have htrace : WordTrace (prefixWord ++ tailWord_1873884) baseStart_1873884 baseEnd_1873884 := by
    simpa [prefixWord, tailWord_1873884, baseEnd_1873884] using wordTrace_append hprefix tailTrace_1873884
  have hstable : (prefixWord ++ tailWord_1873884).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873884).length < 2 ^ (prefixWord ++ tailWord_1873884).sum := by decide
  have hdescent : baseEnd_1873884 < baseStart_1873884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873943 : List Nat := [1, 1, 3, 5, 3, 1, 1, 1, 5]
def baseStart_1873943 : Nat := 118140960795 + 1873943 * 2 ^ 59
def prefixEnd_1873943 : Nat := 4983230072969 + 3 ^ 40 * 1873943 * 2
def baseEnd_1873943 : Nat := 427659323612651965819733

theorem tailTrace_1873943 : CollatzResearch.WordTrace tailWord_1873943 prefixEnd_1873943 427659323612651965819733 := by
  unfold tailWord_1873943
  simp only [CollatzResearch.WordTrace]
  refine ⟨68348316250032029829506483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45565544166688019886337655 68348316250032029829506483)
  ·
    refine ⟨102522474375048044744259725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68348316250032029829506483 102522474375048044744259725)
    ·
      refine ⟨38445927890643016779097397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102522474375048044744259725 38445927890643016779097397)
      ·
        refine ⟨3604305739747782823040381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38445927890643016779097397 3604305739747782823040381)
        ·
          refine ⟨1351614652405418558640143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3604305739747782823040381 1351614652405418558640143)
          ·
            refine ⟨2027421978608127837960215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1351614652405418558640143 2027421978608127837960215)
            ·
              refine ⟨3041132967912191756940323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2027421978608127837960215 3041132967912191756940323)
              ·
                refine ⟨4561699451868287635410485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3041132967912191756940323 4561699451868287635410485)
                ·
                  refine ⟨427659323612651965819733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4561699451868287635410485 427659323612651965819733)
                  ·
                    rfl

theorem cell21_1873943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 1, 1, 5].length) (baseStart_1873943 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873943 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873943 prefixEnd_1873943 := by exact prefixLift 1873943
  have htrace : WordTrace (prefixWord ++ tailWord_1873943) baseStart_1873943 baseEnd_1873943 := by
    simpa [prefixWord, tailWord_1873943, baseEnd_1873943] using wordTrace_append hprefix tailTrace_1873943
  have hstable : (prefixWord ++ tailWord_1873943).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873943).length < 2 ^ (prefixWord ++ tailWord_1873943).sum := by decide
  have hdescent : baseEnd_1873943 < baseStart_1873943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873954 : List Nat := [3, 3, 1, 1, 1, 2, 4, 6]
def baseStart_1873954 : Nat := 118140960795 + 1873954 * 2 ^ 59
def prefixEnd_1873954 : Nat := 4983230072969 + 3 ^ 40 * 1873954 * 2
def baseEnd_1873954 : Nat := 142553944654172797045459

theorem tailTrace_1873954 : CollatzResearch.WordTrace tailWord_1873954 prefixEnd_1873954 142553944654172797045459 := by
  unfold tailWord_1873954
  simp only [CollatzResearch.WordTrace]
  refine ⟨17087179363248044677039229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45565811635328119138771277 17087179363248044677039229)
  ·
    refine ⟨6407692261218016753889711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17087179363248044677039229 6407692261218016753889711)
    ·
      refine ⟨9611538391827025130834567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6407692261218016753889711 9611538391827025130834567)
      ·
        refine ⟨14417307587740537696251851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9611538391827025130834567 14417307587740537696251851)
        ·
          refine ⟨21625961381610806544377777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14417307587740537696251851 21625961381610806544377777)
          ·
            refine ⟨16219471036208104908283333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21625961381610806544377777 16219471036208104908283333)
            ·
              refine ⟨3041150819289019670303125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16219471036208104908283333 3041150819289019670303125)
              ·
                refine ⟨142553944654172797045459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3041150819289019670303125 142553944654172797045459)
                ·
                  rfl

theorem cell21_1873954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 6].length) (baseStart_1873954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873954 prefixEnd_1873954 := by exact prefixLift 1873954
  have htrace : WordTrace (prefixWord ++ tailWord_1873954) baseStart_1873954 baseEnd_1873954 := by
    simpa [prefixWord, tailWord_1873954, baseEnd_1873954] using wordTrace_append hprefix tailTrace_1873954
  have hstable : (prefixWord ++ tailWord_1873954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873954).length < 2 ^ (prefixWord ++ tailWord_1873954).sum := by decide
  have hdescent : baseEnd_1873954 < baseStart_1873954 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1873957 : List Nat := [1, 3, 1, 2, 2, 5, 2, 1, 4]
def baseStart_1873957 : Nat := 118140960795 + 1873957 * 2 ^ 59
def prefixEnd_1873957 : Nat := 4983230072969 + 3 ^ 40 * 1873957 * 2
def baseEnd_1873957 : Nat := 427662518603391052586371

theorem tailTrace_1873957 : CollatzResearch.WordTrace tailWord_1873957 prefixEnd_1873957 427662518603391052586371 := by
  unfold tailWord_1873957
  simp only [CollatzResearch.WordTrace]
  refine ⟨68348826871981310220516125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45565884581320873480344083 68348826871981310220516125)
  ·
    refine ⟨25630810076992991332693547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68348826871981310220516125 25630810076992991332693547)
    ·
      refine ⟨38446215115489486999040321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25630810076992991332693547 38446215115489486999040321)
      ·
        refine ⟨28834661336617115249280241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38446215115489486999040321 28834661336617115249280241)
        ·
          refine ⟨21625996002462836436960181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28834661336617115249280241 21625996002462836436960181)
          ·
            refine ⟨2027437125230890915965017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21625996002462836436960181 2027437125230890915965017)
            ·
              refine ⟨1520577843923168186973763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2027437125230890915965017 1520577843923168186973763)
              ·
                refine ⟨2280866765884752280460645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1520577843923168186973763 2280866765884752280460645)
                ·
                  refine ⟨427662518603391052586371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2280866765884752280460645 427662518603391052586371)
                  ·
                    rfl

theorem cell21_1873957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 4].length) (baseStart_1873957 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1873957 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1873957 prefixEnd_1873957 := by exact prefixLift 1873957
  have htrace : WordTrace (prefixWord ++ tailWord_1873957) baseStart_1873957 baseEnd_1873957 := by
    simpa [prefixWord, tailWord_1873957, baseEnd_1873957] using wordTrace_append hprefix tailTrace_1873957
  have hstable : (prefixWord ++ tailWord_1873957).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1873957).length < 2 ^ (prefixWord ++ tailWord_1873957).sum := by decide
  have hdescent : baseEnd_1873957 < baseStart_1873957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1873957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874255 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 7]
def baseStart_1874255 : Nat := 118140960795 + 1874255 * 2 ^ 59
def prefixEnd_1874255 : Nat := 4983230072969 + 3 ^ 40 * 1874255 * 2
def baseEnd_1874255 : Nat := 427730526263408756619095

theorem tailTrace_1874255 : CollatzResearch.WordTrace tailWord_1874255 prefixEnd_1874255 427730526263408756619095 := by
  unfold tailWord_1874255
  simp only [CollatzResearch.WordTrace]
  refine ⟨68359695824901707114864219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45573130549934471409909479 68359695824901707114864219)
  ·
    refine ⟨102539543737352560672296329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68359695824901707114864219 102539543737352560672296329)
    ·
      refine ⟨76904657803014420504222247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102539543737352560672296329 76904657803014420504222247)
      ·
        refine ⟨115356986704521630756333371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76904657803014420504222247 115356986704521630756333371)
        ·
          refine ⟨173035480056782446134500057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115356986704521630756333371 173035480056782446134500057)
          ·
            refine ⟨129776610042586834600875043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 173035480056782446134500057 129776610042586834600875043)
            ·
              refine ⟨194664915063880251901312565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 129776610042586834600875043 194664915063880251901312565)
              ·
                refine ⟨18249835787238773615748053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 194664915063880251901312565 18249835787238773615748053)
                ·
                  refine ⟨427730526263408756619095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18249835787238773615748053 427730526263408756619095)
                  ·
                    rfl

theorem cell21_1874255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 7].length) (baseStart_1874255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1874255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1874255 prefixEnd_1874255 := by exact prefixLift 1874255
  have htrace : WordTrace (prefixWord ++ tailWord_1874255) baseStart_1874255 baseEnd_1874255 := by
    simpa [prefixWord, tailWord_1874255, baseEnd_1874255] using wordTrace_append hprefix tailTrace_1874255
  have hstable : (prefixWord ++ tailWord_1874255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874255).length < 2 ^ (prefixWord ++ tailWord_1874255).sum := by decide
  have hdescent : baseEnd_1874255 < baseStart_1874255 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874258 : List Nat := [3, 2, 2, 1, 1, 1, 6, 5]
def baseStart_1874258 : Nat := 118140960795 + 1874258 * 2 ^ 59
def prefixEnd_1874258 : Nat := 4983230072969 + 3 ^ 40 * 1874258 * 2
def baseEnd_1874258 : Nat := 142577070301427139356363

theorem tailTrace_1874258 : CollatzResearch.WordTrace tailWord_1874258 prefixEnd_1874258 142577070301427139356363 := by
  unfold tailWord_1874258
  simp only [CollatzResearch.WordTrace]
  refine ⟨17089951310972709656805857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45573203495927225751482285 17089951310972709656805857)
  ·
    refine ⟨12817463483229532242604393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17089951310972709656805857 12817463483229532242604393)
    ·
      refine ⟨9613097612422149181953295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12817463483229532242604393 9613097612422149181953295)
      ·
        refine ⟨14419646418633223772929943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9613097612422149181953295 14419646418633223772929943)
        ·
          refine ⟨21629469627949835659394915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14419646418633223772929943 21629469627949835659394915)
          ·
            refine ⟨32444204441924753489092373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21629469627949835659394915 32444204441924753489092373)
            ·
              refine ⟨1520822083215222819801205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 32444204441924753489092373 1520822083215222819801205)
              ·
                refine ⟨142577070301427139356363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1520822083215222819801205 142577070301427139356363)
                ·
                  rfl

theorem cell21_1874258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 5].length) (baseStart_1874258 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1874258 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1874258 prefixEnd_1874258 := by exact prefixLift 1874258
  have htrace : WordTrace (prefixWord ++ tailWord_1874258) baseStart_1874258 baseEnd_1874258 := by
    simpa [prefixWord, tailWord_1874258, baseEnd_1874258] using wordTrace_append hprefix tailTrace_1874258
  have hstable : (prefixWord ++ tailWord_1874258).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874258).length < 2 ^ (prefixWord ++ tailWord_1874258).sum := by decide
  have hdescent : baseEnd_1874258 < baseStart_1874258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874334 : List Nat := [4, 3, 1, 2, 1, 10]
def baseStart_1874334 : Nat := 118140960795 + 1874334 * 2 ^ 59
def prefixEnd_1874334 : Nat := 4983230072969 + 3 ^ 40 * 1874334 * 2
def baseEnd_1874334 : Nat := 15842539079248969437121

theorem tailTrace_1874334 : CollatzResearch.WordTrace tailWord_1874334 prefixEnd_1874334 15842539079248969437121 := by
  unfold tailWord_1874334
  simp only [CollatzResearch.WordTrace]
  refine ⟨8545322148951937950873757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45575051461077002404660037 8545322148951937950873757)
  ·
    refine ⟨3204495805856976731577659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 8545322148951937950873757 3204495805856976731577659)
    ·
      refine ⟨4806743708785465097366489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3204495805856976731577659 4806743708785465097366489)
      ·
        refine ⟨3605057781589098823024867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4806743708785465097366489 3605057781589098823024867)
        ·
          refine ⟨5407586672383648234537301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3605057781589098823024867 5407586672383648234537301)
          ·
            refine ⟨15842539079248969437121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5407586672383648234537301 15842539079248969437121)
            ·
              rfl

theorem cell21_1874334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 10].length) (baseStart_1874334 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1874334 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1874334 prefixEnd_1874334 := by exact prefixLift 1874334
  have htrace : WordTrace (prefixWord ++ tailWord_1874334) baseStart_1874334 baseEnd_1874334 := by
    simpa [prefixWord, tailWord_1874334, baseEnd_1874334] using wordTrace_append hprefix tailTrace_1874334
  have hstable : (prefixWord ++ tailWord_1874334).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874334).length < 2 ^ (prefixWord ++ tailWord_1874334).sum := by decide
  have hdescent : baseEnd_1874334 < baseStart_1874334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874337 : List Nat := [1, 2, 3, 5, 1, 1, 2, 2, 4]
def baseStart_1874337 : Nat := 118140960795 + 1874337 * 2 ^ 59
def prefixEnd_1874337 : Nat := 4983230072969 + 3 ^ 40 * 1874337 * 2
def baseEnd_1874337 : Nat := 427749239780594836252261

theorem tailTrace_1874337 : CollatzResearch.WordTrace tailWord_1874337 prefixEnd_1874337 427749239780594836252261 := by
  unfold tailWord_1874337
  simp only [CollatzResearch.WordTrace]
  refine ⟨68362686610604635119349265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45575124407069756746232843 68362686610604635119349265)
  ·
    refine ⟨51272014957953476339511949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68362686610604635119349265 51272014957953476339511949)
    ·
      refine ⟨19227005609232553627316981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51272014957953476339511949 19227005609232553627316981)
      ·
        refine ⟨1802531775865551902560967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 19227005609232553627316981 1802531775865551902560967)
        ·
          refine ⟨2703797663798327853841451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1802531775865551902560967 2703797663798327853841451)
          ·
            refine ⟨4055696495697491780762177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2703797663798327853841451 4055696495697491780762177)
            ·
              refine ⟨3041772371773118835571633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4055696495697491780762177 3041772371773118835571633)
              ·
                refine ⟨2281329278829839126678725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3041772371773118835571633 2281329278829839126678725)
                ·
                  refine ⟨427749239780594836252261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2281329278829839126678725 427749239780594836252261)
                  ·
                    rfl

theorem cell21_1874337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 4].length) (baseStart_1874337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1874337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1874337 prefixEnd_1874337 := by exact prefixLift 1874337
  have htrace : WordTrace (prefixWord ++ tailWord_1874337) baseStart_1874337 baseEnd_1874337 := by
    simpa [prefixWord, tailWord_1874337, baseEnd_1874337] using wordTrace_append hprefix tailTrace_1874337
  have hstable : (prefixWord ++ tailWord_1874337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874337).length < 2 ^ (prefixWord ++ tailWord_1874337).sum := by decide
  have hdescent : baseEnd_1874337 < baseStart_1874337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874413 : List Nat := [1, 5, 1, 3, 1, 2, 3, 1, 4]
def baseStart_1874413 : Nat := 118140960795 + 1874413 * 2 ^ 59
def prefixEnd_1874413 : Nat := 4983230072969 + 3 ^ 40 * 1874413 * 2
def baseEnd_1874413 : Nat := 427766584016035592985439

theorem tailTrace_1874413 : CollatzResearch.WordTrace tailWord_1874413 prefixEnd_1874413 427766584016035592985439 := by
  unfold tailWord_1874413
  simp only [CollatzResearch.WordTrace]
  refine ⟨68365458558329300099115893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45576972372219533399410595 68365458558329300099115893)
  ·
    refine ⟨6409261739843371884292115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68365458558329300099115893 6409261739843371884292115)
    ·
      refine ⟨9613892609765057826438173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6409261739843371884292115 9613892609765057826438173)
      ·
        refine ⟨3605209728661896684914315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9613892609765057826438173 3605209728661896684914315)
        ·
          refine ⟨5407814592992845027371473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3605209728661896684914315 5407814592992845027371473)
          ·
            refine ⟨4055860944744633770528605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5407814592992845027371473 4055860944744633770528605)
            ·
              refine ⟨1520947854279237663948227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4055860944744633770528605 1520947854279237663948227)
              ·
                refine ⟨2281421781418856495922341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1520947854279237663948227 2281421781418856495922341)
                ·
                  refine ⟨427766584016035592985439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2281421781418856495922341 427766584016035592985439)
                  ·
                    rfl

theorem cell21_1874413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 3, 1, 4].length) (baseStart_1874413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1874413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1874413 prefixEnd_1874413 := by exact prefixLift 1874413
  have htrace : WordTrace (prefixWord ++ tailWord_1874413) baseStart_1874413 baseEnd_1874413 := by
    simpa [prefixWord, tailWord_1874413, baseEnd_1874413] using wordTrace_append hprefix tailTrace_1874413
  have hstable : (prefixWord ++ tailWord_1874413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874413).length < 2 ^ (prefixWord ++ tailWord_1874413).sum := by decide
  have hdescent : baseEnd_1874413 < baseStart_1874413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874472 : List Nat := [2, 1, 5, 2, 1, 2, 1, 3, 4]
def baseStart_1874472 : Nat := 118140960795 + 1874472 * 2 ^ 59
def prefixEnd_1874472 : Nat := 4983230072969 + 3 ^ 40 * 1874472 * 2
def baseEnd_1874472 : Nat := 427780048619864601501985

theorem tailTrace_1874472 : CollatzResearch.WordTrace tailWord_1874472 prefixEnd_1874472 427780048619864601501985 := by
  unfold tailWord_1874472
  simp only [CollatzResearch.WordTrace]
  refine ⟨34183805232557776587756835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45578406976743702117009113 34183805232557776587756835)
  ·
    refine ⟨51275707848836664881635253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34183805232557776587756835 51275707848836664881635253)
    ·
      refine ⟨4807097610828437332653305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 51275707848836664881635253 4807097610828437332653305)
      ·
        refine ⟨3605323208121327999489979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4807097610828437332653305 3605323208121327999489979)
        ·
          refine ⟨5407984812181991999234969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3605323208121327999489979 5407984812181991999234969)
          ·
            refine ⟨4055988609136493999426227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5407984812181991999234969 4055988609136493999426227)
            ·
              refine ⟨6083982913704740999139341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4055988609136493999426227 6083982913704740999139341)
              ·
                refine ⟨2281493592639277874677253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6083982913704740999139341 2281493592639277874677253)
                ·
                  refine ⟨427780048619864601501985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2281493592639277874677253 427780048619864601501985)
                  ·
                    rfl

theorem cell21_1874472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 4].length) (baseStart_1874472 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1874472 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1874472 prefixEnd_1874472 := by exact prefixLift 1874472
  have htrace : WordTrace (prefixWord ++ tailWord_1874472) baseStart_1874472 baseEnd_1874472 := by
    simpa [prefixWord, tailWord_1874472, baseEnd_1874472] using wordTrace_append hprefix tailTrace_1874472
  have hstable : (prefixWord ++ tailWord_1874472).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874472).length < 2 ^ (prefixWord ++ tailWord_1874472).sum := by decide
  have hdescent : baseEnd_1874472 < baseStart_1874472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874483 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 7]
def baseStart_1874483 : Nat := 118140960795 + 1874483 * 2 ^ 59
def prefixEnd_1874483 : Nat := 4983230072969 + 3 ^ 40 * 1874483 * 2
def baseEnd_1874483 : Nat := 427782558969731026818629

theorem tailTrace_1874483 : CollatzResearch.WordTrace tailWord_1874483 prefixEnd_1874483 427782558969731026818629 := by
  unfold tailWord_1874483
  simp only [CollatzResearch.WordTrace]
  refine ⟨68368011668075702054164103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45578674445383801369442735 68368011668075702054164103)
  ·
    refine ⟨102552017502113553081246155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68368011668075702054164103 102552017502113553081246155)
    ·
      refine ⟨153828026253170329621869233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102552017502113553081246155 153828026253170329621869233)
      ·
        refine ⟨115371019689877747216401925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 153828026253170329621869233 115371019689877747216401925)
        ·
          refine ⟨21632066191852077603075361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 115371019689877747216401925 21632066191852077603075361)
          ·
            refine ⟨16224049643889058202306521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21632066191852077603075361 16224049643889058202306521)
            ·
              refine ⟨12168037232916793651729891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16224049643889058202306521 12168037232916793651729891)
              ·
                refine ⟨18252055849375190477594837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12168037232916793651729891 18252055849375190477594837)
                ·
                  refine ⟨427782558969731026818629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18252055849375190477594837 427782558969731026818629)
                  ·
                    rfl

theorem cell21_1874483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 7].length) (baseStart_1874483 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1874483 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1874483 prefixEnd_1874483 := by exact prefixLift 1874483
  have htrace : WordTrace (prefixWord ++ tailWord_1874483) baseStart_1874483 baseEnd_1874483 := by
    simpa [prefixWord, tailWord_1874483, baseEnd_1874483] using wordTrace_append hprefix tailTrace_1874483
  have hstable : (prefixWord ++ tailWord_1874483).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874483).length < 2 ^ (prefixWord ++ tailWord_1874483).sum := by decide
  have hdescent : baseEnd_1874483 < baseStart_1874483 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874486 : List Nat := [5, 1, 2, 1, 2, 1, 2, 7]
def baseStart_1874486 : Nat := 118140960795 + 1874486 * 2 ^ 59
def prefixEnd_1874486 : Nat := 4983230072969 + 3 ^ 40 * 1874486 * 2
def baseEnd_1874486 : Nat := 142594414536867896089541

theorem tailTrace_1874486 : CollatzResearch.WordTrace tailWord_1874486 prefixEnd_1874486 142594414536867896089541 := by
  unfold tailWord_1874486
  simp only [CollatzResearch.WordTrace]
  refine ⟨4273007567941552097907707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45578747391376555711015541 4273007567941552097907707)
  ·
    refine ⟨6409511351912328146861561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4273007567941552097907707 6409511351912328146861561)
    ·
      refine ⟨4807133513934246110146171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6409511351912328146861561 4807133513934246110146171)
      ·
        refine ⟨7210700270901369165219257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4807133513934246110146171 7210700270901369165219257)
        ·
          refine ⟨5408025203176026873914443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7210700270901369165219257 5408025203176026873914443)
          ·
            refine ⟨8112037804764040310871665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5408025203176026873914443 8112037804764040310871665)
            ·
              refine ⟨6084028353573030233153749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8112037804764040310871665 6084028353573030233153749)
              ·
                refine ⟨142594414536867896089541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6084028353573030233153749 142594414536867896089541)
                ·
                  rfl

theorem cell21_1874486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_1874486 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1874486 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1874486 prefixEnd_1874486 := by exact prefixLift 1874486
  have htrace : WordTrace (prefixWord ++ tailWord_1874486) baseStart_1874486 baseEnd_1874486 := by
    simpa [prefixWord, tailWord_1874486, baseEnd_1874486] using wordTrace_append hprefix tailTrace_1874486
  have hstable : (prefixWord ++ tailWord_1874486).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874486).length < 2 ^ (prefixWord ++ tailWord_1874486).sum := by decide
  have hdescent : baseEnd_1874486 < baseStart_1874486 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874621 : List Nat := [1, 4, 1, 2, 1, 5, 7]
def baseStart_1874621 : Nat := 118140960795 + 1874621 * 2 ^ 59
def prefixEnd_1874621 : Nat := 4983230072969 + 3 ^ 40 * 1874621 * 2
def baseEnd_1874621 : Nat := 47534894716652605946483

theorem tailTrace_1874621 : CollatzResearch.WordTrace tailWord_1874621 prefixEnd_1874621 47534894716652605946483 := by
  unfold tailWord_1874621
  simp only [CollatzResearch.WordTrace]
  refine ⟨68373044941575751622687717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45582029961050501081791811 68373044941575751622687717)
  ·
    refine ⟨12819945926545453429253947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68373044941575751622687717 12819945926545453429253947)
    ·
      refine ⟨19229918889818180143880921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12819945926545453429253947 19229918889818180143880921)
      ·
        refine ⟨14422439167363635107910691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19229918889818180143880921 14422439167363635107910691)
        ·
          refine ⟨21633658751045452661866037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14422439167363635107910691 21633658751045452661866037)
          ·
            refine ⟨2028155507910511187049941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 21633658751045452661866037 2028155507910511187049941)
            ·
              refine ⟨47534894716652605946483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2028155507910511187049941 47534894716652605946483)
              ·
                rfl

theorem cell21_1874621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 7].length) (baseStart_1874621 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1874621 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1874621 prefixEnd_1874621 := by exact prefixLift 1874621
  have htrace : WordTrace (prefixWord ++ tailWord_1874621) baseStart_1874621 baseEnd_1874621 := by
    simpa [prefixWord, tailWord_1874621, baseEnd_1874621] using wordTrace_append hprefix tailTrace_1874621
  have hstable : (prefixWord ++ tailWord_1874621).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874621).length < 2 ^ (prefixWord ++ tailWord_1874621).sum := by decide
  have hdescent : baseEnd_1874621 < baseStart_1874621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874669 : List Nat := [1, 5, 1, 2, 1, 1, 2, 5, 3]
def baseStart_1874669 : Nat := 118140960795 + 1874669 * 2 ^ 59
def prefixEnd_1874669 : Nat := 4983230072969 + 3 ^ 40 * 1874669 * 2
def baseEnd_1874669 : Nat := 427825006703836036718249

theorem tailTrace_1874669 : CollatzResearch.WordTrace tailWord_1874669 prefixEnd_1874669 427825006703836036718249 := by
  unfold tailWord_1874669
  simp only [CollatzResearch.WordTrace]
  refine ⟨68374795645401855820435061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45583197096934570546956707 68374795645401855820435061)
  ·
    refine ⟨6410137091756423983165787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68374795645401855820435061 6410137091756423983165787)
    ·
      refine ⟨9615205637634635974748681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6410137091756423983165787 9615205637634635974748681)
      ·
        refine ⟨7211404228225976981061511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9615205637634635974748681 7211404228225976981061511)
        ·
          refine ⟨10817106342338965471592267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7211404228225976981061511 10817106342338965471592267)
          ·
            refine ⟨16225659513508448207388401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10817106342338965471592267 16225659513508448207388401)
            ·
              refine ⟨12169244635131336155541301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16225659513508448207388401 12169244635131336155541301)
              ·
                refine ⟨1140866684543562764581997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 12169244635131336155541301 1140866684543562764581997)
                ·
                  refine ⟨427825006703836036718249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1140866684543562764581997 427825006703836036718249)
                  ·
                    rfl

theorem cell21_1874669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 3].length) (baseStart_1874669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1874669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1874669 prefixEnd_1874669 := by exact prefixLift 1874669
  have htrace : WordTrace (prefixWord ++ tailWord_1874669) baseStart_1874669 baseEnd_1874669 := by
    simpa [prefixWord, tailWord_1874669, baseEnd_1874669] using wordTrace_append hprefix tailTrace_1874669
  have hstable : (prefixWord ++ tailWord_1874669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874669).length < 2 ^ (prefixWord ++ tailWord_1874669).sum := by decide
  have hdescent : baseEnd_1874669 < baseStart_1874669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874686 : List Nat := [4, 2, 2, 1, 2, 2, 1, 4, 3]
def baseStart_1874686 : Nat := 118140960795 + 1874686 * 2 ^ 59
def prefixEnd_1874686 : Nat := 4983230072969 + 3 ^ 40 * 1874686 * 2
def baseEnd_1874686 : Nat := 427828886335447784934881

theorem tailTrace_1874686 : CollatzResearch.WordTrace tailWord_1874686 prefixEnd_1874686 427828886335447784934881 := by
  unfold tailWord_1874686
  simp only [CollatzResearch.WordTrace]
  refine ⟨8546926960792533465475489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45583610457560178482535941 8546926960792533465475489)
  ·
    refine ⟨6410195220594400099106617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8546926960792533465475489 6410195220594400099106617)
    ·
      refine ⟨4807646415445800074329963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6410195220594400099106617 4807646415445800074329963)
      ·
        refine ⟨7211469623168700111494945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4807646415445800074329963 7211469623168700111494945)
        ·
          refine ⟨5408602217376525083621209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7211469623168700111494945 5408602217376525083621209)
          ·
            refine ⟨4056451663032393812715907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5408602217376525083621209 4056451663032393812715907)
            ·
              refine ⟨6084677494548590719073861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4056451663032393812715907 6084677494548590719073861)
              ·
                refine ⟨1140877030227860759826349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6084677494548590719073861 1140877030227860759826349)
                ·
                  refine ⟨427828886335447784934881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1140877030227860759826349 427828886335447784934881)
                  ·
                    rfl

theorem cell21_1874686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_1874686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1874686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1874686 prefixEnd_1874686 := by exact prefixLift 1874686
  have htrace : WordTrace (prefixWord ++ tailWord_1874686) baseStart_1874686 baseEnd_1874686 := by
    simpa [prefixWord, tailWord_1874686, baseEnd_1874686] using wordTrace_append hprefix tailTrace_1874686
  have hstable : (prefixWord ++ tailWord_1874686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874686).length < 2 ^ (prefixWord ++ tailWord_1874686).sum := by decide
  have hdescent : baseEnd_1874686 < baseStart_1874686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874855 : List Nat := [1, 1, 6, 1, 3, 2, 2, 2, 3]
def baseStart_1874855 : Nat := 118140960795 + 1874855 * 2 ^ 59
def prefixEnd_1874855 : Nat := 4983230072969 + 3 ^ 40 * 1874855 * 2
def baseEnd_1874855 : Nat := 427867454437941046617869

theorem tailTrace_1874855 : CollatzResearch.WordTrace tailWord_1874855 prefixEnd_1874855 427867454437941046617869 := by
  unfold tailWord_1874855
  simp only [CollatzResearch.WordTrace]
  refine ⟨68381579622728009586706019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45587719748485339724470679 68381579622728009586706019)
  ·
    refine ⟨102572369434092014380059029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68381579622728009586706019 102572369434092014380059029)
    ·
      refine ⟨4808079817223063174065267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102572369434092014380059029 4808079817223063174065267)
      ·
        refine ⟨7212119725834594761097901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4808079817223063174065267 7212119725834594761097901)
        ·
          refine ⟨2704544897187973035411713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7212119725834594761097901 2704544897187973035411713)
          ·
            refine ⟨2028408672890979776558785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2704544897187973035411713 2028408672890979776558785)
            ·
              refine ⟨1521306504668234832419089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2028408672890979776558785 1521306504668234832419089)
              ·
                refine ⟨1140979878501176124314317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1521306504668234832419089 1140979878501176124314317)
                ·
                  refine ⟨427867454437941046617869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1140979878501176124314317 427867454437941046617869)
                  ·
                    rfl

theorem cell21_1874855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 3].length) (baseStart_1874855 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1874855 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1874855 prefixEnd_1874855 := by exact prefixLift 1874855
  have htrace : WordTrace (prefixWord ++ tailWord_1874855) baseStart_1874855 baseEnd_1874855 := by
    simpa [prefixWord, tailWord_1874855, baseEnd_1874855] using wordTrace_append hprefix tailTrace_1874855
  have hstable : (prefixWord ++ tailWord_1874855).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874855).length < 2 ^ (prefixWord ++ tailWord_1874855).sum := by decide
  have hdescent : baseEnd_1874855 < baseStart_1874855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874914 : List Nat := [3, 3, 3, 1, 1, 1, 2, 4, 3]
def baseStart_1874914 : Nat := 118140960795 + 1874914 * 2 ^ 59
def prefixEnd_1874914 : Nat := 4983230072969 + 3 ^ 40 * 1874914 * 2
def baseEnd_1874914 : Nat := 427880919041770055134415

theorem tailTrace_1874914 : CollatzResearch.WordTrace tailWord_1874914 prefixEnd_1874914 427880919041770055134415 := by
  unfold tailWord_1874914
  simp only [CollatzResearch.WordTrace]
  refine ⟨17095932882378565665775949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45589154353009508442069197 17095932882378565665775949)
  ·
    refine ⟨6410974830891962124665981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 17095932882378565665775949 6410974830891962124665981)
    ·
      refine ⟨2404115561584485796749743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6410974830891962124665981 2404115561584485796749743)
      ·
        refine ⟨3606173342376728695124615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2404115561584485796749743 3606173342376728695124615)
        ·
          refine ⟨5409260013565093042686923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3606173342376728695124615 5409260013565093042686923)
          ·
            refine ⟨8113890020347639564030385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5409260013565093042686923 8113890020347639564030385)
            ·
              refine ⟨6085417515260729673022789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8113890020347639564030385 6085417515260729673022789)
              ·
                refine ⟨1141015784111386813691773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6085417515260729673022789 1141015784111386813691773)
                ·
                  refine ⟨427880919041770055134415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1141015784111386813691773 427880919041770055134415)
                  ·
                    rfl

theorem cell21_1874914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 4, 3].length) (baseStart_1874914 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1874914 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1874914 prefixEnd_1874914 := by exact prefixLift 1874914
  have htrace : WordTrace (prefixWord ++ tailWord_1874914) baseStart_1874914 baseEnd_1874914 := by
    simpa [prefixWord, tailWord_1874914, baseEnd_1874914] using wordTrace_append hprefix tailTrace_1874914
  have hstable : (prefixWord ++ tailWord_1874914).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874914).length < 2 ^ (prefixWord ++ tailWord_1874914).sum := by decide
  have hdescent : baseEnd_1874914 < baseStart_1874914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874942 : List Nat := [4, 2, 2, 2, 2, 1, 1, 7]
def baseStart_1874942 : Nat := 118140960795 + 1874942 * 2 ^ 59
def prefixEnd_1874942 : Nat := 4983230072969 + 3 ^ 40 * 1874942 * 2
def baseEnd_1874942 : Nat := 142629103007749409555897

theorem tailTrace_1874942 : CollatzResearch.WordTrace tailWord_1874942 prefixEnd_1874942 142629103007749409555897 := by
  unfold tailWord_1874942
  simp only [CollatzResearch.WordTrace]
  refine ⟨8548094096676602930640385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45589835182275215630082053 8548094096676602930640385)
  ·
    refine ⟨6411070572507452197980289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 8548094096676602930640385 6411070572507452197980289)
    ·
      refine ⟨4808302929380589148485217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6411070572507452197980289 4808302929380589148485217)
      ·
        refine ⟨3606227197035441861363913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4808302929380589148485217 3606227197035441861363913)
        ·
          refine ⟨2704670397776581396022935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3606227197035441861363913 2704670397776581396022935)
          ·
            refine ⟨4057005596664872094034403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2704670397776581396022935 4057005596664872094034403)
            ·
              refine ⟨6085508394997308141051605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4057005596664872094034403 6085508394997308141051605)
              ·
                refine ⟨142629103007749409555897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6085508394997308141051605 142629103007749409555897)
                ·
                  rfl

theorem cell21_1874942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 7].length) (baseStart_1874942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1874942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1874942 prefixEnd_1874942 := by exact prefixLift 1874942
  have htrace : WordTrace (prefixWord ++ tailWord_1874942) baseStart_1874942 baseEnd_1874942 := by
    simpa [prefixWord, tailWord_1874942, baseEnd_1874942] using wordTrace_append hprefix tailTrace_1874942
  have hstable : (prefixWord ++ tailWord_1874942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874942).length < 2 ^ (prefixWord ++ tailWord_1874942).sum := by decide
  have hdescent : baseEnd_1874942 < baseStart_1874942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874970 : List Nat := [3, 1, 1, 3, 1, 2, 2, 4, 4]
def baseStart_1874970 : Nat := 118140960795 + 1874970 * 2 ^ 59
def prefixEnd_1874970 : Nat := 4983230072969 + 3 ^ 40 * 1874970 * 2
def baseEnd_1874970 : Nat := 427893699004726402200967

theorem tailTrace_1874970 : CollatzResearch.WordTrace tailWord_1874970 prefixEnd_1874970 427893699004726402200967 := by
  unfold tailWord_1874970
  simp only [CollatzResearch.WordTrace]
  refine ⟨17096443504327846056785591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45590516011540922818094909 17096443504327846056785591)
  ·
    refine ⟨25644665256491769085178387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17096443504327846056785591 25644665256491769085178387)
    ·
      refine ⟨38466997884737653627767581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25644665256491769085178387 38466997884737653627767581)
      ·
        refine ⟨14425124206776620110412843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38466997884737653627767581 14425124206776620110412843)
        ·
          refine ⟨21637686310164930165619265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14425124206776620110412843 21637686310164930165619265)
          ·
            refine ⟨16228264732623697624214449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21637686310164930165619265 16228264732623697624214449)
            ·
              refine ⟨12171198549467773218160837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16228264732623697624214449 12171198549467773218160837)
              ·
                refine ⟨2282099728025207478405157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12171198549467773218160837 2282099728025207478405157)
                ·
                  refine ⟨427893699004726402200967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2282099728025207478405157 427893699004726402200967)
                  ·
                    rfl

theorem cell21_1874970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 4, 4].length) (baseStart_1874970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1874970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1874970 prefixEnd_1874970 := by exact prefixLift 1874970
  have htrace : WordTrace (prefixWord ++ tailWord_1874970) baseStart_1874970 baseEnd_1874970 := by
    simpa [prefixWord, tailWord_1874970, baseEnd_1874970] using wordTrace_append hprefix tailTrace_1874970
  have hstable : (prefixWord ++ tailWord_1874970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874970).length < 2 ^ (prefixWord ++ tailWord_1874970).sum := by decide
  have hdescent : baseEnd_1874970 < baseStart_1874970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1874973 : List Nat := [1, 4, 2, 2, 3, 2, 1, 1, 5]
def baseStart_1874973 : Nat := 118140960795 + 1874973 * 2 ^ 59
def prefixEnd_1874973 : Nat := 4983230072969 + 3 ^ 40 * 1874973 * 2
def baseEnd_1874973 : Nat := 427894383645599063650961

theorem tailTrace_1874973 : CollatzResearch.WordTrace tailWord_1874973 prefixEnd_1874973 427894383645599063650961 := by
  unfold tailWord_1874973
  simp only [CollatzResearch.WordTrace]
  refine ⟨68385883436300515739501573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45590588957533677159667715 68385883436300515739501573)
  ·
    refine ⟨12822353144306346701156545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68385883436300515739501573 12822353144306346701156545)
    ·
      refine ⟨9616764858229760025867409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12822353144306346701156545 9616764858229760025867409)
      ·
        refine ⟨7212573643672320019400557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9616764858229760025867409 7212573643672320019400557)
        ·
          refine ⟨2704715116377120007275209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7212573643672320019400557 2704715116377120007275209)
          ·
            refine ⟨2028536337282840005456407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2704715116377120007275209 2028536337282840005456407)
            ·
              refine ⟨3042804505924260008184611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2028536337282840005456407 3042804505924260008184611)
              ·
                refine ⟨4564206758886390012276917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3042804505924260008184611 4564206758886390012276917)
                ·
                  refine ⟨427894383645599063650961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4564206758886390012276917 427894383645599063650961)
                  ·
                    rfl

theorem cell21_1874973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_1874973 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1874973 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1874973 prefixEnd_1874973 := by exact prefixLift 1874973
  have htrace : WordTrace (prefixWord ++ tailWord_1874973) baseStart_1874973 baseEnd_1874973 := by
    simpa [prefixWord, tailWord_1874973, baseEnd_1874973] using wordTrace_append hprefix tailTrace_1874973
  have hstable : (prefixWord ++ tailWord_1874973).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1874973).length < 2 ^ (prefixWord ++ tailWord_1874973).sum := by decide
  have hdescent : baseEnd_1874973 < baseStart_1874973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1874973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875032 : List Nat := [2, 1, 2, 2, 1, 3, 3, 4, 3]
def baseStart_1875032 : Nat := 118140960795 + 1875032 * 2 ^ 59
def prefixEnd_1875032 : Nat := 4983230072969 + 3 ^ 40 * 1875032 * 2
def baseEnd_1875032 : Nat := 427907848249428072167507

theorem tailTrace_1875032 : CollatzResearch.WordTrace tailWord_1875032 prefixEnd_1875032 427907848249428072167507 := by
  unfold tailWord_1875032
  simp only [CollatzResearch.WordTrace]
  refine ⟨34194017671543384407949675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45592023562057845877266233 34194017671543384407949675)
  ·
    refine ⟨51291026507315076611924513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34194017671543384407949675 51291026507315076611924513)
    ·
      refine ⟨38468269880486307458943385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51291026507315076611924513 38468269880486307458943385)
      ·
        refine ⟨28851202410364730594207539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38468269880486307458943385 28851202410364730594207539)
        ·
          refine ⟨43276803615547095891311309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28851202410364730594207539 43276803615547095891311309)
          ·
            refine ⟨16228801355830160959241741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43276803615547095891311309 16228801355830160959241741)
            ·
              refine ⟨6085800508436310359715653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16228801355830160959241741 6085800508436310359715653)
              ·
                refine ⟨1141087595331808192446685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6085800508436310359715653 1141087595331808192446685)
                ·
                  refine ⟨427907848249428072167507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1141087595331808192446685 427907848249428072167507)
                  ·
                    rfl

theorem cell21_1875032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 3].length) (baseStart_1875032 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1875032 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1875032 prefixEnd_1875032 := by exact prefixLift 1875032
  have htrace : WordTrace (prefixWord ++ tailWord_1875032) baseStart_1875032 baseEnd_1875032 := by
    simpa [prefixWord, tailWord_1875032, baseEnd_1875032] using wordTrace_append hprefix tailTrace_1875032
  have hstable : (prefixWord ++ tailWord_1875032).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875032).length < 2 ^ (prefixWord ++ tailWord_1875032).sum := by decide
  have hdescent : baseEnd_1875032 < baseStart_1875032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875080 : List Nat := [2, 1, 3, 4, 2, 2, 1, 2, 4]
def baseStart_1875080 : Nat := 118140960795 + 1875080 * 2 ^ 59
def prefixEnd_1875080 : Nat := 4983230072969 + 3 ^ 40 * 1875080 * 2
def baseEnd_1875080 : Nat := 427918802503390655367409

theorem tailTrace_1875080 : CollatzResearch.WordTrace tailWord_1875080 prefixEnd_1875080 427918802503390655367409 := by
  unfold tailWord_1875080
  simp only [CollatzResearch.WordTrace]
  refine ⟨34194893023456436506823347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45593190697941915342431129 34194893023456436506823347)
  ·
    refine ⟨51292339535184654760235021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34194893023456436506823347 51292339535184654760235021)
    ·
      refine ⟨19234627325694245535088133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 51292339535184654760235021 19234627325694245535088133)
      ·
        refine ⟨3606492623567671037829025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 19234627325694245535088133 3606492623567671037829025)
        ·
          refine ⟨2704869467675753278371769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3606492623567671037829025 2704869467675753278371769)
          ·
            refine ⟨2028652100756814958778827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2704869467675753278371769 2028652100756814958778827)
            ·
              refine ⟨3042978151135222438168241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2028652100756814958778827 3042978151135222438168241)
              ·
                refine ⟨2282233613351416828626181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3042978151135222438168241 2282233613351416828626181)
                ·
                  refine ⟨427918802503390655367409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2282233613351416828626181 427918802503390655367409)
                  ·
                    rfl

theorem cell21_1875080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 4].length) (baseStart_1875080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1875080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1875080 prefixEnd_1875080 := by exact prefixLift 1875080
  have htrace : WordTrace (prefixWord ++ tailWord_1875080) baseStart_1875080 baseEnd_1875080 := by
    simpa [prefixWord, tailWord_1875080, baseEnd_1875080] using wordTrace_append hprefix tailTrace_1875080
  have hstable : (prefixWord ++ tailWord_1875080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875080).length < 2 ^ (prefixWord ++ tailWord_1875080).sum := by decide
  have hdescent : baseEnd_1875080 < baseStart_1875080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875156 : List Nat := [2, 4, 1, 4, 1, 1, 1, 3, 4]
def baseStart_1875156 : Nat := 118140960795 + 1875156 * 2 ^ 59
def prefixEnd_1875156 : Nat := 4983230072969 + 3 ^ 40 * 1875156 * 2
def baseEnd_1875156 : Nat := 427936146738831412100587

theorem tailTrace_1875156 : CollatzResearch.WordTrace tailWord_1875156 prefixEnd_1875156 427936146738831412100587 := by
  unfold tailWord_1875156
  simp only [CollatzResearch.WordTrace]
  refine ⟨34196278997318768996706661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45595038663091691995608881 34196278997318768996706661)
  ·
    refine ⟨6411802311997269186882499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34196278997318768996706661 6411802311997269186882499)
    ·
      refine ⟨9617703467995903780323749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6411802311997269186882499 9617703467995903780323749)
      ·
        refine ⟨1803319400249231958810703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 9617703467995903780323749 1803319400249231958810703)
        ·
          refine ⟨2704979100373847938216055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1803319400249231958810703 2704979100373847938216055)
          ·
            refine ⟨4057468650560771907324083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2704979100373847938216055 4057468650560771907324083)
            ·
              refine ⟨6086202975841157860986125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4057468650560771907324083 6086202975841157860986125)
              ·
                refine ⟨2282326115940434197869797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6086202975841157860986125 2282326115940434197869797)
                ·
                  refine ⟨427936146738831412100587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2282326115940434197869797 427936146738831412100587)
                  ·
                    rfl

theorem cell21_1875156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 4].length) (baseStart_1875156 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1875156 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1875156 prefixEnd_1875156 := by exact prefixLift 1875156
  have htrace : WordTrace (prefixWord ++ tailWord_1875156) baseStart_1875156 baseEnd_1875156 := by
    simpa [prefixWord, tailWord_1875156, baseEnd_1875156] using wordTrace_append hprefix tailTrace_1875156
  have hstable : (prefixWord ++ tailWord_1875156).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875156).length < 2 ^ (prefixWord ++ tailWord_1875156).sum := by decide
  have hdescent : baseEnd_1875156 < baseStart_1875156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875201 : List Nat := [1, 2, 4, 1, 1, 3, 4, 2, 3]
def baseStart_1875201 : Nat := 118140960795 + 1875201 * 2 ^ 59
def prefixEnd_1875201 : Nat := 4983230072969 + 3 ^ 40 * 1875201 * 2
def baseEnd_1875201 : Nat := 427946416351921333850495

theorem tailTrace_1875201 : CollatzResearch.WordTrace tailWord_1875201 prefixEnd_1875201 427946416351921333850495 := by
  unfold tailWord_1875201
  simp only [CollatzResearch.WordTrace]
  refine ⟨68394199279474510678801457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45596132852983007119200971 68394199279474510678801457)
  ·
    refine ⟨51295649459605883009101093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68394199279474510678801457 51295649459605883009101093)
    ·
      refine ⟨9617934273676103064206455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51295649459605883009101093 9617934273676103064206455)
      ·
        refine ⟨14426901410514154596309683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9617934273676103064206455 14426901410514154596309683)
        ·
          refine ⟨21640352115771231894464525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14426901410514154596309683 21640352115771231894464525)
          ·
            refine ⟨8115132043414211960424197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21640352115771231894464525 8115132043414211960424197)
            ·
              refine ⟨1521587258140164742579537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8115132043414211960424197 1521587258140164742579537)
              ·
                refine ⟨1141190443605123556934653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1521587258140164742579537 1141190443605123556934653)
                ·
                  refine ⟨427946416351921333850495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1141190443605123556934653 427946416351921333850495)
                  ·
                    rfl

theorem cell21_1875201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 2, 3].length) (baseStart_1875201 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1875201 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1875201 prefixEnd_1875201 := by exact prefixLift 1875201
  have htrace : WordTrace (prefixWord ++ tailWord_1875201) baseStart_1875201 baseEnd_1875201 := by
    simpa [prefixWord, tailWord_1875201, baseEnd_1875201] using wordTrace_append hprefix tailTrace_1875201
  have hstable : (prefixWord ++ tailWord_1875201).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875201).length < 2 ^ (prefixWord ++ tailWord_1875201).sum := by decide
  have hdescent : baseEnd_1875201 < baseStart_1875201 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875212 : List Nat := [2, 2, 1, 2, 2, 3, 3, 6]
def baseStart_1875212 : Nat := 118140960795 + 1875212 * 2 ^ 59
def prefixEnd_1875212 : Nat := 4983230072969 + 3 ^ 40 * 1875212 * 2
def baseEnd_1875212 : Nat := 142649642233929253055713

theorem tailTrace_1875212 : CollatzResearch.WordTrace tailWord_1875212 prefixEnd_1875212 142649642233929253055713 := by
  unfold tailWord_1875212
  simp only [CollatzResearch.WordTrace]
  refine ⟨34197300241217329778725945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45596400321623106371634593 34197300241217329778725945)
  ·
    refine ⟨25647975180912997334044459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34197300241217329778725945 25647975180912997334044459)
    ·
      refine ⟨38471962771369496001066689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25647975180912997334044459 38471962771369496001066689)
      ·
        refine ⟨28853972078527122000800017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38471962771369496001066689 28853972078527122000800017)
        ·
          refine ⟨21640479058895341500600013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28853972078527122000800017 21640479058895341500600013)
          ·
            refine ⟨8115179647085753062725005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21640479058895341500600013 8115179647085753062725005)
            ·
              refine ⟨3043192367657157398521877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8115179647085753062725005 3043192367657157398521877)
              ·
                refine ⟨142649642233929253055713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3043192367657157398521877 142649642233929253055713)
                ·
                  rfl

theorem cell21_1875212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 6].length) (baseStart_1875212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1875212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1875212 prefixEnd_1875212 := by exact prefixLift 1875212
  have htrace : WordTrace (prefixWord ++ tailWord_1875212) baseStart_1875212 baseEnd_1875212 := by
    simpa [prefixWord, tailWord_1875212, baseEnd_1875212] using wordTrace_append hprefix tailTrace_1875212
  have hstable : (prefixWord ++ tailWord_1875212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875212).length < 2 ^ (prefixWord ++ tailWord_1875212).sum := by decide
  have hdescent : baseEnd_1875212 < baseStart_1875212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875260 : List Nat := [2, 2, 2, 2, 1, 3, 2, 4, 3]
def baseStart_1875260 : Nat := 118140960795 + 1875260 * 2 ^ 59
def prefixEnd_1875260 : Nat := 4983230072969 + 3 ^ 40 * 1875260 * 2
def baseEnd_1875260 : Nat := 427959880955750342367041

theorem tailTrace_1875260 : CollatzResearch.WordTrace tailWord_1875260 prefixEnd_1875260 427959880955750342367041 := by
  unfold tailWord_1875260
  simp only [CollatzResearch.WordTrace]
  refine ⟨34198175593130381877599617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45597567457507175836799489 34198175593130381877599617)
  ·
    refine ⟨25648631694847786408199713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34198175593130381877599617 25648631694847786408199713)
    ·
      refine ⟨19236473771135839806149785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25648631694847786408199713 19236473771135839806149785)
      ·
        refine ⟨14427355328351879854612339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19236473771135839806149785 14427355328351879854612339)
        ·
          refine ⟨21641032992527819781918509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14427355328351879854612339 21641032992527819781918509)
          ·
            refine ⟨8115387372197932418219441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 21641032992527819781918509 8115387372197932418219441)
            ·
              refine ⟨6086540529148449313664581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8115387372197932418219441 6086540529148449313664581)
              ·
                refine ⟨1141226349215334246312109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6086540529148449313664581 1141226349215334246312109)
                ·
                  refine ⟨427959880955750342367041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1141226349215334246312109 427959880955750342367041)
                  ·
                    rfl

theorem cell21_1875260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 3].length) (baseStart_1875260 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1875260 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1875260 prefixEnd_1875260 := by exact prefixLift 1875260
  have htrace : WordTrace (prefixWord ++ tailWord_1875260) baseStart_1875260 baseEnd_1875260 := by
    simpa [prefixWord, tailWord_1875260, baseEnd_1875260] using wordTrace_append hprefix tailTrace_1875260
  have hstable : (prefixWord ++ tailWord_1875260).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875260).length < 2 ^ (prefixWord ++ tailWord_1875260).sum := by decide
  have hdescent : baseEnd_1875260 < baseStart_1875260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875381 : List Nat := [1, 3, 3, 2, 2, 3, 1, 6]
def baseStart_1875381 : Nat := 118140960795 + 1875381 * 2 ^ 59
def prefixEnd_1875381 : Nat := 4983230072969 + 3 ^ 40 * 1875381 * 2
def baseEnd_1875381 : Nat := 142662498268093673616709

theorem tailTrace_1875381 : CollatzResearch.WordTrace tailWord_1875381 prefixEnd_1875381 142662498268093673616709 := by
  unfold tailWord_1875381
  simp only [CollatzResearch.WordTrace]
  refine ⟨68400764418822401420353997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45600509612548267613569331 68400764418822401420353997)
  ·
    refine ⟨25650286657058400532632749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68400764418822401420353997 25650286657058400532632749)
    ·
      refine ⟨9618857496396900199737281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 25650286657058400532632749 9618857496396900199737281)
      ·
        refine ⟨7214143122297675149802961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9618857496396900199737281 7214143122297675149802961)
        ·
          refine ⟨5410607341723256362352221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7214143122297675149802961 5410607341723256362352221)
          ·
            refine ⟨2028977753146221135882083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5410607341723256362352221 2028977753146221135882083)
            ·
              refine ⟨3043466629719331703823125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2028977753146221135882083 3043466629719331703823125)
              ·
                refine ⟨142662498268093673616709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3043466629719331703823125 142662498268093673616709)
                ·
                  rfl

theorem cell21_1875381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 6].length) (baseStart_1875381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1875381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1875381 prefixEnd_1875381 := by exact prefixLift 1875381
  have htrace : WordTrace (prefixWord ++ tailWord_1875381) baseStart_1875381 baseEnd_1875381 := by
    simpa [prefixWord, tailWord_1875381, baseEnd_1875381] using wordTrace_append hprefix tailTrace_1875381
  have hstable : (prefixWord ++ tailWord_1875381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875381).length < 2 ^ (prefixWord ++ tailWord_1875381).sum := by decide
  have hdescent : baseEnd_1875381 < baseStart_1875381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875423 : List Nat := [1, 1, 2, 3, 3, 1, 10]
def baseStart_1875423 : Nat := 118140960795 + 1875423 * 2 ^ 59
def prefixEnd_1875423 : Nat := 4983230072969 + 3 ^ 40 * 1875423 * 2
def baseEnd_1875423 : Nat := 47555231086277586794449

theorem tailTrace_1875423 : CollatzResearch.WordTrace tailWord_1875423 prefixEnd_1875423 47555231086277586794449 := by
  unfold tailWord_1875423
  simp only [CollatzResearch.WordTrace]
  refine ⟨68402296284670242593382923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45601530856446828395588615 68402296284670242593382923)
  ·
    refine ⟨102603444427005363890074385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68402296284670242593382923 102603444427005363890074385)
    ·
      refine ⟨76952583320254022917555789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102603444427005363890074385 76952583320254022917555789)
      ·
        refine ⟨28857218745095258594083421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 76952583320254022917555789 28857218745095258594083421)
        ·
          refine ⟨10821457029410721972781283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28857218745095258594083421 10821457029410721972781283)
          ·
            refine ⟨16232185544116082959171925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10821457029410721972781283 16232185544116082959171925)
            ·
              refine ⟨47555231086277586794449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16232185544116082959171925 47555231086277586794449)
              ·
                rfl

theorem cell21_1875423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 10].length) (baseStart_1875423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1875423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1875423 prefixEnd_1875423 := by exact prefixLift 1875423
  have htrace : WordTrace (prefixWord ++ tailWord_1875423) baseStart_1875423 baseEnd_1875423 := by
    simpa [prefixWord, tailWord_1875423, baseEnd_1875423] using wordTrace_append hprefix tailTrace_1875423
  have hstable : (prefixWord ++ tailWord_1875423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875423).length < 2 ^ (prefixWord ++ tailWord_1875423).sum := by decide
  have hdescent : baseEnd_1875423 < baseStart_1875423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875485 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 6]
def baseStart_1875485 : Nat := 118140960795 + 1875485 * 2 ^ 59
def prefixEnd_1875485 : Nat := 4983230072969 + 3 ^ 40 * 1875485 * 2
def baseEnd_1875485 : Nat := 428011229021199951116581

theorem tailTrace_1875485 : CollatzResearch.WordTrace tailWord_1875485 prefixEnd_1875485 428011229021199951116581 := by
  unfold tailWord_1875485
  simp only [CollatzResearch.WordTrace]
  refine ⟨68404557610445627182139909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45603038406963751454759939 68404557610445627182139909)
  ·
    refine ⟨12825854551958555096651233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 68404557610445627182139909 12825854551958555096651233)
    ·
      refine ⟨9619390913968916322488425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12825854551958555096651233 9619390913968916322488425)
      ·
        refine ⟨7214543185476687241866319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9619390913968916322488425 7214543185476687241866319)
        ·
          refine ⟨10821814778215030862799479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7214543185476687241866319 10821814778215030862799479)
          ·
            refine ⟨16232722167322546294199219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10821814778215030862799479 16232722167322546294199219)
            ·
              refine ⟨24349083250983819441298829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 16232722167322546294199219 24349083250983819441298829)
              ·
                refine ⟨9130906219118932290487061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 24349083250983819441298829 9130906219118932290487061)
                ·
                  refine ⟨428011229021199951116581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9130906219118932290487061 428011229021199951116581)
                  ·
                    rfl

theorem cell21_1875485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 6].length) (baseStart_1875485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1875485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1875485 prefixEnd_1875485 := by exact prefixLift 1875485
  have htrace : WordTrace (prefixWord ++ tailWord_1875485) baseStart_1875485 baseEnd_1875485 := by
    simpa [prefixWord, tailWord_1875485, baseEnd_1875485] using wordTrace_append hprefix tailTrace_1875485
  have hstable : (prefixWord ++ tailWord_1875485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875485).length < 2 ^ (prefixWord ++ tailWord_1875485).sum := by decide
  have hdescent : baseEnd_1875485 < baseStart_1875485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875488 : List Nat := [2, 1, 1, 6, 1, 3, 1, 1, 5]
def baseStart_1875488 : Nat := 118140960795 + 1875488 * 2 ^ 59
def prefixEnd_1875488 : Nat := 4983230072969 + 3 ^ 40 * 1875488 * 2
def baseEnd_1875488 : Nat := 428011913662072612566575

theorem tailTrace_1875488 : CollatzResearch.WordTrace tailWord_1875488 prefixEnd_1875488 428011913662072612566575 := by
  unfold tailWord_1875488
  simp only [CollatzResearch.WordTrace]
  refine ⟨34202333514717379347249559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45603111352956505796332745 34202333514717379347249559)
  ·
    refine ⟨51303500272076069020874339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34202333514717379347249559 51303500272076069020874339)
    ·
      refine ⟨76955250408114103531311509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51303500272076069020874339 76955250408114103531311509)
      ·
        refine ⟨3607277362880348603030227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 76955250408114103531311509 3607277362880348603030227)
        ·
          refine ⟨5410916044320522904545341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3607277362880348603030227 5410916044320522904545341)
          ·
            refine ⟨2029093516620196089204503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5410916044320522904545341 2029093516620196089204503)
            ·
              refine ⟨3043640274930294133806755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2029093516620196089204503 3043640274930294133806755)
              ·
                refine ⟨4565460412395441200710133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3043640274930294133806755 4565460412395441200710133)
                ·
                  refine ⟨428011913662072612566575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4565460412395441200710133 428011913662072612566575)
                  ·
                    rfl

theorem cell21_1875488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 5].length) (baseStart_1875488 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1875488 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1875488 prefixEnd_1875488 := by exact prefixLift 1875488
  have htrace : WordTrace (prefixWord ++ tailWord_1875488) baseStart_1875488 baseEnd_1875488 := by
    simpa [prefixWord, tailWord_1875488, baseEnd_1875488] using wordTrace_append hprefix tailTrace_1875488
  have hstable : (prefixWord ++ tailWord_1875488).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875488).length < 2 ^ (prefixWord ++ tailWord_1875488).sum := by decide
  have hdescent : baseEnd_1875488 < baseStart_1875488 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875533 : List Nat := [1, 6, 1, 1, 4, 8]
def baseStart_1875533 : Nat := 118140960795 + 1875533 * 2 ^ 59
def prefixEnd_1875533 : Nat := 4983230072969 + 3 ^ 40 * 1875533 * 2
def baseEnd_1875533 : Nat := 15852673454635649419129

theorem tailTrace_1875533 : CollatzResearch.WordTrace tailWord_1875533 prefixEnd_1875533 15852673454635649419129 := by
  unfold tailWord_1875533
  simp only [CollatzResearch.WordTrace]
  refine ⟨68406308314271731379887253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45604205542847820919924835 68406308314271731379887253)
  ·
    refine ⟨3206545702231487408432215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 68406308314271731379887253 3206545702231487408432215)
    ·
      refine ⟨4809818553347231112648323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3206545702231487408432215 4809818553347231112648323)
      ·
        refine ⟨7214727830020846668972485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4809818553347231112648323 7214727830020846668972485)
        ·
          refine ⟨1352761468128908750432341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7214727830020846668972485 1352761468128908750432341)
          ·
            refine ⟨15852673454635649419129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1352761468128908750432341 15852673454635649419129)
            ·
              rfl

theorem cell21_1875533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 8].length) (baseStart_1875533 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1875533 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1875533 prefixEnd_1875533 := by exact prefixLift 1875533
  have htrace : WordTrace (prefixWord ++ tailWord_1875533) baseStart_1875533 baseEnd_1875533 := by
    simpa [prefixWord, tailWord_1875533, baseEnd_1875533] using wordTrace_append hprefix tailTrace_1875533
  have hstable : (prefixWord ++ tailWord_1875533).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875533).length < 2 ^ (prefixWord ++ tailWord_1875533).sum := by decide
  have hdescent : baseEnd_1875533 < baseStart_1875533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875561 : List Nat := [1, 2, 1, 1, 1, 4, 4, 3, 4]
def baseStart_1875561 : Nat := 118140960795 + 1875561 * 2 ^ 59
def prefixEnd_1875561 : Nat := 4983230072969 + 3 ^ 40 * 1875561 * 2
def baseEnd_1875561 : Nat := 428028573256640707849759

theorem tailTrace_1875561 : CollatzResearch.WordTrace tailWord_1875561 prefixEnd_1875561 428028573256640707849759 := by
  unfold tailWord_1875561
  simp only [CollatzResearch.WordTrace]
  refine ⟨68407329558170292161906537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45604886372113528107937691 68407329558170292161906537)
  ·
    refine ⟨51305497168627719121429903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68407329558170292161906537 51305497168627719121429903)
    ·
      refine ⟨76958245752941578682144855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51305497168627719121429903 76958245752941578682144855)
      ·
        refine ⟨115437368629412368023217283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76958245752941578682144855 115437368629412368023217283)
        ·
          refine ⟨173156052944118552034825925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115437368629412368023217283 173156052944118552034825925)
          ·
            refine ⟨32466759927022228506529861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173156052944118552034825925 32466759927022228506529861)
            ·
              refine ⟨6087517486316667844974349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32466759927022228506529861 6087517486316667844974349)
              ·
                refine ⟨2282819057368750441865381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6087517486316667844974349 2282819057368750441865381)
                ·
                  refine ⟨428028573256640707849759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2282819057368750441865381 428028573256640707849759)
                  ·
                    rfl

theorem cell21_1875561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 3, 4].length) (baseStart_1875561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1875561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1875561 prefixEnd_1875561 := by exact prefixLift 1875561
  have htrace : WordTrace (prefixWord ++ tailWord_1875561) baseStart_1875561 baseEnd_1875561 := by
    simpa [prefixWord, tailWord_1875561, baseEnd_1875561] using wordTrace_append hprefix tailTrace_1875561
  have hstable : (prefixWord ++ tailWord_1875561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875561).length < 2 ^ (prefixWord ++ tailWord_1875561).sum := by decide
  have hdescent : baseEnd_1875561 < baseStart_1875561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875668 : List Nat := [2, 4, 1, 3, 1, 1, 1, 8]
def baseStart_1875668 : Nat := 118140960795 + 1875668 * 2 ^ 59
def prefixEnd_1875668 : Nat := 4983230072969 + 3 ^ 40 * 1875668 * 2
def baseEnd_1875668 : Nat := 142684330704810766522069

theorem tailTrace_1875668 : CollatzResearch.WordTrace tailWord_1875668 prefixEnd_1875668 142684330704810766522069 := by
  unfold tailWord_1875668
  simp only [CollatzResearch.WordTrace]
  refine ⟨34205616084391324718025829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45607488112521766290701105 34205616084391324718025829)
  ·
    refine ⟨6413553015823373384629843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 34205616084391324718025829 6413553015823373384629843)
    ·
      refine ⟨9620329523735060076944765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6413553015823373384629843 9620329523735060076944765)
      ·
        refine ⟨3607623571400647528854287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 9620329523735060076944765 3607623571400647528854287)
        ·
          refine ⟨5411435357100971293281431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3607623571400647528854287 5411435357100971293281431)
          ·
            refine ⟨8117153035651456939922147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5411435357100971293281431 8117153035651456939922147)
            ·
              refine ⟨12175729553477185409883221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8117153035651456939922147 12175729553477185409883221)
              ·
                refine ⟨142684330704810766522069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12175729553477185409883221 142684330704810766522069)
                ·
                  rfl

theorem cell21_1875668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 8].length) (baseStart_1875668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1875668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1875668 prefixEnd_1875668 := by exact prefixLift 1875668
  have htrace : WordTrace (prefixWord ++ tailWord_1875668) baseStart_1875668 baseEnd_1875668 := by
    simpa [prefixWord, tailWord_1875668, baseEnd_1875668] using wordTrace_append hprefix tailTrace_1875668
  have hstable : (prefixWord ++ tailWord_1875668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875668).length < 2 ^ (prefixWord ++ tailWord_1875668).sum := by decide
  have hdescent : baseEnd_1875668 < baseStart_1875668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875696 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 6]
def baseStart_1875696 : Nat := 118140960795 + 1875696 * 2 ^ 59
def prefixEnd_1875696 : Nat := 4983230072969 + 3 ^ 40 * 1875696 * 2
def baseEnd_1875696 : Nat := 428059382095910473099483

theorem tailTrace_1875696 : CollatzResearch.WordTrace tailWord_1875696 prefixEnd_1875696 428059382095910473099483 := by
  unfold tailWord_1875696
  simp only [CollatzResearch.WordTrace]
  refine ⟨34206126706340605109035471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45608168941787473478713961 34206126706340605109035471)
  ·
    refine ⟨51309190059510907663553207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34206126706340605109035471 51309190059510907663553207)
    ·
      refine ⟨76963785089266361495329811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51309190059510907663553207 76963785089266361495329811)
      ·
        refine ⟨115445677633899542242994717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76963785089266361495329811 115445677633899542242994717)
        ·
          refine ⟨43292129112712328341123019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 115445677633899542242994717 43292129112712328341123019)
          ·
            refine ⟨64938193669068492511684529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43292129112712328341123019 64938193669068492511684529)
            ·
              refine ⟨48703645251801369383763397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64938193669068492511684529 48703645251801369383763397)
              ·
                refine ⟨9131933484712756759455637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 48703645251801369383763397 9131933484712756759455637)
                ·
                  refine ⟨428059382095910473099483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9131933484712756759455637 428059382095910473099483)
                  ·
                    rfl

theorem cell21_1875696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 6].length) (baseStart_1875696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1875696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1875696 prefixEnd_1875696 := by exact prefixLift 1875696
  have htrace : WordTrace (prefixWord ++ tailWord_1875696) baseStart_1875696 baseEnd_1875696 := by
    simpa [prefixWord, tailWord_1875696, baseEnd_1875696] using wordTrace_append hprefix tailTrace_1875696
  have hstable : (prefixWord ++ tailWord_1875696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875696).length < 2 ^ (prefixWord ++ tailWord_1875696).sum := by decide
  have hdescent : baseEnd_1875696 < baseStart_1875696 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875713 : List Nat := [1, 2, 4, 1, 1, 1, 3, 4, 4]
def baseStart_1875713 : Nat := 118140960795 + 1875713 * 2 ^ 59
def prefixEnd_1875713 : Nat := 4983230072969 + 3 ^ 40 * 1875713 * 2
def baseEnd_1875713 : Nat := 428063261727522221316115

theorem tailTrace_1875713 : CollatzResearch.WordTrace tailWord_1875713 prefixEnd_1875713 428063261727522221316115 := by
  unfold tailWord_1875713
  simp only [CollatzResearch.WordTrace]
  refine ⟨68412873453619622121439793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45608582302413081414293195 68412873453619622121439793)
  ·
    refine ⟨51309655090214716591079845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68412873453619622121439793 51309655090214716591079845)
    ·
      refine ⟨9620560329415259360827471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51309655090214716591079845 9620560329415259360827471)
      ·
        refine ⟨14430840494122889041241207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9620560329415259360827471 14430840494122889041241207)
        ·
          refine ⟨21646260741184333561861811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14430840494122889041241207 21646260741184333561861811)
          ·
            refine ⟨32469391111776500342792717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21646260741184333561861811 32469391111776500342792717)
            ·
              refine ⟨12176021666916187628547269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32469391111776500342792717 12176021666916187628547269)
              ·
                refine ⟨2283004062546785180352613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 12176021666916187628547269 2283004062546785180352613)
                ·
                  refine ⟨428063261727522221316115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2283004062546785180352613 428063261727522221316115)
                  ·
                    rfl

theorem cell21_1875713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 4].length) (baseStart_1875713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1875713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1875713 prefixEnd_1875713 := by exact prefixLift 1875713
  have htrace : WordTrace (prefixWord ++ tailWord_1875713) baseStart_1875713 baseEnd_1875713 := by
    simpa [prefixWord, tailWord_1875713, baseEnd_1875713] using wordTrace_append hprefix tailTrace_1875713
  have hstable : (prefixWord ++ tailWord_1875713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875713).length < 2 ^ (prefixWord ++ tailWord_1875713).sum := by decide
  have hdescent : baseEnd_1875713 < baseStart_1875713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875716 : List Nat := [2, 3, 2, 2, 1, 3, 1, 4, 3]
def baseStart_1875716 : Nat := 118140960795 + 1875716 * 2 ^ 59
def prefixEnd_1875716 : Nat := 4983230072969 + 3 ^ 40 * 1875716 * 2
def baseEnd_1875716 : Nat := 428063946368394882766109

theorem tailTrace_1875716 : CollatzResearch.WordTrace tailWord_1875716 prefixEnd_1875716 428063946368394882766109 := by
  unfold tailWord_1875716
  simp only [CollatzResearch.WordTrace]
  refine ⟨34206491436304376816899501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45608655248405835755866001 34206491436304376816899501)
  ·
    refine ⟨12827434288614141306337313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34206491436304376816899501 12827434288614141306337313)
    ·
      refine ⟨9620575716460605979752985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12827434288614141306337313 9620575716460605979752985)
      ·
        refine ⟨7215431787345454484814739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9620575716460605979752985 7215431787345454484814739)
        ·
          refine ⟨10823147681018181727222109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7215431787345454484814739 10823147681018181727222109)
          ·
            refine ⟨4058680380381818147708291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 10823147681018181727222109 4058680380381818147708291)
            ·
              refine ⟨6088020570572727221562437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4058680380381818147708291 6088020570572727221562437)
              ·
                refine ⟨1141503856982386354042957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6088020570572727221562437 1141503856982386354042957)
                ·
                  refine ⟨428063946368394882766109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1141503856982386354042957 428063946368394882766109)
                  ·
                    rfl

theorem cell21_1875716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 3].length) (baseStart_1875716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1875716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1875716 prefixEnd_1875716 := by exact prefixLift 1875716
  have htrace : WordTrace (prefixWord ++ tailWord_1875716) baseStart_1875716 baseEnd_1875716 := by
    simpa [prefixWord, tailWord_1875716, baseEnd_1875716] using wordTrace_append hprefix tailTrace_1875716
  have hstable : (prefixWord ++ tailWord_1875716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875716).length < 2 ^ (prefixWord ++ tailWord_1875716).sum := by decide
  have hdescent : baseEnd_1875716 < baseStart_1875716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875744 : List Nat := [2, 1, 1, 5, 1, 1, 5, 5]
def baseStart_1875744 : Nat := 118140960795 + 1875744 * 2 ^ 59
def prefixEnd_1875744 : Nat := 4983230072969 + 3 ^ 40 * 1875744 * 2
def baseEnd_1875744 : Nat := 142690112116624352099795

theorem tailTrace_1875744 : CollatzResearch.WordTrace tailWord_1875744 prefixEnd_1875744 142690112116624352099795 := by
  unfold tailWord_1875744
  simp only [CollatzResearch.WordTrace]
  refine ⟨34207002058253657207909143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45609336077671542943878857 34207002058253657207909143)
  ·
    refine ⟨51310503087380485811863715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34207002058253657207909143 51310503087380485811863715)
    ·
      refine ⟨76965754631070728717795573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51310503087380485811863715 76965754631070728717795573)
      ·
        refine ⟨7215539496662880817293335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 76965754631070728717795573 7215539496662880817293335)
        ·
          refine ⟨10823309244994321225940003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7215539496662880817293335 10823309244994321225940003)
          ·
            refine ⟨16234963867491481838910005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10823309244994321225940003 16234963867491481838910005)
            ·
              refine ⟨1522027862577326422397813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16234963867491481838910005 1522027862577326422397813)
              ·
                refine ⟨142690112116624352099795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1522027862577326422397813 142690112116624352099795)
                ·
                  rfl

theorem cell21_1875744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 5].length) (baseStart_1875744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1875744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1875744 prefixEnd_1875744 := by exact prefixLift 1875744
  have htrace : WordTrace (prefixWord ++ tailWord_1875744) baseStart_1875744 baseEnd_1875744 := by
    simpa [prefixWord, tailWord_1875744, baseEnd_1875744] using wordTrace_append hprefix tailTrace_1875744
  have hstable : (prefixWord ++ tailWord_1875744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875744).length < 2 ^ (prefixWord ++ tailWord_1875744).sum := by decide
  have hdescent : baseEnd_1875744 < baseStart_1875744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875775 : List Nat := [1, 1, 2, 2, 6, 1, 2, 1, 5]
def baseStart_1875775 : Nat := 118140960795 + 1875775 * 2 ^ 59
def prefixEnd_1875775 : Nat := 4983230072969 + 3 ^ 40 * 1875775 * 2
def baseEnd_1875775 : Nat := 428077410972223891282655

theorem tailTrace_1875775 : CollatzResearch.WordTrace tailWord_1875775 prefixEnd_1875775 428077410972223891282655 := by
  unfold tailWord_1875775
  simp only [CollatzResearch.WordTrace]
  refine ⟨68415134779395006710196779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45610089852930004473464519 68415134779395006710196779)
  ·
    refine ⟨102622702169092510065295169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68415134779395006710196779 102622702169092510065295169)
    ·
      refine ⟨76967026626819382548971377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102622702169092510065295169 76967026626819382548971377)
      ·
        refine ⟨57725269970114536911728533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 76967026626819382548971377 57725269970114536911728533)
        ·
          refine ⟨2705872029849118917737275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 57725269970114536911728533 2705872029849118917737275)
          ·
            refine ⟨4058808044773678376605913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2705872029849118917737275 4058808044773678376605913)
            ·
              refine ⟨3044106033580258782454435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4058808044773678376605913 3044106033580258782454435)
              ·
                refine ⟨4566159050370388173681653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3044106033580258782454435 4566159050370388173681653)
                ·
                  refine ⟨428077410972223891282655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4566159050370388173681653 428077410972223891282655)
                  ·
                    rfl

theorem cell21_1875775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 5].length) (baseStart_1875775 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1875775 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1875775 prefixEnd_1875775 := by exact prefixLift 1875775
  have htrace : WordTrace (prefixWord ++ tailWord_1875775) baseStart_1875775 baseEnd_1875775 := by
    simpa [prefixWord, tailWord_1875775, baseEnd_1875775] using wordTrace_append hprefix tailTrace_1875775
  have hstable : (prefixWord ++ tailWord_1875775).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875775).length < 2 ^ (prefixWord ++ tailWord_1875775).sum := by decide
  have hdescent : baseEnd_1875775 < baseStart_1875775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875817 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 7]
def baseStart_1875817 : Nat := 118140960795 + 1875817 * 2 ^ 59
def prefixEnd_1875817 : Nat := 4983230072969 + 3 ^ 40 * 1875817 * 2
def baseEnd_1875817 : Nat := 428086995944441151582569

theorem tailTrace_1875817 : CollatzResearch.WordTrace tailWord_1875817 prefixEnd_1875817 428086995944441151582569 := by
  unfold tailWord_1875817
  simp only [CollatzResearch.WordTrace]
  refine ⟨68416666645242847883225705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45611111096828565255483803 68416666645242847883225705)
  ·
    refine ⟨51312499983932135912419279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68416666645242847883225705 51312499983932135912419279)
    ·
      refine ⟨76968749975898203868628919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51312499983932135912419279 76968749975898203868628919)
      ·
        refine ⟨115453124963847305802943379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76968749975898203868628919 115453124963847305802943379)
        ·
          refine ⟨173179687445770958704415069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115453124963847305802943379 173179687445770958704415069)
          ·
            refine ⟨64942382792164109514155651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173179687445770958704415069 64942382792164109514155651)
            ·
              refine ⟨97413574188246164271233477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 64942382792164109514155651 97413574188246164271233477)
              ·
                refine ⟨18265045160296155800856277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 97413574188246164271233477 18265045160296155800856277)
                ·
                  refine ⟨428086995944441151582569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18265045160296155800856277 428086995944441151582569)
                  ·
                    rfl

theorem cell21_1875817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 7].length) (baseStart_1875817 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1875817 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1875817 prefixEnd_1875817 := by exact prefixLift 1875817
  have htrace : WordTrace (prefixWord ++ tailWord_1875817) baseStart_1875817 baseEnd_1875817 := by
    simpa [prefixWord, tailWord_1875817, baseEnd_1875817] using wordTrace_append hprefix tailTrace_1875817
  have hstable : (prefixWord ++ tailWord_1875817).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875817).length < 2 ^ (prefixWord ++ tailWord_1875817).sum := by decide
  have hdescent : baseEnd_1875817 < baseStart_1875817 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875834 : List Nat := [3, 1, 1, 1, 1, 1, 7, 1, 5]
def baseStart_1875834 : Nat := 118140960795 + 1875834 * 2 ^ 59
def prefixEnd_1875834 : Nat := 4983230072969 + 3 ^ 40 * 1875834 * 2
def baseEnd_1875834 : Nat := 428090875576052899799201

theorem tailTrace_1875834 : CollatzResearch.WordTrace tailWord_1875834 prefixEnd_1875834 428090875576052899799201 := by
  unfold tailWord_1875834
  simp only [CollatzResearch.WordTrace]
  refine ⟨17104321671545314946648639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45611524457454173191063037 17104321671545314946648639)
  ·
    refine ⟨25656482507317972419972959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17104321671545314946648639 25656482507317972419972959)
    ·
      refine ⟨38484723760976958629959439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25656482507317972419972959 38484723760976958629959439)
      ·
        refine ⟨57727085641465437944939159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38484723760976958629959439 57727085641465437944939159)
        ·
          refine ⟨86590628462198156917408739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57727085641465437944939159 86590628462198156917408739)
          ·
            refine ⟨129885942693297235376113109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 86590628462198156917408739 129885942693297235376113109)
            ·
              refine ⟨3044201781874153954127651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 129885942693297235376113109 3044201781874153954127651)
              ·
                refine ⟨4566302672811230931191477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3044201781874153954127651 4566302672811230931191477)
                ·
                  refine ⟨428090875576052899799201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4566302672811230931191477 428090875576052899799201)
                  ·
                    rfl

theorem cell21_1875834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 5].length) (baseStart_1875834 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1875834 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1875834 prefixEnd_1875834 := by exact prefixLift 1875834
  have htrace : WordTrace (prefixWord ++ tailWord_1875834) baseStart_1875834 baseEnd_1875834 := by
    simpa [prefixWord, tailWord_1875834, baseEnd_1875834] using wordTrace_append hprefix tailTrace_1875834
  have hstable : (prefixWord ++ tailWord_1875834).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875834).length < 2 ^ (prefixWord ++ tailWord_1875834).sum := by decide
  have hdescent : baseEnd_1875834 < baseStart_1875834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875879 : List Nat := [1, 1, 6, 1, 2, 10]
def baseStart_1875879 : Nat := 118140960795 + 1875879 * 2 ^ 59
def prefixEnd_1875879 : Nat := 4983230072969 + 3 ^ 40 * 1875879 * 2
def baseEnd_1875879 : Nat := 15855597969968252649967

theorem tailTrace_1875879 : CollatzResearch.WordTrace tailWord_1875879 prefixEnd_1875879 15855597969968252649967 := by
  unfold tailWord_1875879
  simp only [CollatzResearch.WordTrace]
  refine ⟨68418927971018232471982691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45612618647345488314655127 68418927971018232471982691)
  ·
    refine ⟨102628391956527348707974037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68418927971018232471982691 102628391956527348707974037)
    ·
      refine ⟨4810705872962219470686283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 102628391956527348707974037 4810705872962219470686283)
      ·
        refine ⟨7216058809443329206029425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4810705872962219470686283 7216058809443329206029425)
        ·
          refine ⟨5412044107082496904522069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7216058809443329206029425 5412044107082496904522069)
          ·
            refine ⟨15855597969968252649967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5412044107082496904522069 15855597969968252649967)
            ·
              rfl

theorem cell21_1875879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 10].length) (baseStart_1875879 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1875879 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1875879 prefixEnd_1875879 := by exact prefixLift 1875879
  have htrace : WordTrace (prefixWord ++ tailWord_1875879) baseStart_1875879 baseEnd_1875879 := by
    simpa [prefixWord, tailWord_1875879, baseEnd_1875879] using wordTrace_append hprefix tailTrace_1875879
  have hstable : (prefixWord ++ tailWord_1875879).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875879).length < 2 ^ (prefixWord ++ tailWord_1875879).sum := by decide
  have hdescent : baseEnd_1875879 < baseStart_1875879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1875927 : List Nat := [1, 1, 3, 2, 1, 1, 6, 3, 3]
def baseStart_1875927 : Nat := 118140960795 + 1875927 * 2 ^ 59
def prefixEnd_1875927 : Nat := 4983230072969 + 3 ^ 40 * 1875927 * 2
def baseEnd_1875927 : Nat := 428112099443105404749011

theorem tailTrace_1875927 : CollatzResearch.WordTrace tailWord_1875927 prefixEnd_1875927 428112099443105404749011 := by
  unfold tailWord_1875927
  simp only [CollatzResearch.WordTrace]
  refine ⟨68420678674844336669730035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45613785783229557779820023 68420678674844336669730035)
  ·
    refine ⟨102631018012266505004595053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68420678674844336669730035 102631018012266505004595053)
    ·
      refine ⟨38486631754599939376723145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 102631018012266505004595053 38486631754599939376723145)
      ·
        refine ⟨28864973815949954532542359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38486631754599939376723145 28864973815949954532542359)
        ·
          refine ⟨43297460723924931798813539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28864973815949954532542359 43297460723924931798813539)
          ·
            refine ⟨64946191085887397698220309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 43297460723924931798813539 64946191085887397698220309)
            ·
              refine ⟨3044352707150971767104077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 64946191085887397698220309 3044352707150971767104077)
              ·
                refine ⟨1141632265181614412664029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3044352707150971767104077 1141632265181614412664029)
                ·
                  refine ⟨428112099443105404749011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1141632265181614412664029 428112099443105404749011)
                  ·
                    rfl

theorem cell21_1875927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 3].length) (baseStart_1875927 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1875927 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1875927 prefixEnd_1875927 := by exact prefixLift 1875927
  have htrace : WordTrace (prefixWord ++ tailWord_1875927) baseStart_1875927 baseEnd_1875927 := by
    simpa [prefixWord, tailWord_1875927, baseEnd_1875927] using wordTrace_append hprefix tailTrace_1875927
  have hstable : (prefixWord ++ tailWord_1875927).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1875927).length < 2 ^ (prefixWord ++ tailWord_1875927).sum := by decide
  have hdescent : baseEnd_1875927 < baseStart_1875927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1875927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876017 : List Nat := [1, 2, 2, 3, 1, 4, 1, 3, 4]
def baseStart_1876017 : Nat := 118140960795 + 1876017 * 2 ^ 59
def prefixEnd_1876017 : Nat := 4983230072969 + 3 ^ 40 * 1876017 * 2
def baseEnd_1876017 : Nat := 428132638669285248248827

theorem tailTrace_1876017 : CollatzResearch.WordTrace tailWord_1876017 prefixEnd_1876017 428132638669285248248827 := by
  unfold tailWord_1876017
  simp only [CollatzResearch.WordTrace]
  refine ⟨68423961244518282040506305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45615974163012188027004203 68423961244518282040506305)
  ·
    refine ⟨51317970933388711530379729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68423961244518282040506305 51317970933388711530379729)
    ·
      refine ⟨38488478200041533647784797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51317970933388711530379729 38488478200041533647784797)
      ·
        refine ⟨14433179325015575117919299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 38488478200041533647784797 14433179325015575117919299)
        ·
          refine ⟨21649768987523362676878949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14433179325015575117919299 21649768987523362676878949)
          ·
            refine ⟨4059331685160630501914803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21649768987523362676878949 4059331685160630501914803)
            ·
              refine ⟨6088997527740945752872205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4059331685160630501914803 6088997527740945752872205)
              ·
                refine ⟨2283374072902854657327077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6088997527740945752872205 2283374072902854657327077)
                ·
                  refine ⟨428132638669285248248827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2283374072902854657327077 428132638669285248248827)
                  ·
                    rfl

theorem cell21_1876017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 4].length) (baseStart_1876017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876017 prefixEnd_1876017 := by exact prefixLift 1876017
  have htrace : WordTrace (prefixWord ++ tailWord_1876017) baseStart_1876017 baseEnd_1876017 := by
    simpa [prefixWord, tailWord_1876017, baseEnd_1876017] using wordTrace_append hprefix tailTrace_1876017
  have hstable : (prefixWord ++ tailWord_1876017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876017).length < 2 ^ (prefixWord ++ tailWord_1876017).sum := by decide
  have hdescent : baseEnd_1876017 < baseStart_1876017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876054 : List Nat := [5, 2, 2, 1, 1, 1, 4, 2, 3]
def baseStart_1876054 : Nat := 118140960795 + 1876054 * 2 ^ 59
def prefixEnd_1876054 : Nat := 4983230072969 + 3 ^ 40 * 1876054 * 2
def baseEnd_1876054 : Nat := 428141082573381406132085

theorem tailTrace_1876054 : CollatzResearch.WordTrace tailWord_1876054 prefixEnd_1876054 428141082573381406132085 := by
  unfold tailWord_1876054
  simp only [CollatzResearch.WordTrace]
  refine ⟨4276581921586514834975201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45616873830256158239735477 4276581921586514834975201)
  ·
    refine ⟨3207436441189886126231401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4276581921586514834975201 3207436441189886126231401)
    ·
      refine ⟨2405577330892414594673551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3207436441189886126231401 2405577330892414594673551)
      ·
        refine ⟨3608365996338621892010327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2405577330892414594673551 3608365996338621892010327)
        ·
          refine ⟨5412548994507932838015491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3608365996338621892010327 5412548994507932838015491)
          ·
            refine ⟨8118823491761899257023237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5412548994507932838015491 8118823491761899257023237)
            ·
              refine ⟨1522279404705356110691857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8118823491761899257023237 1522279404705356110691857)
              ·
                refine ⟨1141709553529017083018893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1522279404705356110691857 1141709553529017083018893)
                ·
                  refine ⟨428141082573381406132085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1141709553529017083018893 428141082573381406132085)
                  ·
                    rfl

theorem cell21_1876054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_1876054 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876054 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876054 prefixEnd_1876054 := by exact prefixLift 1876054
  have htrace : WordTrace (prefixWord ++ tailWord_1876054) baseStart_1876054 baseEnd_1876054 := by
    simpa [prefixWord, tailWord_1876054, baseEnd_1876054] using wordTrace_append hprefix tailTrace_1876054
  have hstable : (prefixWord ++ tailWord_1876054).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876054).length < 2 ^ (prefixWord ++ tailWord_1876054).sum := by decide
  have hdescent : baseEnd_1876054 < baseStart_1876054 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876141 : List Nat := [1, 5, 2, 1, 2, 3, 2, 5]
def baseStart_1876141 : Nat := 118140960795 + 1876141 * 2 ^ 59
def prefixEnd_1876141 : Nat := 4983230072969 + 3 ^ 40 * 1876141 * 2
def baseEnd_1876141 : Nat := 142720312386229529393969

theorem tailTrace_1876141 : CollatzResearch.WordTrace tailWord_1876141 prefixEnd_1876141 142720312386229529393969 := by
  unfold tailWord_1876141
  simp only [CollatzResearch.WordTrace]
  refine ⟨68428483896069051218020277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45618989264046034145346851 68428483896069051218020277)
  ·
    refine ⟨6415170365256473551689401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 68428483896069051218020277 6415170365256473551689401)
    ·
      refine ⟨4811377773942355163767051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6415170365256473551689401 4811377773942355163767051)
      ·
        refine ⟨7217066660913532745650577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4811377773942355163767051 7217066660913532745650577)
        ·
          refine ⟨5412799995685149559237933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7217066660913532745650577 5412799995685149559237933)
          ·
            refine ⟨2029799998381931084714225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5412799995685149559237933 2029799998381931084714225)
            ·
              refine ⟨1522349998786448313535669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2029799998381931084714225 1522349998786448313535669)
              ·
                refine ⟨142720312386229529393969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1522349998786448313535669 142720312386229529393969)
                ·
                  rfl

theorem cell21_1876141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 5].length) (baseStart_1876141 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876141 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876141 prefixEnd_1876141 := by exact prefixLift 1876141
  have htrace : WordTrace (prefixWord ++ tailWord_1876141) baseStart_1876141 baseEnd_1876141 := by
    simpa [prefixWord, tailWord_1876141, baseEnd_1876141] using wordTrace_append hprefix tailTrace_1876141
  have hstable : (prefixWord ++ tailWord_1876141).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876141).length < 2 ^ (prefixWord ++ tailWord_1876141).sum := by decide
  have hdescent : baseEnd_1876141 < baseStart_1876141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876172 : List Nat := [2, 2, 1, 6, 1, 2, 1, 1, 5]
def baseStart_1876172 : Nat := 118140960795 + 1876172 * 2 ^ 59
def prefixEnd_1876172 : Nat := 4983230072969 + 3 ^ 40 * 1876172 * 2
def baseEnd_1876172 : Nat := 428168011781039423165177

theorem tailTrace_1876172 : CollatzResearch.WordTrace tailWord_1876172 prefixEnd_1876172 428168011781039423165177 := by
  unfold tailWord_1876172
  simp only [CollatzResearch.WordTrace]
  refine ⟨34214807279478371756199385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45619743039304495674932513 34214807279478371756199385)
  ·
    refine ⟨25661105459608778817149539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34214807279478371756199385 25661105459608778817149539)
    ·
      refine ⟨38491658189413168225724309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25661105459608778817149539 38491658189413168225724309)
      ·
        refine ⟨1804296477628742260580827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 38491658189413168225724309 1804296477628742260580827)
        ·
          refine ⟨2706444716443113390871241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1804296477628742260580827 2706444716443113390871241)
          ·
            refine ⟨2029833537332335043153431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2706444716443113390871241 2029833537332335043153431)
            ·
              refine ⟨3044750305998502564730147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2029833537332335043153431 3044750305998502564730147)
              ·
                refine ⟨4567125458997753847095221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3044750305998502564730147 4567125458997753847095221)
                ·
                  refine ⟨428168011781039423165177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4567125458997753847095221 428168011781039423165177)
                  ·
                    rfl

theorem cell21_1876172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 5].length) (baseStart_1876172 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876172 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876172 prefixEnd_1876172 := by exact prefixLift 1876172
  have htrace : WordTrace (prefixWord ++ tailWord_1876172) baseStart_1876172 baseEnd_1876172 := by
    simpa [prefixWord, tailWord_1876172, baseEnd_1876172] using wordTrace_append hprefix tailTrace_1876172
  have hstable : (prefixWord ++ tailWord_1876172).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876172).length < 2 ^ (prefixWord ++ tailWord_1876172).sum := by decide
  have hdescent : baseEnd_1876172 < baseStart_1876172 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876259 : List Nat := [1, 1, 1, 4, 2, 2, 5, 5]
def baseStart_1876259 : Nat := 118140960795 + 1876259 * 2 ^ 59
def prefixEnd_1876259 : Nat := 4983230072969 + 3 ^ 40 * 1876259 * 2
def baseEnd_1876259 : Nat := 142729288788782201738333

theorem tailTrace_1876259 : CollatzResearch.WordTrace tailWord_1876259 prefixEnd_1876259 142729288788782201738333 := by
  unfold tailWord_1876259
  simp only [CollatzResearch.WordTrace]
  refine ⟨68432787709641557370815831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45621858473094371580543887 68432787709641557370815831)
  ·
    refine ⟨102649181564462336056223747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68432787709641557370815831 102649181564462336056223747)
    ·
      refine ⟨153973772346693504084335621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102649181564462336056223747 153973772346693504084335621)
      ·
        refine ⟨28870082315005032015812929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 153973772346693504084335621 28870082315005032015812929)
        ·
          refine ⟨21652561736253774011859697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28870082315005032015812929 21652561736253774011859697)
          ·
            refine ⟨16239421302190330508894773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21652561736253774011859697 16239421302190330508894773)
            ·
              refine ⟨1522445747080343485208885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 16239421302190330508894773 1522445747080343485208885)
              ·
                refine ⟨142729288788782201738333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1522445747080343485208885 142729288788782201738333)
                ·
                  rfl

theorem cell21_1876259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 5].length) (baseStart_1876259 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876259 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876259 prefixEnd_1876259 := by exact prefixLift 1876259
  have htrace : WordTrace (prefixWord ++ tailWord_1876259) baseStart_1876259 baseEnd_1876259 := by
    simpa [prefixWord, tailWord_1876259, baseEnd_1876259] using wordTrace_append hprefix tailTrace_1876259
  have hstable : (prefixWord ++ tailWord_1876259).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876259).length < 2 ^ (prefixWord ++ tailWord_1876259).sum := by decide
  have hdescent : baseEnd_1876259 < baseStart_1876259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876355 : List Nat := [1, 1, 1, 3, 7, 1, 2, 1, 4]
def baseStart_1876355 : Nat := 118140960795 + 1876355 * 2 ^ 59
def prefixEnd_1876355 : Nat := 4983230072969 + 3 ^ 40 * 1876355 * 2
def baseEnd_1876355 : Nat := 428209774874271771614803

theorem tailTrace_1876355 : CollatzResearch.WordTrace tailWord_1876355 prefixEnd_1876355 428209774874271771614803 := by
  unfold tailWord_1876355
  simp only [CollatzResearch.WordTrace]
  refine ⟨68436289117293765766310519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45624192744862510510873679 68436289117293765766310519)
  ·
    refine ⟨102654433675940648649465779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68436289117293765766310519 102654433675940648649465779)
    ·
      refine ⟨153981650513910972974198669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102654433675940648649465779 153981650513910972974198669)
      ·
        refine ⟨57743118942716614865324501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 153981650513910972974198669 57743118942716614865324501)
        ·
          refine ⟨1353354350219920660906043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 57743118942716614865324501 1353354350219920660906043)
          ·
            refine ⟨2030031525329880991359065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353354350219920660906043 2030031525329880991359065)
            ·
              refine ⟨1522523643997410743519299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2030031525329880991359065 1522523643997410743519299)
              ·
                refine ⟨2283785465996116115278949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1522523643997410743519299 2283785465996116115278949)
                ·
                  refine ⟨428209774874271771614803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2283785465996116115278949 428209774874271771614803)
                  ·
                    rfl

theorem cell21_1876355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 4].length) (baseStart_1876355 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876355 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876355 prefixEnd_1876355 := by exact prefixLift 1876355
  have htrace : WordTrace (prefixWord ++ tailWord_1876355) baseStart_1876355 baseEnd_1876355 := by
    simpa [prefixWord, tailWord_1876355, baseEnd_1876355] using wordTrace_append hprefix tailTrace_1876355
  have hstable : (prefixWord ++ tailWord_1876355).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876355).length < 2 ^ (prefixWord ++ tailWord_1876355).sum := by decide
  have hdescent : baseEnd_1876355 < baseStart_1876355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876428 : List Nat := [2, 2, 1, 4, 3, 1, 3, 5]
def baseStart_1876428 : Nat := 118140960795 + 1876428 * 2 ^ 59
def prefixEnd_1876428 : Nat := 4983230072969 + 3 ^ 40 * 1876428 * 2
def baseEnd_1876428 : Nat := 142742144822946622299329

theorem tailTrace_1876428 : CollatzResearch.WordTrace tailWord_1876428 prefixEnd_1876428 142742144822946622299329 := by
  unfold tailWord_1876428
  simp only [CollatzResearch.WordTrace]
  refine ⟨34219475823014649616858969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45625967764019532822478625 34219475823014649616858969)
  ·
    refine ⟨25664606867260987212644227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34219475823014649616858969 25664606867260987212644227)
    ·
      refine ⟨38496910300891480818966341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25664606867260987212644227 38496910300891480818966341)
      ·
        refine ⟨7218170681417152653556189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 38496910300891480818966341 7218170681417152653556189)
        ·
          refine ⟨2706814005531432245083571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7218170681417152653556189 2706814005531432245083571)
          ·
            refine ⟨4060221008297148367625357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2706814005531432245083571 4060221008297148367625357)
            ·
              refine ⟨1522582878111430637859509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4060221008297148367625357 1522582878111430637859509)
              ·
                refine ⟨142742144822946622299329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1522582878111430637859509 142742144822946622299329)
                ·
                  rfl

theorem cell21_1876428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 5].length) (baseStart_1876428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876428 prefixEnd_1876428 := by exact prefixLift 1876428
  have htrace : WordTrace (prefixWord ++ tailWord_1876428) baseStart_1876428 baseEnd_1876428 := by
    simpa [prefixWord, tailWord_1876428, baseEnd_1876428] using wordTrace_append hprefix tailTrace_1876428
  have hstable : (prefixWord ++ tailWord_1876428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876428).length < 2 ^ (prefixWord ++ tailWord_1876428).sum := by decide
  have hdescent : baseEnd_1876428 < baseStart_1876428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876456 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 6]
def baseStart_1876456 : Nat := 118140960795 + 1876456 * 2 ^ 59
def prefixEnd_1876456 : Nat := 4983230072969 + 3 ^ 40 * 1876456 * 2
def baseEnd_1876456 : Nat := 428232824450318040431263

theorem tailTrace_1876456 : CollatzResearch.WordTrace tailWord_1876456 prefixEnd_1876456 428232824450318040431263 := by
  unfold tailWord_1876456
  simp only [CollatzResearch.WordTrace]
  refine ⟨34219986444963930007868611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45626648593285240010491481 34219986444963930007868611)
  ·
    refine ⟨51329979667445895011802917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34219986444963930007868611 51329979667445895011802917)
    ·
      refine ⟨9624371187646105314713047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 51329979667445895011802917 9624371187646105314713047)
      ·
        refine ⟨14436556781469157972069571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9624371187646105314713047 14436556781469157972069571)
        ·
          refine ⟨21654835172203736958104357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14436556781469157972069571 21654835172203736958104357)
          ·
            refine ⟨4060281594788200679644567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 21654835172203736958104357 4060281594788200679644567)
            ·
              refine ⟨6090422392182301019466851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4060281594788200679644567 6090422392182301019466851)
              ·
                refine ⟨9135633588273451529200277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6090422392182301019466851 9135633588273451529200277)
                ·
                  refine ⟨428232824450318040431263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9135633588273451529200277 428232824450318040431263)
                  ·
                    rfl

theorem cell21_1876456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 6].length) (baseStart_1876456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876456 prefixEnd_1876456 := by exact prefixLift 1876456
  have htrace : WordTrace (prefixWord ++ tailWord_1876456) baseStart_1876456 baseEnd_1876456 := by
    simpa [prefixWord, tailWord_1876456, baseEnd_1876456] using wordTrace_append hprefix tailTrace_1876456
  have hstable : (prefixWord ++ tailWord_1876456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876456).length < 2 ^ (prefixWord ++ tailWord_1876456).sum := by decide
  have hdescent : baseEnd_1876456 < baseStart_1876456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876487 : List Nat := [1, 1, 4, 3, 3, 1, 1, 7]
def baseStart_1876487 : Nat := 118140960795 + 1876487 * 2 ^ 59
def prefixEnd_1876487 : Nat := 4983230072969 + 3 ^ 40 * 1876487 * 2
def baseEnd_1876487 : Nat := 142746633024222958471511

theorem tailTrace_1876487 : CollatzResearch.WordTrace tailWord_1876487 prefixEnd_1876487 142746633024222958471511 := by
  unfold tailWord_1876487
  simp only [CollatzResearch.WordTrace]
  refine ⟨68441103552815552310115715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45627402368543701540077143 68441103552815552310115715)
  ·
    refine ⟨102661655329223328465173573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68441103552815552310115715 102661655329223328465173573)
    ·
      refine ⟨19249060374229374087220045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 102661655329223328465173573 19249060374229374087220045)
      ·
        refine ⟨7218397640336015282707517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19249060374229374087220045 7218397640336015282707517)
        ·
          refine ⟨2706899115126005731015319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7218397640336015282707517 2706899115126005731015319)
          ·
            refine ⟨4060348672689008596522979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2706899115126005731015319 4060348672689008596522979)
            ·
              refine ⟨6090523009033512894784469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4060348672689008596522979 6090523009033512894784469)
              ·
                refine ⟨142746633024222958471511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6090523009033512894784469 142746633024222958471511)
                ·
                  rfl

theorem cell21_1876487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 7].length) (baseStart_1876487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876487 prefixEnd_1876487 := by exact prefixLift 1876487
  have htrace : WordTrace (prefixWord ++ tailWord_1876487) baseStart_1876487 baseEnd_1876487 := by
    simpa [prefixWord, tailWord_1876487, baseEnd_1876487] using wordTrace_append hprefix tailTrace_1876487
  have hstable : (prefixWord ++ tailWord_1876487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876487).length < 2 ^ (prefixWord ++ tailWord_1876487).sum := by decide
  have hdescent : baseEnd_1876487 < baseStart_1876487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876493 : List Nat := [1, 7, 1, 1, 1, 1, 3, 3, 3]
def baseStart_1876493 : Nat := 118140960795 + 1876493 * 2 ^ 59
def prefixEnd_1876493 : Nat := 4983230072969 + 3 ^ 40 * 1876493 * 2
def baseEnd_1876493 : Nat := 428241268354414198314521

theorem tailTrace_1876493 : CollatzResearch.WordTrace tailWord_1876493 prefixEnd_1876493 428241268354414198314521 := by
  unfold tailWord_1876493
  simp only [CollatzResearch.WordTrace]
  refine ⟨68441322390793815334834133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45627548260529210223222755 68441322390793815334834133)
  ·
    refine ⟨1604093493534230046910175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 68441322390793815334834133 1604093493534230046910175)
    ·
      refine ⟨2406140240301345070365263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1604093493534230046910175 2406140240301345070365263)
      ·
        refine ⟨3609210360452017605547895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2406140240301345070365263 3609210360452017605547895)
        ·
          refine ⟨5413815540678026408321843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3609210360452017605547895 5413815540678026408321843)
          ·
            refine ⟨8120723311017039612482765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5413815540678026408321843 8120723311017039612482765)
            ·
              refine ⟨3045271241631389854681037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 8120723311017039612482765 3045271241631389854681037)
              ·
                refine ⟨1141976715611771195505389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3045271241631389854681037 1141976715611771195505389)
                ·
                  refine ⟨428241268354414198314521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1141976715611771195505389 428241268354414198314521)
                  ·
                    rfl

theorem cell21_1876493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_1876493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876493 prefixEnd_1876493 := by exact prefixLift 1876493
  have htrace : WordTrace (prefixWord ++ tailWord_1876493) baseStart_1876493 baseEnd_1876493 := by
    simpa [prefixWord, tailWord_1876493, baseEnd_1876493] using wordTrace_append hprefix tailTrace_1876493
  have hstable : (prefixWord ++ tailWord_1876493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876493).length < 2 ^ (prefixWord ++ tailWord_1876493).sum := by decide
  have hdescent : baseEnd_1876493 < baseStart_1876493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876560 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 9]
def baseStart_1876560 : Nat := 118140960795 + 1876560 * 2 ^ 59
def prefixEnd_1876560 : Nat := 4983230072969 + 3 ^ 40 * 1876560 * 2
def baseEnd_1876560 : Nat := 428256558667236970697717

theorem tailTrace_1876560 : CollatzResearch.WordTrace tailWord_1876560 prefixEnd_1876560 428256558667236970697717 := by
  unfold tailWord_1876560
  simp only [CollatzResearch.WordTrace]
  refine ⟨34221883040775542888761567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45629177387700723851682089 34221883040775542888761567)
  ·
    refine ⟨51332824561163314333142351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34221883040775542888761567 51332824561163314333142351)
    ·
      refine ⟨76999236841744971499713527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51332824561163314333142351 76999236841744971499713527)
      ·
        refine ⟨115498855262617457249570291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 76999236841744971499713527 115498855262617457249570291)
        ·
          refine ⟨173248282893926185874355437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115498855262617457249570291 173248282893926185874355437)
          ·
            refine ⟨64968106085222319702883289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 173248282893926185874355437 64968106085222319702883289)
            ·
              refine ⟨48726079563916739777162467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64968106085222319702883289 48726079563916739777162467)
              ·
                refine ⟨73089119345875109665743701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 48726079563916739777162467 73089119345875109665743701)
                ·
                  refine ⟨428256558667236970697717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 73089119345875109665743701 428256558667236970697717)
                  ·
                    rfl

theorem cell21_1876560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 9].length) (baseStart_1876560 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876560 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876560 prefixEnd_1876560 := by exact prefixLift 1876560
  have htrace : WordTrace (prefixWord ++ tailWord_1876560) baseStart_1876560 baseEnd_1876560 := by
    simpa [prefixWord, tailWord_1876560, baseEnd_1876560] using wordTrace_append hprefix tailTrace_1876560
  have hstable : (prefixWord ++ tailWord_1876560).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876560).length < 2 ^ (prefixWord ++ tailWord_1876560).sum := by decide
  have hdescent : baseEnd_1876560 < baseStart_1876560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876594 : List Nat := [3, 2, 1, 2, 4, 1, 1, 2, 5]
def baseStart_1876594 : Nat := 118140960795 + 1876594 * 2 ^ 59
def prefixEnd_1876594 : Nat := 4983230072969 + 3 ^ 40 * 1876594 * 2
def baseEnd_1876594 : Nat := 428264317930460467130981

theorem tailTrace_1876594 : CollatzResearch.WordTrace tailWord_1876594 prefixEnd_1876594 428264317930460467130981 := by
  unfold tailWord_1876594
  simp only [CollatzResearch.WordTrace]
  refine ⟨17111251540856977396065209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45630004108951939722840557 17111251540856977396065209)
  ·
    refine ⟨12833438655642733047048907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 17111251540856977396065209 12833438655642733047048907)
    ·
      refine ⟨19250157983464099570573361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12833438655642733047048907 19250157983464099570573361)
      ·
        refine ⟨14437618487598074677930021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19250157983464099570573361 14437618487598074677930021)
        ·
          refine ⟨2707053466424639002111879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14437618487598074677930021 2707053466424639002111879)
          ·
            refine ⟨4060580199636958503167819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2707053466424639002111879 4060580199636958503167819)
            ·
              refine ⟨6090870299455437754751729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4060580199636958503167819 6090870299455437754751729)
              ·
                refine ⟨4568152724591578316063797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6090870299455437754751729 4568152724591578316063797)
                ·
                  refine ⟨428264317930460467130981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4568152724591578316063797 428264317930460467130981)
                  ·
                    rfl

theorem cell21_1876594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 5].length) (baseStart_1876594 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876594 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876594 prefixEnd_1876594 := by exact prefixLift 1876594
  have htrace : WordTrace (prefixWord ++ tailWord_1876594) baseStart_1876594 baseEnd_1876594 := by
    simpa [prefixWord, tailWord_1876594, baseEnd_1876594] using wordTrace_append hprefix tailTrace_1876594
  have hstable : (prefixWord ++ tailWord_1876594).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876594).length < 2 ^ (prefixWord ++ tailWord_1876594).sum := by decide
  have hdescent : baseEnd_1876594 < baseStart_1876594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876622 : List Nat := [4, 1, 1, 3, 1, 1, 10]
def baseStart_1876622 : Nat := 118140960795 + 1876622 * 2 ^ 59
def prefixEnd_1876622 : Nat := 4983230072969 + 3 ^ 40 * 1876622 * 2
def baseEnd_1876622 : Nat := 47585634212437626740473

theorem tailTrace_1876622 : CollatzResearch.WordTrace tailWord_1876622 prefixEnd_1876622 47585634212437626740473 := by
  unfold tailWord_1876622
  simp only [CollatzResearch.WordTrace]
  refine ⟨8555753425915808795785015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45630684938217646910853413 8555753425915808795785015)
  ·
    refine ⟨12833630138873713193677523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8555753425915808795785015 12833630138873713193677523)
    ·
      refine ⟨19250445208310569790516285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12833630138873713193677523 19250445208310569790516285)
      ·
        refine ⟨7218916953116463671443607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 19250445208310569790516285 7218916953116463671443607)
        ·
          refine ⟨10828375429674695507165411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7218916953116463671443607 10828375429674695507165411)
          ·
            refine ⟨16242563144512043260748117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10828375429674695507165411 16242563144512043260748117)
            ·
              refine ⟨47585634212437626740473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 16242563144512043260748117 47585634212437626740473)
              ·
                rfl

theorem cell21_1876622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 10].length) (baseStart_1876622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876622 prefixEnd_1876622 := by exact prefixLift 1876622
  have htrace : WordTrace (prefixWord ++ tailWord_1876622) baseStart_1876622 baseEnd_1876622 := by
    simpa [prefixWord, tailWord_1876622, baseEnd_1876622] using wordTrace_append hprefix tailTrace_1876622
  have hstable : (prefixWord ++ tailWord_1876622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876622).length < 2 ^ (prefixWord ++ tailWord_1876622).sum := by decide
  have hdescent : baseEnd_1876622 < baseStart_1876622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876662 : List Nat := [5, 1, 3, 1, 3, 1, 1, 3, 3]
def baseStart_1876662 : Nat := 118140960795 + 1876662 * 2 ^ 59
def prefixEnd_1876662 : Nat := 4983230072969 + 3 ^ 40 * 1876662 * 2
def baseEnd_1876662 : Nat := 428279836456907459997509

theorem tailTrace_1876662 : CollatzResearch.WordTrace tailWord_1876662 prefixEnd_1876662 428279836456907459997509 := by
  unfold tailWord_1876662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4277967895448847324858515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45631657551454371465157493 4277967895448847324858515)
  ·
    refine ⟨6416951843173270987287773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4277967895448847324858515 6416951843173270987287773)
    ·
      refine ⟨2406356941189976620232915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6416951843173270987287773 2406356941189976620232915)
      ·
        refine ⟨3609535411784964930349373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2406356941189976620232915 3609535411784964930349373)
        ·
          refine ⟨1353575779419361848881015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3609535411784964930349373 1353575779419361848881015)
          ·
            refine ⟨2030363669129042773321523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353575779419361848881015 2030363669129042773321523)
            ·
              refine ⟨3045545503693564159982285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2030363669129042773321523 3045545503693564159982285)
              ·
                refine ⟨1142079563885086559993357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3045545503693564159982285 1142079563885086559993357)
                ·
                  refine ⟨428279836456907459997509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1142079563885086559993357 428279836456907459997509)
                  ·
                    rfl

theorem cell21_1876662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_1876662 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876662 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876662 prefixEnd_1876662 := by exact prefixLift 1876662
  have htrace : WordTrace (prefixWord ++ tailWord_1876662) baseStart_1876662 baseEnd_1876662 := by
    simpa [prefixWord, tailWord_1876662, baseEnd_1876662] using wordTrace_append hprefix tailTrace_1876662
  have hstable : (prefixWord ++ tailWord_1876662).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876662).length < 2 ^ (prefixWord ++ tailWord_1876662).sum := by decide
  have hdescent : baseEnd_1876662 < baseStart_1876662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876673 : List Nat := [1, 2, 6, 2, 2, 1, 7]
def baseStart_1876673 : Nat := 118140960795 + 1876673 * 2 ^ 59
def prefixEnd_1876673 : Nat := 4983230072969 + 3 ^ 40 * 1876673 * 2
def baseEnd_1876673 : Nat := 47586927422974876146017

theorem tailTrace_1876673 : CollatzResearch.WordTrace tailWord_1876673 prefixEnd_1876673 47586927422974876146017 := by
  unfold tailWord_1876673
  simp only [CollatzResearch.WordTrace]
  refine ⟨68447887530141706076386673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45631925020094470717591115 68447887530141706076386673)
  ·
    refine ⟨51335915647606279557290005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68447887530141706076386673 51335915647606279557290005)
    ·
      refine ⟨2406371045981544354247969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 51335915647606279557290005 2406371045981544354247969)
      ·
        refine ⟨1804778284486158265685977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2406371045981544354247969 1804778284486158265685977)
        ·
          refine ⟨1353583713364618699264483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1804778284486158265685977 1353583713364618699264483)
          ·
            refine ⟨2030375570046928048896725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353583713364618699264483 2030375570046928048896725)
            ·
              refine ⟨47586927422974876146017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 2030375570046928048896725 47586927422974876146017)
              ·
                rfl

theorem cell21_1876673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 7].length) (baseStart_1876673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876673 prefixEnd_1876673 := by exact prefixLift 1876673
  have htrace : WordTrace (prefixWord ++ tailWord_1876673) baseStart_1876673 baseEnd_1876673 := by
    simpa [prefixWord, tailWord_1876673, baseEnd_1876673] using wordTrace_append hprefix tailTrace_1876673
  have hstable : (prefixWord ++ tailWord_1876673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876673).length < 2 ^ (prefixWord ++ tailWord_1876673).sum := by decide
  have hdescent : baseEnd_1876673 < baseStart_1876673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876684 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 6]
def baseStart_1876684 : Nat := 118140960795 + 1876684 * 2 ^ 59
def prefixEnd_1876684 : Nat := 4983230072969 + 3 ^ 40 * 1876684 * 2
def baseEnd_1876684 : Nat := 428284857156640310630797

theorem tailTrace_1876684 : CollatzResearch.WordTrace tailWord_1876684 prefixEnd_1876684 428284857156640310630797 := by
  unfold tailWord_1876684
  simp only [CollatzResearch.WordTrace]
  refine ⟨34224144366550927477518553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45632192488734569970024737 34224144366550927477518553)
  ·
    refine ⟨25668108274913195608138915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34224144366550927477518553 25668108274913195608138915)
    ·
      refine ⟨38502162412369793412208373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25668108274913195608138915 38502162412369793412208373)
      ·
        refine ⟨3609577726159668132394535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 38502162412369793412208373 3609577726159668132394535)
        ·
          refine ⟨5414366589239502198591803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3609577726159668132394535 5414366589239502198591803)
          ·
            refine ⟨8121549883859253297887705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5414366589239502198591803 8121549883859253297887705)
            ·
              refine ⟨6091162412894439973415779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8121549883859253297887705 6091162412894439973415779)
              ·
                refine ⟨9136743619341659960123669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6091162412894439973415779 9136743619341659960123669)
                ·
                  refine ⟨428284857156640310630797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 9136743619341659960123669 428284857156640310630797)
                  ·
                    rfl

theorem cell21_1876684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 6].length) (baseStart_1876684 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876684 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876684 prefixEnd_1876684 := by exact prefixLift 1876684
  have htrace : WordTrace (prefixWord ++ tailWord_1876684) baseStart_1876684 baseEnd_1876684 := by
    simpa [prefixWord, tailWord_1876684, baseEnd_1876684] using wordTrace_append hprefix tailTrace_1876684
  have hstable : (prefixWord ++ tailWord_1876684).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876684).length < 2 ^ (prefixWord ++ tailWord_1876684).sum := by decide
  have hdescent : baseEnd_1876684 < baseStart_1876684 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876698 : List Nat := [3, 1, 1, 2, 2, 2, 4, 6]
def baseStart_1876698 : Nat := 118140960795 + 1876698 * 2 ^ 59
def prefixEnd_1876698 : Nat := 4983230072969 + 3 ^ 40 * 1876698 * 2
def baseEnd_1876698 : Nat := 142762684049126465799145

theorem tailTrace_1876698 : CollatzResearch.WordTrace tailWord_1876698 prefixEnd_1876698 142762684049126465799145 := by
  unfold tailWord_1876698
  simp only [CollatzResearch.WordTrace]
  refine ⟨17112199838762783836511687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45632532903367423564031165 17112199838762783836511687)
  ·
    refine ⟨25668299758144175754767531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17112199838762783836511687 25668299758144175754767531)
    ·
      refine ⟨38502449637216263632151297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25668299758144175754767531 38502449637216263632151297)
      ·
        refine ⟨28876837227912197724113473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38502449637216263632151297 28876837227912197724113473)
        ·
          refine ⟨21657627920934148293085105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28876837227912197724113473 21657627920934148293085105)
          ·
            refine ⟨16243220940700611219813829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21657627920934148293085105 16243220940700611219813829)
            ·
              refine ⟨3045603926381364603715093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 16243220940700611219813829 3045603926381364603715093)
              ·
                refine ⟨142762684049126465799145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3045603926381364603715093 142762684049126465799145)
                ·
                  rfl

theorem cell21_1876698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_1876698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876698 prefixEnd_1876698 := by exact prefixLift 1876698
  have htrace : WordTrace (prefixWord ++ tailWord_1876698) baseStart_1876698 baseEnd_1876698 := by
    simpa [prefixWord, tailWord_1876698, baseEnd_1876698] using wordTrace_append hprefix tailTrace_1876698
  have hstable : (prefixWord ++ tailWord_1876698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876698).length < 2 ^ (prefixWord ++ tailWord_1876698).sum := by decide
  have hdescent : baseEnd_1876698 < baseStart_1876698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876746 : List Nat := [3, 1, 2, 2, 1, 2, 3, 4, 3]
def baseStart_1876746 : Nat := 118140960795 + 1876746 * 2 ^ 59
def prefixEnd_1876746 : Nat := 4983230072969 + 3 ^ 40 * 1876746 * 2
def baseEnd_1876746 : Nat := 428299006401341980597337

theorem tailTrace_1876746 : CollatzResearch.WordTrace tailWord_1876746 prefixEnd_1876746 428299006401341980597337 := by
  unfold tailWord_1876746
  simp only [CollatzResearch.WordTrace]
  refine ⟨17112637514719309885948523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45633700039251493029196061 17112637514719309885948523)
  ·
    refine ⟨25668956272078964828922785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17112637514719309885948523 25668956272078964828922785)
    ·
      refine ⟨19251717204059223621692089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25668956272078964828922785 19251717204059223621692089)
      ·
        refine ⟨14438787903044417716269067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19251717204059223621692089 14438787903044417716269067)
        ·
          refine ⟨21658181854566626574403601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 14438787903044417716269067 21658181854566626574403601)
          ·
            refine ⟨16243636390924969930802701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 21658181854566626574403601 16243636390924969930802701)
            ·
              refine ⟨6091363646596863724051013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 16243636390924969930802701 6091363646596863724051013)
              ·
                refine ⟨1142130683736911948259565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6091363646596863724051013 1142130683736911948259565)
                ·
                  refine ⟨428299006401341980597337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1142130683736911948259565 428299006401341980597337)
                  ·
                    rfl

theorem cell21_1876746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 3].length) (baseStart_1876746 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876746 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876746 prefixEnd_1876746 := by exact prefixLift 1876746
  have htrace : WordTrace (prefixWord ++ tailWord_1876746) baseStart_1876746 baseEnd_1876746 := by
    simpa [prefixWord, tailWord_1876746, baseEnd_1876746] using wordTrace_append hprefix tailTrace_1876746
  have hstable : (prefixWord ++ tailWord_1876746).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876746).length < 2 ^ (prefixWord ++ tailWord_1876746).sum := by decide
  have hdescent : baseEnd_1876746 < baseStart_1876746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876794 : List Nat := [3, 1, 1, 1, 7, 1, 1, 2, 4]
def baseStart_1876794 : Nat := 118140960795 + 1876794 * 2 ^ 59
def prefixEnd_1876794 : Nat := 4983230072969 + 3 ^ 40 * 1876794 * 2
def baseEnd_1876794 : Nat := 428309960655304563797239

theorem tailTrace_1876794 : CollatzResearch.WordTrace tailWord_1876794 prefixEnd_1876794 428309960655304563797239 := by
  unfold tailWord_1876794
  simp only [CollatzResearch.WordTrace]
  refine ⟨17113075190675835935385359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45634867175135562494360957 17113075190675835935385359)
  ·
    refine ⟨25669612786013753903078039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17113075190675835935385359 25669612786013753903078039)
    ·
      refine ⟨38504419179020630854617059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25669612786013753903078039 38504419179020630854617059)
      ·
        refine ⟨57756628768530946281925589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38504419179020630854617059 57756628768530946281925589)
        ·
          refine ⟨1353670986762444053482631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 57756628768530946281925589 1353670986762444053482631)
          ·
            refine ⟨2030506480143666080223947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353670986762444053482631 2030506480143666080223947)
            ·
              refine ⟨3045759720215499120335921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2030506480143666080223947 3045759720215499120335921)
              ·
                refine ⟨2284319790161624340251941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3045759720215499120335921 2284319790161624340251941)
                ·
                  refine ⟨428309960655304563797239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2284319790161624340251941 428309960655304563797239)
                  ·
                    rfl

theorem cell21_1876794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 1, 2, 4].length) (baseStart_1876794 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876794 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876794 prefixEnd_1876794 := by exact prefixLift 1876794
  have htrace : WordTrace (prefixWord ++ tailWord_1876794) baseStart_1876794 baseEnd_1876794 := by
    simpa [prefixWord, tailWord_1876794, baseEnd_1876794] using wordTrace_append hprefix tailTrace_1876794
  have hstable : (prefixWord ++ tailWord_1876794).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876794).length < 2 ^ (prefixWord ++ tailWord_1876794).sum := by decide
  have hdescent : baseEnd_1876794 < baseStart_1876794 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876819 : List Nat := [1, 1, 1, 2, 1, 1, 3, 7, 4]
def baseStart_1876819 : Nat := 118140960795 + 1876819 * 2 ^ 59
def prefixEnd_1876819 : Nat := 4983230072969 + 3 ^ 40 * 1876819 * 2
def baseEnd_1876819 : Nat := 428315665995910075880521

theorem tailTrace_1876819 : CollatzResearch.WordTrace tailWord_1876819 prefixEnd_1876819 428315665995910075880521 := by
  unfold tailWord_1876819
  simp only [CollatzResearch.WordTrace]
  refine ⟨68453212587612773011201511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45635475058408515340801007 68453212587612773011201511)
  ·
    refine ⟨102679818881419159516802267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68453212587612773011201511 102679818881419159516802267)
    ·
      refine ⟨154019728322128739275203401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 102679818881419159516802267 154019728322128739275203401)
      ·
        refine ⟨115514796241596554456402551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 154019728322128739275203401 115514796241596554456402551)
        ·
          refine ⟨173272194362394831684603827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115514796241596554456402551 173272194362394831684603827)
          ·
            refine ⟨259908291543592247526905741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 173272194362394831684603827 259908291543592247526905741)
            ·
              refine ⟨97465609328847092822589653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 259908291543592247526905741 97465609328847092822589653)
              ·
                refine ⟨2284350218644853738029445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 97465609328847092822589653 2284350218644853738029445)
                ·
                  refine ⟨428315665995910075880521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2284350218644853738029445 428315665995910075880521)
                  ·
                    rfl

theorem cell21_1876819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 4].length) (baseStart_1876819 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876819 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876819 prefixEnd_1876819 := by exact prefixLift 1876819
  have htrace : WordTrace (prefixWord ++ tailWord_1876819) baseStart_1876819 baseEnd_1876819 := by
    simpa [prefixWord, tailWord_1876819, baseEnd_1876819] using wordTrace_append hprefix tailTrace_1876819
  have hstable : (prefixWord ++ tailWord_1876819).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876819).length < 2 ^ (prefixWord ++ tailWord_1876819).sum := by decide
  have hdescent : baseEnd_1876819 < baseStart_1876819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876839 : List Nat := [1, 1, 5, 1, 2, 4, 1, 3, 3]
def baseStart_1876839 : Nat := 118140960795 + 1876839 * 2 ^ 59
def prefixEnd_1876839 : Nat := 4983230072969 + 3 ^ 40 * 1876839 * 2
def baseEnd_1876839 : Nat := 428320230268394485547147

theorem tailTrace_1876839 : CollatzResearch.WordTrace tailWord_1876839 prefixEnd_1876839 428320230268394485547147 := by
  unfold tailWord_1876839
  simp only [CollatzResearch.WordTrace]
  refine ⟨68453942047540316426929571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45635961365026877617953047 68453942047540316426929571)
  ·
    refine ⟨102680913071310474640394357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68453942047540316426929571 102680913071310474640394357)
    ·
      refine ⟨9626335600435356997536971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 102680913071310474640394357 9626335600435356997536971)
      ·
        refine ⟨14439503400653035496305457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9626335600435356997536971 14439503400653035496305457)
        ·
          refine ⟨10829627550489776622229093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 14439503400653035496305457 10829627550489776622229093)
          ·
            refine ⟨2030555165716833116667955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 10829627550489776622229093 2030555165716833116667955)
            ·
              refine ⟨3045832748575249675001933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2030555165716833116667955 3045832748575249675001933)
              ·
                refine ⟨1142187280715718628125725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3045832748575249675001933 1142187280715718628125725)
                ·
                  refine ⟨428320230268394485547147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1142187280715718628125725 428320230268394485547147)
                  ·
                    rfl

theorem cell21_1876839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 3].length) (baseStart_1876839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876839 prefixEnd_1876839 := by exact prefixLift 1876839
  have htrace : WordTrace (prefixWord ++ tailWord_1876839) baseStart_1876839 baseEnd_1876839 := by
    simpa [prefixWord, tailWord_1876839, baseEnd_1876839] using wordTrace_append hprefix tailTrace_1876839
  have hstable : (prefixWord ++ tailWord_1876839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876839).length < 2 ^ (prefixWord ++ tailWord_1876839).sum := by decide
  have hdescent : baseEnd_1876839 < baseStart_1876839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876864 : List Nat := [2, 1, 1, 2, 1, 2, 2, 5, 5]
def baseStart_1876864 : Nat := 118140960795 + 1876864 * 2 ^ 59
def prefixEnd_1876864 : Nat := 4983230072969 + 3 ^ 40 * 1876864 * 2
def baseEnd_1876864 : Nat := 428325935608999997630429

theorem tailTrace_1876864 : CollatzResearch.WordTrace tailWord_1876864 prefixEnd_1876864 428325935608999997630429 := by
  unfold tailWord_1876864
  simp only [CollatzResearch.WordTrace]
  refine ⟨34227426936224872848294823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45636569248299830464393097 34227426936224872848294823)
  ·
    refine ⟨51341140404337309272442235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34227426936224872848294823 51341140404337309272442235)
    ·
      refine ⟨77011710606505963908663353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51341140404337309272442235 77011710606505963908663353)
      ·
        refine ⟨57758782954879472931497515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 77011710606505963908663353 57758782954879472931497515)
        ·
          refine ⟨86638174432319209397246273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57758782954879472931497515 86638174432319209397246273)
          ·
            refine ⟨64978630824239407047934705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 86638174432319209397246273 64978630824239407047934705)
            ·
              refine ⟨48733973118179555285951029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 64978630824239407047934705 48733973118179555285951029)
              ·
                refine ⟨4568809979829333308057909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48733973118179555285951029 4568809979829333308057909)
                ·
                  refine ⟨428325935608999997630429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4568809979829333308057909 428325935608999997630429)
                  ·
                    rfl

theorem cell21_1876864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 5].length) (baseStart_1876864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876864 prefixEnd_1876864 := by exact prefixLift 1876864
  have htrace : WordTrace (prefixWord ++ tailWord_1876864) baseStart_1876864 baseEnd_1876864 := by
    simpa [prefixWord, tailWord_1876864, baseEnd_1876864] using wordTrace_append hprefix tailTrace_1876864
  have hstable : (prefixWord ++ tailWord_1876864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876864).length < 2 ^ (prefixWord ++ tailWord_1876864).sum := by decide
  have hdescent : baseEnd_1876864 < baseStart_1876864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876918 : List Nat := [5, 1, 4, 1, 1, 2, 1, 6]
def baseStart_1876918 : Nat := 118140960795 + 1876918 * 2 ^ 59
def prefixEnd_1876918 : Nat := 4983230072969 + 3 ^ 40 * 1876918 * 2
def baseEnd_1876918 : Nat := 142779419714902634576773

theorem tailTrace_1876918 : CollatzResearch.WordTrace tailWord_1876918 prefixEnd_1876918 142779419714902634576773 := by
  unfold tailWord_1876918
  simp only [CollatzResearch.WordTrace]
  refine ⟨4278551463390882057440963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 45637882276169408612703605 4278551463390882057440963)
  ·
    refine ⟨6417827195086323086161445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4278551463390882057440963 6417827195086323086161445)
    ·
      refine ⟨1203342599078685578655271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6417827195086323086161445 1203342599078685578655271)
      ·
        refine ⟨1805013898618028367982907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1203342599078685578655271 1805013898618028367982907)
        ·
          refine ⟨2707520847927042551974361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1805013898618028367982907 2707520847927042551974361)
          ·
            refine ⟨2030640635945281913980771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2707520847927042551974361 2030640635945281913980771)
            ·
              refine ⟨3045960953917922870971157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2030640635945281913980771 3045960953917922870971157)
              ·
                refine ⟨142779419714902634576773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3045960953917922870971157 142779419714902634576773)
                ·
                  rfl

theorem cell21_1876918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 6].length) (baseStart_1876918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876918 prefixEnd_1876918 := by exact prefixLift 1876918
  have htrace : WordTrace (prefixWord ++ tailWord_1876918) baseStart_1876918 baseEnd_1876918 := by
    simpa [prefixWord, tailWord_1876918, baseEnd_1876918] using wordTrace_append hprefix tailTrace_1876918
  have hstable : (prefixWord ++ tailWord_1876918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876918).length < 2 ^ (prefixWord ++ tailWord_1876918).sum := by decide
  have hdescent : baseEnd_1876918 < baseStart_1876918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876974 : List Nat := [4, 1, 2, 1, 4, 1, 2, 1, 5]
def baseStart_1876974 : Nat := 118140960795 + 1876974 * 2 ^ 59
def prefixEnd_1876974 : Nat := 4983230072969 + 3 ^ 40 * 1876974 * 2
def baseEnd_1876974 : Nat := 428351039107664250796871

theorem tailTrace_1876974 : CollatzResearch.WordTrace tailWord_1876974 prefixEnd_1876974 428351039107664250796871 := by
  unfold tailWord_1876974
  simp only [CollatzResearch.WordTrace]
  refine ⟨8557358237756404310386747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 45639243934700822988729317 8557358237756404310386747)
  ·
    refine ⟨12836037356634606465580121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8557358237756404310386747 12836037356634606465580121)
    ·
      refine ⟨9627028017475954849185091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12836037356634606465580121 9627028017475954849185091)
      ·
        refine ⟨14440542026213932273777637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9627028017475954849185091 14440542026213932273777637)
        ·
          refine ⟨2707601629915112301333307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 14440542026213932273777637 2707601629915112301333307)
          ·
            refine ⟨4061402444872668451999961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2707601629915112301333307 4061402444872668451999961)
            ·
              refine ⟨3046051833654501338999971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4061402444872668451999961 3046051833654501338999971)
              ·
                refine ⟨4569077750481752008499957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3046051833654501338999971 4569077750481752008499957)
                ·
                  refine ⟨428351039107664250796871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4569077750481752008499957 428351039107664250796871)
                  ·
                    rfl

theorem cell21_1876974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 5].length) (baseStart_1876974 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876974 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876974 prefixEnd_1876974 := by exact prefixLift 1876974
  have htrace : WordTrace (prefixWord ++ tailWord_1876974) baseStart_1876974 baseEnd_1876974 := by
    simpa [prefixWord, tailWord_1876974, baseEnd_1876974] using wordTrace_append hprefix tailTrace_1876974
  have hstable : (prefixWord ++ tailWord_1876974).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876974).length < 2 ^ (prefixWord ++ tailWord_1876974).sum := by decide
  have hdescent : baseEnd_1876974 < baseStart_1876974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876985 : List Nat := [1, 2, 1, 3, 1, 3, 2, 8]
def baseStart_1876985 : Nat := 118140960795 + 1876985 * 2 ^ 59
def prefixEnd_1876985 : Nat := 4983230072969 + 3 ^ 40 * 1876985 * 2
def baseEnd_1876985 : Nat := 142784516485843558704505

theorem tailTrace_1876985 : CollatzResearch.WordTrace tailWord_1876985 prefixEnd_1876985 142784516485843558704505 := by
  unfold tailWord_1876985
  simp only [CollatzResearch.WordTrace]
  refine ⟨68459267105011383361744409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45639511403340922241162939 68459267105011383361744409)
  ·
    refine ⟨51344450328758537521308307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68459267105011383361744409 51344450328758537521308307)
    ·
      refine ⟨77016675493137806281962461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51344450328758537521308307 77016675493137806281962461)
      ·
        refine ⟨28881253309926677355735923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77016675493137806281962461 28881253309926677355735923)
        ·
          refine ⟨43321879964890016033603885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28881253309926677355735923 43321879964890016033603885)
          ·
            refine ⟨16245704986833756012601457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 43321879964890016033603885 16245704986833756012601457)
            ·
              refine ⟨12184278740125317009451093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 16245704986833756012601457 12184278740125317009451093)
              ·
                refine ⟨142784516485843558704505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 12184278740125317009451093 142784516485843558704505)
                ·
                  rfl

theorem cell21_1876985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 8].length) (baseStart_1876985 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876985 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876985 prefixEnd_1876985 := by exact prefixLift 1876985
  have htrace : WordTrace (prefixWord ++ tailWord_1876985) baseStart_1876985 baseEnd_1876985 := by
    simpa [prefixWord, tailWord_1876985, baseEnd_1876985] using wordTrace_append hprefix tailTrace_1876985
  have hstable : (prefixWord ++ tailWord_1876985).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876985).length < 2 ^ (prefixWord ++ tailWord_1876985).sum := by decide
  have hdescent : baseEnd_1876985 < baseStart_1876985 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1876994 : List Nat := [3, 4, 1, 3, 2, 1, 2, 5]
def baseStart_1876994 : Nat := 118140960795 + 1876994 * 2 ^ 59
def prefixEnd_1876994 : Nat := 4983230072969 + 3 ^ 40 * 1876994 * 2
def baseEnd_1876994 : Nat := 142785201126716220154499

theorem tailTrace_1876994 : CollatzResearch.WordTrace tailWord_1876994 prefixEnd_1876994 142785201126716220154499 := by
  unfold tailWord_1876994
  simp only [CollatzResearch.WordTrace]
  refine ⟨17114898840494694474705509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45639730241319185265881357 17114898840494694474705509)
  ·
    refine ⟨3209043532592755214007283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 17114898840494694474705509 3209043532592755214007283)
    ·
      refine ⟨4813565298889132821010925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3209043532592755214007283 4813565298889132821010925)
      ·
        refine ⟨1805086987083424807879097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4813565298889132821010925 1805086987083424807879097)
        ·
          refine ⟨1353815240312568605909323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1805086987083424807879097 1353815240312568605909323)
          ·
            refine ⟨2030722860468852908863985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1353815240312568605909323 2030722860468852908863985)
            ·
              refine ⟨1523042145351639681647989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2030722860468852908863985 1523042145351639681647989)
              ·
                refine ⟨142785201126716220154499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1523042145351639681647989 142785201126716220154499)
                ·
                  rfl

theorem cell21_1876994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 5].length) (baseStart_1876994 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1876994 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1876994 prefixEnd_1876994 := by exact prefixLift 1876994
  have htrace : WordTrace (prefixWord ++ tailWord_1876994) baseStart_1876994 baseEnd_1876994 := by
    simpa [prefixWord, tailWord_1876994, baseEnd_1876994] using wordTrace_append hprefix tailTrace_1876994
  have hstable : (prefixWord ++ tailWord_1876994).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1876994).length < 2 ^ (prefixWord ++ tailWord_1876994).sum := by decide
  have hdescent : baseEnd_1876994 < baseStart_1876994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1876994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877002 : List Nat := [3, 1, 2, 2, 3, 2, 1, 7]
def baseStart_1877002 : Nat := 118140960795 + 1877002 * 2 ^ 59
def prefixEnd_1877002 : Nat := 4983230072969 + 3 ^ 40 * 1877002 * 2
def baseEnd_1877002 : Nat := 142785809696380808110049

theorem tailTrace_1877002 : CollatzResearch.WordTrace tailWord_1877002 prefixEnd_1877002 142785809696380808110049 := by
  unfold tailWord_1877002
  simp only [CollatzResearch.WordTrace]
  refine ⟨17114971786487448816278315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 45639924763966530176742173 17114971786487448816278315)
  ·
    refine ⟨25672457679731173224417473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 17114971786487448816278315 25672457679731173224417473)
    ·
      refine ⟨19254343259798379918313105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 25672457679731173224417473 19254343259798379918313105)
      ·
        refine ⟨14440757444848784938734829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 19254343259798379918313105 14440757444848784938734829)
        ·
          refine ⟨5415284041818294352025561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 14440757444848784938734829 5415284041818294352025561)
          ·
            refine ⟨4061463031363720764019171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5415284041818294352025561 4061463031363720764019171)
            ·
              refine ⟨6092194547045581146028757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4061463031363720764019171 6092194547045581146028757)
              ·
                refine ⟨142785809696380808110049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6092194547045581146028757 142785809696380808110049)
                ·
                  rfl

theorem cell21_1877002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 7].length) (baseStart_1877002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1877002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1877002 prefixEnd_1877002 := by exact prefixLift 1877002
  have htrace : WordTrace (prefixWord ++ tailWord_1877002) baseStart_1877002 baseEnd_1877002 := by
    simpa [prefixWord, tailWord_1877002, baseEnd_1877002] using wordTrace_append hprefix tailTrace_1877002
  have hstable : (prefixWord ++ tailWord_1877002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877002).length < 2 ^ (prefixWord ++ tailWord_1877002).sum := by decide
  have hdescent : baseEnd_1877002 < baseStart_1877002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877061 : List Nat := [1, 3, 1, 1, 1, 3, 4, 7]
def baseStart_1877061 : Nat := 118140960795 + 1877061 * 2 ^ 59
def prefixEnd_1877061 : Nat := 4983230072969 + 3 ^ 40 * 1877061 * 2
def baseEnd_1877061 : Nat := 142790297897657144282231

theorem tailTrace_1877061 : CollatzResearch.WordTrace tailWord_1877061 prefixEnd_1877061 142790297897657144282231 := by
  unfold tailWord_1877061
  simp only [CollatzResearch.WordTrace]
  refine ⟨68462039052736048341511037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45641359368490698894340691 68462039052736048341511037)
  ·
    refine ⟨25673264644776018128066639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 68462039052736048341511037 25673264644776018128066639)
    ·
      refine ⟨38509896967164027192099959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 25673264644776018128066639 38509896967164027192099959)
      ·
        refine ⟨57764845450746040788149939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 38509896967164027192099959 57764845450746040788149939)
        ·
          refine ⟨86647268176119061182224909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 57764845450746040788149939 86647268176119061182224909)
          ·
            refine ⟨32492725566044647943334341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 86647268176119061182224909 32492725566044647943334341)
            ·
              refine ⟨6092386043633371489375189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 32492725566044647943334341 6092386043633371489375189)
              ·
                refine ⟨142790297897657144282231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 6092386043633371489375189 142790297897657144282231)
                ·
                  rfl

theorem cell21_1877061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 7].length) (baseStart_1877061 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1877061 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1877061 prefixEnd_1877061 := by exact prefixLift 1877061
  have htrace : WordTrace (prefixWord ++ tailWord_1877061) baseStart_1877061 baseEnd_1877061 := by
    simpa [prefixWord, tailWord_1877061, baseEnd_1877061] using wordTrace_append hprefix tailTrace_1877061
  have hstable : (prefixWord ++ tailWord_1877061).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877061).length < 2 ^ (prefixWord ++ tailWord_1877061).sum := by decide
  have hdescent : baseEnd_1877061 < baseStart_1877061 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877092 : List Nat := [2, 3, 1, 1, 2, 1, 1, 5, 5]
def baseStart_1877092 : Nat := 118140960795 + 1877092 * 2 ^ 59
def prefixEnd_1877092 : Nat := 4983230072969 + 3 ^ 40 * 1877092 * 2
def baseEnd_1877092 : Nat := 428377968315322267829963

theorem tailTrace_1877092 : CollatzResearch.WordTrace tailWord_1877092 prefixEnd_1877092 428377968315322267829963 := by
  unfold tailWord_1877092
  simp only [CollatzResearch.WordTrace]
  refine ⟨34231584857811870317944765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45642113143749160423926353 34231584857811870317944765)
  ·
    refine ⟨12836844321679451369229287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34231584857811870317944765 12836844321679451369229287)
    ·
      refine ⟨19255266482519177053843931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12836844321679451369229287 19255266482519177053843931)
      ·
        refine ⟨28882899723778765580765897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 19255266482519177053843931 28882899723778765580765897)
        ·
          refine ⟨21662174792834074185574423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 28882899723778765580765897 21662174792834074185574423)
          ·
            refine ⟨32493262189251111278361635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 21662174792834074185574423 32493262189251111278361635)
            ·
              refine ⟨48739893283876666917542453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 32493262189251111278361635 48739893283876666917542453)
              ·
                refine ⟨4569364995363437523519605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 48739893283876666917542453 4569364995363437523519605)
                ·
                  refine ⟨428377968315322267829963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4569364995363437523519605 428377968315322267829963)
                  ·
                    rfl

theorem cell21_1877092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 5].length) (baseStart_1877092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1877092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1877092 prefixEnd_1877092 := by exact prefixLift 1877092
  have htrace : WordTrace (prefixWord ++ tailWord_1877092) baseStart_1877092 baseEnd_1877092 := by
    simpa [prefixWord, tailWord_1877092, baseEnd_1877092] using wordTrace_append hprefix tailTrace_1877092
  have hstable : (prefixWord ++ tailWord_1877092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877092).length < 2 ^ (prefixWord ++ tailWord_1877092).sum := by decide
  have hdescent : baseEnd_1877092 < baseStart_1877092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877216 : List Nat := [2, 1, 1, 3, 1, 4, 4, 1, 4]
def baseStart_1877216 : Nat := 118140960795 + 1877216 * 2 ^ 59
def prefixEnd_1877216 : Nat := 4983230072969 + 3 ^ 40 * 1877216 * 2
def baseEnd_1877216 : Nat := 428406266804725607763043

theorem tailTrace_1877216 : CollatzResearch.WordTrace tailWord_1877216 prefixEnd_1877216 428406266804725607763043 := by
  unfold tailWord_1877216
  simp only [CollatzResearch.WordTrace]
  refine ⟨34233846183587254906701751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45645128244783006542269001 34233846183587254906701751)
  ·
    refine ⟨51350769275380882360052627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 34233846183587254906701751 51350769275380882360052627)
    ·
      refine ⟨77026153913071323540078941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51350769275380882360052627 77026153913071323540078941)
      ·
        refine ⟨28884807717401746327529603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 77026153913071323540078941 28884807717401746327529603)
        ·
          refine ⟨43327211576102619491294405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 28884807717401746327529603 43327211576102619491294405)
          ·
            refine ⟨8123852170519241154617701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 43327211576102619491294405 8123852170519241154617701)
            ·
              refine ⟨1523222281972357716490819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8123852170519241154617701 1523222281972357716490819)
              ·
                refine ⟨2284833422958536574736229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1523222281972357716490819 2284833422958536574736229)
                ·
                  refine ⟨428406266804725607763043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2284833422958536574736229 428406266804725607763043)
                  ·
                    rfl

theorem cell21_1877216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 4].length) (baseStart_1877216 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1877216 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1877216 prefixEnd_1877216 := by exact prefixLift 1877216
  have htrace : WordTrace (prefixWord ++ tailWord_1877216) baseStart_1877216 baseEnd_1877216 := by
    simpa [prefixWord, tailWord_1877216, baseEnd_1877216] using wordTrace_append hprefix tailTrace_1877216
  have hstable : (prefixWord ++ tailWord_1877216).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877216).length < 2 ^ (prefixWord ++ tailWord_1877216).sum := by decide
  have hdescent : baseEnd_1877216 < baseStart_1877216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877385 : List Nat := [1, 2, 1, 1, 7, 2, 2, 1, 4]
def baseStart_1877385 : Nat := 118140960795 + 1877385 * 2 ^ 59
def prefixEnd_1877385 : Nat := 4983230072969 + 3 ^ 40 * 1877385 * 2
def baseEnd_1877385 : Nat := 428444834907218869446031

theorem tailTrace_1877385 : CollatzResearch.WordTrace tailWord_1877385 prefixEnd_1877385 428444834907218869446031 := by
  unfold tailWord_1877385
  simp only [CollatzResearch.WordTrace]
  refine ⟨68473856303562251676305609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45649237535708167784203739 68473856303562251676305609)
  ·
    refine ⟨51355392227671688757229207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68473856303562251676305609 51355392227671688757229207)
    ·
      refine ⟨77033088341507533135843811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 51355392227671688757229207 77033088341507533135843811)
      ·
        refine ⟨115549632512261299703765717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77033088341507533135843811 115549632512261299703765717)
        ·
          refine ⟨2708194512006124211807009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 115549632512261299703765717 2708194512006124211807009)
          ·
            refine ⟨2031145884004593158855257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2708194512006124211807009 2031145884004593158855257)
            ·
              refine ⟨1523359413003444869141443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2031145884004593158855257 1523359413003444869141443)
              ·
                refine ⟨2285039119505167303712165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1523359413003444869141443 2285039119505167303712165)
                ·
                  refine ⟨428444834907218869446031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2285039119505167303712165 428444834907218869446031)
                  ·
                    rfl

theorem cell21_1877385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 2, 2, 1, 4].length) (baseStart_1877385 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1877385 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1877385 prefixEnd_1877385 := by exact prefixLift 1877385
  have htrace : WordTrace (prefixWord ++ tailWord_1877385) baseStart_1877385 baseEnd_1877385 := by
    simpa [prefixWord, tailWord_1877385, baseEnd_1877385] using wordTrace_append hprefix tailTrace_1877385
  have hstable : (prefixWord ++ tailWord_1877385).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877385).length < 2 ^ (prefixWord ++ tailWord_1877385).sum := by decide
  have hdescent : baseEnd_1877385 < baseStart_1877385 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877444 : List Nat := [2, 3, 3, 2, 1, 1, 2, 3, 4]
def baseStart_1877444 : Nat := 118140960795 + 1877444 * 2 ^ 59
def prefixEnd_1877444 : Nat := 4983230072969 + 3 ^ 40 * 1877444 * 2
def baseEnd_1877444 : Nat := 428458299511047877962577

theorem tailTrace_1877444 : CollatzResearch.WordTrace tailWord_1877444 prefixEnd_1877444 428458299511047877962577 := by
  unfold tailWord_1877444
  simp only [CollatzResearch.WordTrace]
  refine ⟨34238004105174252376351693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45650672140232336501802257 34238004105174252376351693)
  ·
    refine ⟨12839251539440344641131885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 34238004105174252376351693 12839251539440344641131885)
    ·
      refine ⟨4814719327290129240424457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12839251539440344641131885 4814719327290129240424457)
      ·
        refine ⟨3611039495467596930318343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4814719327290129240424457 3611039495467596930318343)
        ·
          refine ⟨5416559243201395395477515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3611039495467596930318343 5416559243201395395477515)
          ·
            refine ⟨8124838864802093093216273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5416559243201395395477515 8124838864802093093216273)
            ·
              refine ⟨6093629148601569819912205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8124838864802093093216273 6093629148601569819912205)
              ·
                refine ⟨2285110930725588682467077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6093629148601569819912205 2285110930725588682467077)
                ·
                  refine ⟨428458299511047877962577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2285110930725588682467077 428458299511047877962577)
                  ·
                    rfl

theorem cell21_1877444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 4].length) (baseStart_1877444 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1877444 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1877444 prefixEnd_1877444 := by exact prefixLift 1877444
  have htrace : WordTrace (prefixWord ++ tailWord_1877444) baseStart_1877444 baseEnd_1877444 := by
    simpa [prefixWord, tailWord_1877444, baseEnd_1877444] using wordTrace_append hprefix tailTrace_1877444
  have hstable : (prefixWord ++ tailWord_1877444).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877444).length < 2 ^ (prefixWord ++ tailWord_1877444).sum := by decide
  have hdescent : baseEnd_1877444 < baseStart_1877444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877455 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 7]
def baseStart_1877455 : Nat := 118140960795 + 1877455 * 2 ^ 59
def prefixEnd_1877455 : Nat := 4983230072969 + 3 ^ 40 * 1877455 * 2
def baseEnd_1877455 : Nat := 428460809860914303279221

theorem tailTrace_1877455 : CollatzResearch.WordTrace tailWord_1877455 prefixEnd_1877455 428460809860914303279221 := by
  unfold tailWord_1877455
  simp only [CollatzResearch.WordTrace]
  refine ⟨68476409413308653631353819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45650939608872435754235879 68476409413308653631353819)
  ·
    refine ⟨102714614119962980447030729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 68476409413308653631353819 102714614119962980447030729)
    ·
      refine ⟨77035960589972235335273047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 102714614119962980447030729 77035960589972235335273047)
      ·
        refine ⟨115553940884958353002909571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 77035960589972235335273047 115553940884958353002909571)
        ·
          refine ⟨173330911327437529504364357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 115553940884958353002909571 173330911327437529504364357)
          ·
            refine ⟨32499545873894536782068317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 173330911327437529504364357 32499545873894536782068317)
            ·
              refine ⟨12187329702710451293275619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 32499545873894536782068317 12187329702710451293275619)
              ·
                refine ⟨18280994554065676939913429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 12187329702710451293275619 18280994554065676939913429)
                ·
                  refine ⟨428460809860914303279221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 18280994554065676939913429 428460809860914303279221)
                  ·
                    rfl

theorem cell21_1877455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 7].length) (baseStart_1877455 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1877455 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1877455 prefixEnd_1877455 := by exact prefixLift 1877455
  have htrace : WordTrace (prefixWord ++ tailWord_1877455) baseStart_1877455 baseEnd_1877455 := by
    simpa [prefixWord, tailWord_1877455, baseEnd_1877455] using wordTrace_append hprefix tailTrace_1877455
  have hstable : (prefixWord ++ tailWord_1877455).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877455).length < 2 ^ (prefixWord ++ tailWord_1877455).sum := by decide
  have hdescent : baseEnd_1877455 < baseStart_1877455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877489 : List Nat := [1, 2, 2, 2, 3, 2, 2, 4, 3]
def baseStart_1877489 : Nat := 118140960795 + 1877489 * 2 ^ 59
def prefixEnd_1877489 : Nat := 4983230072969 + 3 ^ 40 * 1877489 * 2
def baseEnd_1877489 : Nat := 428468569124137799712485

theorem tailTrace_1877489 : CollatzResearch.WordTrace tailWord_1877489 prefixEnd_1877489 428468569124137799712485 := by
  unfold tailWord_1877489
  simp only [CollatzResearch.WordTrace]
  refine ⟨68477649495185477438091521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 45651766330123651625394347 68477649495185477438091521)
  ·
    refine ⟨51358237121389108078568641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 68477649495185477438091521 51358237121389108078568641)
    ·
      refine ⟨38518677841041831058926481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 51358237121389108078568641 38518677841041831058926481)
      ·
        refine ⟨28889008380781373294194861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 38518677841041831058926481 28889008380781373294194861)
        ·
          refine ⟨10833378142793014985323073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 28889008380781373294194861 10833378142793014985323073)
          ·
            refine ⟨8125033607094761238992305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10833378142793014985323073 8125033607094761238992305)
            ·
              refine ⟨6093775205321070929244229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8125033607094761238992305 6093775205321070929244229)
              ·
                refine ⟨1142582850997700799233293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6093775205321070929244229 1142582850997700799233293)
                ·
                  refine ⟨428468569124137799712485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1142582850997700799233293 428468569124137799712485)
                  ·
                    rfl

theorem cell21_1877489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 3].length) (baseStart_1877489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1877489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1877489 prefixEnd_1877489 := by exact prefixLift 1877489
  have htrace : WordTrace (prefixWord ++ tailWord_1877489) baseStart_1877489 baseEnd_1877489 := by
    simpa [prefixWord, tailWord_1877489, baseEnd_1877489] using wordTrace_append hprefix tailTrace_1877489
  have hstable : (prefixWord ++ tailWord_1877489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877489).length < 2 ^ (prefixWord ++ tailWord_1877489).sum := by decide
  have hdescent : baseEnd_1877489 < baseStart_1877489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1877596 : List Nat := [2, 2, 4, 1, 2, 2, 2, 2, 4]
def baseStart_1877596 : Nat := 118140960795 + 1877596 * 2 ^ 59
def prefixEnd_1877596 : Nat := 4983230072969 + 3 ^ 40 * 1877596 * 2
def baseEnd_1877596 : Nat := 428492987981929391428933

theorem tailTrace_1877596 : CollatzResearch.WordTrace tailWord_1877596 prefixEnd_1877596 428492987981929391428933 := by
  unfold tailWord_1877596
  simp only [CollatzResearch.WordTrace]
  refine ⟨34240776052898917356118321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 45654368070531889808157761 34240776052898917356118321)
  ·
    refine ⟨25680582039674188017088741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 34240776052898917356118321 25680582039674188017088741)
    ·
      refine ⟨4815109132438910253204139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 25680582039674188017088741 4815109132438910253204139)
      ·
        refine ⟨7222663698658365379806209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4815109132438910253204139 7222663698658365379806209)
        ·
          refine ⟨5416997773993774034854657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7222663698658365379806209 5416997773993774034854657)
          ·
            refine ⟨4062748330495330526140993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5416997773993774034854657 4062748330495330526140993)
            ·
              refine ⟨3047061247871497894605745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4062748330495330526140993 3047061247871497894605745)
              ·
                refine ⟨2285295935903623420954309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3047061247871497894605745 2285295935903623420954309)
                ·
                  refine ⟨428492987981929391428933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2285295935903623420954309 428492987981929391428933)
                  ·
                    rfl

theorem cell21_1877596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_1877596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1877596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1877596 prefixEnd_1877596 := by exact prefixLift 1877596
  have htrace : WordTrace (prefixWord ++ tailWord_1877596) baseStart_1877596 baseEnd_1877596 := by
    simpa [prefixWord, tailWord_1877596, baseEnd_1877596] using wordTrace_append hprefix tailTrace_1877596
  have hstable : (prefixWord ++ tailWord_1877596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1877596).length < 2 ^ (prefixWord ++ tailWord_1877596).sum := by decide
  have hdescent : baseEnd_1877596 < baseStart_1877596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1877596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
